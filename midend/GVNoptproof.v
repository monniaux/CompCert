Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import SSA. 
Require Import SSAtool. 
Require Import SSAutils. 
Require Import SSAtoolinv. 
Require Import Utilsvalidproof.
Require Import DomCompute.
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.
Require Import Bijection.
Require Import Dsd.
Require Import OptInv.
Require Import GVNopt.
Require Import GVNoptProp.
Require Import DLib.
     
(** * Correctness of the optimization *)

Section subject_reduction.

  Variable prog: program.
  Let tprog := transf_program prog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_transf transf_fundef prog).

  Lemma varinfo_preserved:
    forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
  Proof (Genv.find_var_info_transf transf_fundef prog).

  Lemma funct_ptr_translated:
    forall (b: Values.block) (f: fundef),
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef f).
  Proof (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).

  Lemma functions_translated:
    forall (v: val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      Genv.find_funct tge v = Some (transf_fundef f).
  Proof (@Genv.find_funct_transf _ _ _ transf_fundef prog).

  Lemma sig_preserved:
    forall f, funsig (transf_fundef f) = funsig f.
  Proof.
    destruct f;  simpl ; try reflexivity.
  Qed.

  Lemma find_function_translated:
    forall ros rs f,
      find_function ge ros rs = Some f ->
      find_function tge ros rs = Some (transf_fundef f).
  Proof.
    intros until f; destruct ros; simpl.
    intro. apply functions_translated; auto.
    rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intro.
    apply funct_ptr_translated; auto.
    discriminate.
  Qed.
  
  Lemma fn_params_translated : forall (f:function), 
     fn_params f = fn_params (transf_function f).
  Proof.
    intros ; unfold transf_function ; simpl; auto.
  Qed.

  Lemma fn_entrypoint_translated : forall (f:function),
     fn_entrypoint f = fn_entrypoint (transf_function f).
  Proof.
    intros ; unfold transf_function ; simpl; auto.
  Qed.

  Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil: match_stackframes nil nil
  | match_stackframes_cons: 
    forall res (f:function) sp pc rs s st 
      (STACK: (match_stackframes s st))
      (WFF: wf_ssa_function f)
      (HG:forall v, gamma GVN f ge sp pc (rs#2 res <- v))
      (EXE: exec f pc),
      match_stackframes
      ((Stackframe res f sp pc rs) :: s)
      ((Stackframe res (transf_function f) sp pc rs) :: st).

  Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s st sp pc rs m f
        (SINV:s_inv ge (State s f sp pc rs m))
        (HG:gamma GVN f ge sp pc rs)
        (EXE: exec  f pc)
        (STACK: match_stackframes s st),
        match_states (State s f sp pc rs m) (State st (transf_function f) sp pc rs m)
  | match_states_call:
      forall s st f args m
        (SINV:s_inv ge (Callstate s f args m))
        (STACK: match_stackframes s st),
        match_states (Callstate s f args m) (Callstate st (transf_fundef f) args m)
  | match_states_return:
      forall s st v m 
        (SINV:s_inv ge (Returnstate s v m))
        (STACK: match_stackframes s st),
        match_states (Returnstate s v m) (Returnstate st v m).

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
    exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto.
  apply Genv.init_mem_transf; auto.
  change (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  apply funct_ptr_translated; auto.
  rewrite <- H3. apply sig_preserved. 
  go.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. 
  inv STACK.
  constructor.
Qed.

Lemma same_fn_code: forall f pc,
  (forall op args res pc',
    (fn_code f) ! pc <> Some (Iop op args res pc')) ->
    (fn_code (transf_function f)) ! pc = (fn_code f) ! pc.
Proof.
  intros.
  unfold transf_function, Opt.transf_function.
  case_eq (analysis f); intros; simpl.
  destruct p; simpl.
  unfold transf_instr, Opt.transf_function_tool, fn_code; simpl.
  rewrite PTree.gmap; simpl.
  unfold fn_code in *.
  destruct ((SSA.fn_code f) ! pc); simpl; auto.
  destruct i; auto.
  flatten.
Qed.

Lemma new_fn_code: forall f pc op args res pc',
  (fn_code f) ! pc = Some (Iop op args res pc') ->
  ((fn_code (transf_function f)) ! pc = Some (Iop op args res pc'))
  \/ (exists res',
        (fn_code (transf_function f)) ! pc = Some (Iop Omove (res' :: nil) res pc')
        /\ A_r f res = res' 
        /\ res <> res').
Proof. 
  intros.
  generalize H ; intros INSTR.
  unfold transf_function, Opt.transf_function, fn_code.
  case_eq (analysis f) ; intros lv es ANA; simpl.
  unfold analysis in *. inv ANA.
  erewrite PTree.gmap. 
  unfold transf_instr. rewrite INSTR; simpl.
  flatten; go.
  right. exists r. simpl; repeat split; auto.
  intro Hcont; subst.
  eapply andb_true_iff in Eq1; eauto; invh and.
  eapply andb_true_iff in H0; eauto; invh and.
  destruct (p2eq r r); intuition.
Qed.

Hint Constructors ext_params dsd.

Require Opt.
Require OptInv.

Lemma join_point_transf_function : forall f j,
  join_point j (transf_function f) <-> join_point j f.
Proof.
  intros.
  eapply Opt.join_point_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
  apply f.
Qed.   

Lemma successors_transf_function: forall f  pc,
  (successors (transf_function f))!pc = (successors f)!pc.
Proof.
  intros.
  eapply Opt.successors_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
  apply f.
Qed.
  
Lemma make_predecessors_transf_function: forall f,
  (Kildall.make_predecessors (fn_code (transf_function f)) successors_instr) =
  (Kildall.make_predecessors (fn_code f) successors_instr).
Proof.
  intros.
  eapply Opt.make_predecessors_transf_function; eauto.
  eapply new_code_same_or_Iop; eauto.
  apply f.
Qed. 


Lemma eval_iop_correct : forall f m res rs sp v pc pc' args op s,
   exec f pc ->
   gamma GVN f ge sp pc rs ->
   eval_operation ge sp op rs ##2 args m = Some v ->
   s_inv ge (State s f sp pc rs m) ->
   (fn_code f) ! pc = Some (Iop op args res pc') ->
   (fn_code (transf_function f)) ! pc = Some (Iop Omove (A_r f res :: nil) res pc') ->
   res <> A_r f res ->
   eval_operation tge sp Omove rs ##2 (A_r f res :: nil) m = Some v.
Proof.
  intros until s. intros EXE HG EVAL SINV CODE TCODE COND. 
  assert (WF:=wf f).
  assert (GG:= GVN_spec_True f); destruct GG as [Hc Hp  _].
  specialize Hc with pc.
  unfold repr_spec_code in *.
  rewrite CODE in *. repeat invh or ; repeat invh ex ; repeat invh and.
  - congruence.
  - assert (HE:[f,ge,sp,rs]|=(A_r f res)==(Iop op x1 (A_r f res) x0))
      by (inv SINV; eapply SINV0 ; eauto). 
    inv HE. invh SSAtoolinv.eval.
    assert (G_list GVN ge sp rs (map (A_r f) args) (rs##2 args))
      by (eapply gamma_v_args; eauto).
    assert (G_list GVN ge sp rs (map (A_r f) x1) (rs##2 x1)).
    { assert (gamma GVN f ge sp x rs) by (eapply  gamma_sdom_gamma; eauto).
      eapply gamma_v_args in H; go.
      auto. 
      go.
    }             
    assert (map (A_r f) x1 = map (A_r f) args)
      by (symmetry; eapply same_repr_map; eauto).
    rewrite <- EVAL.
    simpl. simpl in EVAL0.
    rewrite <- EVAL0.
    rewrite op_depends_on_memory_correct with (m2:= m); auto.
    rewrite H7 in *. eapply G_list_eval_op; eauto.
Qed.

Lemma match_stackframes_sfg_inv : forall s st, 
  match_stackframes s st ->
  sfg_inv GVN prog s.
Proof.
  induction 1 ; go.
Qed.

Hint Resolve match_stackframes_sfg_inv.

Lemma subj_red_gamma : forall prog,
       forall (f f' : function) (t : trace) (m m' : mem) 
         (rs rs' : regset) (sp sp' : val) (pc pc' : node)
         (s s' : list stackframe),
       gamma GVN f (Genv.globalenv prog) sp pc rs ->
       sfg_inv GVN prog s ->
       exec f pc ->
       s_inv (Genv.globalenv prog) (State s f sp pc rs m) ->
       step (Genv.globalenv prog) (State s f sp pc rs m) t
         (State s' f' sp' pc' rs' m') ->
       gamma GVN f' (Genv.globalenv prog) sp' pc' rs'.
Proof.
  intros. 
  eapply subj_red_gamma; eauto.
  - intros. eapply same_fn_code1; eauto.
  - intros; eapply G_upd_diff; eauto.
  - intros; eapply approx_Iop_correct; eauto.
  - intros; eapply gamma_step_phi; eauto.    
  - intros; flatten ; go.
Qed. 

Lemma transl_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  assert (Hwf1: forall s f sp pc rs m, s_inv ge (State s f sp pc rs m) ->
                 wf_ssa_function f) by (intros s f sp pc rs m H; inv H; auto).

  induction 1; intros; inv MS; auto.

  -  (* Inop not jnp *)
  exists (State st (transf_function f) sp pc' rs m); split;
    [idtac  | econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|eauto|eauto]]; 
    try solve [eapply subj_red_gamma; eauto].
  eapply exec_Inop_njp; eauto.
  rewrite same_fn_code; [auto|congruence].
  rewrite join_point_transf_function; auto. 

  - (* Inop jnp *)
  exists (State st (transf_function f) sp pc' (phi_store k phib rs) m); split;
      [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|eauto|eauto]];
      try solve [eapply subj_red_gamma; eauto].
  eapply exec_Inop_jp; eauto.
  rewrite same_fn_code; [auto|congruence].
  rewrite join_point_transf_function; auto.
  rewrite make_predecessors_transf_function; auto. 
  
  - (* Iop *)
  exists (State st (transf_function f) sp pc' rs#2 res<-v  m); split;
      [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|eauto|eauto]];
      try solve [eapply subj_red_gamma; eauto].
  exploit new_fn_code; eauto; destruct 1 as [Hi|[res' [d [Hi2 Hi3]]]]. 
         + eapply exec_Iop; eauto.
           erewrite eval_operation_preserved; eauto.
           apply symbols_preserved; auto.
         + eapply exec_Iop; eauto. subst.
           eapply eval_iop_correct; eauto.

  - (* Iload *) 
    exists (State st (transf_function f) sp pc' rs#2 dst<-v m); split;
      [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|auto|eauto]];
      try solve [eapply subj_red_gamma; eauto].
    eapply exec_Iload; eauto.
    rewrite same_fn_code; [eauto|congruence].       
    erewrite eval_addressing_preserved; eauto.  
    apply symbols_preserved; auto.
    
  - (* Istore *) 
    exists (State st (transf_function f) sp pc' rs m'); split;
           [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|eauto|eauto;fail]];
           try solve [eapply subj_red_gamma; eauto].
    eapply exec_Istore; eauto.
    rewrite same_fn_code; [eauto|congruence].
    erewrite eval_addressing_preserved; eauto.  
    apply symbols_preserved; auto.  
           
  - (* Icall *) 
    exists (Callstate (Stackframe res (transf_function f) sp pc' rs :: st)
                      (transf_fundef fd) rs ##2 args m); split;
           [idtac| econstructor; [try eapply subj_red_gamma; eauto|econstructor; auto]].
     + eapply exec_Icall with (ros := ros); eauto.
       rewrite same_fn_code; [auto | congruence]. 
       simpl; rewrite sig_preserved; eauto. 
       eapply find_function_translated; eauto.
     + eapply SSAtoolinv.subj_red; eauto. 
     + apply f.
     + intros v x Hyp1 Hyp2.
        { destruct (p2eq x res).
          - subst. exploit (same_fn_code1 f pc); go. 
            eapply G_top; eauto. 
          - rewrite P2Map.gso; auto.
            unfold fn_code in *.
            exploit (HG x); eauto. 
            * destruct dsd_pred_njp with f pc pc' x as 
                  [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
              intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc); congruence.
              go.
              eelim ssa_not_Inop_not_phi; eauto; go. 
            * intros HG'. inv HG'.
              econstructor; eauto. 
              rewrite P2Map.gso; auto.
              intros Hcont.
              simpl in *. 
              exploit (same_fn_code1 f pc); go.
              unfold fn_code; go.
              intros; invh is_at_Top; go.
        }

  - (* Itailcall *)
  exists (Callstate st (transf_fundef fd) rs ##2 args m'); split.
  eapply exec_Itailcall with (ros := ros); eauto.
  rewrite same_fn_code; [eauto|congruence].
  simpl; rewrite sig_preserved; eauto. 
  eapply find_function_translated; eauto.
  constructor; auto.
  eapply SSAtoolinv.subj_red; eauto.

  - (* Ibuiltin *)
  exists (State st (transf_function f) sp pc' rs #2 res <- v m'); split;
      [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|eauto|eauto]];
      try solve [eapply subj_red_gamma; eauto].
  eapply exec_Ibuiltin; eauto.
  rewrite same_fn_code; [eauto|congruence].
  eapply external_call_symbols_preserved; eauto.
  apply symbols_preserved; auto.
  apply varinfo_preserved; auto.
  
  - (* Icond, true *)
  exists (State st (transf_function f) sp ifso rs m); split;
      [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|auto|eauto|eauto;fail]];
      try solve [eapply subj_red_gamma; eauto].
  eapply exec_Icond_true; eauto.
  rewrite same_fn_code; [eauto|congruence].
  
  - (* Icond, false *)
  exists (State st (transf_function f) sp ifnot rs m); split;
      [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|eauto|eauto;fail]];
      try solve [eapply subj_red_gamma; eauto].
  eapply exec_Icond_false; eauto.
  rewrite same_fn_code; [eauto|congruence].

  - (* Ijumptable *)
  exists (State st (transf_function f) sp pc' rs m); split;
      [idtac| econstructor; [eapply SSAtoolinv.subj_red; eauto|eauto|eauto|eauto;fail]];
      try solve [eapply subj_red_gamma; eauto].
  eapply exec_Ijumptable; eauto. 
  rewrite same_fn_code; [eauto|congruence].
  
  - (* Ireturn *)
  exists (Returnstate st (regmap2_optget or Vundef rs) m'); split;
      [idtac| econstructor; eauto].  
  econstructor; eauto.
  rewrite same_fn_code; [eauto|congruence].
  eapply SSAtoolinv.subj_red; eauto.

  - (* internal function *)
  assert (WF:=wf f).
  exists (State st (transf_function f) (Vptr stk Int.zero) 
                (fn_entrypoint (transf_function f)) 
                (init_regs args (fn_params (transf_function f))) m'); split.
  + econstructor; eauto.
  + rewrite <- fn_entrypoint_translated; eauto.
    rewrite <- fn_params_translated; eauto.
    econstructor; eauto.
    * eapply SSAtoolinv.subj_red; eauto.
    * unfold gamma in *; intros x Hyp1.
      exploit ssa_dsd_entry ; eauto.
      intros. 
      exploit gamma_entry; eauto.
    * go.  
      
  - (* external function *)
  exists (Returnstate st res m'); split.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  eapply SSAtoolinv.subj_red; eauto.

  - (* return *)
  inv STACK.
  exists (State st0 (transf_function f) sp pc rs #2 res <- vres m); split.
  econstructor; eauto.
  econstructor; eauto.
  eapply SSAtoolinv.subj_red; eauto.
Qed.

(** * Semantics preservation *)
Theorem transf_program_correct:
  forward_simulation (SSAtool.semantics prog) (SSAtool.semantics tprog).
Proof.
  eapply forward_simulation_step.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  intros; eauto using transl_step_correct. 
Qed.

End subject_reduction.
