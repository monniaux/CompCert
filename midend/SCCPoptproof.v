Require Import Coqlib.
Require Import Maps.
Require Import Maps2.
Require Import AST.
Require Import Op.
Require Import Utils.
Require Import Integers.
Require Import Floats.
Require Import Classical.
Require Import Dom.
Require Import SSA.
Require Import SSAtool.
Require Import SSAutils.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Values.
Require Import Events.
Require Import SCCPopt.
Require Import ConstpropOp.
Require Import ConstpropOpproofSSA.
Require Import DLib.
Require Import Utilsvalidproof.
Require Import KildallComp.
Require Import Dsd.
Require Import Relations.
Require Import SSAtoolinv.
Require Import OptInv.
Require Import SCCPopt.
Require Import SCCPoptProp.

(** Final correctness proof (semantics preservation) of the SCCP optimization *)

Section PRESERVATION.

Hint Unfold exec.

Variable prog: program.

Definition tprog := transf_program prog.
Definition ge := Genv.globalenv prog.
Definition tge := Genv.globalenv tprog.

(** * Simulation relation *)
  Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil: match_stackframes nil nil
  | match_stackframes_cons:
    forall res f sp pc rs s st
      (STACK: (match_stackframes s st))
      (HG:forall v, gamma SCCP f ge sp pc (rs#2 res <- v))
      (EXE: exec f pc),
      match_stackframes
      ((Stackframe res f sp pc rs) :: s)
      ((Stackframe res (transf_function f) sp pc rs) :: st).

  Inductive match_states: SSAtool.state -> SSAtool.state -> Prop :=
  | match_states_intro:
      forall s st sp pc rs m f
        (SINV:s_inv ge (State s f sp pc rs m))
        (HG:gamma SCCP f ge sp pc rs)
        (EXE: exec f pc)
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

(** * Auxiliary, easy lemmas *)
Lemma same_symbols: forall s,
  Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold tge, ge, tprog, transf_program.
  apply Genv.find_symbol_transf.
Qed.

Lemma same_varinfo:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, transf_program.
  apply Genv.find_var_info_transf.
Qed.

Hint Resolve same_varinfo.
Hint Resolve same_symbols.

Lemma same_eval_addressing: forall sp addr rs args,
  eval_addressing tge sp addr rs ##2 args = eval_addressing ge sp addr rs ##2 args.
Proof.
  intros.
  unfold eval_addressing, symbol_address.
  flatten; rewrite <- same_symbols in *; eauto; flatten.
Qed.

Lemma same_eval: forall sp op rs args m,
  eval_operation tge sp op rs ##2 args m = eval_operation ge sp op rs ##2 args m.
Proof.
  intros.
  unfold eval_operation. flatten. unfold symbol_address. rewrite same_symbols. auto.
  unfold eval_addressing. flatten; unfold symbol_address; rewrite same_symbols; auto.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf transf_fundef prog).
Qed.

Lemma funct_ptr_translated:
  forall (b: Values.block) (f: fundef),
    Genv.find_funct_ptr ge b = Some f ->
    Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  exact (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).
Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f;  simpl ; try reflexivity.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros.
  exact (Genv.find_funct_transf transf_fundef _ _ H).
Qed.

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  intros.
  exact (Genv.find_funct_ptr_transf transf_fundef _ _ H).
Qed.

Hint Resolve sdom_dom_pred fn_code_reached fn_entry_pred fn_phicode_inv
             list_nth_z_in.
Hint Constructors clos_refl_trans SSA.step.

Lemma transf_ros_correct:
  forall ros rs f,
  find_function ge ros rs = Some f ->
  find_function tge ros rs = Some (transf_fundef f).
Proof.
  intros.
  unfold find_function in *.
  destruct ros; simpl.
  exploit functions_translated; eauto.
  flatten; rewrite same_symbols in *;
  rewrite Eq in *; eauto using function_ptr_translated.
  inv H.
Qed.

Lemma match_stackframes_sfg_inv : forall s st,
  match_stackframes s st ->
  sfg_inv SCCP prog s.
Proof.
  induction 1 ; go.
Qed.

(** * Soundness invariant of the analysis *)
Lemma subj_red_gamma : forall prog,
       forall (f f':function) t m m' rs rs' sp sp' pc pc' s s',
       gamma SCCP f (Genv.globalenv prog) sp pc rs ->
       sfg_inv SCCP prog s ->
       exec f pc ->
       s_inv (Genv.globalenv prog) (State s f sp pc rs m) ->
       SSAtool.step (Genv.globalenv prog) (State s f sp pc rs m) t
         (State s' f' sp' pc' rs' m') ->
       gamma SCCP f' (Genv.globalenv prog) sp' pc' rs'.
Proof.
  intros.
  eapply subj_red_gamma; eauto.
  - intros; eapply same_fn_code1; eauto.
    apply f0.
  - intros; eapply Iop_correct; eauto.
  - intros; eapply step_phi_aux; eauto.
  - intros. eapply exec_step; eauto.
    apply f0.
Qed.

(** * Proof of the simulation *)
Lemma transf_initial_states:
  forall st1, SSAtool.initial_state prog st1 ->
    exists st2, SSAtool.initial_state tprog st2 /\ match_states st1 st2.
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
  match_states st1 st2 -> SSAtool.final_state st1 r -> SSAtool.final_state st2 r.
Proof.
  intros. invh match_states; invh SSAtool.final_state.
  inv SINV. inv SFINV.
  inv STACK. constructor.
Qed.


Hint Resolve match_stackframes_sfg_inv
             subj_red subj_red_gamma.

Ltac match_go :=
  match goal with
    | id: SSAtool.step _ _ _ _ |- match_states _ _  =>
      econstructor; eauto ; [eapply SSAtoolinv.subj_red; eauto
                            | eapply subj_red_gamma; eauto
                            | eapply exec_step in id; eauto]
  end.

Ltac TransfInstr :=
    match goal with
      | f : function,
        id: (fn_code _)! ?pc = Some ?instr |- _ =>
    case_eq (DS.fixpoint f handle_instr (initial f) f) ;
      intros lv es FIX;
      set (lv' := fun reg => P2Map.get reg lv) in * ;
      assert ((fn_code (transf_function f)) !pc = Some(transf_instr lv' pc instr))
        by (unfold transf_function, Opt.transf_function, fn_code;
            simpl; rewrite PTree.gmap; try rewrite FIX;
            unfold option_map; rewrite id; reflexivity);
      simpl transf_instr in *
    end.

Lemma transf_step_correct:
  forall s1 t s2,
  SSAtool.step ge s1 t s2 ->
  SSAtool.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', SSAtool.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  intros s1 t s2.

  induction 1; intros; inv MS; auto.
  (* Inop *)
  - exists (State st (transf_function f) sp pc' rs m).
    split; try match_go.
    TransfInstr.
    eapply exec_Inop_njp; eauto.
    intro Hcont.
    erewrite join_point_transf_function in Hcont ; go.
    apply f.
  (* Inop phi *)
  - exists (State st (transf_function f) sp pc' (phi_store k phib rs) m).
    split; try match_go.
    TransfInstr.
    eapply exec_Inop_jp; eauto.
    erewrite join_point_transf_function; go.
    rewrite make_predecessors_transf_function; auto.
    apply f.
  (* Iop *)
  - exists (State st (transf_function f) sp pc' rs #2 res <- v m).
    split; try match_go.
    TransfInstr.
    flatten H2; try ( eapply exec_Iop; eauto; rewrite same_eval; auto);
    (assert (val_match_approx ge sp (CO.eval_static_operation op lv ##2 args) v); [
      eapply eval_static_operation_correct; eauto;
      eapply G_list_val_list_match_approx; eauto;
      eapply gamma_v_args; eauto

    | replace (lv##2 args) with (map (fun r : reg => lv' r) args)
               in * by (induction args; go);
      rewrite Eq  in H3 at 1;
      inv H3; auto
    ]).
    apply f.
    apply f.
    apply f.

  - exists (State st (transf_function f) sp pc' rs #2 dst <- v m).
    split; try match_go.
    TransfInstr.
    eapply exec_Iload; eauto. rewrite same_eval_addressing. auto.
    apply f.

  - exists (State st (transf_function f) sp pc' rs m').
    split; try match_go.
    TransfInstr. eapply exec_Istore; eauto. rewrite same_eval_addressing; auto.
    apply f.

  - exists (Callstate (Stackframe res (transf_function f) sp pc' rs::st)
                      (transf_fundef fd) rs ##2 args m); split.
    + TransfInstr; intros.
      eapply exec_Icall; eauto.
      rewrite transf_ros_correct with (f := fd); eauto.
      unfold funsig, transf_fundef.
      destruct fd; simpl; eauto.

    + assert (WF:=wf f).
      econstructor; eauto.
      * eapply SSAtoolinv.subj_red; eauto.
      * constructor; eauto.
        { intros v x Hyp1 Hyp2.
          { destruct (p2eq x res).
            - subst. exploit (same_fn_code1 f pc); go.
              eapply G_top; eauto.
            - rewrite P2Map.gso; auto.
              exploit (HG x); eauto.
              unfold fn_code in *.
              destruct dsd_pred_njp with f pc pc' x as
                  [[Dx Dx']|[[Dx [Dx' Dx'']]|[Dx Dx']]]; simplify_dsd; eauto.
              intro; subst; exploit fn_entry; eauto; intros (succ' & Hscucc);
              congruence.
              go.
              eelim ssa_not_Inop_not_phi; eauto; go.
          }
        }
       eapply exec_step in H2; eauto.

  - exists (Callstate st (transf_fundef fd) rs ##2 args m'); split; try match_go.
    + TransfInstr; intros.
      eapply exec_Itailcall; eauto.
      rewrite transf_ros_correct with (f := fd); eauto.
      unfold funsig, transf_fundef.
      destruct fd; simpl; eauto; unfold transf_function.

    + econstructor; eauto.
      eapply SSAtoolinv.subj_red; eauto.

  - exists (State st (transf_function f) sp pc' rs #2 res <- v m').
    split; try match_go.
    TransfInstr.
    eapply exec_Ibuiltin; eauto.
    eapply external_call_symbols_preserved; eauto.
    apply f.

  - exists (State st (transf_function f) sp ifso rs m).
    split; try match_go.
    TransfInstr. eapply exec_Icond_true; eauto.
    apply f.

  - exists (State st (transf_function f) sp ifnot rs m).
    split; try match_go.
    TransfInstr. eapply exec_Icond_false; eauto.
    apply f.

  - exists (State st (transf_function f) sp pc' rs m).
    split; try match_go.
    TransfInstr. eapply exec_Ijumptable; eauto.
    apply f.

  - exists (Returnstate st (regmap2_optget or Vundef rs) m'); split; try match_go.
    + TransfInstr.    econstructor; eauto.

    + econstructor; eauto.
      eapply SSAtoolinv.subj_red; eauto.

  - assert (WF:=wf f).
    exists (State st (transf_function f) (Vptr stk Int.zero)
                  (fn_entrypoint (transf_function f))
                  (init_regs args (fn_params (transf_function f))) m');
      split; try match_go.
    + econstructor; eauto.
    + replace (fn_entrypoint (transf_function f)) with (fn_entrypoint f).
      replace (fn_params (transf_function f)) with (fn_params f).
      econstructor; eauto. 
      eapply SSAtoolinv.subj_red; eauto.
      eapply gamma_entry; eauto.
      go.
      compute; reflexivity.
      compute; reflexivity.
      
  - exists (Returnstate st res m'); split.
    + econstructor; eauto.
      eapply external_call_symbols_preserved; eauto.
    + econstructor; eauto.
      eapply SSAtoolinv.subj_red; eauto.

  - inv STACK.
    exists (State st0 (transf_function f) sp pc rs #2 res <- vres m); split; go.
    econstructor; eauto.
    eapply SSAtoolinv.subj_red; eauto.
Qed.


Theorem transf_program_correct:
  forward_simulation (SSAtool.semantics prog) (SSAtool.semantics tprog).
Proof.
  eapply forward_simulation_step.
  eexact same_symbols.
  eexact transf_initial_states.
  eexact transf_final_states.
  intros; eapply transf_step_correct; eauto.
Qed.

End PRESERVATION.
