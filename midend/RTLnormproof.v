(** Correctness proof for the RTL normalization phase. *)
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import Smallstep.
Require Import RTL.
Require Import RTLnorm.
Require Import RTLnormspec.
Require Import Kildall.
Require Import Conventions.
Require Import Utils.
Require Import Events.

Section PRESERVATION.

Variable prog: RTL.program.
Variable tprog: RTL.program.
Hypothesis TRANSF_PROG: transl_program_opt prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

  
Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with transl_fundef_opt.
  exact TRANSF_PROG.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef_opt f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_transf_partial transl_fundef_opt). 
  exact TRANSF_PROG.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef_opt f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_ptr_transf_partial transl_fundef_opt).
  exact TRANSF_PROG.
Qed.

Lemma var_info_preserved:
  forall (b: block), Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_var_info_transf_partial with transl_fundef_opt.
  exact TRANSF_PROG.
Qed.

Lemma sig_fundef_translated:
  forall f tf,
  transl_fundef_opt f = Errors.OK tf ->
  funsig tf = RTL.funsig f.
Proof.
  intros f tf. intros.
  destruct f ; simpl in *. Errors.monadInv H.
  eapply transl_function_opt_charact in EQ ; eauto.
  inv EQ. 
  simpl; auto.
  inv H.
  simpl; auto.
Qed.

Lemma find_function_preserved_same : forall r rs f f', 
  find_function ge (inl ident r) rs = Some f ->
  find_function tge (inl ident r) rs = Some f' ->
  funsig f = funsig f'.
Proof.
  intros. simpl in *.
  exploit (functions_translated rs#r) ; eauto.
  intros.
  destruct H1 as [tf [Htf Oktf]].
  symmetry.
  eapply sig_fundef_translated; eauto.
  rewrite Htf in H0. inv H0; auto.
Qed.

Lemma sig_function_translated:
  forall f tf,
  transl_function_opt f = Errors.OK tf ->
  fn_sig tf = RTL.fn_sig f.
Proof.
  intros f tf. destruct f; simpl; intros.
  eapply transl_function_opt_charact in H ; eauto.
  inv H.
  simpl; auto.
Qed. 

Lemma spec_ros_r_find_function:
  forall rs f r,
  RTL.find_function ge (inl _ r) rs = Some f ->
  exists tf,
     RTL.find_function tge (inl _ r) rs = Some tf
  /\ transl_fundef_opt f = Errors.OK tf.
Proof.
  intros.
  eapply functions_translated; eauto.
Qed.

Lemma spec_ros_id_find_function:
  forall rs f id,
  RTL.find_function ge (inr _ id) rs = Some f ->
  exists tf,
     RTL.find_function tge (inr _ id) rs = Some tf
  /\ transl_fundef_opt f = Errors.OK tf.
Proof.
  intros.
  simpl in *. 
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Lemma stacksize_preserved: forall f tf, 
  transl_function_opt f = Errors.OK tf -> 
  fn_stacksize f = fn_stacksize tf.
Proof.
  intros.
  eapply transl_function_opt_charact in H ; eauto. inv H. auto.
Qed.

Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
| match_stackframes_nil: match_stackframes nil nil 
| match_stackframes_cons1: 
  forall res f sp pc rs s tf ts 
    (STACK : (match_stackframes s ts))
    (SPEC: (transl_function_opt f = Errors.OK tf)),
    match_stackframes
    ((Stackframe res f sp pc rs) :: s)
    ((Stackframe res tf sp pc rs) :: ts)
| match_stackframes_cons2: 
  forall res f sp pc pc' rs s tf ts
    (STACK : (match_stackframes s ts))
    (SPEC: (transl_function_opt f = Errors.OK tf))
    (NORM: (fn_code tf) ! pc' = Some (Inop pc)),
    match_stackframes
    ((Stackframe res f sp pc rs) :: s)
    ((Stackframe res tf sp pc' rs) :: ts).

Hint Constructors match_stackframes.
Set Implicit Arguments.

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_states_intro:
      forall s ts sp pc rs m f tf
        (SPEC: transl_function_opt f = Errors.OK tf)
        (STACK: match_stackframes s ts),
        match_states (State s f sp pc rs m) (State ts tf sp pc rs m)
  | match_states_call:
      forall s ts f tf args m
        (SPEC: transl_fundef_opt f = Errors.OK tf)
        (STACK: match_stackframes s ts),
        match_states (Callstate s f args m) (Callstate ts tf args m)
  | match_states_return:
      forall s ts v m 
        (STACK: match_stackframes s ts),
        match_states (Returnstate s v m) (Returnstate ts v m).
Hint Constructors match_states.

Lemma transf_initial_states:
  forall st1, RTL.initial_state prog st1 ->
    exists st2, RTL.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial); eauto).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  rewrite symbols_preserved.
  rewrite (transform_partial_program_main _ _ TRANSF_PROG).  auto.
  rewrite <- H3. apply sig_fundef_translated; auto.
  eapply match_states_call  ; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> RTL.final_state st1 r -> RTL.final_state st2 r.
Proof.
  intros. inv H0. inv H. 
  inv STACK.
  constructor.
Qed.

Create HintDb valagree.
Hint Resolve find_function_preserved_same: valagree.
Hint Resolve symbols_preserved : valagree.
Hint Resolve eval_addressing_preserved : valagree.
Hint Resolve eval_operation_preserved : valagree.
Hint Resolve sig_function_translated : valagree.
Hint Resolve sig_fundef_translated : valagree.
Hint Resolve var_info_preserved : valagree.
Hint Resolve stacksize_preserved: valagree.

Lemma add_nop_entry_prop : forall f nentry s1 INCR,
  add_nop_entry (fn_entrypoint f) (init_state f) = OK nentry s1 INCR ->
  (st_code s1) ! (st_entry s1) = Some (Inop (fn_entrypoint f)).
Proof.
  intros.
  unfold add_nop_entry in *; simpl in *.
  inv H; simpl.
  rewrite PTree.gss ; eauto.
Qed.

Lemma transl_function_spec_entry : forall f tf, 
  transl_function_opt f = Errors.OK tf ->
  exists aux, reach_nops (fn_code tf) (fn_entrypoint tf) (fn_entrypoint f) aux.
Proof.
  intros.
  exploit transl_function_opt_charact ; eauto. intros.
  inv H0; simpl in *.
  exploit add_nop_entry_prop ; eauto.
  intros. destruct u.
  assert (reach_nops (st_code s1) (st_entry s1) (fn_entrypoint f) nil).
  constructor ; auto.  
  exploit mfold_unit_prop_entry ; eauto.
  eapply PTree.elements_keys_norepet ; eauto.
  eapply PTree.elements_complete ; eauto.
Qed.

Ltac allinv := 
  repeat 
    match goal with 
      | [H: value ?s = Some ?s' |- _ ] => inv H
      | [ H1:   (fn_code ?tf) ! ?pc = Some _  ,
        H2: (fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   (RTL.fn_code ?tf) ! ?pc = Some _  ,
        H2: (RTL.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | _ => idtac
    end.
  
Ltac normalized pc := 
  match goal with 
    | [NORM : forall (pc: positive) (ins: instruction), _ -> norm ?jp ?code1 ?code2 pc |- _] => 
      let Hpc := fresh "Hpc" in 
        let Hnorm := fresh "Hnorm" in 
        assert (Hpc := NORM pc); clear NORM ; 
          exploit Hpc ; eauto ; clear Hpc ; intro Hnorm ; inv Hnorm ; allinv ; try congruence
  end.
  
Ltac mks := 
  match goal with 
    | [ H : mks_spec ?jp ?code1 ?code2 ?pc ?news ?k
      |- _ ] => (inv H ; allinv) ; (simpl successors_instr in * ; simpl nth_error in *) ; allinv
    | _ => idtac
  end.

Lemma reach_nop_star :  forall ts pt regs m aux x pcx pc,
reach_nops (fn_code x) pcx pc aux ->
star step tge (RTL.State ts x pt pcx regs m) E0 (RTL.State ts x pt pc regs m).
Proof.
  induction aux; intros.
  
  eapply star_step with (s3 := (RTL.State ts x pt pc regs m)) (s2 := (RTL.State ts x pt pc regs m)) (t2:= E0) (t1:= E0) ; eauto. 
  inv H.
  econstructor ; eauto. 
  econstructor ; eauto.
  
  inv H.
  exploit IHaux ; eauto.
  intros.
  econstructor 2 with (t1:= E0) ; eauto.
  econstructor ; eauto.
Qed.  

Lemma transl_step_correct:
  forall s1 t s2,
    step ge s1 t s2 ->
    forall s1' (MS: match_states s1 s1'),
      exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; auto; 
  match goal with 
    | [H : transl_fundef_opt (Internal ?f) = _ |- _ ] => idtac
    | [H : transl_fundef_opt (External ?f) = _ |- _ ] => idtac
    | [  |- context [Returnstate ?ts ?vres ?m]] => idtac
    | _ => 
      ( (exploit transl_function_opt_charact ; eauto; intros);
        (exploit transl_function_spec_ok ; eauto; intros))
  end ;
  match goal with 
    | [SPEC: transl_function_spec ?f ?tf |- _ ] => inv SPEC
    | _ => idtac
  end.
  
  (* inop *)
  normalized pc. 
  exists  (RTL.State ts tf sp s0 rs m). split.
  eapply plus_one ; eauto.
  econstructor 1 ; eauto.
  constructor ; auto.
  
  (* iop *)
  normalized pc. inv H7. assert (Hpc := H8 O pc').  exploit Hpc ; eauto; intros. 
  mks.  

  (* pc ' is join point *)
  exists  (RTL.State ts tf sp succ (rs#res <- v) m). split.
  eapply plus_two with (s2 := (RTL.State ts tf sp pcnew (rs#res <- v) m)) (t1:= E0) (t2:= E0) ; eauto.
  econstructor 2 ; eauto.
  rewrite <- H0 ; eauto with valagree. 
  econstructor 1 ; auto.  constructor ; auto.

  (* pc ' is not join point *)
  exists  (RTL.State ts tf sp succ (rs#res <- v) m). split.
  eapply plus_one ; eauto.  econstructor 2 ; eauto.
  rewrite <- H0 ; eauto with valagree. 
  econstructor 1 ; auto.
  
  (* iload *)
  normalized pc.   inv H8.  assert (Hpc := H9 O pc').   exploit Hpc ; eauto; intros. 
  mks.

  (* pc ' is join point *)
  exists  (RTL.State ts tf sp succ (rs#dst <- v) m). split.
  eapply plus_two with (s2 := (RTL.State ts tf sp pcnew (rs#dst <- v) m)) (t1:= E0) (t2:= E0) ; eauto.
  econstructor 3 ; eauto.
  rewrite <- H0 ; eauto with valagree. 
  econstructor 1 ; auto.
  constructor ; auto.

  (* pc ' is not join point *)
  exists  (RTL.State ts tf sp succ (rs#dst <- v) m). split.
  eapply plus_one ; eauto.   econstructor 3 ; eauto.  rewrite <- H0 ; eauto with valagree. 
  econstructor 1 ; auto.

  (* istore *)
  normalized pc. inv H8. assert (Hpc := H9 O pc').  exploit Hpc ; eauto; intros. 
  mks.

  (* pc ' is join point *)
  exists  (RTL.State ts tf sp succ rs m'). split.
  eapply plus_two with (s2 := (RTL.State ts tf sp pcnew rs m')) (t1:= E0) (t2:= E0) ; eauto.
  econstructor 4 ; eauto.
  rewrite <- H0 ; eauto with valagree. 
  econstructor 1 ; auto.
  constructor ; auto.

  (* pc ' is not join point *)
  exists  (RTL.State ts tf sp succ rs m'). split.
  eapply plus_one ; eauto.  
  econstructor 4 ; eauto.
  rewrite <- H0 ; eauto with valagree. 
  econstructor 1 ; auto.
  
  (* icall *)
  normalized pc. 
  inv H7.
  assert (Hpc := H8 O pc'). 
  exploit Hpc ; eauto; intros. mks.

  (* pc ' is join point *)
  destruct ros; 
    [ exploit spec_ros_r_find_function ; eauto 
      | exploit spec_ros_id_find_function ; eauto] ; 
    (intros; destruct H5 as [tf' [Hfind OKtf']]);
    
    (exists (Callstate (Stackframe res tf sp pcnew rs :: ts) tf' rs ## args m) ; split;
    [   (eapply plus_one ; eauto);
        (eapply exec_Icall  ; eauto); 
        (eauto with valagree)
      |
          (constructor ; auto);
          (econstructor ; eauto);
          (replace (fn_sig tf) with (fn_sig f); eauto); 
          (symmetry ; eauto with valagree)]).
      
  (* pc ' is not join point *)
    destruct ros; 
    [ exploit spec_ros_r_find_function ; eauto 
      | exploit spec_ros_id_find_function ; eauto] ; 
    (intros; destruct H5 as [tf' [Hfind OKtf']]);
    
    (exists (Callstate (Stackframe res tf sp succ rs :: ts) tf' rs ## args m) ; split;
    [   (eapply plus_one ; eauto);
        (eapply exec_Icall  ; eauto); 
        (eauto with valagree)
      |
          (constructor ; auto);
          (econstructor ; eauto);
          (replace (fn_sig tf) with (fn_sig f); eauto); 
          (symmetry ; eauto with valagree)]).

  (* itailcall *)
    normalized pc.
    destruct ros0;
    [exploit spec_ros_r_find_function ; eauto
      | exploit spec_ros_id_find_function ; eauto];
    (intros; destruct H3 as [tf' [Hfind OKtf']]);
    (exploit (sig_function_translated f tf) ; eauto ; intros);
    ((exists (Callstate ts tf' rs##args0 m');  split);
      [  (eapply plus_one ; eauto); 
        (eapply exec_Itailcall ; eauto with valagree);
        (replace (fn_stacksize tf) with (fn_stacksize f); eauto with valagree)
        | ( (constructor; auto);
          (eapply match_stackframes_change_sig ;eauto with valagree))]);
    eapply tailcall_ok ; eauto.
  
  (* ibuiltin *)
  normalized pc. inv H7. assert (Hpc := H8 O pc').  exploit Hpc ; eauto; intros. 
  mks.

  (* pc ' is join point *)
  exists  (RTL.State ts tf sp succ (rs#res <- v) m'). split.
  eapply plus_two with (s2 := (RTL.State ts tf sp pcnew (rs#res<- v) m')) (t1:= t) (t2:= E0) ; eauto with valagree.
  eapply exec_Ibuiltin ; eauto.
  eapply external_call_symbols_preserved; eauto with valagree.
  econstructor 1 ; eauto. 
  rewrite E0_right; eauto. 
  constructor; auto. 

  (* pc ' is not join point *)
  exists  (RTL.State ts tf sp succ (rs#res <- v) m'). split.
  eapply plus_one ; eauto.  
  econstructor 7 ; eauto.
  eapply external_call_symbols_preserved; eauto with valagree.
  econstructor 1 ; eauto. 
  
  (* ifso *)
  destruct b.
  normalized pc.
  inv H7.
  assert (Hpc := H8 O ifso). 
  exploit Hpc ; eauto; intros. 
  mks.

  exists (RTL.State ts tf sp succ rs m); split ; eauto. 
  eapply plus_two with (s2:= (RTL.State ts tf sp pcnew rs m)) (t1:= E0) (t2:= E0)  ; eauto.
  eapply exec_Icond ; eauto. 
  constructor; auto.  

  exists (RTL.State ts tf sp succ rs m); split ; eauto. 
  eapply plus_one ; eauto.  
  eapply exec_Icond ; eauto. 

  (* ifnot *)
  normalized pc.
  inv H7.
  assert (Hpc := H8 1%nat ifnot). 
  exploit Hpc ; eauto; intros. 
  mks.

  exists (RTL.State ts tf sp succ rs m); split ; eauto. 
  eapply plus_two with (s2:= (RTL.State ts tf sp pcnew rs m)) (t1:= E0) (t2:= E0)  ; eauto.
  eapply exec_Icond ; eauto. 
  constructor; auto.  

  exists (RTL.State ts tf sp succ rs m); split ; eauto. 
  eapply plus_one ; eauto.  
  eapply exec_Icond ; eauto. 
  
  (* ijump *)
  normalized pc.
  inv H8.
  exploit @list_nth_z_nth_error ; eauto.
  intros.
  assert (Hpc := H9 (Z.to_nat (Int.unsigned n)) pc'). 
  exploit Hpc ; eauto; intros. 
  inv H8; allinv. 
  
  simpl successors_instr in *. 

  exists (RTL.State ts tf sp succ rs m); split ; eauto. 
  eapply plus_two with (s2:= (RTL.State ts tf sp pcnew rs m)) (t1:= E0) (t2:= E0)  ; eauto.
  eapply exec_Ijumptable ; eauto.
  inv H17. exploit @nth_error_list_nth_z ; eauto.
  eapply @list_nth_z_ge0 ; eauto.
  intros. rewrite H16 ; symmetry ; auto.
  
  constructor; auto.  simpl in *.
  exploit @list_nth_z_nth_error ; eauto.
  intros. rewrite H8 in H13 ; inv H13.
  econstructor ; auto.

    
  simpl successors_instr in *. 

  exists (RTL.State ts tf sp succ rs m); split ; eauto. 
  eapply plus_one ; eauto.
  eapply exec_Ijumptable ; eauto.
  inv H17. exploit @nth_error_list_nth_z ; eauto.
  eapply @list_nth_z_ge0 ; eauto.
  intros. rewrite H8 ; symmetry ; auto.
  
  simpl in *.
  exploit @list_nth_z_nth_error ; eauto.
  intros. rewrite H8 in H13 ; inv H13.
  econstructor ; auto.
  
  (* ireturn *)
  (exploit transl_function_opt_charact ; eauto; intros).
  (exploit transl_function_spec_ok ; eauto; intros).
  inv H2.
  assert (Hpc := H4 pc). 
  exploit Hpc ; eauto ; intros Hnorm. 
  inv Hnorm; allinv; try congruence. 
  
  exists (Returnstate ts (regmap_optget rov Vundef rs) m'); split ; eauto. 
  eapply plus_one ; eauto.
  eapply exec_Ireturn ; eauto.
  rewrite <- H0 ; eauto with valagree.
  rewrite stacksize_preserved with f tf ; eauto.

  (* internal *)
  simpl in SPEC. Errors.monadInv SPEC. simpl in STACK.
  exists (RTL.State ts x
    (Vptr stk Int.zero)
    f.(fn_entrypoint)
    (init_regs args x.(fn_params))
    m').
  split.
  exploit transl_function_spec_entry ; eauto.
  intros. destruct H0.
  eapply plus_left with (s2:=(RTL.State ts x (Vptr stk Int.zero) (fn_entrypoint x) 
        (init_regs args (fn_params x)) m')) (t1:=E0) (t2:=E0) ; eauto. 
  eapply exec_function_internal; eauto.
  rewrite stacksize_preserved with f x in H ; auto.
  eapply reach_nop_star ; eauto.

  replace (RTL.fn_params f) with (fn_params x).
  econstructor ; eauto.
  unfold transl_function_opt in EQ.
  destruct (add_nop_entry (fn_entrypoint f) (init_state f)). inv EQ.
  destruct (mfold_unit
           (add_nop_after_instruction_opt
              (is_joinpoint (make_predecessors (fn_code f) successors_instr)))
           (PTree.elements (st_code s')) s'). inv EQ.
  inv EQ. auto.

  (* external *)
  inv SPEC.
  exists (Returnstate ts res m'). split. 
  eapply plus_one ; eauto.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto with valagree.
  econstructor ; eauto.
  
  (* return state *)
  inv STACK. 
  exists (RTL.State ts0 tf sp pc (rs# res <- vres) m).
  split. eapply plus_one ; eauto. constructor ; eauto.
  constructor ; auto.
  
  exists (RTL.State ts0 tf sp pc (rs# res <- vres) m).
  split. eapply plus_two with (s2:= (RTL.State ts0 tf sp pc' (rs# res <- vres) m) ) (t1:=E0) (t2:=E0) ; eauto. 
  constructor ; eauto.
  constructor ; auto.
  constructor ; auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transl_step_correct. 
Qed.
  
End PRESERVATION.