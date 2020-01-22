Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions TailcallGoto.
Require Inliningspec Inliningproof.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cunit f tf => tf = transf_fundef (funenv_program cunit) f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program_contextual; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros.
  apply (Genv.find_symbol_match TRANSF).
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  intros.
  apply (Genv.senv_match TRANSF).
Qed.


Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cu f', Genv.find_funct tge v = Some f' /\ f' = transf_fundef (funenv_program cu) f /\ linkorder cu prog.
Proof.
  intros.
  apply (Genv.find_funct_match TRANSF).
  assumption.
Qed.
                                  
Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu f', Genv.find_funct_ptr tge b = Some f' /\ f' = transf_fundef (funenv_program cu) f /\ linkorder cu prog.
Proof.
  intros.
  apply (Genv.find_funct_ptr_match TRANSF).
  assumption.
Qed.

Lemma sig_function_translated:
  forall cu f, funsig (transf_fundef (funenv_program cu) f) = funsig f.
Proof.
  destruct f; simpl; trivial.
Qed.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function (funenv_program prog) f).(fn_code)!pc = Some(transf_instr (funenv_program prog) f pc i).
Proof.
  intros until i. intro Hcode.
  unfold transf_function; simpl.
  rewrite PTree.gmap.
  unfold option_map.
  rewrite Hcode.
  reflexivity.
Qed.

Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ |- _ ] =>
        generalize (transf_function_at _ _ _ A); intros
  end.
Definition is_goto_tailcall (cur_fn : function) (pc : node) : bool :=
    match (fn_code cur_fn) ! pc with
    | Some (Itailcall sig (inr symb) args) =>
      match PTree.get symb (funenv_program prog) with
      | Some f =>
        if function_eq f cur_fn
        then
          match args with
          | nil => true
          | _ => false
          end
        else false
      | _ => false
      end
    | _ => false
    end.

(*
Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs,
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function (funenv_program prog) f) sp pc rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function (funenv_program prog) f) sp pc rs m)
  | match_callstates: forall stk f args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef (funenv_program prog) f) args m)
  | match_goto_callstates: forall stk f stkf pc rs m m' stk'
      (STACKS: list_forall2 match_frames stk stk')
      (GOTO: is_goto_tailcall f pc=true)
      (FREE: Mem.free m' stkf 0 (fn_stacksize f) = Some m),
      match_states (Callstate stk (Internal f) nil m)
                   (State stk' (transf_function (funenv_program prog) f) (Vptr stkf Ptrofs.zero) pc rs m')
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split.
  econstructor.
    eapply (Genv.init_mem_transf TRANSL); eauto.
    rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
    eapply function_ptr_translated; eauto.
    rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.
  
Definition measure (s: state) : nat :=
  match s with
  | (State stk cur_fn sp pc rs m) =>
    if is_goto_tailcall cur_fn pc then 1 else 0
  | _ => 0
  end.

Lemma goto_tailcall_transf:
  forall f pc
         (GOTO : is_goto_tailcall f pc = true),
  (fn_code (transf_function (funenv_program prog) f)) ! pc = Some (Inop (fn_entrypoint f)).
Proof.
  intros.
  unfold is_goto_tailcall in *.
  destruct ((fn_code f) ! pc) eqn:CODE in *.
  2: discriminate.
  rewrite transf_function_at with (i := i) by assumption.
  f_equal.
  unfold transf_instr.
  destruct i; try discriminate.
  destruct s0; try discriminate.
  destruct ((funenv_program prog) ! i) in * ; try discriminate.
  destruct (function_eq f0 f); try discriminate.
  destruct l; try discriminate.
  reflexivity.
Qed.


Lemma ge_is_defmap:
  forall identifier fd rs,
    find_function ge (inr identifier) rs = Some fd ->
    (prog_defmap prog) ! identifier = Some (Gfun fd).
Proof.
  intros until rs. intro FIND.
  rewrite Genv.find_def_symbol.
  unfold find_function in *.
  destruct (Genv.find_symbol _ _) as [block' | ] in *.
  2: discriminate.
  exists block'.
  constructor; trivial.
  rewrite <- Genv.find_funct_ptr_iff.
  exact FIND.
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.
  
- (* nop *)
  exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto.
  rewrite <- H0.
  apply eval_operation_preserved.
  exact symbols_preserved.
  constructor; auto.
  
(* load *)
- exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  rewrite <- H0.
  apply eval_addressing_preserved. exact symbols_preserved.
  constructor; auto.

- (* store *)
  exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply plus_one. eapply exec_Istore; eauto.
  constructor; auto. 
(* call *)
- exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall with (fd := transf_fundef (funenv_program prog) fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. constructor; auto. constructor.
(* tailcall *)
- exploit transf_function_at; eauto. intros TR; inv TR.
  destruct ros as [register | identifier] in *.
  {
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall with (fd := transf_fundef (funenv_program prog) fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. assumption.
  }
  destruct ((funenv_program prog) ! identifier) as [ fn |] eqn:DEF in *.
  2: {
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall with (fd := transf_fundef (funenv_program prog) fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. assumption.
  }
  destruct (function_eq fn f) as [ SAME | NOT_SAME ] eqn:ESAME.
  2: {
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall with (fd := transf_fundef (funenv_program prog) fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. assumption.
  }
  destruct args as [ | args_h args_t].
  2: {
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall with (fd := transf_fundef (funenv_program prog) fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. assumption.
  }
  subst fn.
  right.
  erewrite ge_is_defmap in DEF by eassumption.
  assert (fd = Internal f) as FD by congruence.
  clear DEF.
  assert ((is_goto_tailcall f pc)=true) as GOTOTAIL.
  {
    simpl.
    unfold is_goto_tailcall.
    replace ((fn_code f) ! pc).
    erewrite ge_is_defmap by eassumption.
    rewrite FD.
    rewrite ESAME.
    reflexivity.
  }
  split.
  { unfold measure.
    rewrite GOTOTAIL.
    omega.
  }
  split; trivial.
  rewrite FD.
  apply match_goto_callstates; auto.
  
(* builtin *)
- exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
(* cond *)
- exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  constructor; auto.
(* jumptbl *)
- exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  constructor; auto.
(* return *)
- exploit transf_function_at; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto.
  constructor; auto.
(* internal function *)
- simpl. left; econstructor; split.
  eapply plus_one. eapply exec_function_internal; eauto.
  constructor; auto.
(* goto head tail call *)
- left; econstructor; split.
  eapply plus_one.
  eapply exec_Inop; eauto.
  apply goto_tailcall_transf; assumption.
  admit.
- admit.
(* return *)
- inv STACKS. inv H1.
  left; econstructor; split.
  eapply plus_one.
  eapply exec_return; eauto.
  constructor; auto.
Admitted.
  
Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_star.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.
 *)

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Admitted.

End PRESERVATION.
  