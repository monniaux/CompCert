Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions TailcallGoto.


Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef (prog_defmap p) f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef (prog_defmap prog) f).
Proof.
  intros.
  apply (Genv.find_funct_transf TRANSL).
  assumption.
Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef (prog_defmap prog) f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros.
  apply (Genv.find_symbol_transf TRANSL).
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  intros.
  apply (Genv.senv_transf TRANSL).
Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef (prog_defmap prog) f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef (prog_defmap prog) fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function (prog_defmap prog) f).(fn_code)!pc = Some(transf_instr (prog_defmap prog) f pc i).
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

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs,
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function (prog_defmap prog) f) sp pc rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function (prog_defmap prog) f) sp pc rs m)
  | match_callstates: forall stk f args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef (prog_defmap prog) f) args m)
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
    match (fn_code cur_fn) ! pc with
    | Some (Itailcall sig (inr symb) args) =>
      match PTree.get symb (prog_defmap prog) with
      | Some (Gfun (Internal f)) =>
        if function_eq f cur_fn
        then
          match args with
          | nil => 2
          | _ => 1
          end
        else 1
      | _ => 1
      end
    | _ => 1
    end
  | _ => 1
  end.


Theorem simulation:
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
  eapply plus_one. eapply exec_Icall with (fd := transf_fundef (prog_defmap prog) fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. constructor; auto. constructor.
(* tailcall *)
- admit.
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
(* external function *)
- left; econstructor; split.
  eapply plus_one.
  eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
(* return *)
- inv STACKS. inv H1.
  left; econstructor; split.
  eapply plus_one.
  eapply exec_return; eauto.
  constructor; auto.
Admitted.
