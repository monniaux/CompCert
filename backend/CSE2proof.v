Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.
Require Import Linking Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import CSE2.

Lemma args_unaffected:
  forall rs : regset,
  forall dst : reg,
  forall v,
  forall args : list reg,
    existsb (fun y : reg => peq dst y) args = false ->
    (rs # dst <- v ## args) = (rs ## args).
Proof.
  induction args; simpl; trivial.
  destruct (peq dst a) as [EQ | NEQ]; simpl.
  { discriminate.
  }
  intro EXIST.
  f_equal.
  {
    apply Regmap.gso.
    congruence.
  }
  apply IHargs.
  assumption.
Qed.

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

Section SAME_MEMORY.
  Variable m : mem.

Definition sem_sym_val sym rs :=
  match sym with
  | SMove src => Some (rs # src)
  | SOp op args =>
    eval_operation genv sp op (rs ## args) m
  end.
    
Definition sem_reg (rel : RELATION.t) (x : reg) (rs : regset) : option val :=
  match rel ! x with
  | None => Some (rs # x)
  | Some sym => sem_sym_val sym rs
  end.

Definition sem_rel (rel : RELATION.t) (rs : regset) :=
  forall x : reg, (sem_reg rel x rs) = Some (rs # x).

Definition sem_rel_b (relb : RB.t) (rs : regset) :=
  match relb with
  | Some rel => sem_rel rel rs
  | None => False
  end.

Definition fmap_sem (fmap : option (PMap.t RB.t))
  (pc : node) (rs : regset) :=
  match fmap with
  | None => True
  | Some m => sem_rel_b (PMap.get pc m) rs
  end.

Lemma subst_arg_ok:
  forall f,
  forall pc,
  forall rs,
  forall arg,
    fmap_sem (forward_map f) pc rs ->
    rs # (subst_arg (forward_map f) pc arg) = rs # arg.
Proof.
  intros until arg.
  intro SEM.
  unfold fmap_sem in SEM.
  destruct (forward_map f) as [map |]in *; trivial.
  simpl.
  unfold sem_rel_b, sem_rel, sem_reg in *.
  destruct (map # pc).
  2: contradiction.
  pose proof (SEM arg) as SEMarg.
  simpl. unfold forward_move.
  unfold sem_sym_val in *.
  destruct (t ! arg); trivial.
  destruct s; congruence.
Qed.

Lemma subst_args_ok:
  forall f,
  forall pc,
  forall rs,
  fmap_sem (forward_map f) pc rs ->
  forall args,
    rs ## (subst_args (forward_map f) pc args) = rs ## args.
Proof.
  induction args; trivial.
  simpl.
  f_equal.
  apply subst_arg_ok; assumption.
  assumption.
Qed.

Lemma kill_reg_sound :
  forall rel : RELATION.t,
  forall dst : reg,
  forall rs,
  forall v,
    sem_rel rel rs ->
    sem_rel (kill_reg dst rel) (rs # dst <- v).
Proof.
  unfold sem_rel, kill_reg, sem_reg, sem_sym_val.
  intros until v.
  intros REL x.
  rewrite PTree.gfilter1.
  destruct (Pos.eq_dec dst x).
  {
    subst x.
    rewrite PTree.grs.
    rewrite Regmap.gss.
    reflexivity.
  }
  rewrite PTree.gro by congruence.
  rewrite Regmap.gso by congruence.
  destruct (rel ! x) as [relx | ] eqn:RELx.
  2: reflexivity.
  unfold kill_sym_val.
  pose proof (REL x) as RELinstx.
  rewrite RELx in RELinstx.
  destruct relx eqn:SYMVAL.
  {
    destruct (peq dst src); simpl.
    { reflexivity. }
    rewrite Regmap.gso by congruence.
    assumption.
  }
  { destruct existsb eqn:EXISTS; simpl.
    { reflexivity. }
    rewrite args_unaffected by exact EXISTS.
    assumption.
  }
Qed.

Lemma write_same:
  forall rs : regset,
  forall src dst : reg,
    (rs # dst <- (rs # src)) # src = rs # src.
Proof.
  intros.
  destruct (peq src dst).
  {
    subst dst.
    apply Regmap.gss.
  }
  rewrite Regmap.gso by congruence.
  reflexivity.
Qed.

Lemma move_sound :
  forall rel : RELATION.t,
  forall src dst : reg,
  forall rs,
    sem_rel rel rs ->
    sem_rel (move src dst rel) (rs # dst <- (rs # src)).
Proof.
  intros until rs. intros REL x.
  pose proof (kill_reg_sound rel dst rs (rs # src) REL x) as KILL.
  pose proof (REL src) as RELsrc.
  unfold move.
  destruct (peq x dst).
  {
    subst x.
    unfold sem_reg.
    rewrite PTree.gss.
    rewrite Regmap.gss.
    unfold sem_reg in RELsrc.
    simpl.
    unfold forward_move.
    destruct (rel ! src) as [ sv |]; simpl.
    destruct sv; simpl in *.
    {
      destruct (peq dst src0).
      {
        subst src0.
        rewrite Regmap.gss.
        reflexivity.
      }
      rewrite Regmap.gso by congruence.
      assumption.
    }
    all: f_equal; apply write_same.
  }
  rewrite Regmap.gso by congruence.
  unfold sem_reg.
  rewrite PTree.gso by congruence.
  rewrite Regmap.gso in KILL by congruence.
  exact KILL.
Qed.

Lemma move_cases_neq:
  forall dst rel a,
    a <> dst ->
    (forward_move (kill_reg dst rel) a) <> dst.
Proof.
  intros until a. intro NEQ.
  unfold kill_reg, forward_move.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by congruence.
  destruct (rel ! a); simpl.
  2: congruence.
  destruct s.
  {
    unfold kill_sym_val.
    destruct peq; simpl; congruence.
  }
  all: simpl;
    destruct negb; simpl; congruence.
Qed.

Lemma args_replace_dst :
  forall rel,
  forall args : list reg,
  forall dst : reg,
  forall rs : regset,
  forall v,
    (sem_rel rel rs) ->
    not (In dst args) ->
    (rs # dst <- v)
    ## (map
          (forward_move (kill_reg dst rel)) args) = rs ## args.
Proof.
  induction args; simpl.
  1: reflexivity.
  intros until v.
  intros REL NOT_IN.
  rewrite IHargs by auto.
  f_equal.
  pose proof (REL a) as RELa.
  rewrite Regmap.gso by (apply move_cases_neq; auto).
  unfold kill_reg.
  unfold sem_reg in RELa.
  unfold forward_move.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by auto.
  destruct (rel ! a); simpl; trivial.
  destruct s; simpl in *; destruct negb; simpl; congruence.
Qed.

Lemma oper1_sound :
  forall rel : RELATION.t,
  forall op : operation,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall v,
    sem_rel rel rs ->
    not (In dst args) ->
    eval_operation genv sp op (rs ## args) m = Some v ->
    sem_rel (oper1 op dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL NOT_IN EVAL x.
  pose proof (kill_reg_sound rel dst rs v REL x) as KILL.
  unfold oper1.
  destruct (peq x dst).
  {
    subst x.
    unfold sem_reg.
    rewrite PTree.gss.
    rewrite Regmap.gss.
    simpl.
    rewrite args_replace_dst by auto.
    assumption.
  }
  rewrite Regmap.gso by congruence.
  unfold sem_reg.
  rewrite PTree.gso by congruence.
  rewrite Regmap.gso in KILL by congruence.
  exact KILL.
Qed.

Lemma oper_sound :
  forall rel : RELATION.t,
  forall op : operation,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall v,
    sem_rel rel rs ->
    eval_operation genv sp op (rs ## args) m = Some v ->
    sem_rel (oper op dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL EVAL.
  unfold oper.
  destruct in_dec.
  {
    apply kill_reg_sound; auto. 
  }
  apply oper1_sound; auto.
Qed.

Lemma gen_oper_sound :
  forall rel : RELATION.t,
  forall op : operation,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall v,
    sem_rel rel rs ->
    eval_operation genv sp op (rs ## args) m = Some v ->
    sem_rel (gen_oper op dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL EVAL.
  unfold gen_oper.
  destruct op.
  { destruct args as [ | h0 t0].
    apply oper_sound; auto.
    destruct t0.
    {
      simpl in *.
      replace v with (rs # h0) by congruence.
      apply move_sound; auto.
    }
    apply oper_sound; auto.
  }
  all: apply oper_sound; auto.
Qed.


Lemma find_op_sound :
  forall rel : RELATION.t,
  forall op : operation,
  forall src dst : reg,
  forall args: list reg,
  forall rs : regset,
    sem_rel rel rs ->
    find_op rel op args = Some src ->
    (eval_operation genv sp op (rs ## args) m) = Some (rs # src).
Proof.
  intros until rs.
  unfold find_op.
  rewrite PTree.fold_spec.
  intro REL.
  assert (
     forall start,
             match start with
             | None => True
             | Some src => eval_operation genv sp op rs ## args m = Some rs # src
             end -> fold_left
    (fun (a : option reg) (p : positive * sym_val) =>
     find_op_fold op args a (fst p) (snd p)) (PTree.elements rel) start =
                    Some src ->
             eval_operation genv sp op rs ## args m = Some rs # src) as REC.
  {
    unfold sem_rel, sem_reg in REL.
    generalize (PTree.elements_complete rel).
    generalize (PTree.elements rel).
    induction l; simpl.
    {
      intros.
      subst start.
      assumption.
    }
    destruct a as [r sv]; simpl.
    intros COMPLETE start GEN.
    apply IHl.
    {
      intros.
      apply COMPLETE.
      right.
      assumption.
    }
    unfold find_op_fold.
    destruct start.
    assumption.
    destruct sv.
    { trivial. }
    destruct eq_operation; trivial.
    subst op0.
    destruct eq_args; trivial.
    subst args0.
    simpl.
    assert ((rel ! r) = Some (SOp op args)) as RELatr.
    {
      apply COMPLETE.
      left.
      reflexivity.
    }
    pose proof (REL r) as RELr.
    rewrite RELatr in RELr.
    simpl in RELr.
    assumption.
  }
  apply REC; auto.
Qed.


Lemma kill_reg_weaken:
  forall res mpc rs,
    sem_rel mpc rs ->
    sem_rel (kill_reg res mpc) rs.
Proof.
  Check kill_reg_sound.
  intros until rs.
  intros REL x.
  pose proof (REL x) as RELx.
  unfold kill_reg, sem_reg in *.
  rewrite PTree.gfilter1.
  destruct (peq res x).
  { subst x.
    rewrite PTree.grs.
    reflexivity.
  }
  rewrite PTree.gro by congruence.
  destruct (mpc ! x) as [sv | ]; trivial.
  destruct negb; trivial.
Qed.
End SAME_MEMORY.

Lemma kill_mem_sound :
  forall m m' : mem,
  forall rel : RELATION.t,
  forall rs,
    sem_rel m rel rs -> sem_rel m' (kill_mem rel) rs.
Proof.
  unfold sem_rel, sem_reg.
  intros until rs.
  intros SEM x.
  pose proof (SEM x) as SEMx.
  unfold kill_mem.
  rewrite PTree.gfilter1.
  unfold kill_sym_val_mem.
  destruct (rel ! x) as [ sv | ].
  2: reflexivity.
  destruct sv; simpl in *; trivial.
  {
    destruct op_depends_on_memory eqn:DEPENDS; simpl; trivial.
    rewrite <- SEMx.
    apply op_depends_on_memory_correct; auto.
  }
Qed.
  
End SOUNDNESS.


Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; trivial.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Lemma transf_function_at:
  forall (f : function) (pc : node) (i : instruction),
  (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!pc =
    Some(transf_instr (forward_map f) pc i).
Proof.
  intros until i. intro CODE.
  unfold transf_function; simpl.
  rewrite PTree.gmap.
  unfold option_map.
  rewrite CODE.
  reflexivity.
Qed.

Definition is_killed_in_map (map : PMap.t RB.t) pc res :=
  match PMap.get pc map with
  | None => True
  | Some rel => exists rel', RELATION.ge rel (kill_reg res rel')
  end.

Definition is_killed_in_fmap fmap pc res :=
  match fmap with
  | None => True
  | Some map => is_killed_in_map map pc res
  end.

Definition sem_rel_b' := sem_rel_b fundef unit ge.
Definition fmap_sem' := fmap_sem fundef unit ge.
Definition subst_args_ok' := subst_args_ok fundef unit ge.
Definition kill_mem_sound' := kill_mem_sound fundef unit ge.

Lemma sem_rel_b_ge:
  forall rb1 rb2 : RB.t,
    (RB.ge rb1 rb2) ->
    forall sp m,
    forall rs : regset,
      (sem_rel_b' sp m rb2 rs) -> (sem_rel_b' sp m rb1 rs).
Proof.
  unfold sem_rel_b', sem_rel_b, sem_rel, sem_reg.
  destruct rb1 as [r1 | ];
    destruct rb2 as [r2 | ]; simpl;
      intros GE sp m rs RE; try contradiction.
  intro x.
  pose proof (RE x) as REx.
  pose proof (GE x) as GEx.
  destruct (r1 ! x) as [r1x | ] in *;
    destruct (r2 ! x) as [r2x | ] in *;
    congruence.
Qed.

Lemma apply_instr'_bot :
  forall code,
  forall pc,
    RB.eq (apply_instr' code pc RB.bot) RB.bot.
Proof.
  reflexivity.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
| match_frames_intro: forall res f sp pc rs,
    (forall m : mem, (fmap_sem' sp m (forward_map f) pc rs)) ->
    (is_killed_in_fmap (forward_map f) pc res) ->
      match_frames (Stackframe res f sp pc rs)
                 (Stackframe res (transf_function f) sp pc rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
                                 (STACKS: list_forall2 match_frames stk stk'),
      (fmap_sem' sp m (forward_map f) pc rs) ->
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp pc rs m)
  | match_callstates: forall stk f args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef f) args m)
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).
  
Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ |- _ ] =>
        generalize (transf_function_at _ _ _ A); intros
  end.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
              exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try TR_AT.
- (* nop *)
  econstructor; split. eapply exec_Inop; eauto.
  constructor; auto.
  
  simpl in *.
  unfold fmap_sem', fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply sem_rel_b_ge with (rb2 := map # pc); trivial.
  replace (map # pc) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl. tauto.
  }
  unfold apply_instr'.
  unfold sem_rel_b in *.
  destruct (map # pc) in *; try contradiction.
  rewrite H.
  reflexivity.
- (* op *)
  (*
  econstructor; split.
  eapply exec_Iop with (v := v); eauto.
  rewrite <- H0.
  rewrite subst_args_ok by assumption.
  apply eval_operation_preserved. exact symbols_preserved.
  constructor; auto.

  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  assert (RB.ge (map # pc') (apply_instr' (fn_code f) pc (map # pc))) as GE.
  {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
  }
  unfold apply_instr' in GE.
  rewrite MPC in GE.
  rewrite H in GE.
  
  destruct (op_cases op args res pc' mpc) as [[src [OP [ARGS MOVE]]] | KILL].
  {
    subst op.
    subst args.
    rewrite MOVE in GE.
    simpl in H0.
    simpl in GE.
    apply sem_rel_b_ge with (rb2 := Some (move src res mpc)).
    assumption.
    replace v with (rs # src) by congruence.
    apply move_ok.
    assumption.
  }
  rewrite KILL in GE.
  apply sem_rel_b_ge with (rb2 := Some (kill res mpc)).
  assumption.
  apply kill_ok.
  assumption.
   *)
  admit.
(* load *)
- econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0.
  apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload; eauto.
  rewrite (subst_args_ok' sp m); assumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem', fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply sem_rel_b_ge with (rb2 := Some (kill_reg dst mpc)).
  {
    replace (Some (kill_reg dst mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply kill_reg_sound.
  assumption.

  (* NOT IN THIS VERSION 
- (* load notrap1 *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = None).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload_notrap1; eauto.
  rewrite subst_args_ok; assumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply sem_rel_b_ge with (rb2 := Some (kill dst mpc)).
  {
    replace (Some (kill dst mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply kill_ok.
  assumption.
  
- (* load notrap2 *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload_notrap2; eauto.
  rewrite subst_args_ok; assumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply sem_rel_b_ge with (rb2 := Some (kill dst mpc)).
  {
    replace (Some (kill dst mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply kill_ok.
  assumption.
   *)
  
- (* store *)
  econstructor. split.
  {
    assert (eval_addressing tge sp addr rs ## args = Some a).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    eapply exec_Istore; eauto.
    rewrite (subst_args_ok' sp m); assumption.
  }
  
  constructor; auto.
  simpl in *.
  unfold fmap_sem', fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  apply sem_rel_b_ge with (rb2 := Some (kill_mem mpc)); trivial.
  {
  replace (Some (kill_mem mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl. tauto.
  }
  unfold apply_instr'.
  unfold sem_rel_b in *.
  rewrite MPC.
  rewrite H.
  reflexivity.
  }
  apply (kill_mem_sound' sp m).
  assumption.
  
(* call *)
- econstructor; split.
  eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  rewrite (subst_args_ok' sp m) by assumption.
  constructor. constructor; auto.

  constructor.
  {
    intro m'.
    unfold fmap_sem', fmap_sem in *.
    destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
    destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
    apply sem_rel_b_ge with (rb2 := Some (kill_reg res (kill_mem mpc))).
    {
      replace (Some (kill_reg res (kill_mem mpc))) with (apply_instr' (fn_code f) pc (map # pc)).
      {
        eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
        2: apply apply_instr'_bot.
        simpl. tauto.
      }
      unfold apply_instr'.
      rewrite H.
      rewrite MPC.
      reflexivity.
    }
    apply kill_reg_weaken.
    apply (kill_mem_sound' sp m).
    assumption.
  }
  {
  simpl in *.
  unfold fmap_sem', fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  assert (RB.ge (map # pc') (apply_instr' (fn_code f) pc (map # pc))) as GE.
  {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
  }
  unfold apply_instr' in GE.
  rewrite H in GE.
  simpl in GE.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  unfold is_killed_in_fmap, is_killed_in_map.
  destruct (map # pc') as [mpc' |] eqn:MPC' ; try contradiction.

  exists (kill_mem mpc).
  assumption.
  }
  
(* tailcall *)
- econstructor; split.
  eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  Check subst_args_ok.
  rewrite (subst_args_ok' (Vptr stk Ptrofs.zero) m) by assumption.
  constructor. auto.

    (* TODO *)

(* builtin *)
- econstructor; split.
  eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  destruct (map # pc) as [mpc |] eqn:MPC in *; try contradiction.
  
  apply sem_rel_b_ge with (rb2 := Some RELATION.top).
  {
    replace (Some RELATION.top) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    reflexivity.
  }
  apply top_ok.
  
(* cond *)
- econstructor; split.
  eapply exec_Icond; eauto.
  rewrite subst_args_ok; eassumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply sem_rel_b_ge with (rb2 := map # pc); trivial.
  replace (map # pc) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl.
    destruct b; tauto.
  }
  unfold apply_instr'.
  unfold sem_rel_b in *.
  destruct (map # pc) in *; try contradiction.
  rewrite H.
  reflexivity.
  
(* jumptbl *)
- econstructor; split.
  eapply exec_Ijumptable; eauto.
  rewrite subst_arg_ok; eassumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply sem_rel_b_ge with (rb2 := map # pc); trivial.
  replace (map # pc) with (apply_instr' (fn_code f) pc (map # pc)).
  {
    eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
    2: apply apply_instr'_bot.
    simpl.
    apply list_nth_z_in with (n := Int.unsigned n).
    assumption.
  }
  unfold apply_instr'.
  unfold sem_rel_b in *.
  destruct (map # pc) in *; try contradiction.
  rewrite H.
  reflexivity.
  
(* return *)
- destruct or as [arg | ].
  {
    econstructor; split.
    eapply exec_Ireturn; eauto.
    unfold regmap_optget.
    rewrite subst_arg_ok by eassumption.
    constructor; auto.
  }
    econstructor; split.
    eapply exec_Ireturn; eauto.
    constructor; auto.
  
  
(* internal function *)
-  simpl. econstructor; split.
  eapply exec_function_internal; eauto.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  apply sem_rel_b_ge with (rb2 := Some RELATION.top).
  {
    eapply DS.fixpoint_entry with (code := fn_code f) (successors := successors_instr); try eassumption.
  }
  apply top_ok.
  
(* external function *)
- econstructor; split.
  eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto.

(* return *)
- inv STACKS. inv H1.
  econstructor; split.
  eapply exec_return; eauto.
  constructor; auto.

  simpl in *.
  unfold fmap_sem in *.
  destruct (forward_map _) as [map |] eqn:MAP in *; trivial.
  unfold is_killed_in_fmap in H8.
  unfold is_killed_in_map in H8.
  destruct (map # pc) as [mpc |] in *; try contradiction.
  destruct H8 as [rel' RGE].
  eapply get_rb_killed; eauto.
Qed.


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

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.
 *)

End PRESERVATION.