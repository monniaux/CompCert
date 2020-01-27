Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

Require Import Globalenvs Values.

(* Static analysis *)

Inductive sym_val : Type :=
| SMove (src : reg)
| SOp (op : operation) (args : list reg).

Definition eq_args (x y : list reg) : { x = y } + { x <> y } :=
  list_eq_dec peq x y.

Definition eq_sym_val : forall x y : sym_val,
    {x = y} + { x <> y }.
Proof.
  generalize eq_operation.
  generalize eq_args.
  generalize peq.
  decide equality.
Defined.

Module RELATION.
  
Definition t := (PTree.t sym_val).
Definition eq (r1 r2 : t) :=
  forall x, (PTree.get x r1) = (PTree.get x r2).

Definition top : t := PTree.empty sym_val.

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq.
  intros; reflexivity.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq.
  intros; eauto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq.
  intros; congruence.
Qed.

Definition sym_val_beq (x y : sym_val) :=
  if eq_sym_val x y then true else false.

Definition beq (r1 r2 : t) := PTree.beq sym_val_beq r1 r2.

Lemma beq_correct: forall r1 r2, beq r1 r2 = true -> eq r1 r2.
Proof.
  unfold beq, eq. intros r1 r2 EQ x.
  pose proof (PTree.beq_correct sym_val_beq r1 r2) as CORRECT.
  destruct CORRECT as [CORRECTF CORRECTB].
  pose proof (CORRECTF EQ x) as EQx.
  clear CORRECTF CORRECTB EQ.
  unfold sym_val_beq in *.
  destruct (r1 ! x) as [R1x | ] in *;
    destruct (r2 ! x) as [R2x | ] in *;
    trivial; try contradiction.
  destruct (eq_sym_val R1x R2x) in *; congruence.
Qed.

Definition ge (r1 r2 : t) :=
  forall x,
    match PTree.get x r1 with
    | None => True
    | Some v => (PTree.get x r2) = Some v
    end.

Lemma ge_refl: forall r1 r2, eq r1 r2 -> ge r1 r2.
Proof.
  unfold eq, ge.
  intros r1 r2 EQ x.
  pose proof (EQ x) as EQx.
  clear EQ.
  destruct (r1 ! x).
  - congruence.
  - trivial.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge.
  intros r1 r2 r3 GE12 GE23 x.
  pose proof (GE12 x) as GE12x; clear GE12.
  pose proof (GE23 x) as GE23x; clear GE23.
  destruct (r1 ! x); trivial.
  destruct (r2 ! x); congruence.
Qed.

Definition lub (r1 r2 : t) :=
  PTree.combine
    (fun ov1 ov2 =>
       match ov1, ov2 with
       | (Some v1), (Some v2) =>
         if eq_sym_val v1 v2
         then ov1
         else None
       | None, _
       | _, None => None
       end)
    r1 r2.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub.
  intros r1 r2 x.
  rewrite PTree.gcombine by reflexivity.
  destruct (_ ! _); trivial.
  destruct (_ ! _); trivial.
  destruct (eq_sym_val _ _); trivial.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub.
  intros r1 r2 x.
  rewrite PTree.gcombine by reflexivity.
  destruct (_ ! _); trivial.
  destruct (_ ! _); trivial.
  destruct (eq_sym_val _ _); trivial.
  congruence.
Qed.

End RELATION.

Module Type SEMILATTICE_WITHOUT_BOTTOM.

  Parameter t: Type.
  Parameter eq: t -> t -> Prop.
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Parameter beq: t -> t -> bool.
  Axiom beq_correct: forall x y, beq x y = true -> eq x y.
  Parameter ge: t -> t -> Prop.
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Parameter lub: t -> t -> t.
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End SEMILATTICE_WITHOUT_BOTTOM.

Module ADD_BOTTOM(L : SEMILATTICE_WITHOUT_BOTTOM).
  Definition t := option L.t.
  Definition eq (a b : t) :=
    match a, b with
    | None, None => True
    | Some x, Some y => L.eq x y
    | Some _, None | None, Some _ => False
    end.
  
  Lemma eq_refl: forall x, eq x x.
  Proof.
    unfold eq; destruct x; trivial.
    apply L.eq_refl.
  Qed.

  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq; destruct x; destruct y; trivial.
    apply L.eq_sym.
  Qed.
  
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq; destruct x; destruct y; destruct z; trivial.
    - apply L.eq_trans.
    - contradiction.
  Qed.
  
  Definition beq (x y : t) :=
    match x, y with
    | None, None => true
    | Some x, Some y => L.beq x y
    | Some _, None | None, Some _ => false
    end.
  
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq, eq.
    destruct x; destruct y; trivial; try congruence.
    apply L.beq_correct.
  Qed.
  
  Definition ge (x y : t) :=
    match x, y with
    | None, Some _ => False
    | _, None => True
    | Some a, Some b => L.ge a b
    end.
  
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge.
    destruct x; destruct y; trivial.
    apply L.ge_refl.
  Qed.
  
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge.
    destruct x; destruct y; destruct z; trivial; try contradiction.
    apply L.ge_trans.
  Qed.
  
  Definition bot: t := None.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot.
    destruct x; trivial.
  Qed.
  
  Definition lub (a b : t) :=
    match a, b with
    | None, _ => b
    | _, None => a
    | (Some x), (Some y) => Some (L.lub x y)
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold ge, lub.
    destruct x; destruct y; trivial.
    - apply L.ge_lub_left.
    - apply L.ge_refl.
      apply L.eq_refl.
  Qed.
  
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold ge, lub.
    destruct x; destruct y; trivial.
    - apply L.ge_lub_right.
    - apply L.ge_refl.
      apply L.eq_refl.
  Qed.
End ADD_BOTTOM.

Module RB := ADD_BOTTOM(RELATION).
Module DS := Dataflow_Solver(RB)(NodeSetForward).

Definition kill_sym_val (dst : reg) (sv : sym_val) :=
  match sv with
  | SMove src => if peq dst src then true else false
  | SOp op args => List.existsb (peq dst) args
  end.
                                                 
Definition kill (dst : reg) (rel : RELATION.t) :=
  PTree.filter1 (fun x => negb (kill_sym_val dst x))
                (PTree.remove dst rel).

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

Inductive sym_cases : option sym_val -> Type :=
| Move_case : forall src, (sym_cases (Some (SMove src)))
| Other_case : forall osv, (sym_cases osv).

Definition move_cases (osv : option sym_val) : (sym_cases osv).
Proof.
  destruct osv as [sv |].
  { destruct sv; try apply Move_case; apply Other_case. }
  apply Other_case.
Defined.

Definition move (src dst : reg) (rel : RELATION.t) :=
  PTree.set dst (match move_cases (PTree.get src rel) with
                 | Move_case src' => SMove src'
                 | Other_case _ => SMove src
                 end) (kill dst rel).

Definition oper1 (op: operation) (dst : reg) (args : list reg)
           (rel : RELATION.t) :=
  let rel' := kill dst rel in
  PTree.set dst (SOp op (List.map (fun arg =>
                                     match move_cases (rel' ! arg) with
                                     | Move_case arg' => arg'
                                     | Other_case _ => arg
                                     end) args)) rel'.
Section SOUNDNESS.
  Parameter F V : Type.
  Parameter genv: Genv.t F V.
  Parameter sp : val.
  Parameter m : mem.

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

Lemma kill_sound :
  forall rel : RELATION.t,
  forall dst : reg,
  forall rs,
  forall v,
    sem_rel rel rs ->
    sem_rel (kill dst rel) (rs # dst <- v).
Proof.
  unfold sem_rel, kill, sem_reg, sem_sym_val.
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
  pose proof (kill_sound rel dst rs (rs # src) REL x) as KILL.
  pose proof (REL src) as RELsrc.
  unfold move.
  destruct (peq x dst).
  {
    subst x.
    unfold sem_reg.
    rewrite PTree.gss.
    rewrite Regmap.gss.
    unfold sem_reg in RELsrc.
    destruct move_cases; simpl.
    {
      simpl in RELsrc.
      destruct (peq dst src0).
      {
        subst src0.
        rewrite Regmap.gss.
        reflexivity.
      }
      rewrite Regmap.gso by congruence.
      assumption.
    }
    rewrite write_same.
    reflexivity.
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
    (match move_cases (kill dst rel) ! a with
     | Move_case a' => a'
     | Other_case _ => a
     end) <> dst.
Proof.
  intros until a. intro NEQ.
  unfold kill.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by congruence.
  destruct (rel ! a); simpl.
  2: congruence.
  destruct s.
  { simpl.
    destruct peq; simpl; congruence.
  }
  { simpl.
    destruct negb; simpl; congruence.
  }
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
          (fun arg : positive =>
           match move_cases (kill dst rel) ! arg with
           | Move_case arg' => arg'
           | Other_case _ => arg
           end) args) = rs ## args.
Proof.
  induction args; simpl; trivial.
  intros until v.
  intros REL NOT_IN.
  rewrite IHargs by auto.
  f_equal.
  pose proof (REL a) as RELa.
  rewrite Regmap.gso by (apply move_cases_neq; auto).
  unfold kill.
  unfold sem_reg in RELa.
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
  pose proof (kill_sound rel dst rs v REL x) as KILL.
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

(*
Definition apply_instr instr x :=
  match instr with
  | Inop _
  | Icond _ _ _ _
  | Ijumptable _ _
  | Istore _ _ _ _ _ => Some x
  | Iop Omove (src :: nil) dst _ => Some (move src dst x)
  | Iop _ _ dst _
  | Iload _ _ _ _ dst _
  | Icall _ _ _ dst _ => Some (kill dst x)
  | Ibuiltin _ _ res _ => Some (RELATION.top) (* TODO (kill_builtin_res res x) *)
  | Itailcall _ _ _ | Ireturn _ => RB.bot
  end.

Definition apply_instr' code (pc : node) (ro : RB.t) : RB.t :=
  match ro with
  | None => None
  | Some x =>
    match code ! pc with
    | None => RB.bot
    | Some instr => apply_instr instr x
    end
  end.

Definition forward_map (f : RTL.function) := DS.fixpoint
  (RTL.fn_code f) RTL.successors_instr
  (apply_instr' (RTL.fn_code f)) (RTL.fn_entrypoint f) (Some RELATION.top).

Definition get_r (rel : RELATION.t) (x : reg) :=
  match PTree.get x rel with
  | None => x
  | Some src => src
  end.

Definition get_rb (rb : RB.t) (x : reg) :=
  match rb with
  | None => x
  | Some rel => get_r rel x
  end.

Definition subst_arg (fmap : option (PMap.t RB.t)) (pc : node) (x : reg) : reg :=
  match fmap with
  | None => x
  | Some inv => get_rb (PMap.get pc inv) x
  end.

Definition subst_args fmap pc := List.map (subst_arg fmap pc).

(* Transform *)
Definition transf_instr (fmap : option (PMap.t RB.t))
           (pc: node) (instr: instruction) :=
  match instr with
  | Iop op args dst s =>
    Iop op (subst_args fmap pc args) dst s
  | Iload trap chunk addr args dst s =>
    Iload trap chunk addr (subst_args fmap pc args) dst s
  | Istore chunk addr args src s =>
    Istore chunk addr (subst_args fmap pc args) src s
  | Icall sig ros args dst s =>
    Icall sig ros (subst_args fmap pc args) dst s
  | Itailcall sig ros args =>
    Itailcall sig ros (subst_args fmap pc args)
  | Icond cond args s1 s2 =>
    Icond cond (subst_args fmap pc args) s1 s2
  | Ijumptable arg tbl =>
    Ijumptable (subst_arg fmap pc arg) tbl
  | Ireturn (Some arg) =>
    Ireturn (Some (subst_arg fmap pc arg))
  | _ => instr
  end.

Definition transf_function (f: function) : function :=
  {| fn_sig := f.(fn_sig);
     fn_params := f.(fn_params);
     fn_stacksize := f.(fn_stacksize);
     fn_code := PTree.map (transf_instr (forward_map f)) f.(fn_code);
     fn_entrypoint := f.(fn_entrypoint) |}.


Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
*)