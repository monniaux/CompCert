(*
Replace available expressions by the register containing their value.

Proofs.

David Monniaux, CNRS, VERIMAG
 *)

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

Lemma gpset_inter_none: forall a b i,
    (pset_inter a b) ! i = None <->
    (a ! i = None) \/ (b ! i = None).
Proof.
  intros. unfold pset_inter.
  rewrite PTree.gcombine_null.
  destruct (a ! i); destruct (b ! i); intuition discriminate.
Qed.

Lemma some_some:
  forall x : option unit,
    x <> None <-> x = Some tt.
Proof.
  destruct x as [[] | ]; split; congruence.
Qed.  

Lemma gpset_inter_some: forall a b i,
    (pset_inter a b) ! i = Some tt <->
    (a ! i = Some tt) /\ (b ! i = Some tt).
Proof.
  intros. unfold pset_inter.
  rewrite PTree.gcombine_null.
  destruct (a ! i) as [[] | ]; destruct (b ! i) as [[] | ]; intuition congruence.
Qed.

Definition wellformed_mem (rel : RELATION.t) : Prop :=
  forall i sv,
  (var_to_sym rel) ! i = Some sv ->
  kill_sym_val_mem sv = true ->
  (mem_used rel) ! i = Some tt.

Definition wellformed_reg (rel : RELATION.t) : Prop :=
  forall i j sv,
  (var_to_sym rel) ! i = Some sv ->
  kill_sym_val j sv = true ->
  match (reg_used rel) ! j with
  | Some uses => uses ! i = Some tt
  | None => False
  end.

Lemma wellformed_mem_top : wellformed_mem RELATION.top.
Proof.
  unfold wellformed_mem, RELATION.top, pset_empty.
  simpl.
  intros.
  rewrite PTree.gempty in *.
  discriminate.
Qed.
Local Hint Resolve wellformed_mem_top : wellformed.

Lemma wellformed_reg_top : wellformed_reg RELATION.top.
Proof.
  unfold wellformed_reg, RELATION.top, pset_empty.
  simpl.
  intros.
  rewrite PTree.gempty in *.
  discriminate.
Qed.
Local Hint Resolve wellformed_reg_top : wellformed.

Lemma wellformed_mem_lub : forall a b,
    (wellformed_mem a) -> (wellformed_mem b) -> (wellformed_mem (RELATION.lub a b)).
Proof.
  unfold wellformed_mem, RELATION.lub.
  simpl.
  intros a b Ha Hb.
  intros i sv COMBINE KILLABLE.
  rewrite PTree.gcombine in *.
  2: reflexivity.
  destruct (var_to_sym a) ! i as [syma | ] eqn:SYMA;
    destruct (var_to_sym b) ! i as [symb | ] eqn:SYMB;
    try discriminate.
  destruct (eq_sym_val syma symb); try discriminate.
  subst syma.
  inv COMBINE.
  apply gpset_inter_some.
  split; eauto.
Qed.
Local Hint Resolve wellformed_mem_lub : wellformed.

Lemma wellformed_reg_lub : forall a b,
    (wellformed_reg a) -> (wellformed_reg b) -> (wellformed_reg (RELATION.lub a b)).
Proof.
  unfold wellformed_reg, RELATION.lub.
  simpl.
  intros a b Ha Hb.
  intros i j sv COMBINE KILLABLE.
  specialize Ha with (i := i) (j := j).
  specialize Hb with (i := i) (j := j).
  rewrite PTree.gcombine in *.
  2: reflexivity.
  destruct (var_to_sym a) ! i as [syma | ] eqn:SYMA;
    destruct (var_to_sym b) ! i as [symb | ] eqn:SYMB;
    try discriminate.
  specialize Ha with (sv := syma).
  specialize Hb with (sv := symb).
  destruct (eq_sym_val syma symb); try discriminate.
  subst syma.
  inv COMBINE.
  rewrite PTree.gcombine_null.
  destruct ((reg_used a) ! j) as [uA| ]; destruct ((reg_used b) ! j) as [uB | ]; auto.
  { pose proof (PTree.bempty_canon_correct (pset_inter uA uB) i) as EMPTY.
    destruct PTree.bempty_canon.
  - rewrite gpset_inter_none in EMPTY.
    intuition congruence.
  - rewrite gpset_inter_some.
    auto.
  }
Qed.
Local Hint Resolve wellformed_reg_lub : wellformed.

Lemma wellformed_mem_kill_reg:
  forall dst rel,
    (wellformed_mem rel) -> (wellformed_mem (kill_reg dst rel)).
Proof.
  unfold wellformed_mem, kill_reg, pset_remove.
  simpl.
  intros dst rel Hrel.
  intros i sv KILLREG KILLABLE.
  rewrite PTree.gfilter1 in KILLREG.
  destruct (peq dst i).
  { subst i.
    rewrite PTree.grs in *.
    discriminate.
  }
  rewrite PTree.gro in * by congruence.
  specialize Hrel with (i := i).
  eapply Hrel.
  2: eassumption.  
  destruct (_ ! i); try discriminate.
  destruct negb; congruence.
Qed.
Local Hint Resolve wellformed_mem_kill_reg : wellformed.

Lemma kill_sym_val_referenced:
  forall dst,
  forall sv,
    (kill_sym_val dst sv)=true <-> In dst (referenced_by sv).
Proof.
  intros.
  destruct sv; simpl.
  - destruct peq; intuition congruence.
  - rewrite existsb_exists.
    split.
    + intros [x [IN EQ]].
      destruct peq.
      * subst x; trivial.
      * discriminate.
    + intro.
      exists dst.
      split; trivial.
      destruct peq; trivial.
      congruence.
  - rewrite existsb_exists.
    split.
    + intros [x [IN EQ]].
      destruct peq.
      * subst x; trivial.
      * discriminate.
    + intro.
      exists dst.
      split; trivial.
      destruct peq; trivial.
      congruence.
Qed.
Local Hint Resolve kill_sym_val_referenced : wellformed.

Lemma remove_from_sets_notin:
  forall dst l sets j,
    not (In j l) ->
    (remove_from_sets dst l sets) ! j = sets ! j.
Proof.
  induction l; simpl; trivial.
  intros.
  rewrite IHl by tauto.
  destruct (@PTree.get (PTree.t unit) a sets) eqn:SETSA; trivial.
  pose proof (PTree.bempty_canon_correct (PTree.remove dst t)) as CORRECT.
  destruct (PTree.bempty_canon (PTree.remove dst t)).
  - apply PTree.gro.
    intuition.
  - rewrite PTree.gso by intuition.
    trivial.
Qed.

Lemma remove_from_sets_pass:
  forall dst l sets i j,
    i <> dst ->
    match sets ! j with
    | Some uses => uses ! i = Some tt
    | None => False
    end ->
    match (remove_from_sets dst l sets) ! j with
    | Some uses => uses ! i = Some tt
    | None => False
    end.
Proof.
  induction l; simpl; trivial.
  intros.
  apply IHl; trivial.
  destruct (@PTree.get (PTree.t unit) a sets) eqn:SETSA; trivial.
  pose proof (PTree.bempty_canon_correct (PTree.remove dst t)) as CORRECT.
  specialize CORRECT with (i := i).
  destruct (PTree.bempty_canon (PTree.remove dst t)).
  - rewrite PTree.gro in CORRECT by congruence.
    destruct (peq a j).
    + subst a.
      rewrite SETSA in *.
      intuition congruence.
    + rewrite PTree.gro by congruence.
      assumption.
  - destruct (peq a j).
    + subst a.
      rewrite SETSA in *.
      rewrite PTree.gss.
      rewrite PTree.gro by congruence.
      assumption.
    + rewrite PTree.gso by congruence.
      assumption.
Qed.
Local Hint Resolve remove_from_sets_pass : wellformed.

Lemma rem_comes_from:
  forall A x y (tr: PTree.t A) v,
    (PTree.remove x tr) ! y = Some v -> tr ! y = Some v.
Proof.
  intros.
  destruct (peq x y).
  - subst y.
    rewrite PTree.grs in *.
    discriminate.
  - rewrite PTree.gro in * by congruence.
    assumption.
Qed.
Local Hint Resolve rem_comes_from : wellformed.

Lemma rem_ineq:
  forall A x y (tr: PTree.t A) v,
    (PTree.remove x tr) ! y = Some v -> x<>y.
Proof.
  intros.
  intro.
  subst y.
  rewrite PTree.grs in *.
  discriminate.
Qed.
Local Hint Resolve rem_ineq : wellformed.

Lemma wellformed_reg_kill_reg:
  forall dst rel,
    (wellformed_reg rel) -> (wellformed_reg (kill_reg dst rel)).
Proof.
  unfold wellformed_reg, kill_reg.
  simpl.
  intros dst rel Hrel.
  intros i j sv KILLREG KILLABLE.

  rewrite PTree.gfilter1 in KILLREG.
  destruct PTree.get eqn:REMi in KILLREG.
  2: discriminate.
  destruct negb eqn:NEGB in KILLREG.
  2: discriminate.
  inv KILLREG.

  assert ((var_to_sym rel) ! i = Some sv) as RELi by eauto with wellformed.
  
  destruct (peq dst j).
  { (* absurd case *)
    subst j.
    rewrite KILLABLE in NEGB.
    simpl in NEGB.
    discriminate.
  }
  specialize Hrel with (i := i) (j := j) (sv := sv).
  destruct ((var_to_sym rel) ! dst) eqn:DST; simpl.
  {
    assert (dst <> i) by eauto with wellformed.
    apply remove_from_sets_pass.
    congruence.
    rewrite PTree.gro by congruence.
    apply Hrel; trivial.
  }
  rewrite PTree.gro by congruence.
  apply Hrel; trivial.
Qed.
Local Hint Resolve wellformed_reg_kill_reg : wellformed.

Lemma wellformed_mem_kill_mem:
  forall rel,
    (wellformed_mem rel) -> (wellformed_mem (kill_mem rel)).
Proof.
  unfold wellformed_mem, kill_mem.
  simpl.
  intros rel Hrel.
  intros i sv KILLMEM KILLABLE.
  rewrite PTree.gremove_t in KILLMEM.
  exfalso.
  specialize Hrel with (i := i).
  destruct ((var_to_sym rel) ! i) eqn:RELi.
  - specialize Hrel with (sv := s).
    destruct ((mem_used rel) ! i) eqn:USEDi.
    discriminate.
    inv KILLMEM.
    intuition congruence.
 - destruct ((mem_used rel) ! i); discriminate.
Qed.
Local Hint Resolve wellformed_mem_kill_mem : wellformed.

Lemma wellformed_reg_kill_mem:
  forall rel,
    (wellformed_reg rel) -> (wellformed_reg (kill_mem rel)).
Proof.
  unfold wellformed_reg, kill_mem.
  simpl.
  intros rel Hrel.
  intros i j sv KILLMEM KILLABLE.
  apply Hrel with (sv := sv); trivial.
  rewrite PTree.gremove_t in KILLMEM.
  destruct ((mem_used rel) ! i) in KILLMEM.
  discriminate.
  assumption.
Qed.
Local Hint Resolve wellformed_reg_kill_mem : wellformed.

Lemma wellformed_mem_move:
  forall r dst rel,
    (wellformed_mem rel) -> (wellformed_mem (move r dst rel)).
Proof.
  Local Opaque kill_reg.
  intros; unfold move, wellformed_mem; simpl.
  intros i sv MOVE KILL.
  destruct (peq i dst).
  { subst i.
    rewrite PTree.gss in MOVE.
    inv MOVE.
    simpl in KILL.
    discriminate.
  }
  rewrite PTree.gso in MOVE by congruence.
  eapply wellformed_mem_kill_reg; eauto.
Qed.
Local Hint Resolve wellformed_mem_move : wellformed.

Lemma wellformed_mem_oper2:
  forall op dst args rel,
    (wellformed_mem rel) ->
    (wellformed_mem (oper2 op dst args rel)).
Proof.
  intros until rel. intro WELLFORMED.
  unfold oper2.
  intros i sv MOVE OPER.
  simpl in *.
  destruct (peq i dst).
  { subst i.
    rewrite PTree.gss in MOVE.
    inv MOVE.
    simpl in OPER.
    rewrite OPER.
    apply PTree.gss.
  }
  unfold pset_add.
  rewrite PTree.gso in MOVE by congruence.
  destruct op_depends_on_memory.
  - rewrite PTree.gso by congruence.
    eapply wellformed_mem_kill_reg; eauto.
  - eapply wellformed_mem_kill_reg; eauto.
Qed.
Local Hint Resolve wellformed_mem_oper2 : wellformed.

Lemma wellformed_mem_oper1:
  forall op dst args rel,
    (wellformed_mem rel) ->
    (wellformed_mem (oper1 op dst args rel)).
Proof.
  unfold oper1. intros.
  destruct in_dec ; auto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_oper1 : wellformed.

Lemma wellformed_mem_oper:
  forall op dst args rel,
    (wellformed_mem rel) ->
    (wellformed_mem (oper op dst args rel)).
Proof.
  unfold oper. intros.
  destruct find_op ; auto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_oper : wellformed.

Lemma wellformed_mem_gen_oper:
  forall op dst args rel,
    (wellformed_mem rel) ->
    (wellformed_mem (gen_oper op dst args rel)).
Proof.
  intros.
  unfold gen_oper.
  destruct op; auto with wellformed.
  destruct args; auto with wellformed.
  destruct args; auto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_gen_oper : wellformed.

Lemma wellformed_mem_load2 :
  forall chunk addr dst args rel,
    (wellformed_mem rel) ->
    (wellformed_mem (load2 chunk addr dst args rel)).
Proof.
  intros.
  unfold load2, wellformed_mem.
  simpl.
  intros i sv LOAD KILL.
  destruct (peq i dst).
  { subst i.
    apply PTree.gss.
  }
  unfold pset_add.
  rewrite PTree.gso in * by congruence.
  eapply wellformed_mem_kill_reg; eauto.
Qed.
Local Hint Resolve wellformed_mem_load2 : wellformed.

Lemma wellformed_mem_load1 :
  forall chunk addr dst args rel,
    (wellformed_mem rel) ->
    (wellformed_mem (load1 chunk addr dst args rel)).
Proof.
  intros.
  unfold load1.
  destruct in_dec; eauto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_load1 : wellformed.

Lemma wellformed_mem_load :
  forall chunk addr dst args rel,
    (wellformed_mem rel) ->
    (wellformed_mem (load chunk addr dst args rel)).
Proof.
  intros.
  unfold load.
  destruct find_load; eauto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_load : wellformed.

Definition wellformed_mem_rb (rb : RB.t) :=
  match rb with
  | None => True
  | Some r => wellformed_mem r
  end.

Lemma wellformed_mem_apply_instr:
  forall instr rel,
    (wellformed_mem rel) ->
    (wellformed_mem_rb (apply_instr instr rel)).
Proof.
  destruct instr; simpl; auto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_apply_instr : wellformed.

Lemma wellformed_mem_rb_bot :
  wellformed_mem_rb RB.bot.
Proof.
  simpl.
  trivial.
Qed.
Local Hint Resolve wellformed_mem_rb_bot: wellformed.

Lemma wellformed_mem_rb_top :
  wellformed_mem_rb RB.top.
Proof.
  simpl.
  auto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_rb_top: wellformed.

Lemma wellformed_mem_rb_apply_instr':
  forall code pc rel,
    (wellformed_mem_rb rel) ->
    (wellformed_mem_rb (apply_instr' code pc rel)).
Proof.
  destruct rel; simpl; trivial.
  intro.
  destruct (code ! pc);
  eauto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_rb_apply_instr' : wellformed.

Lemma wellformed_mem_rb_lub : forall a b,
    (wellformed_mem_rb a) -> (wellformed_mem_rb b) -> (wellformed_mem_rb (RB.lub a b)).
Proof.
  destruct a; destruct b; simpl; auto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_rb_lub: wellformed.

Definition wellformed_mem_fmap fmap :=
  forall i, wellformed_mem_rb (fmap !! i).

Theorem wellformed_mem_forward_map : forall f,
    forall fmap, (forward_map f) = Some fmap ->
    wellformed_mem_fmap fmap.
Proof.
  intros.
  unfold forward_map in *.
  unfold wellformed_mem_fmap.
  intro.
  eapply DS.fixpoint_invariant with (ev := Some RELATION.top); eauto with wellformed.
Qed.
Local Hint Resolve wellformed_mem_forward_map: wellformed.

Local Transparent kill_reg.

Section SOUNDNESS.
  Variable F V : Type.
  Variable genv: Genv.t F V.
  Variable sp : val.

Section SAME_MEMORY.
  Variable m : mem.

Definition sem_sym_val sym rs (v : option val) : Prop :=
  match sym with
  | SMove src => v = Some (rs # src)
  | SOp op args =>
    v = (eval_operation genv sp op (rs ## args) m)
  | SLoad chunk addr args =>
    match eval_addressing genv sp addr rs##args with
    | Some a => v = (Mem.loadv chunk m a)
    | None   => v = None \/ v = Some Vundef
    end
  end.
    
Definition sem_reg (rel : RELATION.t) (x : reg) (rs : regset) (v : val) : Prop :=
  match (var_to_sym rel) ! x with
  | None => True
  | Some sym => sem_sym_val sym rs (Some (rs # x)) 
  end.

Definition sem_rel (rel : RELATION.t) (rs : regset) :=
  forall x : reg, (sem_reg rel x rs (rs # x)).

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
  destruct (_ ! arg); trivial.
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
  intros REL x. simpl.
  rewrite PTree.gfilter1.
  destruct (Pos.eq_dec dst x).
  {
    subst x.
    rewrite PTree.grs.
    trivial.
  }
  rewrite PTree.gro by congruence.
  rewrite Regmap.gso by congruence.
  destruct (_ ! x) as [relx | ] eqn:RELx; trivial.
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
    simpl.
    rewrite PTree.gss.
    rewrite Regmap.gss.
    unfold sem_reg in *.
    simpl.
    unfold forward_move.
    destruct (_ ! src) as [ sv |]; simpl.
    destruct sv eqn:SV; simpl in *.
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
    all: f_equal; symmetry; apply write_same.
  }
  rewrite Regmap.gso by congruence.
  unfold sem_reg.
  simpl.
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
  simpl.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by congruence.
  destruct (_ ! a); simpl.
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
  simpl.
  rewrite PTree.gfilter1.
  rewrite PTree.gro by auto.
  destruct (_ ! a); simpl; trivial.
  destruct s; simpl in *; destruct negb; simpl; congruence.
Qed.

Lemma oper2_sound :
  forall rel : RELATION.t,
  forall op : operation,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall v,
    sem_rel rel rs ->
    not (In dst args) ->
    eval_operation genv sp op (rs ## args) m = Some v ->
    sem_rel (oper2 op dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL NOT_IN EVAL x.
  pose proof (kill_reg_sound rel dst rs v REL x) as KILL.
  unfold oper2.
  destruct (peq x dst).
  {
    subst x.
    unfold sem_reg.
    simpl.
    rewrite PTree.gss.
    rewrite Regmap.gss.
    simpl.
    rewrite args_replace_dst by auto.
    symmetry.
    assumption.
  }
  rewrite Regmap.gso by congruence.
  unfold sem_reg.
  simpl.
  rewrite PTree.gso by congruence.
  rewrite Regmap.gso in KILL by congruence.
  exact KILL.
Qed.

Lemma oper1_sound :
  forall rel : RELATION.t,
  forall op : operation,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall v,
    sem_rel rel rs ->
    eval_operation genv sp op (rs ## args) m = Some v ->
    sem_rel (oper1 op dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL EVAL.
  unfold oper1.
  destruct in_dec.
  {
    apply kill_reg_sound; auto. 
  }
  apply oper2_sound; auto.
Qed.

Lemma find_op_sound :
  forall rel : RELATION.t,
  forall op : operation,
  forall src : reg,
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
     find_op_fold op args a (fst p) (snd p)) (PTree.elements (var_to_sym rel)) start =
                    Some src ->
             eval_operation genv sp op rs ## args m = Some rs # src) as REC.
  {
    unfold sem_rel, sem_reg in REL.
    generalize (PTree.elements_complete (var_to_sym rel)).
    generalize (PTree.elements (var_to_sym rel)).
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
    destruct sv; trivial.
    destruct eq_operation; trivial.
    subst op0.
    destruct eq_args; trivial.
    subst args0.
    simpl.
    assert (((var_to_sym rel) ! r) = Some (SOp op args)) as RELatr.
    {
      apply COMPLETE.
      left.
      reflexivity.
    }
    pose proof (REL r) as RELr.
    rewrite RELatr in RELr.
    simpl in RELr.
    symmetry.
    assumption.
  }
  apply REC; auto.
Qed.

Lemma find_load_sound :
  forall rel : RELATION.t,
  forall chunk : memory_chunk,
  forall addr : addressing,
  forall src : reg,
  forall args: list reg,
  forall rs : regset,
    sem_rel rel rs ->
    find_load rel chunk addr args = Some src ->
    match eval_addressing genv sp addr rs##args with
    | Some a => (Mem.loadv chunk m a) = Some (rs # src)
    | None => True
    end.
Proof.
  intros until rs.
  unfold find_load.
  rewrite PTree.fold_spec.
  intro REL.
  assert (
     forall start,
             match start with
             | None => True
             | Some src =>
               match eval_addressing genv sp addr rs##args with
               | Some a => (Mem.loadv chunk m a) = Some (rs # src)
               | None => True
               end               
             end ->
    fold_left
    (fun (a : option reg) (p : positive * sym_val) =>
     find_load_fold chunk addr args a (fst p) (snd p)) (PTree.elements (var_to_sym rel)) start =
    Some src ->
    match eval_addressing genv sp addr rs##args with
               | Some a => (Mem.loadv chunk m a) = Some (rs # src)
               | None => True
               end ) as REC.
  
  {
    unfold sem_rel, sem_reg in REL.
    generalize (PTree.elements_complete (var_to_sym rel)).
    generalize (PTree.elements (var_to_sym rel)).
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
    unfold find_load_fold.
    destruct start.
    assumption.
    destruct sv; trivial.
    destruct chunk_eq; trivial.
    subst chunk0.
    destruct eq_addressing; trivial.
    subst addr0.
    destruct eq_args; trivial.
    subst args0.
    simpl.
    assert (((var_to_sym rel) ! r) = Some (SLoad chunk addr args)) as RELatr.
    {
      apply COMPLETE.
      left.
      reflexivity.
    }
    pose proof (REL r) as RELr.
    rewrite RELatr in RELr.
    simpl in RELr.
    destruct eval_addressing; congruence.
  }
  apply REC; auto.
Qed.

Lemma find_load_sound' :
  forall rel : RELATION.t,
  forall chunk : memory_chunk,
  forall addr : addressing,
  forall src : reg,
  forall args: list reg,
  forall rs : regset,
  forall a,
    sem_rel rel rs ->
    find_load rel chunk addr args = Some src ->
    eval_addressing genv sp addr rs##args = Some a ->
    (Mem.loadv chunk m a) = Some (rs # src).
Proof.
  intros until a. intros REL LOAD ADDR.
  pose proof (find_load_sound rel chunk addr src args rs REL LOAD) as Z.
  destruct eval_addressing in *; congruence.
Qed.

Lemma forward_move_map:
  forall rel args rs,
    sem_rel rel rs ->
    rs ## (map (forward_move rel) args) = rs ## args.
Proof.
  induction args; simpl; trivial.
  intros rs REL.
  f_equal.
  2: (apply IHargs; assumption).
  unfold forward_move, sem_rel, sem_reg, sem_sym_val in *.
  pose proof (REL a) as RELa.
  destruct (_ ! a); trivial.
  destruct s; congruence.
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
  destruct find_op eqn:FIND.
  {
    assert (eval_operation genv sp op rs ## (map (forward_move rel) args) m = Some rs # r) as FIND_OP.
    {
      apply (find_op_sound rel); trivial.
    }
    rewrite forward_move_map in FIND_OP by assumption.
    replace v with (rs # r) by congruence.
    apply move_sound; auto.
  }
  apply oper1_sound; trivial.
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


Lemma load2_sound :
  forall rel : RELATION.t,
  forall chunk : memory_chunk,
  forall addr : addressing,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall a,
  forall v,
    sem_rel rel rs ->
    not (In dst args) ->
    eval_addressing genv sp addr (rs ## args) = Some a ->
    Mem.loadv chunk m a = Some v ->
    sem_rel (load2 chunk addr dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL NOT_IN ADDR LOAD x.
  pose proof (kill_reg_sound rel dst rs v REL x) as KILL.
  unfold load2.
  destruct (peq x dst).
  {
    subst x.
    unfold sem_reg.
    simpl.
    rewrite PTree.gss.
    rewrite Regmap.gss.
    simpl.
    rewrite args_replace_dst by auto.
    destruct eval_addressing; congruence.
  }
  rewrite Regmap.gso by congruence.
  unfold sem_reg.
  simpl.
  rewrite PTree.gso by congruence.
  rewrite Regmap.gso in KILL by congruence.
  exact KILL.
Qed.

Lemma load1_sound :
  forall rel : RELATION.t,
  forall chunk : memory_chunk,
  forall addr : addressing,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall a,
  forall v,
    sem_rel rel rs ->
    eval_addressing genv sp addr (rs ## args) = Some a ->
    Mem.loadv chunk m a = Some v ->
    sem_rel (load1 chunk addr dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL ADDR LOAD.
  unfold load1.
  destruct in_dec.
  {
    apply kill_reg_sound; auto. 
  }
  apply load2_sound with (a := a); auto.
Qed.

Lemma load_sound :
  forall rel : RELATION.t,
  forall chunk : memory_chunk,
  forall addr : addressing,
  forall dst : reg,
  forall args: list reg,
  forall rs : regset,
  forall a,
  forall v,
    sem_rel rel rs ->
    eval_addressing genv sp addr (rs ## args) = Some a ->
    Mem.loadv chunk m a = Some v ->
    sem_rel (load chunk addr dst args rel) (rs # dst <- v).
Proof.
  intros until v.
  intros REL ADDR LOAD.
  unfold load.
  destruct find_load eqn:FIND.
  {
    assert (match eval_addressing genv sp addr rs##(map (forward_move rel) args) with
    | Some a => (Mem.loadv chunk m a) = Some (rs # r)
    | None => True
    end) as FIND_LOAD.
    {
      apply (find_load_sound rel); trivial.
    }
    rewrite forward_move_map in FIND_LOAD by assumption.
    destruct eval_addressing in *.
    2: discriminate.
    replace v with (rs # r) by congruence.
    apply move_sound; auto.
  }
  apply load1_sound with (a := a); trivial.
Qed.

Lemma kill_reg_weaken:
  forall res mpc rs,
    sem_rel mpc rs ->
    sem_rel (kill_reg res mpc) rs.
Proof.
  intros until rs.
  intros REL x.
  pose proof (REL x) as RELx.
  unfold kill_reg, sem_reg in *.
  simpl.
  rewrite PTree.gfilter1.
  destruct (peq res x).
  { subst x.
    rewrite PTree.grs.
    reflexivity.
  }
  rewrite PTree.gro by congruence.
  destruct (_ ! x) as [sv | ]; trivial.
  destruct negb; trivial.
Qed.

Lemma top_ok:
  forall rs, sem_rel RELATION.top rs.
Proof.
  unfold sem_rel, sem_reg, RELATION.top.
  intros.
  rewrite PTree.gempty.
  reflexivity.
Qed.

Lemma sem_rel_ge:
  forall r1 r2 : RELATION.t,
    (RELATION.ge r1 r2) ->
    forall rs : regset,
      (sem_rel r2 rs) -> (sem_rel r1 rs).
Proof.
  intros r1 r2 GE rs RE x.
  pose proof (RE x) as REx.
  pose proof (GE x) as GEx.
  unfold sem_reg in *.
  destruct ((var_to_sym r1) ! x) as [r1x | ] in *;
    destruct ((var_to_sym r2) ! x) as [r2x | ] in *;
    congruence.
Qed.
End SAME_MEMORY.

Lemma kill_mem_sound :
  forall m m' : mem,
  forall rel : RELATION.t,
  forall rs,
    wellformed_mem rel ->
    sem_rel m rel rs -> sem_rel m' (kill_mem rel) rs.
Proof.
  unfold sem_rel, sem_reg.
  intros until rs.
  intros WELLFORMED SEM x.
  unfold wellformed_mem in *.
  specialize SEM with (x := x).
  specialize WELLFORMED with (i := x).
  unfold kill_mem.
  simpl.
  rewrite PTree.gremove_t.
  unfold kill_sym_val_mem.
  destruct ((var_to_sym rel) ! x) as [ sv | ] eqn:VAR.
  - specialize WELLFORMED with (sv0 := sv).
    destruct ((mem_used rel) ! x) eqn:USED; trivial.
    unfold sem_sym_val in *.
    destruct sv; simpl in *; trivial.
    + rewrite op_depends_on_memory_correct with (m2 := m).
      assumption.
      destruct op_depends_on_memory; intuition congruence.
    + intuition discriminate.
  - replace (match (mem_used rel) ! x with
        | Some _ | _ => None
             end) with (@None sym_val) by
        (destruct ((mem_used rel) ! x); trivial).
    trivial.
Qed.

End SOUNDNESS.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

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
Definition subst_arg_ok' := subst_arg_ok fundef unit ge.
Definition subst_args_ok' := subst_args_ok fundef unit ge.
Definition kill_mem_sound' := kill_mem_sound fundef unit ge.

Lemma sem_rel_b_ge:
  forall rb1 rb2 : RB.t,
    (RB.ge rb1 rb2) ->
    forall sp m,
    forall rs : regset,
      (sem_rel_b' sp m rb2 rs) -> (sem_rel_b' sp m rb1 rs).
Proof.
  unfold sem_rel_b', sem_rel_b.
  destruct rb1 as [r1 | ];
    destruct rb2 as [r2 | ]; simpl;
      intros GE sp m rs RE; try contradiction.
  apply sem_rel_ge with (r2 := r2); assumption.
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
    (forall m : mem,
     forall vres, (fmap_sem' sp m (forward_map f) pc rs # res <- vres)) ->
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

Lemma wellformed_mem_mpc:
  forall f map pc mpc,
    (forward_map f) = Some map ->
    map # pc = Some mpc ->
    wellformed_mem mpc.
Proof.
  intros.
  assert (wellformed_mem_fmap map) by eauto with wellformed.
  unfold wellformed_mem_fmap, wellformed_mem_rb in *.
  specialize H1 with (i := pc).
  rewrite H0 in H1.
  assumption.
Qed.
Hint Resolve wellformed_mem_mpc : wellformed.

Lemma match_same_option :
  forall { A B : Type},
  forall x : option A,
  forall y : B,
    (match x with Some _ => y | None => y end) = y.
Proof.
  destruct x; trivial.
Qed.

Lemma match_same_bool :
  forall { B : Type},
  forall x : bool,
  forall y : B,
    (if x then y else y) = y.
Proof.
  destruct x; trivial.
Qed.

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
  unfold transf_instr in *.
  destruct (if is_trivial_op op then None else find_op_in_fmap (forward_map f)  pc op (subst_args (forward_map f) pc args)) eqn:FIND_OP.
  {
    destruct is_trivial_op. discriminate.
    unfold find_op_in_fmap, fmap_sem', fmap_sem in *.
    destruct (forward_map f) as [map |] eqn:MAP.
    2: discriminate.
    change (@PMap.get (option RELATION.t) pc map) with (map # pc) in *. 
    destruct (map # pc) as [mpc | ] eqn:MPC.
    2: discriminate.
    econstructor; split.
    {
      eapply exec_Iop with (v := v); eauto.
      simpl.
      rewrite <- subst_args_ok with (genv := ge) (f := f) (pc := pc) (sp := sp) (m := m) in H0.
      {
        rewrite MAP in H0.
        rewrite find_op_sound with (rel := mpc) (src := r) in H0 by assumption.
        assumption.
      }
      unfold fmap_sem. rewrite MAP. rewrite MPC. assumption.
    }
    constructor; eauto.
    unfold fmap_sem', fmap_sem in *.
    rewrite MAP.
    apply sem_rel_b_ge with (rb2 := Some (gen_oper op res args mpc)).
    {
      replace (Some (gen_oper op res args mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
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
    unfold sem_rel_b', sem_rel_b.
    apply gen_oper_sound; auto.
  }
  {
    econstructor; split.
    {
      eapply exec_Iop with (v := v); eauto.
      rewrite (subst_args_ok' sp m) by assumption.
      rewrite <- H0.
      apply eval_operation_preserved. exact symbols_preserved.
    }
    constructor; eauto.
    unfold fmap_sem', fmap_sem in *.
    unfold find_op_in_fmap, fmap_sem', fmap_sem in *.
    destruct (forward_map f) as [map |] eqn:MAP.
    2: constructor.
    change (@PMap.get (option RELATION.t) pc map) with (map # pc) in *. 
    destruct (map # pc) as [mpc | ] eqn:MPC.
    2: contradiction.

    apply sem_rel_b_ge with (rb2 := Some (gen_oper op res args mpc)).
    {
      replace (Some (gen_oper op res args mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
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
    unfold sem_rel_b', sem_rel_b.
    apply gen_oper_sound; auto.
  }
    
(* load *)
- unfold transf_instr in *.
  destruct find_load_in_fmap eqn:FIND_LOAD.
  {
    unfold find_load_in_fmap, fmap_sem', fmap_sem in *.
    destruct (forward_map f) as [map |] eqn:MAP.
    2: discriminate.
    change (@PMap.get (option RELATION.t) pc map) with (map # pc) in *. 
    destruct (map # pc) as [mpc | ] eqn:MPC.
    2: discriminate.
    econstructor; split.
    {
      eapply exec_Iop with (v := v); eauto.
      simpl.
      rewrite <- subst_args_ok with (genv := ge) (f := f) (pc := pc) (sp := sp) (m := m) in H0.
      {
        rewrite find_load_sound' with (genv := ge) (sp := sp) (addr := addr) (args := subst_args (Some map) pc args) (rel := mpc) (src := r) (rs := rs) in H1; trivial.
        rewrite MAP in H0.
        assumption.
      }
      unfold fmap_sem. rewrite MAP. rewrite MPC. assumption.
    }
    constructor; eauto.
    unfold fmap_sem', fmap_sem in *.
    rewrite MAP.
    apply sem_rel_b_ge with (rb2 := Some (load chunk addr dst args mpc)).
    {
      replace (Some (load chunk addr dst args mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
      {
        eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
        2: apply apply_instr'_bot.
        simpl. tauto.
      }
      unfold apply_instr'.
      rewrite H.
      rewrite MPC.
      simpl.
      reflexivity.
    }
    unfold sem_rel_b', sem_rel_b.
    apply load_sound with (a := a); auto.
  }
  {  
  econstructor; split.
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
  apply sem_rel_b_ge with (rb2 := Some (load chunk addr dst args mpc)).
  {
    replace (Some (load chunk addr dst args mpc)) with (apply_instr' (fn_code f) pc (map # pc)).
    {
      eapply DS.fixpoint_solution with (code := fn_code f) (successors := successors_instr); try eassumption.
      2: apply apply_instr'_bot.
      simpl. tauto.
    }
    unfold apply_instr'.
    rewrite H.
    rewrite MPC.
    simpl.
    reflexivity.
  }
  apply load_sound with (a := a); assumption.
  }
  
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
  apply (kill_mem_sound' sp m); eauto with wellformed.
  
(* call *)
- econstructor; split.
  eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  rewrite (subst_args_ok' sp m) by assumption.
  constructor. constructor; auto.

  constructor.
  {
    intros m' vres.
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
    apply kill_reg_sound.
    apply (kill_mem_sound' sp m); eauto with wellformed.
  }
  
(* tailcall *)
- econstructor; split.
  eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  rewrite (subst_args_ok' (Vptr stk Ptrofs.zero) m) by assumption.
  constructor. auto.

(* builtin *)
- econstructor; split.
  eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

  simpl in *.
  unfold fmap_sem', fmap_sem in *.
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
  rewrite (subst_args_ok' sp m); eassumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem', fmap_sem in *.
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
  rewrite (subst_arg_ok' sp m); eassumption.
  constructor; auto.

  simpl in *.
  unfold fmap_sem', fmap_sem in *.
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
    rewrite (subst_arg_ok' (Vptr stk Ptrofs.zero) m) by eassumption.
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
  unfold fmap_sem', fmap_sem in *.
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
Admitted.


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

End PRESERVATION.
