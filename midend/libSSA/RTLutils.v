(** Utility definitions and lemmas about the RTL representation *)
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Registers.
Require Import Op.
Require Import RTL.
Require Import Kildall.
Require Import KildallComp.
Require Import Utils.
Require Import Classical.


(** * The [cfg] predicate *)
Inductive cfg (code:code) (i j:node) : Prop :=
  | CFG : forall ins
    (HCFG_ins: code!i = Some ins)
    (HCFG_in : In j (successors_instr ins)),
    cfg code i j.

Inductive cfg_star (code:code) (i:node) : node -> Prop :=
| cfg_star0 : cfg_star code i i
| cfg_star1 : forall j k, cfg_star code i j -> cfg code j k -> cfg_star code i k.

Lemma cfg_star_same : forall code i j,
  cfg_star code i j <-> (cfg code)** i j.
Proof.
  split.
  induction 1.
  constructor 2.
  constructor 3 with j; auto.
  assert (forall i j, (cfg code**) i j -> forall k, cfg_star code k i -> cfg_star code k j).
    clear i j; induction 1; auto.
    intros.
    constructor 2 with x; auto.
  intros; apply H with i; auto.
  constructor 1.
Qed.

Lemma cfg_star_same_code: forall code1 code2 i,
  (forall k, cfg_star code1 i k -> code1!k = code2!k) ->
  forall j, cfg_star code1 i j -> cfg_star code2 i j.
Proof.
  induction 2.
  constructor 1.
  constructor 2 with j; auto.
  inv H1.
  rewrite H in *; auto.
  econstructor; eauto.
Qed.


Ltac simpl_succs := 
  match goal with 
    | [H1 : (RTL.fn_code ?f) ! ?pc = Some _ |- _ ] =>
      unfold successors_list, RTL.successors_map ; rewrite PTree.gmap1 ;
        (rewrite H1; simpl; auto)
  end.
  
(** * Registers that are used in the code of a RTL function *)
(** This has to be cleaned out. Cf RTL.use_instr *)
  Inductive use_rtl_code (f: function) : Registers.reg -> node -> Prop := 
  | UIop: forall pc arg op args dst s, 
    (RTL.fn_code f) !pc = Some (RTL.Iop op args dst s)  -> In arg args -> use_rtl_code f arg pc
  | UIload: forall pc arg chk adr args dst s,
    (RTL.fn_code f) !pc = Some (RTL.Iload chk adr args dst s) -> In arg args -> use_rtl_code f arg pc
  | UIcond: forall pc arg cond args s s',
    (RTL.fn_code f) !pc = Some (RTL.Icond cond args s s') -> In arg args -> use_rtl_code f arg pc 
  | UIbuiltin: forall pc arg ef args dst s,
    (RTL.fn_code f) !pc = Some (RTL.Ibuiltin ef args dst s) -> In arg args -> use_rtl_code f arg pc
  | UIstore: forall pc arg chk adr args src s,
    (RTL.fn_code f) !pc = Some (RTL.Istore chk adr args src s) -> In arg (src::args) -> use_rtl_code f arg pc
  | UIcall: forall pc arg sig r args dst s,
    (RTL.fn_code f) !pc = Some (RTL.Icall sig (inl ident r) args dst s) -> In arg (r::args) -> use_rtl_code f arg pc
  | UIcall2: forall pc arg sig id args dst s,
    (RTL.fn_code f) !pc = Some (RTL.Icall sig (inr _ id) args dst s) -> In arg args -> use_rtl_code f arg pc
  | UItailcall: forall pc arg sig r args,
    (RTL.fn_code f) !pc = Some (RTL.Itailcall sig (inl ident r) args) -> In arg (r::args) -> use_rtl_code f arg pc
  | UItailcall2: forall pc arg sig id args,
    (RTL.fn_code f) !pc = Some (RTL.Itailcall sig (inr _ id) args) -> In arg args -> use_rtl_code f arg pc
  | UIjump: forall pc arg tbl, 
    (RTL.fn_code f) !pc = Some (RTL.Ijumptable arg tbl) -> use_rtl_code f arg pc
  | UIret: forall pc arg,
    (RTL.fn_code f) !pc = Some (RTL.Ireturn (Some arg)) -> use_rtl_code f arg pc.
  
  Lemma rtl_cfg_succs : forall f pc pc', 
    cfg (fn_code f)  pc pc' ->
    In pc' (RTL.successors_map f) !!! pc.
  Proof.
    intros. inv H.
    unfold successors_list, RTL.successors_map.
    rewrite PTree.gmap1. unfold option_map. 
    rewrite HCFG_ins ; auto.
  Qed.

  Lemma rtl_cfg_succs_instr : forall f pc ins pc', 
    cfg (fn_code f)  pc pc' ->
    (fn_code f) ! pc = Some ins ->
    In pc' (RTL.successors_instr ins).
  Proof.
    intros. inv H.
    congruence. 
  Qed.

  Hint Resolve rtl_cfg_succs.
  Hint Resolve rtl_cfg_succs_instr.
  Hint Constructors use_rtl_code.
  Hint Extern 4 (In _ (successors_instr _)) => simpl successors_instr.
  Hint Constructors cfg.

(** * Lemmas about [successors] and [make_predecessors]  *)
Lemma succ_code_incl : forall f1 f2,
  (forall i ins, (RTL.fn_code f1)!i = Some ins -> (RTL.fn_code f2)!i = Some ins) ->
  forall i, incl ((RTL.successors_map f1)!!!i) ((RTL.successors_map f2)!!!i).
Proof.
  intros.
  unfold successors_list.
  unfold RTL.successors_map.
  repeat rewrite PTree.gmap1.
  case_eq ((RTL.fn_code f1) !i); simpl; intros.
  rewrite (H _ _ H0); simpl.
  intro; auto.
  intro; simpl; intuition.
Qed.

Lemma add_successors_correct_inv:
  forall tolist from pred n s,
  In n (add_successors pred from tolist)!!!s ->
  In n pred!!!s \/ (n = from /\ In s tolist). 
Proof.
  induction tolist; simpl; intros.
  tauto.
  elim IHtolist with (1:=H); eauto.
  unfold successors_list at 1. rewrite PTree.gsspec. destruct (peq s a).
  subst a. simpl. destruct 1. auto with coqlib. 
  auto.
  fold (successors_list pred s). intuition congruence.
  intuition congruence.
Qed.

Lemma make_predecessors_eq : forall (A: Type) (m1 m2 : PTree.t A) succs,
  (forall i, (m1!i) = (m2!i)) -> 
  make_predecessors m1 succs  = make_predecessors m2 succs.
Proof.
  unfold make_predecessors.
  intros.
  apply fold_eq; auto.
Qed.

      
(* BROKEN ACROSS COMPCERT PORTING - NOT NEEDED ANYMORE
Lemma make_predecessors_correct_inv:
  forall succs m n s ,
  In n (make_predecessors m succs)!!!s ->
  In s m !!!n.
Proof.
  intros succs.
  set (P := fun pred succ =>
          forall s n, In s succ!!!n -> In n pred!!!s).
  unfold make_predecessors.
  intros m.
  apply PTree_Properties.fold_rec with (P:=P).
(* extensionality *)
  unfold P; unfold successors_list; intros.
  rewrite <- H. auto.
(* base case *)
  red; unfold successors_list. intros n s. repeat rewrite PTree.gempty. auto.
(* inductive case *)
  unfold P; intros.
  elim add_successors_correct_inv with (1:=H2); auto; intros.
  - unfold successors_list. rewrite PTree.gsspec.
    destruct (peq s k).
    * subst. 
      generalize (H1 _ _ H3).
      unfold successors_list; rewrite H; simpl; intuition.
    * fold (successors_list m0 s). auto.
  - unfold successors_list. rewrite PTree.gsspec.
    destruct (peq s k).
    *  subst; intuition.
    * intuition.
Qed.

Lemma make_predecessors_incl : forall m1 m2,
  (forall i, incl (m1!!!i) (m2!!!i)) -> 
  (forall i, incl (make_predecessors m1)!!!i (make_predecessors m2)!!!i).
Proof.
  unfold incl; intros.
  apply make_predecessors_correct_inv in H0.
  apply make_predecessors_correct; auto.
Qed.

*)

Inductive join_point (jp : node) (f : function) : Prop :=
  |  jp_cons : forall l,
                 forall (Hpreds : (make_predecessors (fn_code f) successors_instr) ! jp = Some l)
                        (Hl : (length l > 1)%nat),
                   join_point jp f.


Section UDEF.

Variable f : function.

Inductive assigned_code_spec (code:code) (pc:node) : reg -> Prop :=
| AIop: forall op args dst succ,
  code!pc = Some (Iop op args dst succ)  ->
  assigned_code_spec code pc dst
| AIload: forall chunk addr args dst succ,
  code!pc = Some (Iload chunk addr args dst succ) ->
  assigned_code_spec code pc dst
| AIcall: forall sig fn args dst succ,
  code!pc = Some (Icall sig fn args dst succ) ->
  assigned_code_spec code pc dst
| AIbuiltin: forall fn args dst succ,
  code!pc = Some (Ibuiltin fn args dst succ) ->
  assigned_code_spec code pc dst.
Hint Constructors assigned_code_spec.

End UDEF.