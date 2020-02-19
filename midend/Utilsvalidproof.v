(** This file contains utility lemmas for the correctness proof of the type system.
   The proof uses an auxiliary specification for the type system.
   The specification parts common to both type system are defined in this file as well.
*)
Require Import Coq.Unicode.Utf8.
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import KildallComp.
Require Import Conventions.
Require Import SSA.
Require Import SSAutils.
Require Import SSAvalid.
Require Import Utils.
Require Import Classical.

(** * Tactics *)
Ltac allinv := 
  repeat 
    match goal with 
      | [ H1:   (fn_code ?tf) ! ?pc = Some _  ,
        H2: (fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   (RTL.fn_code ?tf) ! ?pc = Some _  ,
        H2: (RTL.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   (fn_phicode ?tf) ! ?pc = Some _  ,
        H2: (fn_phicode ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1: ?Γ ! ?pc =  _  ,
        H2: ?Γ ! ?pc =  _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1: index_pred  _ ?pc ?pc' = Some _  ,
        H2: index_pred  _ ?pc ?pc' = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1: ?Δ ! ?pc = _  ,
        H2: ?Δ ! ?pc = _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H:  ?Γ _ = ?Γ _  |- _ ] => rewrite H in *
      | _ => idtac
    end.

Ltac elimAndb :=
  match goal with
  | [ H: _ && _ = true |- _ ] =>
      elim (andb_prop _ _ H); clear H; intros; elimAndb
  | _ =>
      idtac
  end.

(** * Common part of both type systems *)


Definition update (rindex: Registers.reg -> index) (r:Registers.reg) (i:index):Registers.reg -> index :=
  fun reg: Registers.reg => if (peq reg r) then i else rindex reg. 

(** ** The erasure function *)
(** This explains the correspondance between an SSA form candidate and
its initial RTL version: the latter should be recover by unindexing
registers, and removing phi-block. *)

Definition erase_reg (r: reg) := fst  r.

Lemma map_map_erase : forall f l,
  map erase_reg (map (fun r : Registers.reg => (r, f r)) l) = l.
Proof.
  induction l ; intros; simpl ; eauto.
  rewrite IHl ; reflexivity.
Qed.

Lemma map_map_erase2 : forall x l,
  map erase_reg (map (fun r : Registers.reg => (r, x)) l) = l.
Proof.
  induction l ; intros; simpl ; eauto.
  rewrite IHl ; reflexivity.
Qed.

Definition get_index (r: reg) := snd r.

Definition erase_instr instr : RTL.instruction :=
  match instr with 
    | Inop n => RTL.Inop n
    | Iop op args dst succ => 
      RTL.Iop op (List.map (erase_reg) args) (erase_reg dst) succ
    | Iload chunk addr args dst succ => 
      RTL.Iload chunk addr (List.map (erase_reg) args) (erase_reg dst) succ
    | Istore chunk addr args src succ =>
      RTL.Istore chunk addr (List.map (erase_reg) args) (erase_reg src) succ
    | Icall sig fn args dst succ =>
      match fn with 
        | inl r => RTL.Icall sig (inl ident (erase_reg r)) (List.map (erase_reg) args) (erase_reg dst) succ 
        | inr id => RTL.Icall sig (inr _ id) (List.map (erase_reg) args) (erase_reg dst) succ
      end      
    | Itailcall sig fn args => 
      match fn with 
        | inl r => RTL.Itailcall sig (inl ident (erase_reg r)) (List.map (erase_reg) args) 
        | inr id => RTL.Itailcall sig (inr _ id) (List.map (erase_reg) args) 
      end
    | Ibuiltin fn args dst succ =>
      RTL.Ibuiltin fn (List.map (erase_reg)args) (erase_reg dst) succ
    | Icond cond args ifso ifnot =>
      RTL.Icond cond (List.map (erase_reg)args) ifso ifnot
    | Ijumptable arg tbl =>
      RTL.Ijumptable (erase_reg arg) tbl
    | Ireturn reg => 
      match reg with 
        | None => RTL.Ireturn None
        | Some r => RTL.Ireturn (Some (erase_reg r))
      end
  end. 

Definition erase_code (rtlphi:function) : RTL.code :=
  PTree.map (fun pc i => erase_instr i) (fn_code rtlphi).

Inductive check_erased_spec (rtl: RTL.function) (rtlphi:SSA.function) :=
| ces_intros: forall
  (HSIG : (RTL.fn_sig rtl) = (SSA.fn_sig rtlphi))
  (HPARAMS: (RTL.fn_params rtl) = (map (erase_reg) (SSA.fn_params rtlphi)))
  (HSSIZE : (RTL.fn_stacksize rtl) = (SSA.fn_stacksize rtlphi))
  (HENTRY : (RTL.fn_entrypoint rtl) = (SSA.fn_entrypoint rtlphi))
  (HCODE: forall p, (RTL.fn_code rtl) ! p = (erase_code rtlphi) ! p),
  check_erased_spec rtl rtlphi.

Lemma check_erase_entrypoint : forall f tf, 
check_erased_spec f tf ->
(RTL.fn_entrypoint f) = (fn_entrypoint tf).
Proof.
  intros. inv H; auto. 
Qed.

Lemma check_erase_params : forall f tf, 
check_erased_spec f tf ->
(RTL.fn_params f) = (map (erase_reg) (fn_params tf)).
Proof.
  intros. inv H. auto.
Qed.
   
Lemma extensional_assigned_code_spec :  forall m m' pc r, 
  m ! pc = m' ! pc -> 
  assigned_code_spec m pc r  -> 
  assigned_code_spec m' pc r.
Proof.
  intros.
  inv H0; (rewrite H in H1; eauto).
Qed.

Inductive check_args_spec : list Registers.reg -> list reg -> Prop :=
| check_args_nil: check_args_spec nil nil
| check_args_cons: 
  forall argl argl' arg, 
    check_args_spec argl argl' ->
    check_args_spec ((erase_reg arg)::argl) (arg::argl').

Lemma check_args_spec_erased_rwt: forall args args',
  check_args_spec args args'  -> 
  (List.map (erase_reg) args') = args.
Proof.
  induction args ; intros; inv H. 
  constructor.
  simpl. rewrite IHargs ; eauto.
Qed.

Lemma check_args_spec_erased: forall args,
  check_args_spec (List.map (erase_reg) args) args.
Proof.
  induction args ; simpl; constructor; auto.
Qed.

Inductive check_ros_spec:  Registers.reg + ident -> reg + ident -> Prop :=
  | check_ros_reg: forall r, 
    check_ros_spec (inl ident (erase_reg r)) (inl ident r)
  | check_ros_ident: forall id, 
    check_ros_spec (inr _ id) (inr reg id).

Inductive check_instrs_spec (rtlphi:function)  : RTL.instruction -> instruction -> Prop :=
| MInop: forall n, 
  check_instrs_spec rtlphi (RTL.Inop n) (Inop n)
| MIop: forall op args args' dst  succ, 
  (check_args_spec args args') ->
  check_instrs_spec rtlphi (RTL.Iop op args (erase_reg dst) succ) 
  (Iop op args' dst succ)
| MIload: forall chunk addr args args' dst succ,
  (check_args_spec args args' ) ->
  check_instrs_spec  rtlphi   (RTL.Iload chunk addr args (erase_reg dst) succ) 
  (Iload chunk addr args' dst succ)
| MIstore: forall chunk addr args args' src succ,
  (check_args_spec args args' ) ->
  check_instrs_spec rtlphi   (RTL.Istore chunk addr args (erase_reg src) succ) 
  (Istore chunk addr args' src succ)
| MIcall: forall sig fn fn' args args' dst succ,
  (check_args_spec args args' ) ->
  (check_ros_spec fn fn') ->
  check_instrs_spec rtlphi  (RTL.Icall sig fn args (erase_reg dst) succ)
   (Icall sig fn' args' dst succ)
| MItailcall: forall sig fn fn' args args',
  (check_args_spec args args' ) ->
  (check_ros_spec fn fn') ->
  check_instrs_spec rtlphi  (RTL.Itailcall sig fn args) (Itailcall sig fn' args')
| MIbuiltin: forall fn args args' dst succ,
  (check_args_spec args args' ) ->
  check_instrs_spec  rtlphi   (RTL.Ibuiltin fn args (erase_reg dst) succ)
  (Ibuiltin fn args' dst succ)
| MIcond: forall cond args args' ifso ifnot,
  (check_args_spec args args' ) ->
  check_instrs_spec rtlphi (RTL.Icond cond args ifso ifnot) 
  (Icond cond args' ifso ifnot)
| MIjumptable: forall arg tbl, 
  check_instrs_spec  rtlphi (RTL.Ijumptable (erase_reg arg) tbl) (Ijumptable arg tbl)
| MIreturn_none: check_instrs_spec rtlphi   (RTL.Ireturn None) (Ireturn None)
| MIreturn_some: forall r, 
  check_instrs_spec rtlphi (RTL.Ireturn (Some (erase_reg r))) (Ireturn (Some r)).

Lemma check_instr_spec_erase: forall f tf pc rinstr rinstr',
  check_erased_spec f tf -> 
  (RTL.fn_code f)!pc = Some rinstr ->
  (fn_code tf)!pc = Some rinstr' ->
  (erase_instr rinstr' = rinstr) /\ check_instrs_spec tf rinstr rinstr'.
Proof. 
  intros. inv H. 
  split;
    ((rewrite  HCODE in H0 ; eauto);
    (unfold erase_code in *) ; 
    (rewrite PTree.gmap in H0) ; 
    (unfold option_map in H0; rewrite H1 in H0; try congruence)).
 inv H0.
 
 destruct rinstr'; 
        try constructor ; try (eapply check_args_spec_erased; eauto).
    (* call *)
 destruct s0; constructor ; try (eapply check_args_spec_erased; eauto) ; constructor.
 (* tail call *)
 destruct s0; constructor; try (eapply check_args_spec_erased; eauto) ; try constructor.
 (* return *) destruct o; constructor.
Qed.
    
Set Printing Notations.

Lemma in_erased_in : forall params r,
  In r (map (erase_reg) params) ->  exists ri, exists i, ri = (r, i) /\ In ri params.
Proof.
  induction params; intros.
  simpl in H. elim H.
  simpl map in H.
  destruct H. 
  case_eq (a); intros.
  unfold erase_reg in * ;
  rewrite H0 in *; simpl in H. inv H.
  exists (r,p) ; exists p; intuition.
  assert (IH' := IHparams r H). 
  destruct IH' as [ri [i [Hrmap Hin]]].
  exists ri ; exists i. auto.
Qed.

Lemma in_params_in_erased: forall params ri r i,
  ri = (r, i) ->
  In ri params ->
  In r (map (erase_reg) params).
Proof.
  induction params ; intros; inv H0.
  simpl; auto.
  simpl. right.
  eapply IHparams; eauto.
Qed.
      
Lemma no_repet_in_diff :  forall params r ri ri' i i',
  list_norepet params ->
  list_norepet (map (erase_reg) params) ->
  In r (map (erase_reg) params) ->
  In ri params ->   In ri' params ->
  ri = (r, i) ->
  ri' = (r, i') ->
  i = i'.
Proof.
  induction params; intros.
  inv H1.
  inv H0. 
  case_eq a; intros.   unfold erase_reg in * ;
 rewrite H0 in * ; simpl in *.
  destruct H2; destruct H3. 
  (* both are in the hd *)
  inv H2. congruence.
  (* one is the hd, other is in tail *)
  inv H2.
  elim H8. eapply in_params_in_erased with (ri := (r,i')); eauto.
  (* other is in the hd, other in tail *)
  inv H3. elim H8. 
  eapply in_params_in_erased with (ri:= (r,i)); eauto.
  (* both are in the tail *)
  eapply IHparams with (ri:= (r,i)) (ri':=(r,i')); eauto. inv H; auto.
  destruct H1. try rewrite H0 in *. inv H1. simpl in *. eapply in_params_in_erased; eauto. auto.
Qed.
  
Lemma not_in_erased_diff: forall params r,
~ In r (map (erase_reg) params) ->
forall a i, a = (r, i) -> ~ In a params.
Proof.
  induction params ; intros ; auto.
  assert (IHr := IHparams r). 
  assert ( ~ In r (map (erase_reg) params)).
  intro. elim H. constructor 2; auto.
  intro.
  inv H2. elim H.  simpl.  auto.
  elim H1. eapply in_params_in_erased; eauto.
Qed.

Lemma erase_funct_no_add: forall tf f pc rinstr,
  check_erased_spec f tf ->
  ((RTL.fn_code f)!pc = Some rinstr) ->
  exists pinstr, (fn_code tf)!pc = Some pinstr.
Proof.
  intros.  inv H. 
  unfold erase_code in HCODE; simpl; intros.
  assert  (HCODEpc:= HCODE pc). 
  rewrite PTree.gmap in HCODEpc.
  destruct (fn_code tf) ! pc ; simpl; eauto.
  simpl in HCODEpc. congruence.
Qed.

Lemma erased_funct_erased_instr: forall pc f tf rinstr,
  check_erased_spec f tf  ->
  ((RTL.fn_code f)!pc = Some rinstr) ->
  exists pinstr,
    ((SSA.fn_code tf) ! pc = Some pinstr)
    /\ (rinstr =  (erase_instr pinstr)).
Proof.
  intros.
  assert (Hpinstr:= erase_funct_no_add tf f pc rinstr H H0).
  destruct Hpinstr as [pinstr Hpinstr]; exists pinstr.
  split ; auto.
  unfold erase_code in H0. simpl in H0.
  inv H.
  rewrite HCODE in H0.
  unfold erase_code in H0. 
  rewrite PTree.gmap in H0. 
  rewrite Hpinstr in H0. 
  inv H0 ; auto.
Qed.
  
Inductive spec_ros : Registers.reg + ident -> reg + ident ->  Prop :=
  | spec_ros_l: forall r, spec_ros (inl _ (erase_reg r)) (inl _ r) 
  | spec_ros_r: forall id, spec_ros (inr _ id) (inr _ id).
  
Definition assigned (ri: reg) (block:phiblock) := 
  exists args, In (Iphi args ri) block.

Definition erased_reg_assigned (r:Registers.reg) (block:phiblock) :=
  (exists ri, ((assigned ri block) /\ erase_reg ri = r)).

Lemma not_erased_reg_assigned_cons: forall r a block, 
  ~ (erased_reg_assigned r (a::block)) ->
  ~ (erased_reg_assigned r block).
Proof.
  intros r a block Hcont. intro.
  elim Hcont.
  destruct H as [x [Hx1 Hx2]]. 
  exists x; intuition.
  inv Hx1. 
  exists x0; constructor 2;auto.
Qed.

Lemma not_erased_reg_assigned_not_in: forall r block,
  ~  erased_reg_assigned r block   ->
  forall x args, (erase_reg x = r -> not (In (Iphi args x) block)).
Proof.
  induction block; intros. 
  intro. elim H1. 
  intro.
  assert (Hcont:= (in_inv H1)).
  destruct Hcont.
  assert (IHblock2 := (IHblock (not_erased_reg_assigned_cons  r a block H))); clear IHblock.
  rewrite H2 in * ; simpl in *.
  elim H. exists x; auto. split; auto.
  exists args; auto.
  eapply IHblock; eauto. 
  eapply not_erased_reg_assigned_cons; eauto.
Qed.
 
Lemma erased_reg_assigned_dec: forall r block, 
  erased_reg_assigned r block \/ not (erased_reg_assigned r block).
Proof.
induction block.
(* nil *)
right. intro. destruct H as [ri [Hassig Herase]].
inv Hassig. inv H.
(* a::block *)
destruct IHblock as [IHb1 | IHb2].
  (* IHb1 *)
  left.  
  inv IHb1; destruct H.      
  destruct H as [args Hin].
  exists x. split; auto. 
  exists args. constructor 2; auto.
  (* IHb2 *)
  destruct a; case (peq r (erase_reg r0)); intros.  
     (* equal *) 
     inv e. left.
     exists r0; split ; auto.
     exists l; constructor; auto.
     (* diff *)
     right. intro.
     destruct H as [x [Hx1 Hx2]].
     destruct Hx1. 
     assert (Hcont:= (not_erased_reg_assigned_not_in r block IHb2 x x0 Hx2)).
     assert (HIninv:= in_inv H). 
     destruct HIninv. rewrite <- Hx2 in n.
     elim n. inv H0; auto. 
     intuition.
Qed.

(** ** Well-typed instructions *)
Inductive wt_eidx (g : Registers.reg -> index) : instruction -> Prop :=
| wt_eidx_nop: forall s, wt_eidx g (Inop s)
| wt_eidx_istore: forall chk adr args src succ, wt_eidx g (Istore chk adr args src succ)
| wt_eidx_itailcall: forall sig fn args, wt_eidx g (Itailcall sig fn args)
| wt_eidx_icond: forall cond args ifso ifnot,  wt_eidx g (Icond cond args ifso ifnot)
| wt_eidx_ijumptable : forall arg tbl, wt_eidx g (Ijumptable arg tbl)
| wt_eidx_ireturn: forall optr, wt_eidx g (Ireturn optr)
| wt_eidx_iop : forall op args dst succ r i, 
  dst = (r,i) ->
  g r <> i ->  wt_eidx  g (Iop op args dst succ)    
| wt_eidx_iload : forall chk adr args dst succ r i, 
  dst = (r,i) ->  g r <> i ->
  wt_eidx  g (Iload chk adr args dst succ)    
| wt_eidx_icall : forall sig ros args dst succ r i, 
  dst = (r,i) ->  g r <> i ->
  wt_eidx  g (Icall sig ros args dst succ)    
| wt_eidx_ibuiltin: forall ef args dst succ r i, 
  dst = (r,i) ->  g r <> i ->
  wt_eidx  g (Ibuiltin ef args dst succ).

Inductive wt_ephi (g: Registers.reg -> index) : phiblock -> Prop := 
| wt_ephi_intro : forall block, 
  (forall ri r i, assigned ri block -> ri = (r,i) ->  g r <> i) ->
  wt_ephi g block.

Notation "a [ x ← v ]" := (update a x v) (at level 1, v at next level).
Notation use_ok := (fun (args: list reg) (γ: Registers.reg -> index) => (forall r i, In (r,i) args -> γ r = i) : Prop).
Reserved Notation "x ⊢ y ; z" (at level 40, no associativity).

Inductive wt_instr : (Registers.reg -> index) -> instruction -> (Registers.reg -> index) -> Prop :=
| wt_Inop: forall γ s,   γ ⊢ (Inop s) ; γ
  
| wt_Icond: forall γ cond args s1 s2,
  use_ok args γ -> 
  γ ⊢ (Icond cond args s1 s2) ; γ
  
| wt_Ijumptable: forall γ arg tbl,
  (use_ok (arg::nil) γ) ->
  wt_instr γ (Ijumptable arg tbl) γ
  
| wt_Ireturn_some: forall γ r,
  use_ok (r::nil) γ ->
  γ ⊢ (Ireturn (Some r)) ; γ
| wt_Ireturn_none: forall γ, γ ⊢ (Ireturn None) ; γ
  
| wt_Iop: forall γ op args s r i,
  use_ok args γ  -> 
  γ ⊢ (Iop op args (r,i) s) ; γ[r← i]
  
| wt_Iload: forall γ chunk addr args s r i,
  use_ok args γ ->
  γ ⊢ (Iload chunk addr args (r,i) s) ; γ[r←i]
  
| wt_Istore: forall γ chunk addr args s src,
  use_ok (src::args) γ ->
  γ ⊢ (Istore chunk addr args src s) ; γ
  
| wt_Icall_id: forall γ sig args s id r i,
  use_ok args γ ->
  γ ⊢ (Icall sig (inr reg id) args (r,i) s) ; γ[r←i]
  
| wt_Icall_reg : forall γ sig args s r i rfun,
  use_ok (rfun::args) γ ->
  γ ⊢ (Icall sig (inl ident rfun) args (r,i) s) ; γ[r←i]
  
| wt_Itailcall_id: forall γ sig args id,
  use_ok args γ ->
  γ ⊢ (Itailcall sig (inr reg id) args) ; γ
  
| wt_Itailcall_reg: forall γ sig  args rfun,
  use_ok (rfun::args) γ ->
  γ ⊢ (Itailcall sig (inl ident rfun) args) ; γ
  
| wt_Ibuiltin: forall γ ef args s r i,
  use_ok args γ ->
  γ ⊢ (Ibuiltin ef args (r,i) s) ; γ[r←i]
  where " a ⊢ ins ; b " := (wt_instr a ins b).

Inductive is_out_node (f: function) : node -> Prop:=
| Out_tailcall: forall i sig fn args, 
  (fn_code f)!i = Some (Itailcall sig fn args) ->
  is_out_node f i
| Out_return : forall i or,
  (fn_code f)!i = Some (Ireturn or) ->
  is_out_node f i
| Out_jtable : forall i arg,
  (fn_code f)!i = Some (Ijumptable arg nil) ->
  is_out_node f i.

Inductive wt_out (f: function) : tgamma  -> node -> Prop :=
  | wt_out_node: forall (Γ:tgamma) (i :node) instr, 
    (fn_code f)!i = Some instr ->
    (wt_instr (Γ i) instr (Γ i)) ->
    (wt_out f Γ i).

Inductive wf_init (f: function) (Γ:tgamma): Prop :=
| wf_init_gamma:  
  (forall p, In p (fn_params f) -> exists r, p = (r,(Γ (fn_entrypoint f)) r)) ->
  wf_init f Γ.


(** ** Additional structural invariants *)

(** A phi-instruction is well formed when it has the right number of arguments, 
   and when at least two arguments are distinct *)

Definition check_phi_params_spec (rtlphi: function) :=
  forall pc pc0 phiinstr args dst k,
    rtlphi.(fn_phicode)!pc = Some phiinstr ->
    index_pred (make_predecessors (fn_code rtlphi) successors_instr) pc0 pc = Some k ->
    In (Iphi args dst) phiinstr -> 
    (nth_okp k args).

Definition check_no_duplicates_spec (rtlphi:function) :=
  forall pc phiinstr args args' dst dst', 
    rtlphi.(fn_phicode)!pc = Some phiinstr ->
    NoDup phiinstr ->
    In (Iphi args dst) phiinstr -> 
    In (Iphi args' dst') phiinstr ->
    (args <> args' \/ dst <> dst') ->
    (erase_reg dst) <> (erase_reg dst').

Definition check_para_block_spec (rtl:function) :=
  forall pc block,
    (fn_phicode rtl) ! pc = Some block ->
    para_block block.

Definition structural_checks_spec (rtl: RTL.function) (rtlphi: SSA.function) :=
  (RTL.fn_sig rtl = SSA.fn_sig rtlphi) 
  /\ ((RTL.fn_stacksize rtl) = (SSA.fn_stacksize rtlphi)) 
  /\ (check_erased_spec rtl rtlphi)
  /\ (unique_def_spec rtlphi)
  /\ (check_phi_params_spec rtlphi)
  /\  (check_para_block_spec rtlphi)
  /\ (check_no_duplicates_spec rtlphi).

Lemma no_duplicates_erased: forall r1 r2 tf block pc r,
  unique_def_spec tf ->
  check_no_duplicates_spec tf ->
  (fn_phicode tf)! pc = Some block ->
  assigned r1 block ->  assigned r2 block ->
  erase_reg r1 = r ->  erase_reg r2 = r ->
  r1 = r2.
Proof.
  intros.
  destruct H2 as [args Hargs]; destruct H3 as [args' Hargs'].
  rewrite <- H5 in H4.
  unfold check_no_duplicates_spec in H0.
  destruct (p2eq r1 r2) ; auto.
  exploit (H0 pc block args args'); eauto; intuition. 
  destruct H as [_ Hdup]. 
  exploit Hdup ; eauto ; intuition. 
Qed.

(** * Utility lemmas about junction points *)

Lemma is_joinpoint_iff_join_point_ssa : forall f jp,
  join_point jp f <-> is_joinpoint (make_predecessors (fn_code f) SSA.successors_instr) jp = true.
Proof.
  intros. split; intros.
  - inv H.
    unfold is_joinpoint. 
    rewrite Hpreds.
    destruct l ; simpl in *; try omega.
    destruct l; simpl in *; try (apply False_ind; omega).
    auto.    
  - unfold is_joinpoint in *.
    case_eq ((make_predecessors (fn_code f) SSA.successors_instr)!jp).
    * intros l' Hc.
      rewrite Hc in *.
      destruct l' ; simpl in *; try congruence.
      destruct l' ; simpl in *; try congruence.
      econstructor; eauto.
      simpl; omega.
    * intros Hc. rewrite Hc in *.
      congruence. 
Qed.

Lemma is_joinpoint_iff_join_point : forall f jp,
  RTLutils.join_point jp f <-> 
  is_joinpoint (make_predecessors (RTL.fn_code f) RTL.successors_instr) jp = true.
Proof.
  intros. split; intros.
  - inv H.
    unfold is_joinpoint. 
    rewrite Hpreds.
    destruct l ; simpl in *; try omega.
    destruct l; simpl in *; try (apply False_ind; omega).
    auto.    
  - unfold is_joinpoint in *.
    case_eq ((make_predecessors (RTL.fn_code f) RTL.successors_instr)!jp).
    * intros l' Hc.
      rewrite Hc in *.
      destruct l' ; simpl in *; try congruence.
      destruct l' ; simpl in *; try congruence.
      econstructor; eauto.
      simpl; omega.
    * intros Hc. rewrite Hc in *.
      congruence. 
Qed.

(** * Utility lemmas for the checker [check_unique_def] *)

Lemma not_assigned_monotone : forall m r k i,
  m ! k = None ->
  (forall pc : node, ~ assigned_code_spec (PTree.set k i m) pc r) ->
  forall pc : node, ~ assigned_code_spec m pc r.
Proof.
  intros.
  intro Hcont.
  elim (H0 pc).
  destruct (peq k pc).
  inv e; try congruence.
  inv Hcont; congruence.
  assert ((PTree.set k i m) ! pc = m ! pc) by (rewrite PTree.gso ; auto).
  symmetry in H1.
  eapply extensional_assigned_code_spec; eauto.
Qed.

Lemma record_assigned_reg_phi_preserve : forall pc pc' phib t l r,
  t !2 r = Some l ->
  In pc l ->
  exists l', (record_assigned_reg_phi t pc' phib) !2 r = Some l' /\ In pc l'.
Proof.
  induction phib; intros. 
  simpl. exists l ; auto.
  case_eq a ; intros; inv H1.
  simpl.
  destruct (p2eq r0 r).  
  inv e.
  destruct (t!2 r). inv H. 
  exploit (IHphib ((P2Tree.set r (pc' :: l) t)) (pc'::l)); eauto. 
  rewrite P2Tree.gss; auto.
  inv H.
  
  destruct (t!2 r0). 
  exploit (IHphib (P2Tree.set r0 (pc'::l1) t) l); eauto. 
  rewrite P2Tree.gso; auto. 
  exploit (IHphib (P2Tree.set r0 (pc'::nil) t) l); eauto. 
  rewrite P2Tree.gso; auto. 
Qed.

Lemma assigned_code_preserved : forall k i m pc r,
pc <> k ->
assigned_code_spec (PTree.set k i m) pc r ->
assigned_code_spec m pc r.
Proof.
  induction 2; rewrite PTree.gso in H0; eauto.
Qed.

Hint Resolve assigned_code_preserved.

Lemma fold_record_preserve: forall t l pc r,
    t !2 r = Some l ->
    In pc l ->
    forall code, exists l', (PTree.fold record_assigned_reg_phi code t) !2 r = Some l' /\ In pc l'.
Proof.
  intros t l pc r Hl Hpcl code.
  set (P := fun (code:phicode) (c : P2Tree.t (list positive))  => exists l', c !2 r = Some l' /\ In pc l').
  apply PTree_Properties.fold_rec with (P:= P) (f:= record_assigned_reg_phi) (init:= t).
  
  (* extensionality *)
  unfold P; intros.
  apply H0; eauto.
  
  (* base case *)
  red. intros. eauto.
  
  (* inductive case *)
   unfold P; intros.
   destruct H1 as [l' [Hal' Hinl']]. 
   eapply record_assigned_reg_phi_preserve ; eauto.   
 Qed.

Lemma assigned_phi_noteq_init: forall k v m pc r, 
  assigned_phi_spec (PTree.set k v m) pc r ->
  pc <> k -> 
  assigned_phi_spec m pc r.
Proof.
  intros.
  inv H. rewrite PTree.gso in H1; auto.
  eauto.
Qed.
 
Lemma record_assigned_reg_phi_in_block : forall phib x r a k l,
  In (Iphi x r) phib ->
  (record_assigned_reg_phi a k phib) !2 r = Some l 
  -> In k l.
Proof.
  induction phib; intros. 
  inv H. 
  inv H.
  Focus 2. eapply IHphib ; eauto. 
  simpl in H0.
  case_eq  (a0 !2 r). intros. rewrite H in *.
  assert (In k (k::l0)) by (left ; auto).
  assert ((P2Tree.set r (k :: l0) a0) !2 r = Some (k::l0)) by (rewrite P2Tree.gss; auto).
  eapply record_assigned_reg_phi_preserve with (phib := phib) (pc' := k) in H2 ; eauto. 
  destruct H2 as [l' [Hl' Hinl']].  rewrite Hl' in H0 ; inv H0; auto.
  intros.
  rewrite H in *.
  assert (In k (k::nil)) by (left ; auto).
  assert ((P2Tree.set r (k :: nil) a0) !2 r = Some (k::nil)) by (rewrite P2Tree.gss; auto).
  eapply record_assigned_reg_phi_preserve with (phib := phib) (pc' := k) in H2 ; eauto. 
  destruct H2 as [l' [Hl' Hinl']].  rewrite Hl' in H0 ; inv H0; auto.
Qed.  

Lemma record_assigned_reg_phi_preserve2 : forall pc phib t l r,
  t !2 r = Some l ->
  exists l', (record_assigned_reg_phi t pc phib) !2 r = Some l'.
Proof.
  induction phib; intros; eauto.
  case_eq a ; intros; inv H0.
  simpl.
  destruct (p2eq r0 r).  
  inv e.
  destruct (t!2 r). inv H. 
  exploit (IHphib ((P2Tree.set r (pc :: l) t)) (pc::l)); eauto. 
  rewrite P2Tree.gss; auto.
  inv H.
  
  destruct (t!2 r0). 
  exploit (IHphib (P2Tree.set r0 (pc::l1) t) l); eauto. 
  rewrite P2Tree.gso; auto. 
  exploit (IHphib (P2Tree.set r0 (pc::nil) t) l); eauto. 
  rewrite P2Tree.gso; auto. 
Qed.
  
Lemma fold_record_preserve2: forall t l r,
    t !2 r = Some l ->
    forall code, exists l', (PTree.fold record_assigned_reg_phi code t) !2 r = Some l'.
Proof.
  intros t l r Hl code.
  set (P := fun (code:phicode) (c : P2Tree.t (list positive))  => exists l', c !2 r = Some l').
  apply PTree_Properties.fold_rec with (P:= P) (f:= record_assigned_reg_phi) (init:= t).
  
  (* extensionality *)
  unfold P; intros.
  apply H0; eauto.
  
  (* base case *)
  red. intros. eauto.
  
  (* inductive case *)
   unfold P; intros.
   destruct H1 as [l' Hl']. 
   exploit record_assigned_reg_phi_preserve2 ; eauto.   
Qed.

Lemma record_assigned_reg_phi_in_block2 : forall phib x r a k,
  In (Iphi x r) phib ->
  exists l, (record_assigned_reg_phi a k phib) !2 r = Some l.
Proof.
  induction phib ; intros; inv H. 
  simpl.   
  case_eq (a0 !2 r) ; intros.
  assert ((P2Tree.set r (k :: l) a0)  !2 r=  Some (k::l)) by (rewrite P2Tree.gss ; auto).
  exploit record_assigned_reg_phi_preserve2; eauto.
  assert ((P2Tree.set r (k :: nil) a0)  !2 r=  Some (k::nil)) by (rewrite P2Tree.gss ; auto).
  exploit record_assigned_reg_phi_preserve2 ; eauto.
  simpl. eapply IHphib ; eauto. 
Qed.



Lemma assigned_phi_spec_inlist2 : forall t code r pc,
  (assigned_phi_spec code pc r) ->
  exists l, ((PTree.fold record_assigned_reg_phi code t) !2 r = Some l /\ In pc l).
Proof.
  set (P := fun (code : phicode)  (c : P2Tree.t (list positive))  =>
    forall r pc, assigned_phi_spec code pc r ->
    exists l, c !2 r = Some l /\ In pc l).
  intros t code.
  apply PTree_Properties.fold_rec with (P:= P).

   (* extensionality *)
   unfold P; intros.
   apply H0; eauto.
   inv H1; rewrite <- (H pc) in H2 ; eauto.
      
   (* base case *)
   red. intros.
   inv H; rewrite PTree.gempty in H0; congruence.

   (* inductive case *)
   unfold P; intros.
   destruct v. 
   destruct (peq pc k) ; inv H2.
   rewrite PTree.gss in H3.  inv H3. inv H4. inv H2.
   rewrite PTree.gso in H3; auto. exploit H1 ; eauto. 
      
   destruct (peq k pc); inv H2.
   rewrite PTree.gss in H3. inv H4. inv H3.
   exploit (record_assigned_reg_phi_in_block2 (p::v) x r a pc) ; eauto.
   intros. destruct H3. exists x0.
   split ; auto. 
   eapply record_assigned_reg_phi_in_block ; eauto. 
   
   rewrite PTree.gso in H3; auto.
   exploit H1 ; eauto. intros. destruct H2 as [l [Hal Hinpc]].
   exploit record_assigned_reg_phi_preserve ; eauto. 
Qed.


Lemma record_assigned_reg_phi_inlist3_stronger : forall r pc phiinstr l m,
  m !2 r = Some l ->
  NoDup phiinstr -> 
  (forall x, In (Iphi x r) phiinstr ->
    (forall x', In (Iphi x' r) phiinstr -> x' = x) ->
    exists l', (record_assigned_reg_phi m pc phiinstr) !2 r = Some (pc::l'++l))
  /\
  (forall x, In (Iphi x r) phiinstr ->
    (exists x', In (Iphi x' r) phiinstr /\ x' <> x) ->
    exists l', exists l'', (record_assigned_reg_phi m pc phiinstr) !2 r = Some (pc::l'++pc::l''++l))
  /\
  ((forall x, ~ In (Iphi x r) phiinstr) ->
    (record_assigned_reg_phi m pc phiinstr) !2 r = Some l)
.
Proof.
  induction phiinstr; simpl; split. 
  
  (* nil *) intuition. intuition.
  
  (* a::phiinstr *) 
  intuition. subst.
  
  simpl; rewrite H.
  elim IHphiinstr with (pc::l) (P2Tree.set r (pc :: l) m).
  intros IH1 [IH2 IH3].
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H1 as [x' H1].
  destruct (classic (exists x'', In (Iphi x'' r) phiinstr /\ x'' <> x')) as [EM1|EM2].
  destruct EM1 as [x'' [EM11 EM12]].
  
  elim IH2 with (1:=H1). intros l' H'.
  destruct H' as [l'' Hl''].
  exists  (l' ++ pc :: l'' ++ pc::nil).
  rewrite app_ass; simpl. rewrite <- ass_app. simpl. auto. 
  eauto.
  
  elim IH1 with (1:=H1). intros.
  exists (x0++pc::nil). rewrite <- ass_app. simpl. auto.
  intros.  
  destruct (list_eq_dec p2eq x' x'0). auto. elim EM2; eauto.
  
  rewrite IH3. exists nil; auto.
  intros; elim H1 ; eauto.
  rewrite P2Tree.gss; auto.
  inv H0; auto.

  destruct a as [x' r'].
  destruct (p2eq r' r); subst.
  simpl.
  rewrite H.
  elim IHphiinstr with (pc::l) (P2Tree.set r (pc :: l) m).
  intros IH1 [IH2 IH3].
  
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H1 as [x'' H1].
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x'' <> x')) as [EM1|EM2].
  destruct EM1 as [x''' [EM11 EM12]].
    
  elim IH2 with (1:=H1). intros l' H'.
  destruct H' as [l'' Hl''].
  exists (l'++pc::l''++pc::nil).
  repeat rewrite app_ass. simpl. rewrite <- ass_app ; simpl; auto.
  exists x'''; auto.
  
  elim IH1 with (1:=H1). intros l' H'.
  exists (l'++pc::nil).
  repeat rewrite app_ass. simpl. auto.
  intros.  destruct (list_eq_dec p2eq x'0 x''). auto.
  elim EM2; eauto. 
  
  rewrite IH3.
  exists nil; auto.
  intros; elim H1; eauto.
  rewrite P2Tree.gss; auto.
  inv H0 ; auto.

  elim IHphiinstr with l (add_phi_assigned_reg pc m (Iphi x' r')).
  intros IH1 [IH2 IH3].
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H1 as [x'' H1].
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x'' <> x')) as [EM1|EM2].
  destruct EM1 as [x''' [EM11 EM12]].   

  elim IH2 with (1:=H1). intros l' H'.
  destruct H' as [l'' Hl''].
  eauto.
  eauto.

  elim IH1 with (1:=H1). intros l' Hl'. eauto.
  intros. 
  destruct (list_eq_dec p2eq x'0 x''). auto.
  elim EM2; eauto.
  
  rewrite IH3.
  elim H1; eauto.
  intros; elim H1; eauto.
  simpl.
  destruct (m !2 r');  rewrite P2Tree.gso; auto.
  inv H0; auto.

  intuition. inv H3. 
  simpl. destruct m!2 r.
  
  inv H. elim IHphiinstr with (pc::l) (P2Tree.set r (pc::l) m).
  intros IH1 [IH2 IH3].
  
  destruct H2. destruct H. destruct H. inv H. elim H1; auto.

  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x0)) as [EM1|EM2].
  destruct EM1 as [x''' [EM11 EM12]].   

  elim IH2 with (1:=H). intros l' H'.
  destruct H'. 
  exists l'. exists (x1++pc::nil). 
  rewrite app_ass ; eauto. eauto. 
  
  elim IH1 with (1:=H). intros.
  exists x1. exists nil.
  eauto. 
  intros. destruct (list_eq_dec p2eq x' x0); auto. elim EM2 ; eauto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.
  
  inv H.
  
  destruct a.
  destruct (p2eq r0 r).  inv e.
  assert (x <> l0) by (intro; inv H; inv H0; elim H4; auto).
  simpl. destruct m!2 r. inv H.
  elim IHphiinstr with (pc::l) (P2Tree.set r (pc::l) m).
  intros IH1 [IH2 IH3].
  
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x)) as [EM1|EM2].
  destruct EM1 as [x''' [EM11 EM12]].   

  elim IH2 with (1:=H3). intros l' H'.
  destruct H'. exists l'. exists (x0++pc::nil).  rewrite app_ass; eauto.
  eauto.

  elim IH1 with (1:=H3). intros.
  exists x0.  exists nil. simpl. eauto.
  intros. destruct (list_eq_dec p2eq x' x); auto. elim EM2 ; eauto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.
  inv H.
  
  destruct H2. destruct H1. destruct H1. inv H1. elim n; auto.
  simpl. destruct m!2 r0. 
  
  elim IHphiinstr with l (P2Tree.set r0 (pc::l1) m).
  intros IH1 [IH2 IH3].
  
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x)) as [EM1|EM2].
  destruct EM1 as [x''' [EM11 EM12]].   

  elim IH2 with (1:=H3). intros l' H'.
  destruct H'. eauto. eauto. 

  elim EM2. eauto.
  rewrite P2Tree.gso ; auto.
  inv H0; auto.

  elim IHphiinstr with l (P2Tree.set r0 (pc::nil) m).
  intros IH1 [IH2 IH3].
  
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x)) as [EM1|EM2].
  destruct EM1 as [x''' [EM11 EM12]].   

  elim IH2 with (1:=H3). intros l' H'.
  destruct H'. eauto. eauto. 

  elim EM2. eauto.
  rewrite P2Tree.gso ; auto.
  inv H0; auto.
  
  destruct a.
  destruct (p2eq r r0). inv e. elim H1 with l0; eauto.

  elim IHphiinstr with l (add_phi_assigned_reg pc m (Iphi l0 r0)).
  intros IH1 [IH2 IH3].
  
  rewrite IH3. auto.  intros.  elim H1 with x; auto. 
  simpl.  destruct m!2 r0; rewrite P2Tree.gso ; auto.
  inv H0; auto.
Qed.


Lemma record_assigned_reg_phi_inlist3_none_stronger : forall r pc phiinstr m,
  m !2 r = None ->
  NoDup phiinstr -> 
  (forall x, In (Iphi x r) phiinstr ->
    (forall x', In (Iphi x' r) phiinstr -> x' = x) ->
    exists l', (record_assigned_reg_phi m pc phiinstr) !2 r = Some (pc::l'))
  /\
  (forall x, In (Iphi x r) phiinstr ->
    (exists x', In (Iphi x' r) phiinstr /\ x' <> x) ->
    exists l', exists l'', (record_assigned_reg_phi m pc phiinstr) !2 r = Some (pc::l'++pc::l''))
  /\
  ((forall x, ~ In (Iphi x r) phiinstr) ->
    (record_assigned_reg_phi m pc phiinstr) !2 r = None)
.
Proof.
  induction phiinstr; simpl; repeat split. 
  
  (* nil *) intuition. intuition. intuition.
  
  (* a::phiinstr *) 
  destruct a.  
  intuition.  inv H3. 
  destruct (classic (exists x', In (Iphi x' r) phiinstr)) as [EM1|EM2].
  destruct EM1 as [x''' EM11].
  assert (x''' <> x) by (intro; inv H1; inv H0; auto). 

  elim record_assigned_reg_phi_inlist3_stronger with r pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi x r)); eauto.
  intros IH1 [IH2 IH3].
  
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x''')) as [EM1|EM2].
  destruct EM1 as [x' [EM1 EM2]].   
    
  elim IH2 with x'''; auto. intros.
  destruct H3.  eauto. eauto.

  elim IH1 with x'''; eauto. intros. destruct (list_eq_dec p2eq x' x''') ; auto; elim EM2 ; eauto. 
  simpl. rewrite H. rewrite P2Tree.gss ; auto. inv H0 ; auto.

  exists nil.   
  elim record_assigned_reg_phi_inlist3_stronger with r pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi x r)); eauto.
  intros IH1 [IH2 IH3].
  rewrite IH3. auto. intros. intro. elim EM2 ; eauto.
  simpl. rewrite H; auto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.
  
  destruct (p2eq r0 r). inv e.
  
  exploit (H2 l). left ; auto. intros. inv H1. inv H0. elim H5 ; auto.
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x)) as [EM1|EM2].
  destruct EM1 as [x' [EM1 EM2]].   
  elim IHphiinstr with (add_phi_assigned_reg pc m (Iphi l r0)). intros IH1 [IH2 IH3].
  elim IH2 with x'; auto. intros.
  destruct H1.  eauto. eauto. simpl. destruct m!2 r0; rewrite P2Tree.gso ; auto. inv H0 ; auto.

  elim IHphiinstr with (add_phi_assigned_reg pc m (Iphi l r0)). intros IH1 [IH2 IH3].
  elim IH1 with x; auto. intros.
  eauto. simpl. destruct m!2 r0; rewrite P2Tree.gso ; auto. inv H0 ; auto.

  intros. intuition. inv H3. destruct H2. destruct H1. destruct H1. inv H1. elim H2. auto.
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x0)) as [EM1|EM2].
  destruct EM1 as [x' [EM1 EM2]].   

  elim record_assigned_reg_phi_inlist3_stronger with r pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi x r)); eauto.
  intros IH1 [IH2 IH3].
  elim IH2 with (1:= H1). intros.  destruct H3.  eauto. eauto. 
  simpl. rewrite H; auto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.

  elim record_assigned_reg_phi_inlist3_stronger with r pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi x r)); eauto.
  intros IH1 [IH2 IH3].
  elim IH1 with (1:= H1). intros.  eauto. 
  intros.  destruct (list_eq_dec p2eq x' x0) ; auto.  elim EM2 ; auto. eauto.
  simpl. rewrite H; auto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.
  
  destruct H2. destruct H1. destruct H1. inv H1.
  
  destruct (classic (exists x', In (Iphi x' r) phiinstr /\ x' <> x)) as [EM1|EM2].
  destruct EM1 as [x' [EM1 EM2]].   

  elim record_assigned_reg_phi_inlist3_stronger with r pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi x r)); eauto.
  intros IH1 [IH2 IH3].
  elim IH2 with (1:= EM1). intros.  destruct H1.  eauto. eauto. 
  simpl. rewrite H; auto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.

  elim record_assigned_reg_phi_inlist3_stronger with r pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi x r)); eauto.
  intros IH1 [IH2 IH3].
  elim IH1 with (1:= H3). intros.  eauto. 
  intros.  destruct (list_eq_dec p2eq x' x) ; auto.  elim EM2 ; auto. eauto.
  simpl. rewrite H; auto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.

  destruct a. destruct (p2eq r r0). inv e.
  destruct (classic (exists x', In (Iphi x' r0) phiinstr /\ x' <> x)) as [EM1|EM2].
  destruct EM1 as [x' [EM1 EM2]].   
  
  elim record_assigned_reg_phi_inlist3_stronger with r0 pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi l r0)); eauto.
  intros IH1 [IH2 IH3].
  elim IH2 with (1:= EM1). intros.  destruct H4.  eauto. eauto. 
  simpl. rewrite H; auto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.

  elim record_assigned_reg_phi_inlist3_stronger with r0 pc phiinstr (pc::nil) (add_phi_assigned_reg pc m (Iphi l r0)); eauto.
  intros IH1 [IH2 IH3].
  elim IH1 with (1:= H3). intros.  eauto. 
  intros.  destruct (list_eq_dec p2eq x' x) ; auto.  elim EM2 ; auto. eauto.
  simpl. rewrite H; auto.
  rewrite P2Tree.gss ; auto.
  inv H0; auto.
  
  elim IHphiinstr with (add_phi_assigned_reg pc m (Iphi l r0)).
  intros IH1 [IH2 IH3].
  
  elim IH2 with (1:=H1). intros l' H'.
  destruct H' as [l'' Hl'']. eauto. eauto.
  simpl. destruct m!2 r0 ; rewrite P2Tree.gso ; auto. inv H0 ; auto.
  
  intros.
  destruct a.
  elim IHphiinstr with (add_phi_assigned_reg pc m (Iphi l r0)). intros IH1 [IH2 IH3].
  rewrite IH3. auto. 
  intros. intro. elim (H1 x). right ; auto.
  simpl. destruct m!2 r0 ; rewrite P2Tree.gso ; auto. 
  intro. inv H2. elim (H1 l) ; auto.
  intro. inv H2. elim (H1 l) ; auto.
  inv H0 ; auto.
Qed.

Lemma record_assigned_reg_phi_inlist2_stronger : forall r pc phiinstr l m,
  m !2 r = Some l ->
  (forall x, In (Iphi x r) phiinstr ->
    exists l', (record_assigned_reg_phi m pc phiinstr) !2 r = Some (pc::l'++l))
  /\
  ((forall x, ~ In (Iphi x r) phiinstr) ->
    (record_assigned_reg_phi m pc phiinstr) !2 r = Some l)
.
Proof.
  induction phiinstr; simpl; split;  intuition; subst.

  simpl; rewrite H.
  elim IHphiinstr with (pc::l) (P2Tree.set r (pc :: l) m).
  intros IH1 IH2.
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H0 as [x' H0].
  elim IH1 with (1:=H0); intros l' H'.
  exists (l'++pc::nil).
  rewrite app_ass; simpl; auto.
  rewrite IH2.
  exists nil; auto.
  intros; elim H0; eauto.
  rewrite P2Tree.gss; auto.

  destruct a as [x' r'].
  destruct (p2eq r' r); subst.
  simpl.
  rewrite H.
  elim IHphiinstr with (pc::l) (P2Tree.set r (pc :: l) m).
  intros IH1 IH2.
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H0 as [x'' H0].
  elim IH1 with (1:=H0); intros l' H'.
  exists (l'++pc::nil).
  rewrite app_ass; simpl; auto.
  rewrite IH2.
  exists nil; auto.
  intros; elim H0; eauto.
  rewrite P2Tree.gss; auto.
  elim IHphiinstr with l (add_phi_assigned_reg pc m (Iphi x' r')).
  intros IH1 IH2.
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H0 as [x'' H0].
  elim IH1 with (1:=H0); intros l' H'.
  eauto.
  rewrite IH2.
  elim H0; eauto.
  intros; elim H0; eauto.
  simpl.
  destruct (m !2 r');  rewrite P2Tree.gso; auto.

  destruct a as [x' r'].
  destruct (p2eq r' r); subst.
  elim H0 with x'; auto.
  elim IHphiinstr with l (add_phi_assigned_reg pc m (Iphi x' r')).
  intros IH1 IH2.
  rewrite IH2; auto.
  intros.
  elim H0 with x; eauto.
  simpl.
  destruct (m !2 r');  rewrite P2Tree.gso; auto.
Qed.

Lemma record_assigned_reg_phi_inlist4_stronger : forall r pc phiinstr m,
  m !2 r = None ->
  (forall x, In (Iphi x r) phiinstr ->
    exists l', (record_assigned_reg_phi m pc phiinstr) !2 r = Some (pc::l'))
  /\
  ((forall x, ~ In (Iphi x r) phiinstr) ->
    (record_assigned_reg_phi m pc phiinstr) !2 r = None)
.
Proof.
  induction phiinstr.
  
  (* nil *)
  simpl. intros; split. intros. 
  elim H0. 
  auto. 

  (* a::phiiinstr *)
  intros. split ; intros.
  inv H0. simpl. rewrite H.
  elim record_assigned_reg_phi_inlist2_stronger with 
    r pc phiinstr (pc::nil) (P2Tree.set r (pc::nil) m)  ; eauto.
  intros IH1 IH2.
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H0 as [x' H0].
  elim IH1 with (1:=H0); intros l' H'.
  eauto.
  rewrite IH2.
  exists nil; auto.
  intros. intro. elim H0; eauto.
  rewrite P2Tree.gss; auto.

  destruct a as [x' r'].
  destruct (p2eq r' r); subst.
  simpl.
  rewrite H.
  elim record_assigned_reg_phi_inlist2_stronger with 
    r pc phiinstr (pc::nil) (P2Tree.set r (pc::nil) m)  ; eauto.
  intros IH1 IH2.
  destruct (classic (exists x, In (Iphi x r) phiinstr)).
  destruct H0 as [x'' H0].
  elim IH1 with (1:=H0); intros l' H'.
  exists (l'++pc::nil). auto.
  rewrite IH2.
  exists nil; auto.
  intros; elim H0; eauto.
  rewrite P2Tree.gss; auto.
  
  simpl.
  destruct m!2 r'.
  elim IHphiinstr with (P2Tree.set r' (pc :: l) m); auto.
  intros IH1 IH2.
  elim IH1 with (1:=H1); intros l' H'.
  exists (l'); auto. rewrite P2Tree.gso ; auto.
  elim IHphiinstr with (P2Tree.set r' (pc :: nil) m); auto.
  intros IH1 IH2.
  elim IH1 with (1:=H1); intros l' H'.
  exists (l'); auto. rewrite P2Tree.gso ; auto.

  destruct a as [x' r'].
  destruct (p2eq r' r); subst.
  elim H0 with x'; auto.
  simpl. destruct m!2 r'.
  elim IHphiinstr with (P2Tree.set r' (pc::l) m).
  intros IH1 IH2. simpl.
  rewrite IH2; eauto.
  rewrite P2Tree.gso; auto.

  elim IHphiinstr with (P2Tree.set r' (pc::nil) m).
  intros IH1 IH2. simpl.
  rewrite IH2; eauto.
  rewrite P2Tree.gso; auto.
Qed.


Inductive assigned_phi_spec_twice (phicode: phicode) (pc: node): reg -> Prop :=
  APhi2: forall phi dst, 
    (phicode!pc) = Some phi ->
    (∃args : list reg, exists args', 
      In (Iphi args dst) phi /\ In (Iphi args' dst) phi /\ args' <> args) ->
    assigned_phi_spec_twice phicode pc dst.

Lemma record_assigned_reg_phi_preserve3 : forall  phiinstr a r pc l, 
  a !2  r = Some l ->
  exists l', (record_assigned_reg_phi a pc phiinstr) !2  r = Some (l' ++ l).
Proof.
  induction phiinstr.

  (* nil *)
  intros. simpl. exists nil. auto.
  
  (* a::phiinstr *)
  destruct a. intros. simpl.
  destruct (p2eq r r0). inv e.
  rewrite H. 
  elim  IHphiinstr with (P2Tree.set r0 (pc::l0) a) r0 pc (pc::l0).
  intros.
  exists (x++pc::nil). rewrite app_ass ; auto. rewrite P2Tree.gss ; auto.
  destruct a!2 r.
  elim  IHphiinstr with (P2Tree.set r (pc::l1) a) r0 pc (l0).
  intros.
  eauto. rewrite P2Tree.gso ; auto.
  elim  IHphiinstr with (P2Tree.set r (pc::nil) a) r0 pc (l0).
  intros.
  eauto. rewrite P2Tree.gso ; auto.
Qed.

Inductive assigned_phi_spec_once (phicode: phicode) (pc: node): reg -> Prop :=
  APhi1: forall phi dst, 
    (phicode!pc) = Some phi ->
    (∃args : list reg, In (Iphi args dst) phi /\ 
      forall args', In (Iphi args' dst) phi -> args' = args) ->
    (NoDup phi) ->
    assigned_phi_spec_once phicode pc dst.

Lemma assigned_phi_spec_stronger : forall r l code t,
  t !2  r = Some l ->
  (forall pc phi, code ! pc = Some phi -> NoDup phi) ->
  (forall pc phi, code ! pc = Some phi -> NoDup phi) ->
  (forall pc, (assigned_phi_spec_once code pc r) ->
    exists l', 
      exists l'', (PTree.fold record_assigned_reg_phi code t) !2  r = Some (l'++pc::l''++l))
  /\
  (forall pc, (assigned_phi_spec_twice code pc r) ->
    exists l', 
      exists l'', 
        exists l''', (PTree.fold record_assigned_reg_phi code t) !2  r = Some (l'++pc::l''++pc::l'''++l))
  /\
  ((forall pc, ~ (assigned_phi_spec code pc r)) ->
      (PTree.fold record_assigned_reg_phi code t) !2  r = Some l).
Proof.
  intros r l.
  intros code t Ha Hcode.
  set (P := fun (code : phicode)  (t : P2Tree.t (list positive))  =>
    (forall pc phi, code ! pc = Some phi -> NoDup phi) ->
    (forall pc, assigned_phi_spec_once code pc r
    → (∃l', ∃l'',
       t !2  r = Some (l'++pc :: l'' ++ l)))
    /\
    (forall pc, assigned_phi_spec_twice code pc r
    → (∃l', ∃l'', exists l''',
       t !2  r = Some (l'++pc :: l'' ++ pc::l''' ++l)))
    /\ ((forall pc, ~ assigned_phi_spec code pc r)
      → t !2  r = Some l)).
  apply PTree_Properties.fold_rec with (P:= P); unfold P in *; clear P; intros.

   (* extensionality *)
  split ; intros.
  elim H0. intros IH1 [IH2 IH3].
  elim IH1 with pc. intros.  eauto. 
  inv H2. rewrite <- (H pc) in H3 ; destruct H4. exists phi ; eauto. 
  intros. rewrite (H pc0) in H3. eapply H1 ; eauto.
  
  split ; intros.
  elim H0. intros IH1 [IH2 IH3].
  elim IH2 with  pc. intros. 
  eauto. 
  inv H2. rewrite <- (H pc) in H3 ; destruct H4. exists phi ; eauto. 
  intros.  eapply (H1 pc0) ; eauto. rewrite (H pc0) in H3; auto.
  
  elim H0. intros IH1 [IH2 IH3].  
  rewrite IH3. auto. 
  intros. intro. elim H2 with pc.
  inv H3. rewrite (H pc) in H4. eauto. 
  
  intros. rewrite (H pc) in H3. eapply H1 ; eauto.

  (* base case *)
  split; intros; auto. 
  inv H0. rewrite PTree.gempty in H1; congruence.
  split ; intros.
  inv H0. rewrite PTree.gempty in H1; congruence.
  auto.

   (* inductive case *)
  
  assert (HNodup: forall pc phi, m ! pc = Some phi -> NoDup phi).
  intros.
  destruct (peq k pc). inv e. congruence.
  eapply (H2 pc) ; eauto. rewrite PTree.gso; auto.
  assert (HH := H1 HNodup) ; eauto. clear H1.
  destruct HH as [IH1 [IH2 IH3]].

  intuition; intros.  
   
  (* assigned once set k v m *)
  destruct (peq pc k) as [eq| neq] ; inv H1.
  
  (* eq *)
  rewrite PTree.gss in H3.  inv H3. inv H4.
  destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].
  destruct EM1 as [pc EM1].

  (* EM1 *)
  generalize EM1 ; inv EM1 ; intros EM1.
  destruct H4.
  destruct (classic (exists args', In (Iphi args' r) phiinstr /\ x0 <> args')) as [EM11|EM12].

      (* EM11 *)
      destruct EM11 as [args' EM11].
      elim IH2 with pc; auto. intros l' [l'' [l''' H']].
      elim record_assigned_reg_phi_inlist2_stronger with r k phi (l' ++ pc :: l'' ++ pc::l'''++l) a; auto.
      intros. elim H6 with x; auto. intros l'''' H''.
      exists nil. exists (l''''++ l' ++ pc :: l''++pc::l'''). simpl. 
      repeat (rewrite app_ass ; (repeat rewrite <- app_comm_cons)). eauto.
      intuition ; auto. 
      destruct EM11. exists phiinstr; eauto. 
  
      (* EM12 *)      
      elim IH1 with pc; auto. intros l''' H''. 
      destruct H''.
      elim record_assigned_reg_phi_inlist2_stronger with r k phi (l'''++pc::x1++l) a; auto.
      intros. elim H7 with x; auto. intros l'' H''.
      exists nil; simpl; eauto. exists (l''++l'''++pc::x1).
      repeat (rewrite app_ass ; (repeat rewrite <- app_comm_cons)). eauto.
      intuition; auto.
      exists phiinstr; eauto. exists x0 ; eauto. split ; auto.
      intros. destruct (list_eq_dec p2eq args' x0); auto. 
      elim EM12; auto.  exists args'. split ; auto.
  
  (* EM2 *)
   elim record_assigned_reg_phi_inlist2_stronger  with r k phi l a.
   intros.  elim H3 with x. intros.
   exists nil. simpl. exists x0 ; auto. destruct H1 ; auto.
   rewrite IH3. auto. 
   intros. elim EM2. eauto. 

   (* neq k pc *)
   rewrite PTree.gso in H3 ; auto.
   destruct H4. destruct H1.
   elim IH1 with pc. intros. destruct H6.
   elim record_assigned_reg_phi_inlist2_stronger  with r k v (x0++pc::x1++l) a ; auto.
   intros.
   destruct (classic (exists x, In (Iphi x r) v)) as [EM1 | EM2].
   destruct EM1 as [args Hargs].
   elim H7 with args; auto. intros.
   exists (k::x2++x0).  exists x1.
   repeat rewrite ass_app in H9.
   repeat rewrite app_ass. rewrite app_comm_cons in H9. auto.
   
   rewrite H8. eauto. intros. intro. elim EM2 ; eauto.
   exists phi ; eauto.

   (* assigned twice set k v m *)
   destruct (peq pc k) as [eq | neq] ; inv H1 .
   
   (* eq *)
   rewrite PTree.gss in H3. inv H3.
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].
   destruct EM1 as [pc EM1].

   (* EM1 *)
   generalize EM1 ; inv EM1 ; intros EM1.
   destruct H3.
   
       (* EM11 *)
       destruct (classic (exists args', In (Iphi args' r) phiinstr /\ x <> args')) as [EM11|EM12].
       destruct EM11 as [args' EM11].
       
       elim IH2 with pc; auto. intros l' [l'' [l''' H']].
       elim record_assigned_reg_phi_inlist3_stronger with r k phi (l' ++ pc :: l'' ++ pc::l'''++l) a; auto.
       intros. elim H6 ; auto. intros.  destruct H4. destruct H4.
       elim H7 with x0. intros.
       exists nil. simpl.  
       exists x2. destruct H9.
       exists (x3++ l' ++ pc :: l''++pc::l'''). simpl.
       repeat (rewrite app_ass ; (repeat rewrite <- app_comm_cons)). eauto.

       intuition. auto. exists x1 ; intuition ; eauto.
       eapply Hcode ; eauto.       
       exists phiinstr; eauto. exists args' ; exists x    ; intuition ; eauto.
  
      (* EM12 *)      
       elim IH1 with pc; auto. intros l' [l'' H''].
       elim record_assigned_reg_phi_inlist3_stronger with r k phi (l' ++ pc :: l'' ++ l) a; auto.
       intros. elim H6 ; auto. intros.  destruct H4. destruct H4.
       elim H7 with x0. intros.
       exists nil. simpl.  
       exists x2. destruct H9.
       exists (x3++ l' ++ pc :: l''). simpl. 
       repeat (rewrite app_ass ; (repeat rewrite <- app_comm_cons)). eauto.
       intuition ; auto. intuition ; eauto. 
       eapply Hcode ; eauto.
       exists phiinstr; eauto. exists x ; intuition; eauto. 
       destruct (list_eq_dec p2eq args' x); auto. elim EM12 ; eauto.
  
  (* EM2 *)
   elim record_assigned_reg_phi_inlist3_stronger  with r k phi l a.
   intros.  destruct H4. destruct H4. elim H3. intros. elim H5 with x. intros.
   exists nil. simpl. eauto. intuition; eauto.  intuition; eauto. 
   rewrite IH3. auto. 
   intros. elim EM2. eauto. 
   eapply Hcode ; eauto.

   (* neq k pc *) 
   rewrite PTree.gso in H3 ; auto.
   destruct H4 as [x [x0 Hx]].

   elim IH2 with pc. intros. destruct H1 as [l'' [l''' H''']].
   elim record_assigned_reg_phi_inlist2_stronger  with r k v (x1++pc::l''++pc::l'''++l) a ; auto.
   intros.
   destruct (classic (exists x, In (Iphi x r) v)) as [EM1 | EM2].
   destruct EM1 as [args Hargs].
   elim H1 with args; auto. intros.
   exists (k::x2++x1).  exists l''. exists l'''. 
   repeat rewrite ass_app in H5.
   repeat rewrite app_ass.  rewrite app_comm_cons in H5. auto.
   
   rewrite H4. eauto. intros. intro. elim EM2 ; eauto.
   exists phi ; eauto.
   
   (* not assigned set k v m *)
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].

   (* EM1 *)
   generalize EM1 ; inv EM1 ; intros EM1.
   destruct H3.
   
   elim record_assigned_reg_phi_inlist2_stronger  with dst k v l a ; auto.
   intros. rewrite H6; auto. 
   intros. intro. elim (H1 k). exists v; eauto. rewrite PTree.gss ; auto.
   rewrite IH3; auto.
   intros. elim H1 with x. exists phiinstr ; eauto.
   rewrite PTree.gso; auto. intro. inv H6. congruence.
   
   (* EM2 *)
   elim record_assigned_reg_phi_inlist2_stronger  with r k v l a ; auto.
   intros. rewrite H4; auto. 
   intros. intro. elim (H1 k). exists v; eauto. rewrite PTree.gss ; auto.
   rewrite IH3; auto.
   intros. elim EM2. eauto. 
Qed. 
 

Lemma assigned_phi_spec_none_stronger : forall r code t,
  t !2  r = None ->
  (forall pc phi, code ! pc = Some phi -> NoDup phi) ->
  (forall pc phi, code ! pc = Some phi -> NoDup phi) ->
  (forall pc, (assigned_phi_spec_once code pc r) ->
    exists l', 
      exists l'', (PTree.fold record_assigned_reg_phi code t) !2  r = Some (l'++pc::l''))
  /\
  (forall pc, (assigned_phi_spec_twice code pc r) ->
    exists l', 
      exists l'', 
        exists l''', (PTree.fold record_assigned_reg_phi code t) !2  r = Some (l'++pc::l''++pc::l'''))
  /\
  ((forall pc, ~ (assigned_phi_spec code pc r)) ->
      (PTree.fold record_assigned_reg_phi code t) !2  r = None).
Proof.
  intros r.
  intros code t Ha Hcode.
  set (P := fun (code : phicode)  (t : P2Tree.t (list positive))  =>
    (forall pc phi, code ! pc = Some phi -> NoDup phi) ->
    (forall pc, assigned_phi_spec_once code pc r
    → (∃l', ∃l'',
       t !2  r = Some (l'++pc :: l'')))
    /\
    (forall pc, assigned_phi_spec_twice code pc r
    → (∃l', ∃l'', exists l''',
       t !2  r = Some (l'++pc :: l'' ++ pc::l''')))
    ∧ ((forall pc, ~ assigned_phi_spec code pc r)
      → t !2  r = None)).
  apply PTree_Properties.fold_rec with (P:= P); unfold P in *; clear P; intros.

   (* extensionality *)
  split ; intros.
  elim H0. intros IH1 [IH2 IH3].
  elim IH1 with pc. intros.  eauto. 
  inv H2. rewrite <- (H pc) in H3 ; destruct H4. exists phi ; eauto. 
  intros. rewrite (H pc0) in H3. eapply H1 ; eauto.
  
  split ; intros.
  elim H0. intros IH1 [IH2 IH3].
  elim IH2 with  pc. intros. 
  eauto. 
  inv H2. rewrite <- (H pc) in H3 ; destruct H4. exists phi ; eauto. 
  intros.  eapply (H1 pc0) ; eauto. rewrite (H pc0) in H3; auto.
  
  elim H0. intros IH1 [IH2 IH3].  
  rewrite IH3. auto. 
  intros. intro. elim H2 with pc.
  inv H3. rewrite (H pc) in H4. eauto. 
  
  intros. rewrite (H pc) in H3. eapply H1 ; eauto.

  (* base case *)
  split; intros; auto. 
  inv H0. rewrite PTree.gempty in H1; congruence.
  split ; intros.
  inv H0. rewrite PTree.gempty in H1; congruence.
  auto.

  (* inductive case *)
  
  assert (HNodup: forall pc phi, m ! pc = Some phi -> NoDup phi).
  intros.
  destruct (peq k pc). inv e. congruence.
  eapply (H2 pc) ; eauto. rewrite PTree.gso; auto.
  assert (HH := H1 HNodup) ; eauto. clear H1.
  destruct HH as [IH1 [IH2 IH3]].

  intuition; intros.  
   
  (* assigned once set k v m *)
  destruct (peq pc k) as [eq| neq] ; inv H1.
  
  (* eq *)
  rewrite PTree.gss in H3.  inv H3. inv H4.
  destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].
  destruct EM1 as [pc EM1].

  (* EM1 *)
  generalize EM1 ; inv EM1 ; intros EM1.
  destruct H4.
  destruct (classic (exists args', In (Iphi args' r) phiinstr /\ x0 <> args')) as [EM11|EM12].

      (* EM11 *)
      destruct EM11 as [args' EM11].
      elim IH2 with pc; auto. intros l' [l'' [l''' H']].
      elim record_assigned_reg_phi_inlist2_stronger with r k phi (l' ++ pc :: l'' ++ pc::l''') a; auto.
      intros. elim H6 with x; auto. intros l'''' H''.
      exists nil. exists (l''''++ l' ++ pc :: l''++pc::l'''). simpl. 
      repeat (rewrite app_ass ; (repeat rewrite <- app_comm_cons)). eauto.
      intuition ; auto. 
      destruct EM11. exists phiinstr; eauto. 
  
      (* EM12 *)      
      elim IH1 with pc; auto. intros l''' H''. 
      destruct H''.
      elim record_assigned_reg_phi_inlist2_stronger with r k phi (l'''++pc::x1) a; auto.
      intros. elim H7 with x; auto. intros l'' H''.
      exists nil; simpl; eauto. 
      intuition; auto.
      exists phiinstr; eauto. exists x0 ; eauto. split ; auto.
      intros. destruct (list_eq_dec p2eq args' x0); auto. 
      elim EM12; auto.  exists args'. split ; auto.
  
  (* EM2 *)
   elim record_assigned_reg_phi_inlist3_none_stronger  with r k phi a.
   intros.  elim H3 with x. intros.
   exists nil. simpl. exists x0 ; auto. destruct H1 ; auto.
   eapply  H1; eauto.

   rewrite IH3. auto. 
   intros. elim EM2. eauto. 
   eapply Hcode ; eauto.

   (* neq k pc *)
   rewrite PTree.gso in H3 ; auto.
   destruct H4. destruct H1.
   elim IH1 with pc. intros. destruct H6.
   elim record_assigned_reg_phi_inlist2_stronger  with r k v (x0++pc::x1) a ; auto.
   intros.
   destruct (classic (exists x, In (Iphi x r) v)) as [EM1 | EM2].
   destruct EM1 as [args Hargs].
   elim H7 with args; auto. intros.
   exists (k::x2++x0).  exists x1.
   repeat rewrite ass_app in H9.
   repeat rewrite app_ass. rewrite app_comm_cons in H9. auto.
   
   rewrite H8. eauto. intros. intro. elim EM2 ; eauto.
   exists phi ; eauto.

   (* assigned twice set k v m *)
   destruct (peq pc k) as [eq | neq] ; inv H1 .
   
   (* eq *)
   rewrite PTree.gss in H3. inv H3.
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].
   destruct EM1 as [pc EM1].

   (* EM1 *)
   generalize EM1 ; inv EM1 ; intros EM1.
   destruct H3.
   
       (* EM11 *)
       destruct (classic (exists args', In (Iphi args' r) phiinstr /\ x <> args')) as [EM11|EM12].
       destruct EM11 as [args' EM11].
       
       elim IH2 with pc; auto. intros l' [l'' [l''' H']].
       elim record_assigned_reg_phi_inlist3_stronger with r k phi (l' ++ pc :: l'' ++ pc::l''') a; auto.
       intros. elim H6 ; auto. intros.  destruct H4. destruct H4.
       elim H7 with x0. intros.
       exists nil. simpl.  
       exists x2. destruct H9.
       exists (x3++ l' ++ pc :: l''++pc::l'''). simpl.
       repeat (rewrite app_ass ; (repeat rewrite <- app_comm_cons)). eauto.

       intuition. auto. exists x1 ; intuition ; eauto.
       eapply Hcode ; eauto.       
       exists phiinstr; eauto. exists args' ; exists x    ; intuition ; eauto.
  
      (* EM12 *)      
       elim IH1 with pc; auto. intros l' [l'' H''].
       elim record_assigned_reg_phi_inlist3_stronger with r k phi (l' ++ pc :: l'') a; auto.
       intros. elim H6 ; auto. intros.  destruct H4. destruct H4.
       elim H7 with x0. intros.
       exists nil. simpl.  
       exists x2. destruct H9.
       exists (x3++ l' ++ pc :: l''). simpl. 
       repeat (rewrite app_ass ; (repeat rewrite <- app_comm_cons)). eauto.
       intuition ; auto. intuition ; eauto. 
       eapply Hcode ; eauto.
       exists phiinstr; eauto. exists x ; intuition; eauto. 
       destruct (list_eq_dec p2eq args' x); auto. elim EM12 ; eauto.
  
  (* EM2 *)
   elim record_assigned_reg_phi_inlist3_none_stronger  with r k phi a.
   intros.  destruct H4. destruct H4. elim H3. intros. elim H5 with x. intros.
   exists nil. simpl. eauto. intuition; eauto.  intuition; eauto. 
   rewrite IH3. auto. 
   intros. elim EM2. eauto. 
   eapply Hcode ; eauto.

   (* neq k pc *) 
   rewrite PTree.gso in H3 ; auto.
   destruct H4 as [x [x0 Hx]].

   elim IH2 with pc. intros. destruct H1 as [l'' [l''' H''']].
   elim record_assigned_reg_phi_inlist2_stronger  with r k v (x1++pc::l''++pc::l''') a ; auto.
   intros.
   destruct (classic (exists x, In (Iphi x r) v)) as [EM1 | EM2].
   destruct EM1 as [args Hargs].
   elim H1 with args; auto. intros.
   exists (k::x2++x1).  exists l''. exists l'''. 
   repeat rewrite ass_app in H5.
   repeat rewrite app_ass.  rewrite app_comm_cons in H5. auto.
   
   rewrite H4. eauto. intros. intro. elim EM2 ; eauto.
   exists phi ; eauto.
   
   (* not assigned set k v m *)
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].

   (* EM1 *)
   generalize EM1 ; inv EM1 ; intros EM1.
   destruct H3.
   
   elim record_assigned_reg_phi_inlist3_none_stronger  with dst k v a ; auto.
   intros. elim H6 ; intros. rewrite H8; auto. 
   intros. intro. elim (H1 k). exists v; eauto. rewrite PTree.gss ; auto.
   rewrite IH3; auto.
   intros. elim H1 with x. exists phiinstr ; eauto.
   rewrite PTree.gso; auto. intro. inv H6. congruence.
   eapply Hcode ; eauto.

   (* EM2 *)
   elim record_assigned_reg_phi_inlist3_none_stronger  with r k v a ; auto.
   intros. elim H4 ; intros. rewrite H6; auto. 
   intros. intro. elim (H1 k). exists v; eauto. rewrite PTree.gss ; auto.
   rewrite IH3; auto.
   intros. elim EM2. eauto. 
   eapply Hcode ; eauto.
Qed. 

 
Lemma assigned_phi_spec_inlist2_stronger : forall r l code t,
  t !2  r = Some l ->
  (forall pc, (assigned_phi_spec code pc r) ->
    exists l', 
      exists l'', (PTree.fold record_assigned_reg_phi code t) !2  r = Some (l'++pc::l''++l))
  /\
  ((forall pc, ~ (assigned_phi_spec code pc r)) ->
      (PTree.fold record_assigned_reg_phi code t) !2  r = Some l).
Proof.
  intros r l.
  intros code t Ha.
  set (P := fun (code : phicode)  (t : P2Tree.t (list positive))  =>
    (forall pc, assigned_phi_spec code pc r
    → (∃l', ∃l'',
       t !2  r = Some (l'++pc :: l'' ++ l)))
   ∧ ((forall pc, ~ assigned_phi_spec code pc r)
      → t !2  r = Some l)).
  apply PTree_Properties.fold_rec with (P:= P); unfold P in *; clear P; intros.

   (* extensionality *)
   destruct H0; split; intros.
   apply H0; eauto.
   inv H2; rewrite <- (H pc) in H3 ; eauto.
   apply H1; eauto.
   intros pc T; elim H2 with pc; inv T; rewrite (H pc) in H3 ; eauto.
      
   (* base case *)
   split; intros; auto.
   inv H; rewrite PTree.gempty in H0; congruence.

   (* inductive case *)
   split; intros; destruct H1.

   destruct (peq pc k) ; inv H2.
   rewrite PTree.gss in H4.  inv H4. inv H5.
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM|EM].
   destruct EM as [pc EM].
   elim H1 with pc; auto; intros l' [l'' H'].
   elim record_assigned_reg_phi_inlist2_stronger with r k phiinstr (l' ++ pc :: l'' ++ l) a; auto.
   intros.
   elim H4 with x; auto; intros l''' H''.
   exists nil.
   exists (l'''++ l' ++ pc :: l'').
   repeat rewrite app_ass; auto.
   elim record_assigned_reg_phi_inlist2_stronger with r k phiinstr l a; auto.
   intros.
   elim H4 with x; auto; intros l'' H''.
   exists nil; simpl; eauto.
   apply H3; intros.
   intro; elim EM; eauto.

   rewrite PTree.gso in *; auto.
   destruct H5 as [x H5].
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM|EM].
   destruct EM as [pc' EM].
   elim H1 with pc; auto.
   intros l' [l'' H'].
   elim record_assigned_reg_phi_inlist2_stronger with r k v (l' ++ pc :: l'' ++ l) a; auto.
   intros.
   destruct (classic (exists x, In (Iphi x r) v)) as [EM1|EM1].
   destruct EM1 as [x' EM1].
   elim H2 with x'; auto; intros l''' H''.
   exists ((k :: l''') ++ l').
   exists l''.
   rewrite app_ass; auto.
   rewrite H6; eauto.
   exists phiinstr; eauto.
   
   clear H1.
   elim EM; exists pc; exists phiinstr; eauto.

   elim record_assigned_reg_phi_inlist2_stronger with r k v l a; auto.
   intros _ H5.
   rewrite H5; auto.
   red; intros.
   elim H2 with k.
   exists v.
   rewrite PTree.gss; auto.
   eauto.
   apply H3.
   intros.
   intro.
   elim H2 with pc; clear H2.   
   destruct (peq k pc); inv H4.
   congruence.
   exists phiinstr; eauto.
   rewrite PTree.gso; auto.
Qed.

Lemma assigned_phi_spec_inlist3_stronger : forall r code t,
  t !2  r = None ->
  (forall pc, (assigned_phi_spec code pc r) ->
    exists l', 
      exists l'', (PTree.fold record_assigned_reg_phi code t) !2  r = Some (l'++pc::l''))
  /\
  ((forall pc, ~ (assigned_phi_spec code pc r)) ->
      (PTree.fold record_assigned_reg_phi code t) !2  r = None).
Proof.
  intros r code t Ha.
  set (P := fun (code : phicode)  (t : P2Tree.t (list positive))  =>
    (forall pc, assigned_phi_spec code pc r
    → (∃l', ∃l'',
       t !2  r = Some (l'++pc :: l'')))
   ∧ ((forall pc, ~ assigned_phi_spec code pc r)
      → t !2  r = None)).
  apply PTree_Properties.fold_rec with (P:= P); unfold P in *; clear P; intros.

   (* extensionality *)
   destruct H0; split; intros.
   apply H0; eauto.
   inv H2; rewrite <- (H pc) in H3 ; eauto.
   apply H1; eauto.
   intros pc T; elim H2 with pc; inv T; rewrite (H pc) in H3 ; eauto.
      
   (* base case *)
   split; intros; auto.
   inv H; rewrite PTree.gempty in H0; congruence.

   (* inductive case *)
   split; intros; destruct H1.

   destruct (peq pc k) ; inv H2.
   rewrite PTree.gss in H4.  inv H4. inv H5.
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].

   destruct EM1 as [pc EM1].
   elim H1 with pc; auto; intros l' [l'' H'].
   elim record_assigned_reg_phi_inlist2_stronger with r k phiinstr (l' ++ pc :: l'') a; auto.
   intros.
   elim H4 with x; auto; intros l''' H''.
   exists nil. simpl.
   exists (l'''++ l' ++ pc :: l'').
   auto. 
   elim record_assigned_reg_phi_inlist4_stronger with r k phiinstr a; eauto.
   intros.
   elim H4 with x; auto; intros l'' H''.
   exists nil; simpl; eauto.
   rewrite PTree.gso in * ; auto.
   destruct H5 as [x H5].
   destruct (classic (exists pc, assigned_phi_spec m pc r)) as [EM1|EM2].
   destruct EM1 as [pc' EM1].
   elim H1 with pc; auto.
   intros l' [l'' H'].
   elim record_assigned_reg_phi_inlist2_stronger with r k v (l' ++ pc :: l'') a; auto.
   intros.
   destruct (classic (exists x, In (Iphi x r) v)) as [EMM1|EMM2].
   destruct EMM1 as [x' EMM1].
   elim H2 with x'; auto; intros l''' H''.
   exists ((k :: l''') ++ l').
   exists l''.
   rewrite app_ass; auto.
   rewrite H6; eauto.
   exists phiinstr; eauto.
   
   clear H1.
   elim EM2; exists pc; exists phiinstr; eauto.

   elim record_assigned_reg_phi_inlist4_stronger with r k v a; auto.
   intros _ H5.
   rewrite H5; auto.
   red; intros.
   elim H2 with k.
   exists v.
   rewrite PTree.gss; auto.
   eauto.
   apply H3.
   intros.
   intro.
   elim H2 with pc; clear H2.   
   destruct (peq k pc); inv H4.
   congruence.
   exists phiinstr; eauto.
   rewrite PTree.gso; auto.
Qed.

Lemma ex_nodup {A: Type} :
  (forall x y:A, {x = y}+{x <> y}) ->
  forall (l: list A), NoDup l \/ ~ NoDup l.
Proof.
  induction l.
  left; econstructor.
  destruct (In_dec X a l).
  right. intro. inv H. elim H2 ; auto.
  destruct IHl.
  left. econstructor; auto.
  right. intro. inv H0. congruence.
Qed.
  
Lemma assigned_code_spec_inlist2 : forall code r pc,
  (assigned_code_spec code pc r) ->
  exists l, ((PTree.fold record_assigned_reg code (P2Tree.empty (list positive))) !2  r = Some l
    /\ In pc l).
Proof.
  set (P := fun (code : code)  (c : P2Tree.t (list positive))  =>
    forall r pc, assigned_code_spec code pc r ->
    exists l, c !2  r = Some l /\ In pc l).
   intros code.
   apply PTree_Properties.fold_rec with (P:= P).
   
   (* extensionality *)
   unfold P; intros.
   apply H0; eauto.
   inv H1; rewrite <- (H pc) in H2 ; eauto.
      
   (* base case *)
   red. intros.
   inv H; rewrite PTree.gempty in H0; congruence.
   
   (* inductive case *)
   unfold P; intros.
   unfold record_assigned_reg.
   destruct v;
     try (destruct s0);
     match goal with
       | [ H : ?code ! ?k = Some ?i |- _  ] =>
         try (
            destruct (peq k pc) as [Heq1 | Heq2]; try inv Heq1;
            (* *)
              [(assert (Hk : ((PTree.set pc i m) ! pc = Some i)) by (rewrite PTree.gss ; auto));
                (destruct (p2eq r0 r) as [Heq1 | Heq2]; try inv Heq1);
                  (***) [destruct (a !2  r); eauto;
                             [ exists (pc::l0) ; rewrite P2Tree.gss  ; eauto
                               | exists (pc::nil) ; rewrite P2Tree.gss  ; eauto]
                  (***)
                    |inv H2; rewrite H3 in Hk ; inv Hk; elim Heq2 ; eauto]
            (* *)
                |exploit (H1 r pc) ; eauto; (intros; destruct H3);
                  destruct (p2eq r r0) as [rr0 | diff]; try inv rr0;
                    [ destruct H3 ; rewrite H3 in * ; exists (k::x) ; rewrite P2Tree.gss ; eauto
                      | destruct (a !2  r0); rewrite P2Tree.gso ; eauto]]);
         try (
           eapply H1; eauto;
           destruct (peq k pc) as [Heq1 | Heq2]; try inv Heq1;
             [(assert (Hk : ((PTree.set pc i m) ! pc = Some i)) by (rewrite PTree.gss ; auto)); (inv H2; try congruence)
               | (assert (Hk : ((PTree.set k i m) ! pc = m ! pc)) by (rewrite PTree.gso ; auto)); inv H2; try (rewrite Hk in * ; eauto)])
     end.
 Qed.


Lemma check_unique_def_correct1 : forall tf, 
  check_unique_def tf = true -> 
  (forall (r : reg) (pc pc' : node),
    assigned_code_spec (fn_code tf) pc r ->
    assigned_code_spec (fn_code tf) pc' r -> pc = pc').
Proof.
  intros tf CHECK ; intros. 
  generalize CHECK ; intros CHECK'.
  generalize H H0 ; intros.
  eapply assigned_code_spec_inlist2 in H; eauto.
  destruct H as [lr [Hlr Hinpc]].
  eapply assigned_code_spec_inlist2 in H0; eauto.
  destruct H0 as [lr' [Hlr' Hinpc']].
  rewrite Hlr in Hlr'. inv Hlr'.
  
  generalize Hlr ; intro Hlr'.
  eapply fold_record_preserve with (pc:= pc') (code:= (fn_phicode tf)) in Hlr; eauto. 
  eapply fold_record_preserve with (pc:= pc) (code:= (fn_phicode tf)) in Hlr'; eauto. 
  
  destruct Hlr' as [llr' [Hllr' Hinllr']].
  destruct Hlr as [llr [Hllr Hinllr]].
  rewrite Hllr' in *. inv Hllr'. inv Hllr.
  eapply ptree2_forall with (i := r) in CHECK'; eauto. 
  rewrite H0 in *.
    
  destruct llr.  inv Hinllr'.
  case_eq llr ; intros; rewrite H in *.  
  inv Hinllr; auto. inv Hinllr'; auto. 
  elim H. elim H3. inv CHECK'.
Qed.  

Lemma check_unique_def_correct2 : forall tf,
  check_unique_def tf = true -> 
    (forall (r : reg) (pc pc' : node),
      assigned_phi_spec (fn_phicode tf) pc r ->
      assigned_phi_spec (fn_phicode tf) pc' r -> pc = pc').
Proof.
  intros tf CHECK ; intros.   
  generalize CHECK ; intros CHECK'.
  generalize H H0 ; intros.

  set (t:= PTree.fold record_assigned_reg (fn_code tf) (P2Tree.empty (list positive))).
  eapply assigned_phi_spec_inlist2 with (t := t) in H; eauto.
  destruct H as [lr [Hlr Hinpc]].
  eapply assigned_phi_spec_inlist2 with (t := t) in H0; eauto.
  destruct H0 as [lr' [Hlr' Hinpc']].
  rewrite Hlr in Hlr'. inv Hlr'.
  
  eapply ptree2_forall with (i := r) in CHECK'; eauto. 
  unfold t in Hlr. rewrite Hlr in *.

  destruct lr'. inv Hinpc.
  case_eq lr' ; intros; rewrite H in *.
  assert (p = pc). inv Hinpc ; auto ; elim H0.
  rewrite <- H0. inv Hinpc'; auto. elim H3. inv CHECK'.
Qed.

     
Lemma check_unique_def_correct3_help : forall tf,
  check_unique_def tf = true -> 
  (forall (r : reg) (pc pc' : node),
    assigned_code_spec (fn_code tf) pc r -> assigned_phi_spec (fn_phicode tf) pc' r -> False). 
Proof.
  intros tf CHECK ; intros.
  generalize CHECK ; intros CHECK'.
  generalize H ; intros.
  generalize H0 ; intros.
  eapply assigned_code_spec_inlist2 in H; eauto.
  destruct H as [lr [Hlr Hinpc]].
  
  set (t:= PTree.fold record_assigned_reg (fn_code tf) (P2Tree.empty (list positive))).
  eapply assigned_phi_spec_inlist2 with (t := t) in H0; eauto.
  destruct H0 as [lr' [Hlr' Hinpc']].

  generalize Hlr ; intro Hlr''.
  eapply fold_record_preserve with (pc:= pc) (code:= (fn_phicode tf)) in Hlr; eauto.
  destruct Hlr as [llr' [Hllr' Hinllr']].
  
  unfold t in *. clear t.
  eapply ptree2_forall with (i := r) in CHECK'; eauto.
  rewrite Hllr' in *. inv Hlr'.

  case_eq lr' ; intros.
  (* zero elems *) inv H. inv Hinllr'.
  (* one elements *) inv H. destruct l ; try congruence.   clear CHECK'.
  assert (Hppc: p = pc) by (inv Hinllr' ; auto ; elim H;  inv CHECK').
  rewrite Hppc in *. inv Hinpc'; try congruence. 
  set (t:= (PTree.fold record_assigned_reg (fn_code tf)
                (P2Tree.empty (list positive)))) in *.
  clear Hinllr'.
  exploit (assigned_phi_spec_inlist2_stronger r lr (fn_phicode tf)) ; eauto.
  intros. destruct H as [HH _].
  exploit HH ; eauto. 
  intros. destruct H as [l' [l'' Hr]].
  rewrite Hr in Hllr'. inv Hllr'.
  
  rewrite app_comm_cons in H0. 
  rewrite <- app_ass in H0.
  elim app_eq_unit with (1:= H0); intros.
  destruct H. symmetry in H. eapply app_cons_not_nil in H; eauto.
  destruct H. inv H2.
  inv Hinpc. inv H.
Qed.

Lemma check_unique_def_correct31 : forall tf,
  check_unique_def tf = true -> 
  (forall (r : reg) (pc pc' : node),
    (assigned_phi_spec (fn_phicode tf) pc' r) -> ~ assigned_code_spec (fn_code tf) pc r). 
Proof.
  intros.
  intro HCONT.
  eapply check_unique_def_correct3_help ; eauto.
Qed.

Lemma check_unique_def_correct32 : forall tf,
  check_unique_def tf = true -> 
  (forall (r : reg) (pc pc' : node),
    (assigned_code_spec (fn_code tf) pc' r) -> ~ assigned_phi_spec (fn_phicode tf) pc r). 
Proof.
  intros.
  intro HCONT.
  eapply check_unique_def_correct3_help ; eauto.
Qed.

Lemma not_assigned_code_spec_none : forall code r,
  (forall pc, ~ assigned_code_spec code pc r) ->
  (PTree.fold record_assigned_reg code (P2Tree.empty (list positive))) !2  r = None.
Proof.
  set (P := fun (code : code)  (c : P2Tree.t (list positive))  =>
    forall r, (forall pc, ~ assigned_code_spec code pc r) -> c !2  r = None).
   intros code.
   apply PTree_Properties.fold_rec with (P:= P).
   
   (* extensionality *)
   unfold P; intros.
   apply H0; eauto. intros ; intro.
   inv H2 ; rewrite (H pc) in H3; eauto ; elim (H1 pc); eauto.
      
   (* base case *)
   red.
   intros.  rewrite P2Tree.gempty; auto.
   
   (* inductive case *)
   unfold P; intros.
   case_eq v ; intros; inv H3 ; (try (apply H1; eapply not_assigned_monotone; eauto));
   try ( ((destruct (p2eq r0 r) as [Heq1 | Heq2];
     [ inv Heq1;
       elim (H2 k);
         match goal with
           |[H : ?code ! ?k = Some ?i |- _ ] =>
             (assert (Hk : ((PTree.set k i m) ! k = Some i)) by (rewrite PTree.gss ; auto));
               eauto
         end
             | unfold record_assigned_reg;
               assert (Hr : a !2  r = None) by (apply H1 ; eapply not_assigned_monotone; eauto);
                 destruct (a !2  r0); rewrite P2Tree.gso ; auto]))
         ).
 Qed.

Lemma check_unique_def_correct41 : forall tf,
  check_unique_def tf = true ->
  (forall pc phi, tf.(fn_phicode) ! pc = Some phi -> NoDup phi) ->
  forall pc phiinstr,  tf.(fn_phicode) ! pc = Some phiinstr ->
    (forall r args args',
      In (Iphi args r) phiinstr -> In (Iphi args' r) phiinstr -> args = args').
Proof.
  intros tf CHECK. intros.
  
  generalize CHECK ; intros CHECK'.  
  unfold check_unique_def in CHECK.
  
  assert (Hass : assigned_phi_spec (fn_phicode tf) pc r) by (exists phiinstr ; eauto ).
  assert (Hnotass: forall pc', ~ assigned_code_spec (fn_code tf) pc' r) by ( intros; eapply check_unique_def_correct31 with (2:= Hass); eauto).
  
  exploit not_assigned_code_spec_none ; eauto. intros.
  set (t:= PTree.fold record_assigned_reg (fn_code tf) (P2Tree.empty (list positive))) in *.
  
  destruct (list_eq_dec p2eq args args'); auto.

  elim (assigned_phi_spec_none_stronger r (fn_phicode tf) t); eauto. 
  intros _ [HH _]. 
  exploit (HH pc); eauto. 
  exists phiinstr; eauto.
  intros. destruct H4 as [l' [l'' [l''' Hr]]].
  
  eapply ptree2_forall with (i := r) in CHECK; eauto. 
  rewrite Hr in *. clear HH.
  destruct l'. simpl in CHECK.
  destruct l''. simpl in CHECK. congruence. 
  simpl in CHECK. congruence.
  simpl in CHECK. 
  destruct l'. simpl in CHECK. congruence.
  simpl in CHECK. congruence.
Qed.

Inductive dup : list phiinstruction -> reg -> Prop := 
| dup_intro1: forall args reg phi,
    In (Iphi args reg) phi -> dup  ((Iphi args reg)::phi) reg
| dup_intro2: forall r phi iphi, 
   dup phi r -> dup (iphi::phi) r.

Lemma not_nodup_dup : forall phiblock, 
  ~ NoDup phiblock -> 
  exists r, dup phiblock r.
Proof.
  induction phiblock ; intros ; auto.
  elim H. econstructor ; eauto.
  assert (forall (iphi1 iphi2: phiinstruction), {iphi1 = iphi2}+{iphi1 <> iphi2}) by
    (repeat decide equality).
  destruct a.
  destruct (In_dec X (Iphi l r) phiblock).
  exists r. econstructor 1  ; eauto.
  exploit IHphiblock ; eauto.
  intro Hcont. elim H ; auto.
  econstructor ; eauto.
  intros [r' Hr']. exists r'. econstructor ; eauto.
Qed.

Lemma dup_v_in_v : forall phi v,
  dup phi v ->
  exists args,  In (Iphi args v) phi.
Proof.
  induction 1 ; intros.
  exists args ; auto.
  destruct IHdup ; eauto.
Qed.


Lemma dup_record_assigned_reg_phi : forall phi dst a pc,  
  dup phi dst -> 
  ∃l : list positive,
  (record_assigned_reg_phi a pc phi) !2  dst = Some l ∧ length l ≥ 2.
Proof.
  induction phi ; intros. 
  inv H. 
  
  inv H. simpl.
  destruct a0 !2  dst.
  exploit (record_assigned_reg_phi_inlist2_stronger dst pc phi (pc::l) (P2Tree.set dst (pc::l) a0)) ; eauto.
  rewrite P2Tree.gss ; auto.
  intros. destruct H as [HH _].
  
  exploit (HH args) ; eauto.
  intros. destruct H. exists (pc::x ++ pc::l) ; split ; eauto.
  destruct x; destruct l; (simpl; lia).
  exploit (record_assigned_reg_phi_inlist2_stronger dst pc phi (pc::nil) (P2Tree.set dst (pc::nil) a0)) ; eauto.
  rewrite P2Tree.gss ; auto.
  intros. destruct H as [HH _].
  exploit (HH args) ; eauto.
  intros. destruct H. exists (pc::x ++ pc::nil) ; split ; eauto.
  destruct x;  (simpl; lia).

  simpl.
  exploit IHphi ; eauto.
Qed.    
  
Lemma dup_more_than_two : forall phicode t pc dst phi , 
  phicode ! pc = Some phi -> 
  dup phi dst ->  
  exists l, 
    (PTree.fold record_assigned_reg_phi phicode t) !2 dst = Some l
    /\ (length l >= 2)%nat.
Proof.
  set (P := fun (code : phicode)  (c : P2Tree.t (list positive))  =>
    forall pc dst phi, 
      code ! pc = Some phi ->
      dup phi dst ->
      exists l, c !2 dst = Some l /\ (length l >= 2)%nat).
  intros code t. apply PTree_Properties.fold_rec with (P:= P).
   
   (* extensionality *)
   unfold P; intros.
   eapply (H0 pc); eauto.
   rewrite <- (H pc) in H1 ; eauto.
      
   (* base case *)
   red. intros.
   unfold P.
   rewrite PTree.gempty in H; congruence.
   
   (* inductive case *)
   unfold P; intros.
   destruct v.

   destruct (peq k pc) as [Heq1 | Heq2]; try inv Heq1.
   
   simpl.
   rewrite PTree.gss in H2.
   inv H2. inv H3.
   rewrite PTree.gso in H2.
   exploit H1 ; eauto. auto.

   destruct (peq k pc) as [Heq1 | Heq2]; try inv Heq1.
   
   simpl.
   rewrite PTree.gss in H2.
   inv H2. generalize H3 ; inv H3 ; intros H3.
   simpl.
   destruct a !2 dst. 
   exploit (record_assigned_reg_phi_inlist2_stronger dst pc v (pc :: l) (P2Tree.set dst (pc :: l) a)) ; eauto.
   rewrite P2Tree.gss ; auto. intros.
   destruct H2 as [HH _].
   exploit dup_v_in_v ; eauto.
   exploit HH ; eauto. intros. destruct H2. 
   exists (pc::x++pc::l); split ; auto.
   destruct x; destruct l; (simpl; lia).
   exploit (record_assigned_reg_phi_inlist2_stronger dst pc v (pc :: nil) (P2Tree.set dst (pc :: nil) a)) ; eauto.
   rewrite P2Tree.gss ; auto. intros.
   destruct H2 as [HH _].
   exploit HH ; eauto. intros. destruct H2. 
   exists (pc::x++pc::nil); split ; auto.
   destruct x;  (simpl; lia).
  
   eapply dup_record_assigned_reg_phi ; eauto.   
   
   rewrite PTree.gso in H2; auto.
   exploit H1 ; eauto. intros. 
   destruct H4. destruct H4. 
   exploit (record_assigned_reg_phi_preserve3 (p::v) a dst  k x) ; eauto.
   intros. destruct H6.
   exists (x0++x) ; split ; auto.
   rewrite app_length ; eauto. lia.
Qed.   
   
Lemma check_unique_def_correct42 : forall tf,
  check_unique_def tf = true ->
  (forall  pc phi, tf.(fn_phicode) ! pc = Some phi -> NoDup phi).
Proof.
  intros tf CHECK pc phi Hphi.
  assert (forall (iphi1 iphi2: phiinstruction), {iphi1 = iphi2}+{iphi1 <> iphi2}).
  repeat decide equality. 
  destruct (ex_nodup X phi) ; auto.
  eapply not_nodup_dup in H.
  destruct H.
  
  unfold check_unique_def in CHECK.
  exploit (dup_more_than_two (fn_phicode tf) (PTree.fold record_assigned_reg (fn_code tf)
                  (P2Tree.empty (list positive)))) ; eauto.
  intros [l [Hl1 Hl2]].
  eapply ptree2_forall with (i := x) in CHECK; eauto.
  rewrite Hl1 in *. destruct l.
  inv Hl2.
  destruct l. inv Hl2. lia.
  inv CHECK. 
Qed. 

Lemma check_unique_def_correct : forall tf, 
  check_unique_def tf = true ->
  unique_def_spec tf.
Proof.
  intros. unfold unique_def_spec.
  split. intros; split.  eapply check_unique_def_correct1; eauto.
  split ; intros. eapply check_unique_def_correct2; eauto.
  split ; intros. eapply check_unique_def_correct32; eauto. eapply check_unique_def_correct31; eauto.
  intros. split. eapply check_unique_def_correct42; eauto.
  intros. eapply check_unique_def_correct41 ; eauto. intros. eapply check_unique_def_correct42 with tf pc0 ; auto.
Qed.  
    
Lemma phiblock_unique_dst: forall args dst a block
  (SPEC: NoDup (a::block)
    /\ (forall (r : reg) (args args' : list reg),
         (In (Iphi args r) (a::block) → In (Iphi args' r) (a::block))
         → args = args'))
  (IN: In (Iphi args dst) (a::block)),
  (a = (Iphi args dst) /\ forall argss, (In (Iphi argss dst) block) -> argss = args)
    \/ (In (Iphi args dst) block).
Proof.
  intros; destruct SPEC as [_ Hphi].
  inversion IN.
  left; intuition; exploit (Hphi dst args argss); eauto.
  right; auto.
Qed.
  
Lemma unique_def_spec_correct: forall tf pc dst block args
  (UDEF: unique_def_spec tf)
  (BLOCK: (fn_phicode tf)! pc = Some ((Iphi args dst)::block)),
  (forall args' dst', 
    In (Iphi args' dst') ((Iphi args dst)::block) ->
    In (Iphi args' dst') block
    -> dst' <> dst).
Proof.
  intros.
  intro. rewrite H1 in *.
  destruct UDEF as [_ UDEF].
  exploit UDEF; eauto. 
  intros. 
  destruct H2 as [Hnodup Hargs'].
  case (list_eq_dec p2eq args' args); intro.
  inv e. 
  inv Hnodup.  elim H3; auto. 
  elim n. exploit (Hargs' dst args args'); eauto.
Qed.
  
Lemma phi_store_copy: forall k block rs dst arg args
  (NODUP: NoDup block)
  (NODUP': (forall r args args', 
    In (Iphi args r) block -> In (Iphi args' r) block → args = args'))
  (IN: In (Iphi args dst) block /\ nth_error args k = Some arg),
  (phi_store  k block rs)#2 dst = rs#2 arg.
Proof.
  induction block; intros; destruct IN as [Hin Hnth].
  inv Hin.
  destruct a; inv Hin. 
  (* (Iphi args dst)  is the head element of the block *)
  inv H; simpl. rewrite Hnth.
  rewrite P2Map.gss ; eauto.
  (* (Iphi args dst) is in the tail of the block *)
  case_eq (nth_error l k); intros;   simpl; rewrite H0. 
  (* case Some *) 
  assert (dst <> r) by (intro; inv H1; inv NODUP; exploit (NODUP' r args l); eauto; intro;
    inv H1; elim H3 ; auto). 
  rewrite P2Map.gso ; eauto.
  symmetry; rewrite <- IHblock with (dst:= dst) (arg:= arg) (args:= args) at 1 ; eauto. 
  inv NODUP; auto.
  (* case None *)
  eapply IHblock ; eauto; inv NODUP ; eauto.
Qed.  

Lemma check_udef_spec_no_dup: forall tf  pc block,
  unique_def_spec tf ->
   (fn_phicode tf) ! pc = Some block ->
   NoDup block.
Proof.
  intros. destruct H as [_ Hdup].
  exploit (Hdup pc); eauto. 
  intro. intuition.
Qed.

Lemma phi_store_copy2: forall f, 
  wf_ssa_function f ->
  forall rs pc phiinstr args arg dst k,
    (fn_phicode f) ! pc = Some phiinstr ->
    In (Iphi args dst) phiinstr ->
    nth_error args k = Some arg ->
    (phi_store k phiinstr rs) #2 dst = rs #2 arg.
Proof.
  intros. 
  eapply phi_store_copy; eauto.
  eapply check_udef_spec_no_dup ; eauto.
  eapply fn_ssa ; eauto.

  intros.
  exploit check_udef_spec_no_dup ; eauto ; intuition.
  eapply fn_ssa ; eauto.
  destruct (list_eq_dec p2eq args0 args') ; auto.
  destruct (fn_ssa f) as [_ Hssa]; eauto.
  exploit Hssa ; eauto. intuition.
  exploit H8 ; eauto.
Qed.  

Lemma unique_def_elim2: forall f pc pc' x, 
  unique_def_spec f ->
  assigned_code_spec (fn_code f) pc x ->
  assigned_code_spec (fn_code f) pc' x -> 
  pc = pc'.
Proof.
  intros.
  inv H.  
  generalize (H2 x pc pc') ; intros Hcont.  
  intuition.
Qed.

Lemma unique_def_elim3: forall f pc pc' x, 
  unique_def_spec f ->
  assigned_phi_spec (fn_phicode f) pc x ->
  assigned_phi_spec (fn_phicode f) pc' x -> 
  pc <> pc' ->
  False.
Proof.
  intros.
  inv H.  
  generalize (H3 x pc pc') ; intros Hcont.  
  intuition.
Qed.

Lemma phi_store_notin_preserved_map: forall k block rs  args,
  (forall dst, In dst args -> forall phiargs, ~ In (Iphi phiargs dst) block)->
  (phi_store k block rs) ##2 args = rs ##2 args.
Proof.
  induction args; intros.
  simpl ; auto.
  simpl. 
  rewrite phi_store_notin_preserved ; eauto.
  rewrite IHargs ; eauto.
Qed.