(** This file contain the equational lemmas that are enabled by the
well-formed SSA functions (see end of file). *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import RTL.
Require Import Dom.
Require Import SSA. 
Require Import SSAtool. 
Require Import SSAutils. 
Require Import Utilsvalidproof.
Require Import Conventions1.
Require Import Kildall.
Require Import KildallComp.
Require Import Relation_Operators.
Require Import Events.

(** The [rhs] (right hand side) predicate *)
Inductive rhs (f:function) (x : reg) : instruction -> Prop := 
| rhs_iop : forall op args pc succ
  (RHS: (fn_code f) ! pc  = Some (Iop op args x succ))
  (MIND: op_depends_on_memory op = false),
  rhs f x (Iop op args x succ).
Hint Constructors rhs.

(** Evaluating an [Iop] instruction *)
Inductive eval : genv -> val -> regset -> instruction -> val -> Prop := 
| eval_Iop : forall ge sp rs m op args res pc' v
  (EVAL: eval_operation ge sp op rs##2 args m = Some v)
  (MIND: op_depends_on_memory op = false),  
  eval ge sp rs (Iop op args res pc') v.
Hint Constructors eval.

(** Definition of semantic equation *)
Inductive models : function -> genv -> val -> regset -> reg -> instruction -> Prop := 
| models_state : forall f ge x x' i sp rs v, 
  rs #2 x = v ->
  rhs f x' i ->
  eval ge sp rs i v ->
  models f ge sp rs x i.
Hint Constructors models.

Notation "[ a , b , c , d ] |= x == i" := (models a b c d x i) (at level 1, b at next level).

(** Equational invariant *)
Inductive sf_inv (ge: genv) : stackframe -> Prop := 
  | sf_inv_intro: forall res (f:function) sp pc rs
    (SFINV: forall x d i, 
      def f x d -> rhs f x i -> 
      sdom f d pc -> [f, ge , sp , rs] |= x == i)
    (SINS: exists pred sig ros args, (fn_code f) ! pred = Some (Icall sig ros args res pc)),    
    sf_inv ge (Stackframe res f sp pc rs).
Hint Constructors sf_inv.

Inductive sfl_inv (ge: genv) : list stackframe -> Prop := 
| sfl_nil : sfl_inv ge nil 
| sfl_cons : forall s sl, 
               sf_inv ge s ->
               sfl_inv ge sl ->
               sfl_inv ge (s::sl).

Inductive s_inv (ge: genv) : state -> Prop := 
  | si_State : forall s (f:function) sp pc rs m
    (WFF: wf_ssa_function f)
    (SINV: forall x d i, 
      def f x d -> rhs f x i -> sdom f d pc -> [f, ge, sp , rs] |= x == i)
    (SFINV: sfl_inv ge s),
    s_inv ge (State s f sp pc rs m)
  | si_Callstate : forall s f args m
    (SFINV: sfl_inv ge s),
    s_inv ge (Callstate s f args m)
  | si_Returnstate: forall s v m
    (SFINV: sfl_inv ge s),
    s_inv ge (Returnstate s v m).
Hint Constructors s_inv.

(** Proving that the equational lemma holds *)
Section INV.

Variable prog : program.
Let ge_prog := Genv.globalenv prog.

Ltac simpl_ext_params := 
  match goal with 
    | [h : ext_params ?f ?x |- _ ] => 
      inv h ; 
      [ (exploit fn_ssa_params ; eauto); 
        (intros [HH HH']; exploit HH ; eauto ; intuition)
        | match goal with 
            |  [ h2 : forall pc : node, ~ assigned_phi_spec (fn_phicode ?f) _ _,
                 h3 : forall pc : node, ~ assigned_code_spec (SSA.fn_code ?f) _ _ |- _ ] =>
            solve [ exploit h2 ; eauto ; intuition | exploit h3 ; eauto ; intuition ]
            end]
  end.

Ltac ssa_f Hwf f := 
      inv Hwf ;
      solve [eelim (unique_def_elim1 f) ; eauto
        | eelim (unique_def_elim3 f) ; eauto].

Ltac wf_ssa f := 
  try (solve [ eapply (fn_ssa f) ; eauto 
    | eapply (fn_code_reached f) ; eauto
    | eapply (fn_phicode_code f) ; eauto
    | eapply (fn_entry f) ; eauto]).

Ltac def_def HWF f x pc pc' :=
  match goal with 
    | [ |- _ ] =>
      (exploit (def_def_eq f HWF x pc pc'); eauto); 
      try (econstructor ; eauto);
        try (solve [econstructor ; eauto])
    | [ |- _ ] =>
      (exploit (def_def_eq f x pc pc' HWF); eauto); 
      try (econstructor ; eauto);
        try (solve [econstructor ; eauto])
  end.

Lemma map_gso : forall (rs: P2Map.t val) args x v,
  (forall arg, In arg args -> arg <> x) ->
  (rs #2 x <- v)##2 args = rs ##2 args.
Proof.
  induction args ; intros.
  simpl ; auto.
  simpl.
  rewrite P2Map.gso ; eauto.
  rewrite IHargs; eauto.
Qed.

Ltac allinv := 
  repeat 
    match goal with 
      | [ H1:   (SSA.fn_code ?s) ! ?pc = Some _  ,
        H2: (SSA.fn_code ?s) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   Some _ = (SSA.fn_code ?s) ! ?pc  ,
        H2: (SSA.fn_code ?s) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | _ => idtac
    end.


Lemma subj_red : forall s s' t,
  s_inv ge_prog s ->
  step ge_prog s t s' ->
  s_inv ge_prog s'.  
Proof.
  intros s s' t HINV STEP.
  inv HINV.

  (* from State *)
  - inv STEP; econstructor ; eauto ; intros.

  (* inop sans block *)
    + unfold fn_code in *.
      destruct (peq d pc).
      * inv e. inv H; try (inv H2; congruence).
        inv H0. simpl_ext_params.
        inv H0.
        inv WFF; eelim (unique_def_elim1 f); eauto.
      * exploit (@sdom_dom_pred node peq) ; eauto; wf_ssa f.
        econstructor ; eauto. simpl ; auto.
        intros Hdom.
        assert (sdom f d pc) by (econstructor ; eauto).
        exploit SINV ; eauto.
  
  (* inop avec block *)
  + destruct (peq d pc).
  unfold fn_code in *.
  inv e. inv H; try (inv H2; congruence).
  inv H0. simpl_ext_params.   
  inv H0.
  assert (assigned_code_spec (fn_code f) pc0 x) by (econstructor ; eauto).
  inv WFF; eelim (unique_def_elim1 f); eauto.
  exploit (@sdom_dom_pred node peq) ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros Hdom.
  assert (sdom f d pc) by (econstructor ; eauto).
  exploit SINV ; eauto. intros Hrs.
  
  econstructor ; eauto.
  inv Hrs. inv H5.
  eapply eval_Iop with (m:= m0); eauto.
  rewrite phi_store_notin_preserved.
  rewrite phi_store_notin_preserved_map; auto.
  (* Po1 *)
  inv H0. intros. 
  intro Hcont. 
  assert (def f dst pc'). econstructor 3 ; eauto. 
  assert (use f dst pc0).  econstructor ; eauto. econstructor ; eauto.
  exploit fn_strict ; eauto; wf_ssa f. intros Hdom'.   
  assert (pc0 = d) by (destruct (peq pc0 d); auto; def_def WFF f res pc0 d). inv H6.
  eapply (@sdom_not_dom node peq) in H1 ; eauto.
  
  (* Po2 *)
  inv H0. intros. intro Hcont.
  assert (assigned_phi_spec (fn_phicode f) pc' res).   
  econstructor ; eauto.
  assert (assigned_code_spec (fn_code f) pc0 res).
  econstructor ; eauto. 
  ssa_f WFF f.
  
  + (* Iop *)
  assert (HDOM: dom f d pc). 
  eapply (@sdom_dom_pred node peq) ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.

  unfold fn_code in *.
  edestruct (dom_eq_sdom peq _ _ _ d pc HDOM).
  symmetry in H2. inv H2. 
  assert (res = x). clear HDOM.
  inv H0. inv H. simpl_ext_params.
  inv H0; allinv. auto.
  eelim (unique_def_elim1 f pc d x); eauto; wf_ssa f.
  econstructor ; eauto.
  inv H2.
  inv H0.  assert (pc = d) by (def_def WFF f x d pc).
  inv H0. unfold fn_code in *; allinv.
  eapply eval_Iop with (m:= m) ; eauto.
  rewrite P2Map.gss. 
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use_code f x d). econstructor ; eauto.
  eelim fn_use_def_code ; eauto; wf_ssa f.
  econstructor ; eauto.

  exploit SINV ; eauto.
  intros. inv H3. inv H6. 
  eapply eval_Iop with (m:= m0); auto. 
  assert (x <> res) by (intro Hcont; inv Hcont;  def_def WFF f res pc d; (intros Heq; inv Heq ; inv H2 ; auto)).  
  rewrite P2Map.gso ; eauto.
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use f res d). 
  inv H0. 
  assert (d = pc0). destruct (peq d pc0) ; auto. 
  def_def WFF f res0 d pc0; eauto. inv H0; eauto.
  econstructor ; eauto.  
  econstructor ; eauto.
  assert (def f res pc); eauto. 

  exploit fn_strict ; eauto; wf_ssa f. intro Hdom.
  eapply (@sdom_not_dom node peq) in H2; eauto.

  + (* Iload *)
  assert (HDOM: dom f d pc). 
  eapply (@sdom_dom_pred node peq) ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.

  destruct (peq pc d).
  inv e. inv H0.  assert (pc = d) by (def_def WFF f x d pc). inv H0. congruence.
  exploit SINV ; eauto.
  econstructor ; eauto.
  intros. inv H2. inv H5. econstructor ; eauto. 
  eapply eval_Iop with (m:= m0); auto. 
  assert (x <> dst). (intro Hcont; inv Hcont;  def_def WFF f dst pc d). 
  rewrite P2Map.gso ; eauto.
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use f dst d).
  inv H0. 
  assert (d = pc0). destruct (peq d pc0) ; auto. 
  def_def WFF f res d pc0. inv H0.
  econstructor ; eauto.  
  econstructor ; eauto.
  assert (def f dst pc). econstructor ; eauto. 

  exploit fn_strict ; eauto; wf_ssa f. intro Hdom.
  eapply (@sdom_not_dom node peq) in Hdom ; eauto. econstructor ; eauto.                                    

  + (* Istore *)
  eapply SINV ; eauto.
  exploit (@sdom_dom_pred node peq) ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros.
  destruct (peq d pc).
  inv e. inv H0. def_def WFF f x pc0 pc. congruence.
  econstructor ; eauto. 

  + (* Icall *) 
  { econstructor ; eauto.
    econstructor; eauto. 
    intros. eapply SINV ; eauto.
    exploit (@sdom_dom_pred node peq) ; eauto; wf_ssa f.
    econstructor ; eauto. simpl ; auto.
    intros.
    destruct (peq d pc).
    inv e. inv H0. def_def WFF f x pc0 pc. inv H0. congruence.
    econstructor ; eauto. 
  } 
  
  (* tailcall *)
  

  + (* Ibuiltin *)
  assert (HDOM: dom f d pc). 
  eapply (@sdom_dom_pred node peq) ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.
  destruct (peq pc d).
  inv e. inv H0.  assert (pc = d) by (def_def WFF f x d pc). inv H0. congruence.
  exploit SINV ; eauto.
  econstructor ; eauto.
  intros. inv H2. inv H5. econstructor ; eauto. 
  eapply eval_Iop with (m:= m0); auto. 
  assert (x <> res). (intro Hcont; inv Hcont;  def_def WFF f res pc d). 
  rewrite P2Map.gso ; eauto.
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use f res d). 
  inv H0. 
  assert (d = pc0). destruct (peq d pc0) ; auto. 
  def_def WFF f res0 d pc0. inv H0.
  econstructor ; eauto.  
  econstructor ; eauto.
  assert (def f res pc). econstructor ; eauto. 

  exploit fn_strict ; eauto; wf_ssa f. intro Hdom.
  eapply (@sdom_not_dom node peq) in Hdom ; eauto. econstructor ; eauto.

  + (* Icond *)
  eapply SINV ; eauto.
  exploit (@sdom_dom_pred node peq) ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros.
  destruct (peq d pc).
  inv e. inv H0. def_def WFF f x pc0 pc. congruence.
  econstructor ; eauto.
  
  + (* Icond *)
  eapply SINV ; eauto.
  exploit (@sdom_dom_pred node peq) ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros.
  destruct (peq d pc).
  inv e. inv H0.  def_def WFF f x pc0 pc.  congruence.
  econstructor ; eauto.
 
  + (* Ijumptable *)
  eapply SINV ; eauto.
  exploit (@sdom_dom_pred node peq) ; eauto; wf_ssa f.
  econstructor ; eauto. 
  simpl. eapply list_nth_z_in ; eauto.
  intros.
  destruct (peq d pc).
  inv e. inv H0. def_def WFF f x pc0 pc. congruence.
  econstructor ; eauto.

  - (* from Callstate *) 
  inv STEP; eauto.
  econstructor ; eauto.
  apply f0.
  intros ; eelim (@entry_sdom node peq) ; eauto.
  
  - (* from Return *) 
  generalize STEP ; inv STEP ; intros STEP.
  assert (HWF:=wf f).
  inv SFINV. inv H1. econstructor ; eauto.
  intros. exploit SFINV; eauto. intros. 
  inv H3. 
  destruct SINS as [pred [sig [ros [args Hpred]]]].
  
  inv H6. 
  econstructor ; eauto.
  eapply eval_Iop with (m:= m0) ; eauto.
  
  assert (x <> res).
  intro Hcont. inv Hcont. 
  inv H0. 
  def_def HWF f res0 pred pc0. congruence. 
  rewrite P2Map.gso ; eauto.
  
  rewrite map_gso; auto.
  intros. intro Hcont. inv Hcont. 
  inv H0. def_def HWF f res0 pc0 d. intros Heq. inv Heq.

  assert (def f res pred). econstructor  ; eauto. 
  assert (use f res d). econstructor ; eauto. econstructor ; eauto.
  exploit fn_strict ; eauto; wf_ssa f. intros Hdom'.   
  assert (dom f d pred). eapply (@sdom_dom_pred node peq) ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.
  exploit (@dom_antisym node peq) ; eauto. congruence.
Qed.

End INV.