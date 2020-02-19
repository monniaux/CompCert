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
Require Import SSA. 
Require Import SSAutils. 
Require Import Utilsvalidproof.
Require Import Conventions1.
Require Import Kildall.
Require Import KildallComp.
Require Import Relation_Operators.
Require Import Events.

(** * The [rhs] (right hand side) predicate, and equational invariant *)
Inductive rhs (f:function) (x : reg) : instruction -> Prop := 
| rhs_iop : forall op args pc succ
  (RHS: (fn_code f) ! pc  = Some (Iop op args x succ))
  (MIND: op_depends_on_memory op = false),
  rhs f x (Iop op args x succ).
Hint Constructors rhs.

Inductive eval : genv -> val -> regset -> instruction -> val -> Prop := 
| eval_Iop : forall ge sp rs m op args res pc' v
  (EVAL: eval_operation ge sp op rs##2 args m = Some v)
  (MIND: op_depends_on_memory op = false),  
  eval ge sp rs (Iop op args res pc') v.
Hint Constructors eval.

Inductive models : function -> genv -> val -> regset -> reg -> instruction -> Prop := 
| models_state : forall f ge x x' i sp rs v, 
  rs #2 x = v ->
  rhs f x' i ->
  eval ge sp rs i v ->
  models f ge sp rs x i.
Hint Constructors models.

Notation "[ a , b , c , d ] |= x == i" := (models a b c d x i) (at level 1, b at next level).

Inductive sf_inv (ge: genv) : stackframe -> Prop := 
  | sf_inv_intro: forall res f sp pc rs
    (WFF: wf_ssa_function f)
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
  | si_State : forall s f sp pc rs m
    (WFF: wf_ssa_function f)
    (SINV: forall x d i, 
      def f x d -> rhs f x i -> sdom f d pc -> [f, ge, sp , rs] |= x == i)
    (SFINV: sfl_inv ge s),
    s_inv ge (State s f sp pc rs m)
  | si_Callstate : forall s f args m
    (WFF: wf_ssa_fundef f)
    (SFINV: sfl_inv ge s),
    s_inv ge (Callstate s f args m)
  | si_Returnstate: forall s v m
    (SFINV: sfl_inv ge s),
    s_inv ge (Returnstate s v m).
Hint Constructors s_inv.

(** * Useful tactics *)

Ltac ssa_f f := 
  match goal with 
    | [Hwf: wf_ssa_function f |- _] =>
      inv Hwf ;
      solve [eelim (unique_def_elim1 f) ; eauto
        | eelim (unique_def_elim3 f) ; eauto]
  end.

Ltac wf_ssa f := 
  try (solve [ eapply (fn_ssa f) ; eauto 
    | eapply (fn_code_reached f) ; eauto
    | eapply (fn_phicode_code f) ; eauto
    | eapply (fn_entry f) ; eauto]).

Ltac def_def f x pc pc' :=
  match goal with 
    | [HWF: wf_ssa_function f |- _ ] =>
      (exploit (def_def_eq f HWF x pc pc'); eauto); 
      try (econstructor ; eauto);
        try (solve [econstructor ; eauto])
    | [HWF: wf_ssa_function f |- _ ] =>
      (exploit (def_def_eq f x pc pc' HWF); eauto); 
      try (econstructor ; eauto);
        try (solve [econstructor ; eauto])
  end.

Lemma ssa_rhs_exists_def : forall f x i,
  wf_ssa_function f -> rhs f x i -> exists d, def f x d.
Proof.
  intros.
  inv H0.
  exists pc ; auto.
  econstructor ; eauto.
Qed.

Ltac simpl_ext_params := 
  match goal with 
    | [h : ext_params ?f ?x |- _ ] => 
      inv h ; 
      [ (exploit fn_ssa_params ; eauto); 
        (intros [HH HH']; exploit HH ; eauto ; intuition)
        | match goal with 
            |  [ h2 : forall pc : node, ~ assigned_phi_spec (fn_phicode ?f) _ _,
                 h3 : forall pc : node, ~ assigned_code_spec (fn_code ?f) _ _ |- _ ] =>
            solve [ exploit h2 ; eauto ; intuition | exploit h3 ; eauto ; intuition ]
            end]
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

(** * Proof of the equational lemma *)
Section INV.

Variable prog : program.
Hypothesis HWF: wf_ssa_program prog. 
Let ge_prog := Genv.globalenv prog.

Lemma subj_red : forall s s' t,
  s_inv ge_prog s ->
  step ge_prog s t s' ->
  s_inv ge_prog s'.  
Proof.
  intros s s' t HINV STEP.
  inv HINV.

  (* from State *)
  inv STEP; econstructor ; eauto ; intros.

  (* inop sans block *)
  destruct (peq d pc).
  inv e. inv H; try (inv H2; congruence).
  inv H0. simpl_ext_params.
  inv H0.
  assert (assigned_code_spec (fn_code f) pc0 x) by (econstructor ; eauto).
  ssa_f f.
  exploit (sdom_dom_pred f d pc pc') ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros Hdom.
  assert (sdom f d pc) by (econstructor ; eauto).
  exploit SINV ; eauto.
  
  (* inop avec block *)
  destruct (peq d pc).
  inv e. inv H; try (inv H2; congruence).
  inv H0. simpl_ext_params.   
  inv H0.
  assert (assigned_code_spec (fn_code f) pc0 x) by (econstructor ; eauto).
  ssa_f f.
  exploit (sdom_dom_pred f d pc pc') ; eauto; wf_ssa f.
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
  assert (pc0 = d) by (destruct (peq pc0 d); auto; def_def f res pc0 d). inv H6.
  eapply sdom_not_dom in H1 ; eauto.
  
  (* Po2 *)
  inv H0. intros. intro Hcont.
  assert (assigned_phi_spec (fn_phicode f) pc' res).   
  econstructor ; eauto.
  assert (assigned_code_spec (fn_code f) pc0 res).
  econstructor ; eauto. 
  ssa_f f.
  
  (* Iop *)
  assert (HDOM: dom f d pc). 
  eapply sdom_dom_pred ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.

  destruct (dom_eq_sdom f d pc HDOM).
  symmetry in H2. inv H2. 
  assert (res = x). clear HDOM.
  inv H0. inv H. simpl_ext_params.
  inv H0; allinv. auto.
  eelim (unique_def_elim1 f pc d x); eauto; wf_ssa f.
  econstructor ; eauto.
  inv H2.
  inv H0.  assert (pc = d) by (def_def f x d pc).
  inv H0. allinv.
  eapply eval_Iop with (m:= m) ; eauto.
  rewrite P2Map.gss. 
Locate map_gso.
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use_code f x d). econstructor ; eauto.
  eelim fn_use_def_code ; eauto; wf_ssa f.
  econstructor ; eauto.

  exploit SINV ; eauto.
  intros. inv H3. inv H6. 
  eapply eval_Iop with (m:= m0); auto. 
  assert (x <> res) by (intro Hcont; inv Hcont;  def_def f res pc d; (intros Heq; inv Heq ; inv H2 ; auto)).  
  rewrite P2Map.gso ; eauto.
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use f res d). 
  inv H0. 
  assert (d = pc0). destruct (peq d pc0) ; auto. 
  def_def f res0 d pc0; eauto. inv H0; eauto.
  econstructor ; eauto.  
  econstructor ; eauto.
  assert (def f res pc); eauto. 

  exploit fn_strict ; eauto; wf_ssa f. intro Hdom.
  eapply sdom_not_dom in H2; eauto.

  (* Iload *)
  assert (HDOM: dom f d pc). 
  eapply sdom_dom_pred ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.

  destruct (peq pc d).
  inv e. inv H0.  assert (pc = d) by (def_def f x d pc). inv H0. congruence.
  exploit SINV ; eauto.
  econstructor ; eauto.
  intros. inv H2. inv H5. econstructor ; eauto. 
  eapply eval_Iop with (m:= m0); auto. 
  assert (x <> dst). (intro Hcont; inv Hcont;  def_def f dst pc d). 
  rewrite P2Map.gso ; eauto.
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use f dst d).
  inv H0. 
  assert (d = pc0). destruct (peq d pc0) ; auto. 
  def_def f res d pc0. inv H0.
  econstructor ; eauto.  
  econstructor ; eauto.
  assert (def f dst pc). econstructor ; eauto. 

  exploit fn_strict ; eauto; wf_ssa f. intro Hdom.
  eapply sdom_not_dom in Hdom ; eauto. econstructor ; eauto.                                    

  (* Istore *)
  eapply SINV ; eauto.
  exploit (sdom_dom_pred f d pc pc') ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros.
  destruct (peq d pc).
  inv e. inv H0. def_def f x pc0 pc. congruence.
  econstructor ; eauto. 

  (* Icall *)
  { unfold find_function in H8.
    generalize HWF ; intro Hwf.
    destruct ros ; simpl in H8.  
    eapply Genv.find_funct_prop with (p:= prog) ; eauto.
    destruct Genv.find_symbol; 
    [eapply Genv.find_funct_ptr_prop with (p:= prog) ; eauto | congruence]. 
  } 
  { econstructor ; eauto.
    econstructor; eauto. 
    intros. eapply SINV ; eauto.
    exploit (sdom_dom_pred f d pc pc') ; eauto; wf_ssa f.
    econstructor ; eauto. simpl ; auto.
    intros.
    destruct (peq d pc).
    inv e. inv H0. def_def f x pc0 pc. inv H0. congruence.
    econstructor ; eauto. 
  } 
  
  (* tailcall *)
  
    unfold find_function in H8.
  generalize HWF ; intro Hwf.
  destruct ros ; simpl in H8.  
  eapply Genv.find_funct_prop with (p:= prog) ; eauto.
  destruct Genv.find_symbol; 
    [eapply Genv.find_funct_ptr_prop with (p:= prog) ; eauto | congruence]. 

  (* Ibuiltin *)
  assert (HDOM: dom f d pc). 
  eapply sdom_dom_pred ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.
  destruct (peq pc d).
  inv e. inv H0.  assert (pc = d) by (def_def f x d pc). inv H0. congruence.
  exploit SINV ; eauto.
  econstructor ; eauto.
  intros. inv H2. inv H5. econstructor ; eauto. 
  eapply eval_Iop with (m:= m0); auto. 
  assert (x <> res). (intro Hcont; inv Hcont;  def_def f res pc d). 
  rewrite P2Map.gso ; eauto.
  rewrite map_gso ; eauto.
  intros.   intro Hcont. inv Hcont.  
  assert (use f res d). 
  inv H0. 
  assert (d = pc0). destruct (peq d pc0) ; auto. 
  def_def f res0 d pc0. inv H0.
  econstructor ; eauto.  
  econstructor ; eauto.
  assert (def f res pc). econstructor ; eauto. 

  exploit fn_strict ; eauto; wf_ssa f. intro Hdom.
  eapply sdom_not_dom in Hdom ; eauto. econstructor ; eauto.

  (* Icond *)
  eapply SINV ; eauto.
  exploit (sdom_dom_pred f d pc ifso) ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros.
  destruct (peq d pc).
  inv e. inv H0. def_def f x pc0 pc. congruence.
  econstructor ; eauto.

  (* Icond *)
  eapply SINV ; eauto.
  exploit (sdom_dom_pred f d pc ifnot) ; eauto; wf_ssa f.
  econstructor ; eauto. simpl ; auto.
  intros.
  destruct (peq d pc).
  inv e. inv H0.  def_def f x pc0 pc.  congruence.
  econstructor ; eauto.
 
  (* Ijumptable *)
  eapply SINV ; eauto.
  exploit (sdom_dom_pred f d pc pc') ; eauto; wf_ssa f.
  econstructor ; eauto. 
  simpl. eapply list_nth_z_in ; eauto.
  intros.
  destruct (peq d pc).
  inv e. inv H0. def_def f x pc0 pc. congruence.
  econstructor ; eauto.

  (* from Callstate *) 
  inv STEP; eauto.
  econstructor ; eauto.
  inv WFF ; auto.
  intros ; eelim entry_sdom ; eauto.
  
  (* from Return *) 
  generalize STEP ; inv STEP ; intros STEP.
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
  def_def f res0 pred pc0. congruence. 
  rewrite P2Map.gso ; eauto.
  
  rewrite map_gso; auto.
  intros. intro Hcont. inv Hcont. 
  inv H0. def_def f res0 pc0 d. intros Heq. inv Heq.

  assert (def f res pred). econstructor  ; eauto. 
  assert (use f res d). econstructor ; eauto. econstructor ; eauto.
  exploit fn_strict ; eauto; wf_ssa f. intros Hdom'.   
  assert (dom f d pred). eapply sdom_dom_pred ; eauto; wf_ssa f. econstructor ; eauto ; simpl ; auto.
  exploit dom_antisym ; eauto. congruence.
Qed.

Lemma s_inv_initial : forall s, 
  initial_state prog s ->
  s_inv ge_prog s.
Proof.
  intros. inv H. econstructor ; eauto. 
  generalize HWF ; intro Hwf.
  eapply Genv.find_funct_ptr_prop ; eauto.
  econstructor; eauto. 
Qed.

Lemma ssa_inv1_aux : forall s s' t, 
  s_inv ge_prog s ->
  star step ge_prog s t s' ->
  s_inv ge_prog s'.
Proof.
  induction 2 ; intros. 
  auto.
  eapply IHstar ; eauto.
  eapply subj_red ; eauto.
Qed.

Theorem ssa_inv1 : forall  s s' t, 
  initial_state prog s -> 
  star step ge_prog s t s' -> 
  s_inv ge_prog s'.
Proof.
  intros.
  eapply ssa_inv1_aux ; eauto.  
  eapply s_inv_initial ; eauto.
Qed.


(** * Main results *)
Definition reachable (prog:program) (s:state) :=
  exists s0, exists t,
      initial_state prog s0 
      /\  star step (Genv.globalenv prog) s0 t s.

Lemma equation_lemma : 
  forall d op args x succ f m rs sp pc s, 
      (fn_code f) ! d  = Some (Iop op args x succ) ->
      op_depends_on_memory op = false ->
      sdom f d pc -> 
      reachable prog (State s f sp pc rs m) -> 
      eval_operation ge_prog sp op (rs##2 args) m = Some (rs #2 x).
Proof.
  intros.
  unfold reachable in H2.
  destruct H2 as [s0 [t [Hinit Hstar]]].
  exploit ssa_inv1; eauto. intro Hinv.
  inv Hinv ; auto.
  exploit (SINV x d (Iop op args x succ)) ; eauto. intros Hmodels.
  inv Hmodels ; eauto.
  inv H4 ; auto.
  rewrite <- EVAL. 
  eapply op_depends_on_memory_correct ; eauto.
Qed.

Lemma equation_corolary : 
  forall d op args x succ f m rs sp pc s, 
    wf_ssa_program prog ->
      (fn_code f) ! d  = Some (Iop op args x succ) ->
      op_depends_on_memory op = false ->
      use f x pc ->
      reachable prog (State s f sp pc rs m) -> 
      eval_operation (Genv.globalenv prog) sp op (rs##2 args) m = Some (rs #2 x).
Proof.
  intros.
  unfold reachable in H3.
  destruct H3 as [s0 [t [Hinit Hstar]]].
  exploit ssa_inv1; eauto. intro Hinv.
  inv Hinv ; auto.
  exploit (SINV x d (Iop op args x succ)) ; eauto. 
  exploit fn_strict ; eauto. intros Hdom.
  eapply dom_eq_sdom in Hdom. destruct Hdom as [Hdom1 | Hdom2] ; auto.
  inv Hdom1.
  inv H2.
  eelim fn_use_def_code ; eauto.
  inv H3. 
  generalize PHIB ; intros PHIB'.
  eapply fn_phicode_code in PHIB'; eauto.
  destruct PHIB' as [ins Hins].
  eapply fn_phicode_inv1 in PHIB ; eauto.
  exploit (fn_normalized f WFF pc0 pc); eauto.
  eapply index_pred_some_nth in KPRED.
  eapply nth_error_some_in in KPRED.
  eapply make_predecessors_correct2 in KPRED ; eauto.
  unfold successors_list, successors. 
  rewrite PTree.gmap1. unfold option_map. rewrite H0.
  auto.
  congruence.
  
  intros Hmodels.
  inv Hmodels ; eauto.
  inv H5 ; auto.
  rewrite <- EVAL. 
  eapply op_depends_on_memory_correct ; eauto.
Qed.

End INV.  
