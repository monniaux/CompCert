(** Formalization of paths in a RTL cfg. *)

Require Import Coqlib.
Require Import Relation_Operators.
Require Import Classical.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Registers.
Require Import Utils.
Require Import SSA.
Require Import Dom.
Require Import RTL. 

Section PATHS.  
  
  Variable f : function.
  Notation entry := (fn_entrypoint f).
  Notation code := (fn_code f).
  Notation pstate := (@pstate node).
  
  Inductive rtl_cfg (i j:node) : Prop :=
  | rtl_CFG : forall ins
    (HCFG_ins: (fn_code f) !i = Some ins)
    (HCFG_in : In j (successors_instr ins)),
    rtl_cfg i j.
  
  Definition rtl_reached (pc: node) : Prop := 
    (rtl_cfg **) (fn_entrypoint f) pc.
   
  Inductive rtl_path_step : pstate -> node -> pstate -> Prop :=
  | rtl_step_i: forall i pc pc'
    (INS: code !pc = Some i)
    (CFG : rtl_reached pc)
    (STEP: In pc' (successors_instr i)), 
    rtl_path_step (PState pc) pc (PState pc')
  | step_stop: forall pc i
    (INS: code !pc = Some i)
    (CFG : rtl_reached pc)
    (NOSTEP : successors_instr i = nil),
    rtl_path_step (PState pc) pc PStop.
    
  Inductive rtl_path : pstate -> list node -> pstate -> Prop :=
  | rtl_path_refl : forall s,  rtl_path s nil s  
  | rtl_path_cons : forall s1 t s2 pc s3 
    (STEP: rtl_path_step s1 pc s2)
    (PATH: rtl_path s2 t s3),
    rtl_path s1 (pc::t) s3.  
  Hint Constructors rtl_path rtl_path_step.

  Inductive rtl_path_right : pstate -> list node -> pstate -> Prop :=
  | rtl_path_rrefl : forall s,  rtl_path_right s nil s  
  | rtl_path_rcons : forall s1 t s2 pc s3 
    (STEP: rtl_path_right s1 t s2)
    (PATH: rtl_path_step s2 pc s3),
    rtl_path_right s1 (t++(pc::nil)) s3.  
  Hint Constructors rtl_path_right.  
  
  Lemma rtl_path_app : forall p1 s1 s2 s3 p2, 
    rtl_path s1 p1 s2 ->
    rtl_path s2 p2 s3 ->
    rtl_path s1 (p1++p2) s3.
  Proof.
    induction p1; intros. 
    inv H. simpl ; auto.
    simpl.
    inv H.
    econstructor ; eauto.
  Qed.   

  Lemma rtl_path_from_ret_nil : forall p s,
    rtl_path PStop p s ->  p = nil.
  Proof.
    induction p ; intros. auto.
    inv H ; auto.
    inv STEP.
  Qed.
  
  Lemma rtl_path_from_ret_ret : forall p s,
    rtl_path PStop p s ->  s = PStop.
  Proof.
    intros.
    exploit rtl_path_from_ret_nil ; eauto.
    intros. inv H0.
    inv H. auto.
  Qed.

  Lemma rtl_in_path_split : forall (pc pc' pc'' : node) (p : list node),
    rtl_path (PState pc) p (PState pc') ->
    In pc'' p ->
    exists p' : list node,
      exists p'' : list node,
        rtl_path (PState pc) p' (PState pc'') /\
        ~ In pc'' p' /\ 
        rtl_path (PState pc'') (pc'' :: p'') (PState pc').
  Proof.
    induction 1 ; intros.
    inv H.

    inv STEP.  
    destruct (peq pc'' pc0). 
    inv e. clear H0.   
    exists nil ; exists t ; split ; (econstructor ; eauto).

    inv H0. congruence. 
    exploit IHrtl_path ; eauto.  intros [p' [p'' [Hp' [Hnotin Hp'']]]].
    
    exists (pc0::p').    
    exists p''.
    split.
    econstructor 2 ; eauto. 
    econstructor ; eauto.
    intro Hcont ; inv Hcont ; intuition. 

    exploit rtl_path_from_ret_nil ; eauto. intros Heq. inv Heq. inv H0. 
    inv H. exists nil; exists nil. 
    split; (econstructor ; eauto).
    intuition.
  Qed.

  Lemma rtl_in_path_split_app : forall pc pc' pc'' p, 
    rtl_path (PState pc) p (PState pc') ->
    In pc'' p ->
    exists p', exists p'', 
      rtl_path (PState pc) p' (PState pc'')
      /\ ~ In pc'' p'
      /\ p = p'++(pc''::p'').
  Proof.
    induction 1 ; intros.
    inv H.

    inv STEP.  
    destruct (peq pc'' pc0). 
    inv e. clear H0.   
    exists nil. exists t ; split ; econstructor ; eauto.
    
    inv H0. congruence. 
    exploit IHrtl_path ; eauto.  intros [p' [p'' [Hp' [Hnotin Happ]]]].
    rewrite Happ.
    
    exists (pc0::p').    
    exists p''.
    split.
    econstructor 2 ; eauto. 
    econstructor ; eauto.
    intro Hcont. inv Hcont. elim n ; auto. elim Hnotin ; auto. 

    exploit rtl_path_from_ret_nil ; eauto. intros. inv H1. inv H.
    inv H0. exists nil. exists nil. split.
    econstructor ; eauto.
    split ; auto.
    elim H.
  Qed.      

  Lemma rtl_path_first : forall p pc pc', 
    rtl_path (PState pc) p (PState pc') ->
    pc <> pc' ->
    exists pc'', exists p', 
      rtl_path (PState pc) p' (PState pc'') /\
      ~ In pc' p' /\
      pc'' <> pc' /\
      rtl_path_step (PState pc'') pc'' (PState pc').
  Proof.
    induction p ; intros; inv H. 
    congruence.
    assert (a = pc) by (inv STEP; auto). inv H.
    destruct s2.
    destruct (peq pc0 pc').
    (* peq *)
    inv e.  exists pc. exists nil.
    split; auto. 
    (* diff *)
    exploit IHp ; eauto. intros [pc'' [p' [Hp' [Hpc'' [Hdiff Hnotin]]]]].
    exists pc''. exists (pc::p').
    split ; auto.
    econstructor ; eauto. 
    split ; auto.
    intro Hcont. inv Hcont. congruence. elim Hpc'' ; auto.
    exploit rtl_path_from_ret_nil ; eauto. intros Heq ; inv Heq.
    inv PATH.
  Qed.

  Lemma rtl_cfg_path : forall pc pc', 
    rtl_cfg** pc pc' -> rtl_reached pc -> exists p, rtl_path (PState pc) p (PState pc'). 
  Proof.
    intros pc pc' HCFG.
    eapply (clos_refl_trans_ind node) with 
      (P :=  fun a b => rtl_reached a -> exists p, rtl_path (PState a) p (PState b)) ; eauto; intros.

    inv H. exists (x::nil). 
    econstructor ; eauto. 

    exploit H0 ; eauto ; intros [pxy Hpxy].
    assert (rtl_reached y). eapply rt_trans ; eauto.
    exploit H2 ; eauto ; intros [pyz Hpyz].
    exists (pxy++pyz). eapply rtl_path_app; eauto.
  Qed.
  
  Lemma rtl_reached_path : forall pc', 
    rtl_reached pc' -> exists p, rtl_path (PState entry) p (PState pc').
  Proof.
    intros.
    apply rtl_cfg_path; auto.
    eapply rt_refl ; eauto.  
  Qed.  

End PATHS.