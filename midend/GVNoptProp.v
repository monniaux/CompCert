Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import Dom.
Require Import SSA. 
Require Import SSAtool. 
Require Import SSAutils. 
Require Import SSAtoolinv. 
Require Import Utilsvalidproof.
Require Import DomCompute.
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.
Require Import Opt.
Require Import OptInv.
Require Import DLib.
Require Import GVNopt.
Require Import Dsd.

(** Instantiating the generic analysis in [Opt] to the GVN-CSE case *)

(** * The dominance based analysis *)
Section DsdAnalysis. 

  Definition approx := reg.
  Definition result := reg -> approx.

  Inductive G : genv -> val -> regset -> approx -> val -> Prop :=
  | G_intro : forall ge sp rs r v, 
              forall (EQ: v = rs#2 r),
                G ge sp rs r v.

  Inductive is_at_Top : result -> reg -> Prop :=
  | is_at_Top_intro : forall R r,
                        R r = r ->
                        (forall r', R r' = r -> r' = r) ->
                        is_at_Top R r.
 
  Definition A f := ((fun x => fst (get_extern_gvn f x)),
                     P2Map.init true).

  Let A_r f := fst (A f).
 
  Lemma list_top_at_Top : 
    forall (f:function) r, 
      In r (dst_at_top (fn_ext_params f f) (fn_code f)) -> is_at_Top (A_r f) r.
  Proof.
    unfold A_r, A; simpl; intros.
    unfold get_extern_gvn, get_repr, check_GVN.
    match goal with |- context[if ?b then _ else _] => destruct b eqn:E end.
    - edestruct andb_prop as (E1 & E2); eauto; clear E.
      edestruct andb_prop as (E3 & E4); eauto; clear E1.
      rewrite forallb_forall in E3.
      set (ep:=(dst_at_top (fn_ext_params f f) (fn_code f))) in *.
      assert (HH: (fst (make_repr f (extern_gvn f) ep r)) = r).
      + apply p2eqb_true.
        apply E3; auto.
      + constructor; auto.
        intros r' H'.
        symmetry.
        eapply make_repr_not_id; [idtac|eapply H'].
        auto.
    - simpl; go.
  Qed.

 Lemma params_Top : 
   forall (f:function) r, ext_params f r -> is_at_Top (A_r f) r.
 Proof.
   intros; apply list_top_at_Top; auto.
   apply dst_at_top_prop0.
   apply fn_ext_params_correct; auto.
 Qed.
 
 Lemma G_top : forall f r ge sp rs, is_at_Top (A_r f) r -> G ge sp rs (A_r f r) (rs#2 r).
 Proof.
   intros. invh is_at_Top.
   clear H1 H2. 
   econstructor; eauto.
   rewrite H0 at 1; auto.
 Qed.

 Lemma is_at_Top_eq_is_at_Top : forall f dst x,
   is_at_Top (A_r f) dst -> A_r f x = A_r f dst -> is_at_Top (A_r f) x.
  Proof.
    induction 1; intros.
    rewrite H in H1.
    assert (x = r) by (eapply H0; eauto).  
    rewrite <- H2 in H1.
    constructor; auto. 
    intros. rewrite H2. eapply H0; eauto.
    congruence.
  Qed.

  Definition exec : function -> node -> Prop := (fun _ _ => True).
  Lemma exec_fn_entrypoint : forall f, exec f (fn_entrypoint f).
  Proof.
    go.
  Qed.    

  Definition GVN := 
    (Build_DsdAnalysis approx G is_at_Top A exec exec_fn_entrypoint 
                       is_at_Top_eq_is_at_Top params_Top G_top).


  (** ** Auxiliary properties about the GVN checker *)
  Inductive same_repr (repr : reg -> reg) : list reg -> list reg -> Prop :=
  | same_repr_nil: same_repr repr nil nil
  | same_repr_cons: forall x1 l1 x2 l2,
    same_repr repr l1 l2 -> 
    repr x1 = repr x2 -> 
    same_repr repr (x1::l1) (x2::l2).

  Lemma same_repr_sym : forall repr l1 l2,
    same_repr repr l1 l2 -> same_repr repr l2 l1.
  Proof.
    induction 1; constructor; auto.
  Qed.
  
  Lemma same_repr_trans : forall repr l1 l2,
    same_repr repr l1 l2 -> 
    forall l3, same_repr repr l2 l3 -> same_repr repr l1 l3.
  Proof.
    induction 1; intros l3 T3; inv T3; constructor; eauto.
    congruence.
  Qed.

  Lemma same_repr_trans_phi1 : forall repr a args_x args_y,
    same_repr repr args_x args_y ->    
    (forall z : reg, In z args_y -> a = repr z) ->
    (forall z : reg, In z args_x -> a = repr z).
  Proof.
    induction 1; simpl; intros.
    intuition.
    destruct H2; subst; eauto.
    rewrite H0; auto.
  Qed.

  Lemma same_repr_nth_error : forall repr args args',
    same_repr repr args args' -> 
    forall  k x x',
      nth_error args k = Some x ->
      nth_error args' k = Some x' ->
      repr x = repr x'.
  Proof.
    induction 1; destruct k; simpl; intros; try congruence.
    inv H1; inv H2; auto.
    eauto.
  Qed.

  Lemma same_repr_map : forall R rl rl', same_repr R rl rl' -> map R rl = map R rl'.
  Proof.
    induction 1 ; go. 
  Qed.

 Definition repr_spec_code (f: function) (pc: node) (R: reg -> reg) : Prop :=
   match (fn_code f) ! pc with 
     | Some i => 
       match i with 
         | Iop op args r _ =>
           R r = r 
           \/ 
           (exists pc_r pc_r' args_r, 
              (fn_code f) ! pc_r = Some (Iop op args_r (R r) pc_r')
              /\ same_repr R args args_r
              /\ (r <> R r)
              /\ sdom f pc_r pc
              /\ op_depends_on_memory op = false)
         | Iload _ _ _ r _ 
         | Icall _ _ _ r _
         | Ibuiltin _ _ r _ => is_at_Top R r
         | _ => True 
       end
     | None => True
   end.

 Definition repr_spec_phicode (f: function) (pc: node) (R: reg -> reg) : Prop :=
   match (fn_phicode f) ! pc with 
     | None => True 
     | Some phib =>
       forall r args, In (Iphi args r) phib ->
            R r = r 
             \/ exists args_r, 
               In (Iphi args_r (R r)) phib /\ same_repr R args args_r
   end.

 Record GVN_spec (f: function) : Prop := {
   GVN_spec_code : forall pc, repr_spec_code f pc (A_r f);
   GVN_spec_phicode : forall pc, repr_spec_phicode f pc (A_r f);
   GVN_spec_idempotence : forall r, A_r  f (A_r f r) = A_r f r
 }.
 
 Lemma repr_spec_code_id : forall f pc, repr_spec_code f pc (fun x : reg => x).
 Proof.
   unfold repr_spec_code; intros; flatten; go.
 Qed.
 Hint Resolve repr_spec_code_id.

 Lemma same_repr_refl: forall R args,
   same_repr R args args.
 Proof.
   induction args; go.
 Qed.

 Lemma repr_spec_phicode_id : forall f pc, repr_spec_phicode f pc (fun x : reg => x).
 Proof.
   unfold repr_spec_phicode; intros; flatten; go.
 Qed.
 Hint Resolve repr_spec_phicode_id.

(* Move this *)
Lemma p2eqb_true_iff : forall x y, 
  p2eqb x y = true <-> x = y.
Proof.
  unfold p2eqb; intros; destruct p2eq; intuition congruence.
Qed.

(* Move this *)
Ltac boolInv :=
  match goal with
  | [ H: context[op_eq _ _ = true] |- _ ] => 
      rewrite op_eq_true_iff in H; boolInv
  | [ H: context[p2eqb _ _ = true] |- _ ] => 
      rewrite p2eqb_true_iff in H; boolInv
  | [ H: context[_ || _ = true] |- _ ] => 
      rewrite orb_true_iff in H; boolInv
  | [ H: context[_ && _ = true] |- _ ] => 
      rewrite andb_true_iff in H; boolInv
  | _ =>
      idtac
  end.

Lemma forall_list2_same_repr :
  forall R l args,
    forall_list2 (fun x y : reg => p2eqb (R x) (R y)) l args = true ->
    same_repr R l args.
Proof.
  induction l; destruct args; simpl; go.
  intros; boolInv.
  destruct H; go.
Qed.

Lemma repr_idempotent : 
  forall f,
    let R:=make_repr f (extern_gvn f) (dst_at_top (fn_ext_params f f) (fn_code f)) in
    forall r, fst (R (fst (R r))) = fst (R r).
Proof.
  intros f R r.
  unfold R.
  rewrite make_repr_itempotent; auto.
Qed.

(* Move this *)
  Lemma G_unique : forall ge sp rs r v v',
                     G ge sp rs r v ->
                     G ge sp rs r v' ->
                     v = v'.
  Proof.
    intros until v'.
    intros HGv HGv'.
    repeat invh G. auto.
  Qed.
      
  Lemma G_list_eval_op_helper : 
    forall rs ge sp al vl vl',
      G_list GVN ge sp rs al vl ->
      G_list GVN ge sp rs al vl' ->
      vl = vl'.
  Proof.
    induction al ; intros. 
    - repeat invh G_list; auto.
    - inv H. inv H0. 
      assert (v0 = v) by (erewrite G_unique ; eauto); subst.
      exploit (IHal vl0 vl); eauto. intros Heq; subst.
      auto. 
  Qed.
     
  Lemma G_list_eval_op : 
    forall rs ge sp op m al vl vl',
      G_list GVN ge sp rs al vl ->
      G_list GVN ge sp rs al vl' ->
      eval_operation ge sp op vl m = eval_operation ge sp op vl' m.
  Proof.
    intros. 
    erewrite G_list_eval_op_helper with (vl:= vl) (vl':= vl'); eauto. 
  Qed.  

(* End of Move this *)
 
(** * The checker satisfies its specification *)
Lemma GVN_spec_True : forall f, GVN_spec f.
Proof.
  intros f; assert (WF:=wf f); constructor.
  - generalize (list_top_at_Top f).
    unfold A_r.
    unfold A_r, A, get_extern_gvn, get_repr, check_GVN; simpl.     
    flatten; simpl; auto.
    flatten Eq.
    edestruct andb_prop as (T1 & T2); eauto; clear Eq0.
    edestruct andb_prop as (T3 & T4); eauto; clear T1.
    unfold repr_spec_code; flatten; auto.
    exploit ptree_forall; eauto; clear T4.
    simpl.
    set (R:=make_repr f (extern_gvn f) (dst_at_top (fn_ext_params f f) (fn_code f))).
    flatten.
    + flatten Eq3.
      boolInv.
      destruct (p2eq (fst (R r)) r); auto.
      destruct H3; [elim n1; auto|right].
      repeat invh and; subst.
      do 3 econstructor; split; [eauto|idtac].
      repeat split; auto.
      * eapply forall_list2_same_repr; eauto.
      * eapply fn_dom_test_correct; eauto.
      * unfold fn_code in *; congruence.
      * destruct (op_depends_on_memory op); simpl in *; congruence.
    + flatten Eq3.
    + intros H; boolInv; destruct H; auto; go.
    + intros H; boolInv; destruct H; auto; go.
    + intros H; boolInv; destruct H; auto; go.
    + apply H0; auto.
      generalize (dst_at_top_prop1 (fn_code f) (fn_ext_params f f) pc).
      flatten.
    + apply H0; auto.
      generalize (dst_at_top_prop1 (fn_code f) (fn_ext_params f f) pc).
      flatten.
    + apply H0; auto.
      generalize (dst_at_top_prop1 (fn_code f) (fn_ext_params f f) pc).
      flatten.
  - unfold A_r, A, get_extern_gvn, get_repr, check_GVN; simpl.     
    flatten; simpl; auto.
    flatten Eq.
    edestruct andb_prop as (T1 & T2); eauto; clear Eq0.
    edestruct andb_prop as (T3 & T4); eauto; clear T1.
    unfold repr_spec_phicode; flatten; auto.
    clear T3 T4.
    exploit ptree_forall; eauto; clear T2.
    set (R:=make_repr f (extern_gvn f) (dst_at_top (ext_params_list f) (fn_code f))).
    unfold check_GVN_phiblock.      
    rewrite forallb_forall.
    intros.
    exploit H; eauto; clear H; simpl; intros.
    boolInv.
    destruct H; auto.
    right.
    flatten H.
    * boolInv.
      repeat invh and.
      destruct peq; inv H1.
      assert (p0=p) by congruence; subst.
      { econstructor; split.
        - eapply nth_error_in; eauto.
        - eapply forall_list2_same_repr; eauto. }
    * destruct peq; inv H.
    * destruct peq; inv H.
  - intros r.
    unfold A_r, A, get_extern_gvn, get_repr, check_GVN; simpl.
    flatten; auto.
    flatten Eq; auto.
    rewrite repr_idempotent; auto.
Qed.

End DsdAnalysis.

(** * Proof that GVN preserves the wf_ssa_function predicate *)
(** This is only provable here, where we have the specification
[GVN_spec] of the checker *)

Section WFSSA. 

Lemma check_def_correct: forall f pc x,
  check_def (fn_code f) pc x = true -> def f x pc.
Proof.
  intros; constructor 2.
  unfold check_def in H.
  case_eq ((fn_code f)!pc); intros; rewrite H0 in *; try congruence.
  destruct i; try congruence; destruct p2eq; go.
Qed.

Lemma new_code_same_or_Iop : forall (f:function) (WF:wf_ssa_function f) pc ins,
    (fn_code f) ! pc = Some ins ->
    transf_instr (fst (analysis f)) pc ins = ins
    \/ match ins with
         | Iop _ _ dst pc' 
         | Iload _ _ _ dst pc'
         | Icall _ _ _ dst pc'  
         | Ibuiltin _ _ dst pc' => 
           exists op' args',
             transf_instr (fst (analysis f)) pc ins = Iop op' args' dst pc'
             /\ forall x, In x args' -> exists d : node, def f x d /\ sdom f d pc
         | _ => False
       end.
Proof. 
  destruct ins; simpl; flatten; eauto. 
  right.
  edestruct andb_prop; eauto; clear Eq1.
  edestruct andb_prop; eauto; clear H0.
  econstructor; econstructor; split; eauto.
  simpl. 
  destruct 1 as [HH|HH]; [subst|elim HH].
  exists n0; split.
  - eapply check_def_correct; eauto.
  - split.
    + destruct (GVN_spec_True f) as [Hc _ _ ].
      specialize Hc with pc.
      unfold repr_spec_code in Hc; flatten Hc.
      destruct Hc.
      * unfold A in *.
        simpl in H.
        assert (x=r) by (rewrite Eq0 in H; simpl in H; congruence).
        subst x.
        destruct (p2eq r r); go.
      * destruct H as (pc0 & pc' & args' & T1 & T2 & T3 & T4 & T5).
        assert (fst (A f) r = x).
          unfold A; simpl; rewrite Eq0; auto.
        rewrite H in *.  
        apply check_def_correct in H3.
        assert (def f x pc0) by go.        
        assert (n0=pc0) by (eapply ssa_def_unique; eauto).
        subst.
        destruct T4; auto.
    + intro; subst.
      destruct peq in H1; simpl in *; congruence.
Qed.

End WFSSA.

(** * Local correctness obligation proofs about the analysis *)
Notation A_r f := (fst (A f)).
Notation A_e f := (snd (A f)).

Lemma same_fn_code3 : forall (f:function) res,
                        (ext_params f res) ->
                        forall x dx, def f x dx -> A_r f x = res -> x = res.
Proof.
  intros.
  assert (WF:=wf f).
  destruct (GVN_spec_True f) as [Hcode Hphicode _].
  specialize Hcode with dx.
  specialize Hphicode with dx.
  subst.
  invh def.
  - exploit params_Top; eauto. intros. 
    invh is_at_Top. congruence. 
  - unfold repr_spec_code in *.
    unfold fn_code in *.
    invh assigned_code_spec;
      try match goal with 
        | id : (SSA.fn_code f) ! _ = Some _ |- _ => 
          rewrite id in *; go
      end; try solve [invh is_at_Top; congruence]; rewrite H0 in Hcode;
    repeat invh or ; repeat invh ex ; repeat invh and.
    + congruence.
    + inv H. 
      eelim fn_ssa_params; eauto. 
      * intros. eelim H; go. 
      * eelim H8; go.
    + destruct Hcode; auto.
    + destruct Hcode; auto.
    + destruct Hcode; auto.
  - unfold repr_spec_phicode in *. 
    invh assigned_phi_spec;
      try match goal with 
        | id : (fn_phicode f) ! _ = Some _ |- _ => 
          rewrite id in *; go
      end.
    rewrite H0 in Hphicode.
    specialize (Hphicode x).
    repeat invh or ; repeat invh ex ; repeat invh and.
    + inv H. 
      * eelim fn_ssa_params; eauto.
        intros. 
        eelim (Hphicode x0); eauto.  
        intros [args' [Hin Hsame]]. 
        eelim H3; eauto. 
      * eelim (Hphicode x0); eauto.  
        intros [args' [Hin Hsame]]. 
        eelim H3; eauto. 
Qed.

Lemma G_phi_notassigned : forall ge sp rs phib k r v,
                            G ge sp rs r v ->
                            (forall args, ~ In (Iphi args r) phib) ->
                            G ge sp (phi_store k phib rs) r v.
Proof.
  intros until v. intros G NOPHI.
  econstructor; eauto. 
  erewrite phi_store_notin_preserved; eauto.
  inv G. auto. 
Qed. 

Lemma exec_true : forall f pc pc', 
   (A_e f) !!2 (pc, pc') = true.
Proof.
  intros.
  unfold A; simpl.
  eapply P2Map.gi; eauto.
Qed.

Lemma exec_step : forall (f:function) ge t sf sp pc rs m f s',
                   exec f pc ->
                   step ge (State sf f sp pc rs m) t s' ->
                   match s' with 
                     | (State _ _ _ pc' _ _) => exec  f pc'
                     | _ => True
                   end.
Proof.
  intros. invh step; try solve [invh exec]; auto;
          try solve [econstructor 2; eauto;
                     econstructor; split; eauto using exec_true].
Qed.    
  
Hint Resolve exec_true.

Lemma gamma_step_phi: forall (f:function) ge sp pc pc' phib k rs,
  reached f pc ->
  exec f pc ->
  
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_phicode f) ! pc' = Some phib ->
  index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
  
  gamma GVN f ge sp pc rs ->
  gamma GVN f ge sp pc' (phi_store k phib rs).
Proof.
  intros f ge sp pc pc' phib k rs Hreached Hexe Hcode Hphi Hpred HGamma. 
  assert (WFF:=wf f).
  intros x Hx He; simpl.    
  destruct (classic (assigned_phi_spec (fn_phicode f) pc' x)) as [HCase | HCase].
  - invh assigned_phi_spec. invh ex. allinv.
    exploit fn_phiargs; eauto. intros [arg Harg]. 
    destruct (GVN_spec_True f) as [_ GSPEC].
    specialize GSPEC with pc'.
    unfold repr_spec_phicode in * ; rewrite Hphi in GSPEC.
    edestruct (GSPEC x) as [CC | CC]; go. 
    + rewrite CC at 1. 
      constructor.
      erewrite phi_store_copy2 ; eauto.
    + repeat invh ex ; repeat invh and.
      clear GSPEC.
      assert (ARG' : exists arg', nth_error x1 k = Some arg'). 
      { eapply nth_error_some_same_length ; eauto. 
        generalize H2. clear. 
        induction 1 ; go. } 
      invh ex.
      edestruct wf_ssa_use_phi_dsd; go.
      * assert (HG2 := HGamma x2 H3 Hexe). 
        { edestruct wf_ssa_use_phi_dsd with (arg:= arg); go.
          - eapply upc_intro with (3:= Harg); eauto.
          - assert (HG2' := HGamma arg H4 Hexe). 
            inv HG2. inv HG2'.
            replace (OptInv.A_r GVN f arg) with (OptInv.A_r GVN f x2) 
              in * by (symmetry ; eapply same_repr_nth_error; eauto).  
            econstructor; eauto.
            erewrite phi_store_copy2 ; eauto.
            erewrite phi_store_copy2 with (dst:= A_r f x) (arg:= x2) ; eauto.
            congruence.
          - inv HG2. 
            econstructor; eauto.
            erewrite phi_store_copy2 ; eauto.
            erewrite phi_store_copy2 with (dst:= A_r f x) (arg:= x2) ; eauto.
            replace (OptInv.A_r GVN f x2) with (A_r f arg) 
              in * by (eapply same_repr_nth_error; eauto).
            exploit params_Top; eauto. intros; invh is_at_Top; congruence.
        } 
      * exploit params_Top; eauto; intros.
        econstructor.
        erewrite phi_store_copy2 ; eauto.
        erewrite phi_store_copy2 with (dst:= A_r f x) (arg:= x2) ; eauto.
        inv H4. clear H7 H8. 
        exploit (ssa_use_exists_def f WFF arg pc); go.
        econstructor 2; eauto.
        eapply upc_intro with (2:= H1); eauto. intros [d Hd].
        exploit same_fn_code3; eauto.
        rewrite <- H5. eapply same_repr_nth_error; eauto. 
        congruence.
      
  - destruct (peq pc (fn_entrypoint f)); subst.
    * exploit dsd_entry_ext_param; eauto. intros Hext_param.
      exploit params_Top; eauto. intro TOP.
      eapply G_top; eauto.
    * exploit (dsd_pred_njp f WFF pc pc' x) ; eauto.
      go.
      intros [Hcase1 | [Hcase2 | Hcase3]]; repeat invh and; try congruence.
    + edestruct (GVN_spec_True f) as [C PC].
      assert (ext_params f x 
              \/ (exists pc', assigned_code_spec (fn_code f) pc' x)
              \/ exists pc', assigned_phi_spec (fn_phicode f) pc' x).
        { inv Hx; go.
          inv H1; go.
        }            
      { destruct H1 as [ Hparams | [[ dx Hdx] | [dx Hdx]]].
        - exploit params_Top; eauto. intros. eapply G_top; eauto. 
        - unfold repr_spec_code in *.
          specialize PC with pc'.
          unfold repr_spec_phicode in *.
          rewrite Hphi in *. clear H0.
          specialize (C dx). 
          inv Hdx; flatten C; try solve [eapply G_top; eauto].
          destruct C.
          + constructor. 
            rewrite phi_store_notin_preserved; eauto.
            rewrite phi_store_notin_preserved; eauto.
            rewrite <- H0 at 1. 
            reflexivity.
            intros args' Hcont. eelim HCase; go.
            rewrite <- H0. econstructor; eauto.
          + repeat invh ex; repeat invh and.
            constructor. 
            rewrite phi_store_notin_preserved; eauto.
            rewrite phi_store_notin_preserved; eauto.
            exploit HGamma ; eauto.
            intros. inv H4; go.
            intros args' Hcont.
            eelim assigned_code_and_phi; eauto.
        - assert (PCx:= PC dx). 
          inv Hdx. unfold repr_spec_phicode in *. flatten PC. 
          constructor. 
          rewrite phi_store_notin_preserved; eauto.
          rewrite phi_store_notin_preserved; eauto.
          exploit HGamma ; eauto.
          intros. inv H1; go.
          intros args' Hcont.
          invh ex.
          eelim (PCx x x0); eauto.
          * intros. 
            eelim HCase; go.
            rewrite <- H2. econstructor; eauto. 
          * intros [args_r [Hin HsR]]. 
            assert (dx = pc').
            eapply ssa_def_unique; eauto. subst.
            eelim HCase; go.
      }          
    + inv Hx; try congruence. clear H4.
      assert (def_x = pc) by (eapply ssa_def_unique; eauto); subst. 
      inv H; try congruence. 
      unfold fn_code in *.
      invh assigned_code_spec; try congruence. 
Qed.      

Lemma same_fn_code1 : forall f pc res,
    (forall op args res pc', (fn_code f) ! pc <> Some (Iop op args res pc')) ->
    assigned_code_spec (fn_code f) pc res -> is_at_Top (A_r f) res.
Proof.
  intros.
  destruct (GVN_spec_True f) as [Hcode _ _].
  specialize Hcode with pc.
  unfold repr_spec_code in *. 
  invh assigned_code_spec ; 
    match goal with 
      | id : (fn_code f) ! _ = Some _ |- _ => 
        rewrite id in *; go
    end.
Qed.

Lemma def_not_top_dsd : forall f x dx, 
                          assigned_code_spec (fn_code f) dx x ->
                          x <> A_r f x ->
                          dsd f (A_r f x) dx.
Proof.
  intros f x dx Dx xRx.
  destruct (GVN_spec_True f) as [Hcode Hpcode _].
  specialize Hcode with dx.
  unfold repr_spec_code in *. 
  invh assigned_code_spec; 
    match goal with 
      | id: (fn_code f) ! _ = Some _ |- _ =>
        rewrite id in *
    end;
    try solve [invh is_at_Top; congruence].
  invh or ; try solve [congruence].
  repeat invh ex ; repeat invh and.
  eapply def_sdom_dsd; eauto.
Qed.

Lemma Iop_correct : forall f pc sf op args res pc' v rs ge sp m x,
                    forall (SINV: s_inv ge (State sf f sp pc rs m)),
                      (fn_code f) ! pc = Some (Iop op args res pc') ->
                      eval_operation ge sp op rs ##2 args m = Some v ->
                      gamma GVN f ge sp pc rs ->
                      exec  f pc ->
                      dsd f x pc' ->
                      G ge sp rs #2 res <- v (A_r f x) (rs #2 res <- v) !!2 x.
Proof.
  intros. 
  assert (WF:= wf f).
  destruct (p2eq x res).
  - subst. 
    rewrite P2Map.gss; eauto.
    destruct (p2eq res (A_r f res)).
    * rewrite <- e. econstructor; eauto.
      rewrite P2Map.gss; eauto.
    * destruct (GVN_spec_True f) as [Hcode _]. 
      specialize Hcode with pc.
      unfold repr_spec_code in Hcode.
      rewrite H in Hcode. 
      { destruct Hcode as [Htop | Hntop].
        - inv Htop; congruence.
        - repeat invh ex ; repeat invh and.
          econstructor; eauto.
          rewrite P2Map.gso; auto.
          
          assert (HE:[f,ge,sp,rs]|=(A_r f res)==(Iop op x1 (A_r f res) x0))
            by (inv SINV; eapply SINV0 ; eauto). 
          inv HE. invh SSAtoolinv.eval.
          rewrite op_depends_on_memory_correct with (m2:= m) in EVAL; auto.
          
          assert (Heval : eval_operation ge sp op rs ##2 args m = 
                          eval_operation ge sp op rs ##2 x1 m).
          { eapply G_list_eval_op; eauto.
            eapply gamma_v_args; eauto.
            assert (gamma GVN f ge sp x rs) by (eapply  gamma_sdom_gamma; eauto).
            assert (Heq : map (OptInv.A_r GVN f) args = map (OptInv.A_r GVN f) x1) 
              by (eapply same_repr_map; eauto).
            rewrite Heq at 1.
            eapply gamma_v_args in H5; eauto.
          }             
          congruence.
      }
  - exploit (dsd_pred_not_join_point f WF pc pc' x); eauto.          
    go.
    + intro contra. eapply fn_normalized with (pc := pc) in contra; eauto. 
      * unfold fn_code in *; congruence. 
      * unfold successors, Kildall.successors_list. 
        rewrite PTree.gmap1. unfold option_map.
        unfold fn_code in *.
        rewrite H. auto. 
    + intros [Hcase1 | [ Hcase2 | Hcase3]]; invh and; try congruence.
      * exploit params_Top; go. intros.
        eapply G_top; eauto.
      * assert (HX: exists def_x, def f x def_x) by (invh dsd; go).
        destruct HX as [dx Dx].
        exploit (H1 x); eauto. intros HGx.
        assert ((A_r f x) <> res). 
        { intro Hcont. subst. 
          assert (assigned_code_spec (fn_code f) pc (A_r f x)) by go.
          assert (Hrx: dsd f (A_r f x) dx).
          { eapply def_not_top_dsd; eauto. 
            inv Dx; auto.
            - exploit params_Top; eauto ; intros; invh is_at_Top; congruence.
            - destruct (GVN_spec_True f) as [_ Hpcode].
              specialize Hpcode with dx.
              inv H7. unfold repr_spec_phicode in *.
              rewrite H8 in *.
              invh ex.
              eelim (Hpcode x); eauto.
              + intros. rewrite H9 in *. congruence.
              + intros.
                repeat invh ex ; repeat invh and.
                eelim assigned_code_and_phi; eauto. 
          }
          inv Hrx.
          * ssa_def. inv H4; repeat ssa_def.
            eelim (elim_sdom_sdom peq); eauto.
            inv H8. congruence. 
          * eelim assigned_code_and_phi; eauto.
        } 
        econstructor; eauto.
        repeat rewrite P2Map.gso; auto. inv HGx; auto.
      * unfold fn_code in *.
        invh assigned_code_spec; try congruence.
Qed.    

Lemma G_upd_diff_help : forall f ge sp rs dst x v,
                          x <> dst ->
                          (G ge sp rs (A_r f x) rs !!2 x) ->
                          G ge sp rs #2 dst <- v (A_r f x) rs !!2 x \/
                          ~ is_at_Top (A_r f) x.
Proof.
  intros.
  destruct (p2eq (A_r f x) dst).
  - subst. right. intro Hcont. inv Hcont. congruence.
  - left. econstructor; eauto. 
    rewrite P2Map.gso; auto.
    invh G; auto.
Qed.
        
Lemma G_upd_diff : forall f ge sp rs dst x v,
                     x <> dst ->
                     A_r f x <> A_r f dst ->
                     (G ge sp rs (A_r f x) rs !!2 x) ->
                     G ge sp rs #2 dst <- v (A_r f x) rs !!2 x.
Proof.                     
  intros.
  edestruct G_upd_diff_help with (1:= H); eauto.
  destruct (p2eq (A_r f x) dst).
  - subst. generalize (GVN_spec_idempotence f (GVN_spec_True f)); go.
  - econstructor; eauto. 
    rewrite P2Map.gso; auto.
    invh G; auto.
Qed.

Lemma approx_Iop_correct : forall f pc sf op args res pc' v rs ge sp m x, 
   s_inv ge (State sf f sp pc rs m) ->
   (fn_code f) ! pc = Some (Iop op args res pc') ->
   eval_operation ge sp op rs ##2 args m = Some v ->
   gamma GVN f ge sp pc rs ->
   exec f pc ->
   dsd f x pc' ->
   G ge sp rs #2 res <- v (A_r f x) (rs #2 res <- v) !!2 x.
Proof.
  intros until x. intros SINV CODE EVAL GAMMA EXE DSD.
  assert (WF:= wf f).
  destruct (p2eq x res).
  - subst. rewrite P2Map.gss.
    destruct (p2eq res (A_r f res)).
    * rewrite <- e. econstructor; eauto.
      rewrite P2Map.gss; eauto.
    * destruct (GVN_spec_True f) as [Hcode _]. 
      specialize Hcode with pc.
      unfold repr_spec_code in Hcode.
      rewrite CODE in Hcode. 
      { destruct Hcode as [Htop | Hntop].
        - inv Htop. congruence.
        - repeat invh ex ; repeat invh and.
          econstructor; eauto.
          rewrite P2Map.gso; auto.
          assert (HE:[f,ge,sp,rs]|=(A_r f res)==(Iop op x1 (A_r f res) x0))
            by (inv SINV; eapply SINV0 ; eauto). 
          inv HE. invh SSAtoolinv.eval.
          rewrite op_depends_on_memory_correct with (m2:= m) in EVAL0; auto.
          
          assert (Heval : eval_operation ge sp op rs ##2 args m = 
                          eval_operation ge sp op rs ##2 x1 m).
          { eapply G_list_eval_op; eauto.
            eapply gamma_v_args; eauto.
            assert (gamma GVN f ge sp x rs) by (eapply  gamma_sdom_gamma; eauto).
            assert (Heq : map (OptInv.A_r GVN f) args = map (OptInv.A_r GVN f) x1) 
              by (eapply same_repr_map; eauto).
            rewrite Heq at 1.
            eapply gamma_v_args in H0; eauto. 
          }             
          congruence.
      }                
  - exploit (dsd_pred_not_join_point f WF pc pc' x); eauto.
    go.
    + intro contra. eapply fn_normalized with (pc := pc) in contra; eauto. 
      * unfold fn_code in *; congruence. 
      * unfold successors, Kildall.successors_list. 
        rewrite PTree.gmap1. unfold option_map.
        unfold fn_code in *.
        rewrite CODE. auto. 
    + intros [Hcase1 | [ Hcase2 | Hcase3]]; invh and; try congruence.
      * exploit params_Top; go. intros.
        eapply G_top; eauto.
      * assert (HX: exists def_x, def f x def_x) by (invh dsd; go).
        destruct HX as [dx Dx].
        exploit (GAMMA x); eauto. intros HGx.
        assert ((A_r f x) <> res). 
        { intro Hcont. subst. 
          assert (assigned_code_spec (fn_code f) pc (A_r f x)) by go.
          assert (Hrx: dsd f (A_r f x) dx).
          { eapply def_not_top_dsd; eauto. 
            inv Dx; auto.
            - exploit params_Top; eauto ; intros; invh is_at_Top; congruence.
            - destruct (GVN_spec_True f) as [_ Hpcode].
              specialize Hpcode with dx.
              inv H2. unfold repr_spec_phicode in *.
              rewrite H3 in *. invh ex.
              eelim  (Hpcode x x0); eauto.
              * intros; congruence.
              * intros.
                repeat invh ex ; repeat invh and.
                eelim assigned_code_and_phi; eauto. 
          }
          inv Hrx.
          * ssa_def. inv H; repeat ssa_def.
            eelim (elim_sdom_sdom peq); eauto.
            inv H3; congruence. 
          * eelim assigned_code_and_phi; eauto.
        } 
        econstructor; eauto.
        repeat rewrite P2Map.gso; auto. inv HGx; auto.
      * unfold fn_code in *.
        invh assigned_code_spec; try congruence.
Qed.  

(** * Now we have completed all obligation proofs for instanciating
[Opt.transf_function] *)

Definition transf_function (f: function) := 
  @Opt.transf_function_tool res analysis transf_instr new_code_same_or_Iop f.
     
Definition transf_fundef (f: fundef) : fundef :=
  @Opt.transf_fundef_tool res analysis transf_instr new_code_same_or_Iop f.

Definition transf_program (p: program) : program :=
  @Opt.transf_program_tool res analysis transf_instr new_code_same_or_Iop p.

