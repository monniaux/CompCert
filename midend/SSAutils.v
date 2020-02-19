Require Import Coqlib.
Require Import Maps.
Require Import Maps2.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Floats.
Require Import Kildall. 
Require Import KildallComp.
Require Import SSA.
Require Import Utils.
Require Import Relation_Operators.
Require Import Classical.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require Import DLib.
Require FSetAVL.


(** * Decidable equalities over various types *)
Lemma zeq : forall (x y:Z), {x = y} + {x <> y}.
Proof. 
  decide equality; decide equality.
Qed.

Lemma eq_memory_chunk:
  forall (x y: memory_chunk), {x=y} + {x<>y}.
Proof.
  decide equality.
Qed.

Lemma eq_addressing:
  forall (x y: addressing), {x=y} + {x<>y}.
Proof.
  eapply eq_addressing.
Qed.  

Lemma eq_comparison:
  forall (x y: comparison), {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

Lemma eq_condition:
  forall (x y: condition), {x=y} + {x<>y}.
Proof.
  generalize eq_operation; intro.
  decide equality;
  match goal with
      [ |- {?c = ?c0} + { _ <> _} ]=>
      case_eq c ; case_eq c0; intros ; try eapply eq_comparison; try (eapply Int.eq_dec)
  end.
Qed.

Lemma eq_typ:
  forall (x y:typ), {x=y} + {x<>y}.
Proof.
  decide equality. 
Qed.

Lemma eq_signature:
  forall (x y: signature), {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec ; intro.
  generalize Float.eq_dec ; intro.
  generalize eq_typ ; intro.
  decide equality;
  case_eq sig_res ; case_eq sig_res0; intros; try decide equality; auto.
Qed.

Lemma eq_external_function:
  forall (x y: external_function), {x = y} + {x <> y}.
Proof.
  repeat (decide equality;
          try apply eq_signature;
          try eapply Int.eq_dec).
  apply Float.eq_dec.
Qed.

(** * Utility lemmas about [get_index_acc] and [get_index] *)

Lemma get_index_acc_progress: forall (l: list node) (a b:node) acc k,
  b <> a ->
  get_index_acc (b::l) a acc = Some k ->
  get_index_acc l a (acc+1) = Some k.
Proof.
  induction l; intros.
  inv H0.
  destruct (peq b a). 
  elim H ; auto.
  inv H2.
  simpl in *. 
  destruct (peq b a0).
  elim H ; auto.
  auto. 
Qed.


Lemma get_index_acc_ge_acc: forall l e acc k, 
  get_index_acc l e acc = Some k ->
  ge k acc.
Proof.
  induction l; intros.
  inv H. 
  simpl in H.
  destruct (peq a e).  inv H; auto.
  assert (IHl' := IHl e (acc+1)%nat k H). 
  omega.
Qed.

Lemma get_index_acc_inv2 : forall l a (acc acc' :nat) x,
  get_index_acc l a (acc+acc') = Some (x+acc')%nat ->
  get_index_acc l a acc = Some x.
Proof.
  induction l; intros.
  inv H. simpl in *.
  destruct (peq a a0). inv H. 
  assert (acc = x) by omega. inv H1; auto. 
  assert (Hacc : (acc+acc'+1)%nat = (acc+1+acc')%nat) by omega.
  rewrite Hacc in *. 
  eapply IHl; eauto.
Qed.

Lemma get_index_some_sn: forall l a e k acc,
  a <> e ->
  get_index_acc (a :: l) e acc = Some ((k+1)%nat) ->
  get_index_acc l e acc = Some k.
Proof.
  destruct l; intros.
  simpl in H0.
  case_eq (peq a e) ; intros; ((rewrite peq_false in H0 ; auto); inv H0). 
  eapply get_index_acc_progress in H0; auto.
  eapply get_index_acc_inv2; eauto.
Qed.  
  
Lemma get_index_some_in: forall l e k, 
  get_index l e = Some k ->
  In e l.
Proof.
  induction l; intros.
  inv H.
  case_eq (peq a e); intros. 
  inversion e0 ; auto.
  right.    
  destruct k. 
  unfold get_index in *.
  simpl in H. rewrite peq_false in H; auto. 
  eapply get_index_acc_ge_acc in H. inv H.
  eapply IHl with (k:= k); eauto.
  replace (Datatypes.S k) with ((k+1)%nat) in *.   
  eapply get_index_some_sn ;  eauto.
  omega.
Qed.

Lemma get_index_acc_inv : forall l a (acc acc' :nat) x,
  get_index_acc l a acc = Some x ->
  get_index_acc l a (acc+acc') = Some (x+acc')%nat.
Proof.
  induction l; intros.
  inv  H.
  simpl in *.  
  case_eq (peq a a0); intros.
  rewrite H0 in H.
  inversion H. auto.
  rewrite H0 in H. 
  assert ( (acc + acc' + 1)%nat = (acc + 1 + acc')%nat) by omega.  
  rewrite H1.
  eapply IHl  ; eauto.
Qed.
  
Lemma in_get_index_some: forall l a, 
  In a l -> exists k, get_index l a = Some k.
Proof.
  induction l ; intros.
  inv H.
  inv H. exists O. unfold get_index.  simpl.
  rewrite peq_true ; auto.
  assert (Ha0 := IHl a0 H0). 
  destruct Ha0.
  unfold get_index in *. 
  unfold get_index_acc.  
  case_eq (peq a a0); intros. 
  exists O ; auto.
  generalize (get_index_acc_progress l a0 a 0 (x+1)) ; intros.
  exists (x+1)%nat. eapply H2 ; eauto.
  simpl. rewrite H1.
  eapply get_index_acc_inv with (acc:= O); eauto.
Qed.  

Lemma get_index_progress: forall l p pc0 k, 
  (p <> pc0) ->
  get_index (p::l) pc0 = Some (Datatypes.S k) ->
  get_index l pc0 = Some k.
Proof.
  induction l; intros.
  unfold get_index in *.
  simpl in *. rewrite peq_false in *; auto; congruence. 
  unfold get_index in *; simpl in *.
  rewrite peq_false in H0; auto. 
  destruct (peq a pc0). inv e. congruence.
  eapply get_index_acc_inv2 with (acc':= 1%nat); eauto.
  replace (k+1)%nat with (Datatypes.S k); auto. omega.
Qed.

Lemma get_index_some : forall l pc k, 
  get_index l pc = Some k ->
  (k < length l)%nat.
Proof.
  induction l ; intros.
  inv H.
  destruct k ; simpl in * ;  auto. omega.
  destruct (peq a pc). inv e.
  unfold get_index in * ; simpl in *.
  rewrite peq_true in H ; eauto. inv H.
  unfold get_index in *.
  replace (Datatypes.S k) with (k+1)%nat in *; try omega.
  eapply get_index_some_sn in H ; eauto.
  exploit IHl ; eauto. intros. omega. 
Qed.

Lemma get_index_nth_error: forall pc l k, 
  get_index l pc = Some k ->
  nth_error l k = Some pc.
Proof.
  induction l; intros.
  inv H. unfold get_index in H.
  destruct (peq a pc). simpl in *.  inv e; auto. rewrite peq_true in H ; auto. inv H. auto.
  destruct k. simpl in H. rewrite peq_false in H ; auto.
  eapply get_index_acc_ge_acc in H ; eauto. inv H.
  replace (Datatypes.S k) with (k+1)%nat in H; try omega.
  eapply get_index_some_sn  in H ; eauto. 
Qed.

Lemma get_index_acc_nth_okp_aux : forall pc l k k',
  SSA.get_index_acc l pc k' = Some (k'+k)%nat -> nth_okp k l.
Proof.
  induction l; simpl.
  congruence.
  intros; destruct peq.
  assert (k=O).
    inversion H. omega.
  subst; constructor.
  destruct k.
  constructor.
  replace (k' + Datatypes.S k)%nat with ((k'+1)+k)%nat in * by omega.
  constructor 2; eauto.
Qed.

Lemma get_index_acc_nth_okp : forall pc l k,
  get_index l pc = Some k -> nth_okp k l.
Proof.
  unfold SSA.get_index; intros.
  apply get_index_acc_nth_okp_aux with pc O.
  simpl; auto.
Qed.
    
(** * Utility lemmas about [index_pred] *)
Lemma index_pred_some : forall pc t k pc0,
  index_pred t pc0 pc = Some k ->
  (k < length (t!!!pc))%nat.
Proof.
  intros.
  unfold index_pred in H.
  destruct t!!!pc; inv H.
  eapply get_index_some ; eauto.
Qed.  

Lemma index_pred_some_nth: forall pc t k pc0, 
  index_pred t pc0 pc = Some k ->
  nth_error (t!!!pc) k = Some pc0.
Proof.
  intros.
  unfold index_pred in H.
  destruct t !!! pc. 
  inv H.
  eapply get_index_nth_error ; eauto.
Qed.

(** * Utility lemmas about [successors] *)
Lemma successors_instr_succs : forall f pc pc' instr, 
(fn_code f) ! pc = Some instr ->
In pc' (successors_instr instr) ->
exists succs, (successors f) ! pc = Some succs /\ In pc' succs .
Proof.
  intros.
  unfold successors.
  rewrite PTree.gmap1. rewrite H. simpl.
  exists (successors_instr instr) ; auto.
Qed.

Lemma succ_code_instr_succs : forall f pc pc' instr, 
(fn_code f) ! pc = Some instr ->
In pc' (successors_instr instr) ->
exists succs, (successors f) ! pc = Some succs /\ In pc' succs .
Proof.
  intros.
  unfold successors.
  rewrite PTree.gmap1. rewrite H. simpl.
  exists (successors_instr instr) ; auto.
Qed.

Lemma index_pred_instr_some : 
  forall instr pc' f pc  , 
    (fn_code f)!pc = Some instr -> 
    In pc' (successors_instr instr) ->
    (exists k, index_pred (make_predecessors (fn_code f) successors_instr) pc pc' = Some k).
Proof.
  intros. 
  unfold index_pred.
  generalize ((make_predecessors_correct_1 (fn_code f) successors_instr) pc instr pc') ; intros.
  generalize (successors_instr_succs f pc pc' instr H H0) ; intros.
  destruct H2 as [succs [Hsuccs Hinsucc]].
  unfold successors_list in *.
  exploit H1; auto.
  intros.
  case_eq ((make_predecessors (fn_code f) successors_instr) ! pc') ; intros.
  rewrite H3 in *.
  destruct l. inv H2.
  eapply (in_get_index_some) ; eauto.  
  rewrite H3 in H2. inv H2.
  Qed.

(** * Utility lemmas about [wf_ssa_function] *)
Lemma fn_phiargs: forall f, 
  wf_ssa_function f -> 
  forall pc block x args pred k, 
    (fn_phicode f) ! pc = Some block -> 
    In (Iphi args x) block -> 
    index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pred pc = Some k ->
    exists arg, nth_error args k = Some arg.
Proof.
  intros. exploit fn_wf_block ; eauto. intros.
  exploit index_pred_some_nth ; eauto.
  intros. eapply nth_error_some_same_length ; eauto.
Qed.
  
Lemma fn_parablock: forall f, 
  wf_ssa_function f -> 
  forall pc block, 
    (fn_phicode f) ! pc = Some block -> 
    NoDup block /\ True. 
Proof.
  intros. exploit fn_ssa ; eauto.
  intros. split ; auto.
  eapply H1 ; eauto.
Qed.

Lemma  fn_phicode_code : forall f, 
  wf_ssa_function f ->
  forall pc block, 
    (fn_phicode f) ! pc = Some block -> 
    exists ins, (fn_code f) ! pc = Some ins.
Proof.
  intros.
  generalize (fn_phicode_inv f H pc) ; eauto.
  intros [HH1 HH2].
  exploit HH2; eauto. congruence.
  intros. inv H1.
  
  assert ((make_predecessors (fn_code f) successors_instr) !!! pc = l). 	 
  { unfold successors_list. rewrite Hpreds. auto. }
  assert (exists pred, In pred l). destruct l.  simpl in *. omega. 
  exists p ; eauto. destruct H2. 	 
  exploit @make_predecessors_some; eauto. intros [i Hi].
  assert (In pc (successors_instr i)). 	 
  { eapply make_predecessors_correct2 ; eauto. 	 
    unfold successors_list. 	 
    unfold make_preds. rewrite Hpreds. auto. 
  } 
  
  exploit fn_code_closed ; eauto. 	 
Qed.

Lemma fn_entrypoint_inv: forall f, 
  wf_ssa_function f ->
    (exists i, (f.(fn_code) ! (f.(fn_entrypoint)) = Some i)) /\ 
    ~ join_point f.(fn_entrypoint) f.
Proof.
  intros.   
  exploit fn_entry ; eauto. 
  intros (s & Hentry). 
  split;  eauto.

  intro Hcont. inv Hcont. 
  destruct l. simpl in *. omega.
  
  generalize (make_predecessors_correct2 (fn_code f) successors_instr).
  intros Hcont. 
  exploit @make_predecessors_some; eauto.
  intros [ip Hip].
  specialize (Hcont p ip (fn_entrypoint f) Hip).
  eelim fn_entry_pred with (pc := p); eauto. econstructor ; eauto.
  apply Hcont.
  unfold successors_list, make_preds. 
  rewrite Hpreds; auto.
Qed.  

Lemma def_at_entry_ext_params: forall f r,
  wf_ssa_function f ->
  def f r (fn_entrypoint f) -> ext_params f r.
Proof.
  intros.
  destruct (fn_entry f) as [pc' Hentry]; eauto.
  invh def; eauto.
  invh assigned_code_spec; congruence; auto.
  invh assigned_phi_spec.
  assert ((fn_phicode f) ! (fn_entrypoint f) <> None) as Habs. 
  congruence.
  apply fn_phicode_inv in Habs; auto. 
  destruct (fn_entrypoint_inv f); auto. contradiction.
Qed.
  
Lemma fn_code_inv2: forall f, 
  wf_ssa_function f -> 
  forall jp pc, (join_point jp f) ->
    In jp ((successors f) !!! pc) ->
    f.(fn_code) ! pc = Some (Inop jp).
Proof.
  intros.
  exploit fn_normalized ; eauto.
Qed.
  
Lemma  fn_phicode_inv1: forall f, 
  wf_ssa_function f ->
  forall phib jp i,
    f.(fn_code) ! jp = Some i -> 
    f.(fn_phicode) ! jp = Some phib ->
    join_point jp f. 
Proof.
  intros. 
  eapply fn_phicode_inv ; eauto. congruence.
Qed.
  
Lemma  fn_phicode_inv2: forall f, 
  wf_ssa_function f -> 
  forall jp i,
    join_point jp f ->
    f.(fn_code) ! jp = Some i -> 
    exists phib, f.(fn_phicode) ! jp = Some phib.
Proof.
  intros. 
  case_eq (fn_phicode f) ! jp ; intros ; eauto.
  destruct (fn_phicode_inv f H jp)  ; eauto.
  eapply H3 in H0. 
  congruence.
Qed.  


Lemma ssa_def_unique2 : forall  f,
  wf_ssa_function f ->
  forall  x pc1 pc2,
  assigned_code_spec (fn_code f) pc1 x ->
  assigned_phi_spec (fn_phicode f) pc2 x -> False.
Proof.
  intros.
  inv H. inv fn_ssa. 
  generalize (H x pc1 pc2).
  intuition.
Qed.

Lemma not_jnp_not_assigned_phi_spec: forall f pc y,
  wf_ssa_function f ->
  ~ join_point pc f ->
  ~ assigned_phi_spec (fn_phicode f) pc y.
Proof.
  intros.
  intro Hcont.
  inv Hcont.
  exploit fn_phicode_code ; eauto. intros. inv H3.
  exploit fn_phicode_inv1 ; eauto.
Qed.

Lemma param_spec : forall f,
  wf_ssa_function f ->
  forall pc pc' k x args phiinstr,
  index_pred (make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
  In (Iphi args x) phiinstr ->
  (fn_phicode f) ! pc' = Some phiinstr ->
  exists arg, nth_error args k = Some arg.
Proof.
  intros.
  eapply (fn_phiargs f H); eauto. 
Qed.

Lemma ssa_def_dom_use : forall f,
  wf_ssa_function f -> 
  forall  x u d, use f x u -> def f x d -> dom f d u.
Proof.
  intros. eapply fn_strict ; eauto.
Qed.

Lemma ssa_use_exists_def : forall f,
  wf_ssa_function f -> 
  forall x u,
  use f x u -> exists d, def f x d.
Proof.
  intros.
  destruct (classic (exists pc, assigned_code_spec (fn_code f) pc x)).
  destruct H1 ; eauto.
  destruct (classic (exists pc, assigned_phi_spec (fn_phicode f) pc x)).
  destruct H2 ; eauto.
  exists (fn_entrypoint f) ; eauto.
  econstructor ; eauto.
  econstructor 2 ; eauto.
Qed.  

Lemma wf_ssa_reached : forall f,
  wf_ssa_function f ->
  forall  pc ins, 
  (fn_code f) ! pc = Some ins ->
  reached f pc.
Proof.
  intros. inv H ; eauto.
Qed.
Hint Resolve wf_ssa_reached.

Lemma ssa_def_use_code_false : forall f,
  wf_ssa_function f ->
  forall x pc,
  use_code f x pc ->
  assigned_code_spec (fn_code f) pc x ->
  False.
Proof.
  intros. eapply fn_use_def_code ; eauto.
Qed.
  
Lemma ssa_not_Inop_not_phi : forall f,
  wf_ssa_function f ->
  forall pc x pc' ins,
  In pc' (successors_instr ins) ->
  (fn_code f) ! pc = Some ins ->
  (forall n, ins <> Inop n) ->
  ~ assigned_phi_spec (fn_phicode f) pc' x.
Proof.
  intros.
  intro Hcont. inv Hcont. 
  exploit fn_phicode_code ; eauto. intros [ins' Hins].
  exploit fn_phicode_inv1 ; eauto. intros Hjp.
  exploit (fn_code_inv2 f H pc' pc) ; eauto.
  unfold successors. simpl.
  unfold Kildall.successors_list.
  rewrite PTree.gmap1 ; eauto.
  unfold option_map. rewrite H1. auto. 
  congruence. 
Qed.

Lemma unique_def_spec_def : forall f x d1 d2
  (HWF: wf_ssa_function f),
  def f x d1 ->
  def f x d2 ->
  d1 <> d2 -> False.
Proof.
  intros.
  destruct (fn_ssa f) as [Hssa1 Hssa2]; auto.  
  generalize (fn_entry f HWF) ; intros. destruct H2 as [succ Hentry].
  generalize (fn_ssa_params f HWF); intros Hparams.
  inv H ; inv H0 ; inv H ; inv H2;
  solve [
    intuition
    exploit Hparams ; eauto; intros [HH HH'] ; (exploit HH ; eauto)
    |exploit Hparams ; eauto; intros [HH HH'] ; (exploit HH' ; eauto)
    | exploit Hparams ; eauto ; intuition
    | exploit H3 ; eauto 
    | exploit H4 ; eauto; intuition
    |   (eelim (Hssa1 x d1 d2) ; eauto; intuition ; eauto)].
Qed.  

Lemma def_def_eq : forall f x d1 d2
  (HWF: wf_ssa_function f),
  def f x d1 ->
  def f x d2 ->
  d1 = d2.
Proof.
  intros.
  destruct (peq d1 d2) ; auto.
  eelim (unique_def_spec_def f x d1 d2) ; eauto.
Qed.  

Ltac def_def f x pc pc' :=
  match goal with 
    | [HWF: wf_ssa_function f |- _ ] =>
      (exploit (def_def_eq f x pc pc' HWF); eauto); 
      try (econstructor ; eauto);
        try (solve [econstructor ; eauto])
  end.

Require RTL.
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
      | _ => idtac
    end.

Lemma ssa_def_unique : forall f x d1 d2,
  wf_ssa_function f -> def f x d1 -> def f x d2 -> d1 = d2.
Proof.
  intros.
  def_def f x d1 d2.
Qed.


Lemma assigned_code_and_phi: forall f,
  wf_ssa_function f -> forall r pc pc',
    assigned_code_spec (fn_code f) pc r ->
    assigned_phi_spec (fn_phicode f) pc' r -> False.
Proof.
  intros f WFF r pc pc' H1 H2.
  destruct (fn_ssa _ WFF) as [T _].
  destruct (T r pc pc'); intuition.
Qed.

Lemma assigned_code_unique : forall f,
  wf_ssa_function f -> forall r pc pc',
    assigned_code_spec (fn_code f) pc r ->
    assigned_code_spec (fn_code f) pc' r -> pc=pc'.
Proof.
  intros f WFF r pc pc' H1 H2.
  destruct (fn_ssa _ WFF) as [T _].
  destruct (T r pc pc'); intuition.
Qed.

Lemma assigned_phi_unique : forall f,
  wf_ssa_function f -> forall r pc pc',
    assigned_phi_spec (fn_phicode f) pc r ->
    assigned_phi_spec (fn_phicode f) pc' r -> pc=pc'.
Proof.
  intros f WFF r pc pc' H1 H2.
  destruct (fn_ssa _ WFF) as [T _].
  destruct (T r pc pc'); intuition.
Qed.

Lemma assigned_phi_spec_join_point : forall f x pc,
  wf_ssa_function f -> 
  assigned_phi_spec (fn_phicode f) pc x ->
  join_point pc f.
Proof.
  intros.
  inv H0.
  exploit fn_phicode_code; eauto.
  intros [ins Hi].
  eapply fn_phicode_inv1; eauto.
Qed.


Lemma wf_ssa_use_and_def_same_pc : forall f x pc,
  wf_ssa_function f ->
  use f x pc ->
  def f x pc ->
  assigned_phi_spec (fn_phicode f) pc x \/ ext_params f x.
Proof.
  intros f x pc Hw Hu Hd.
  inv Hd; auto.
  inv Hu.
  eelim fn_use_def_code; eauto.
  inv H0.
  exploit fn_phicode_code; eauto; intros [ins Hins].
  exploit fn_phicode_inv1; eauto; intros Hj.
  exploit index_pred_some_nth; eauto.
  intros T.
  eapply nth_error_in in T; eauto.
  exploit (fn_code_inv2 f Hw pc0 pc); eauto.
  
  assert (exists i, (fn_code f) ! pc = Some i ) by (inv H; eauto).
  destruct H0 as (i & Hi).
  
  generalize (make_predecessors_correct2 (fn_code f) successors_instr pc i pc0 Hi); eauto.
  intros HH. 
  unfold successors, successors_list. rewrite PTree.gmap1. 
  unfold option_map. rewrite Hi. 
  apply HH; auto.
  intros Hnop.
  inv H; try congruence.
Qed.

(** * Properties and more lemmas about well-formed SSA functions *)
Section WF_SSA_PROP.

Variable f: function.
Hypothesis HWF : wf_ssa_function f.
Hint Resolve HWF.

Lemma elim_structural : forall pc pc' instr instr' block,
    (fn_code f)! pc = Some instr ->
    (fn_code f)! pc' = Some instr' ->
    (fn_phicode f)!pc' = Some block ->
    In pc' (successors_instr instr) ->
    instr = Inop pc'.
Proof.
  intros.
  assert (Hjp : join_point pc' f).
  eapply (fn_phicode_inv1 _) with (phib := block); eauto.
  exploit (fn_code_inv2 _ HWF pc' pc) ; eauto.
  unfold successors_list.
  unfold successors.
  rewrite PTree.gmap1.
  unfold option_map. simpl. rewrite H. auto.
  intros. simpl in *; congruence.
Qed.

Lemma phicode_joinpoint: forall  pc block i,
  (fn_code f) ! pc = Some i ->
  (fn_phicode f) ! pc = Some block ->
  join_point pc f.
Proof.
  intros.
  eapply (fn_phicode_inv1 _) ; eauto.
Qed.

Lemma nophicode_nojoinpoint: forall pc i,
  (fn_code f) ! pc = Some i ->
  (fn_phicode f) ! pc = None ->
  ~ join_point pc f.
Proof.
  intros.
  intro.
  exploit (fn_phicode_inv2 _ HWF); eauto. intros.
  destruct H2. simpl in *.
  congruence.
Qed.

Lemma join_point_exclusive: forall pc i,
  (fn_code f) ! pc = Some i ->
  ~ join_point pc f \/  join_point pc f.
Proof.
  intros.
  case_eq ((fn_phicode f) ! pc); intros.
  right ; eapply phicode_joinpoint; eauto.
  left ; eapply nophicode_nojoinpoint; eauto.
Qed.


Lemma use_ins_code : forall pc x, 
  use f x pc ->
  exists ins, (fn_code f) ! pc = Some ins.
Proof.
  intros. inv H.
  inv H0 ; eauto.
  inv H0. 
  assert (join_point pc0 f) by ( eapply fn_phicode_inv; eauto; congruence).
  inv H.
  exploit index_pred_some_nth; eauto. intros. 
  exploit nth_error_some_in ; eauto. intros.
  exploit @make_predecessors_some; eauto.
  unfold successors_list in H0. rewrite Hpreds in H0. auto.
Qed.

Lemma use_reached : forall pc x, 
  use f x pc ->
  reached f pc.
Proof.
  intros.
  exploit use_ins_code ; eauto.
  intros [ins Hins]. 
  inv HWF.
  eapply fn_code_reached ; eauto.  
Qed.

End WF_SSA_PROP.

(** * Auxiliary semantics for phi-blocks *)

(** This semantics is sequential, and it is equivalent to the parallel one 
whenever the block is parallelizable *)
Definition phi_store_aux k phib (rs:SSA.regset) :=
  List.fold_left (fun rs phi  =>
    match phi with
      | (Iphi args dst) => 
        match nth_error args k with 
          | None =>  rs (* should not happen *)
          | Some r => rs #2 dst <- (rs #2 r)
        end
    end
  ) phib rs.

(** Lemmas about the sequential semantics of phiblocks *)
Lemma notin_cons_notin : forall dst block a,
  (forall args, ~ In (Iphi args dst) (a:: block)) ->
  forall args, ~ In (Iphi args dst) block.
Proof. 
  intros. 
  intro ; exploit (H args); eauto. 
Qed.
Hint Resolve notin_cons_notin.

Lemma phi_store_notin_preserved_aux: forall k block r v dst rs,
  (forall args, ~ In (Iphi args dst) block) ->
  r <> dst ->
  (phi_store k block (rs#2 r <- v))#2 dst = rs#2 dst.
Proof.
  induction block; intros; simpl.
  (* *) eapply P2Map.gso; eauto. 
  (* *) destruct a; simpl. 
        case_eq (nth_error l k); intros ; eauto. 
        (**) rewrite P2Map.gso ; eauto. 
        intro Hcont. inv Hcont. eelim H  ; eauto.
Qed.
    
Lemma phi_store_notin_preserved: forall k  block rs dst,
  (forall args, ~ (In (Iphi args dst) block)) ->
    (phi_store k block rs)#2 dst = rs#2 dst.
Proof.
  induction block; intros.
  (* *) simpl; auto.
  (* *) destruct a; simpl. 
        case_eq (nth_error l k); intros; eauto.
        (* case some *)
        rewrite P2Map.gso ; eauto.
        intro Hinv; inv Hinv; exploit (H l); eauto. 
Qed.

Lemma phistore_compat: forall k block (rs1 rs2: SSA.regset), 
  (forall r, rs1#2 r = rs2#2 r) ->
  (forall r, (phi_store k block rs1)#2 r = (phi_store k block rs2)#2 r).
Proof.
  induction block; intros.
  (* *) simpl; auto.
  (* *) destruct a; simpl.
        destruct (nth_error l k); eauto.  
        (* case some *) 
        rewrite H.  
        case_eq (p2eq r r0); intros ; auto. 
           (* case eq *)
           rewrite P2Map.gsspec. rewrite H0.
           rewrite P2Map.gsspec. rewrite H0. 
           auto.           
           repeat (rewrite P2Map.gso; eauto).
Qed.

Lemma phi_store_copy_preserved: forall k  block rs dst arg , 
  (forall args, not (In (Iphi args dst) block)) ->
  (phi_store k block rs #2 dst <- (rs #2 arg)) #2 dst = rs #2 arg.
Proof.
  intros. 
  case (p2eq arg dst); intros.
  (* case eq *) 
  inv e.
  assert (Hrs: (forall r, (rs#2 dst <- (rs#2 dst))#2 r = rs#2 r)) by (eapply gsregset2; eauto).
  rewrite (phistore_compat _ _ (rs#2 dst<- (rs#2 dst)) rs); eauto.
  rewrite phi_store_notin_preserved; eauto.
  (* case diff *)
  rewrite phi_store_notin_preserved; eauto.
  eapply P2Map.gss ; eauto.
Qed.

(** * How to compute the list of registers of a SSA function. *)
Module MiniOrderedTypeProd (O1 O2:OrderedType) <: MiniOrderedType.

  Module P1 := OrderedTypeFacts O1.
  Module P2 := OrderedTypeFacts O2.

  Definition t : Type := (O1.t * O2.t)%type.

  Definition eq : t -> t -> Prop :=
    fun a b => O1.eq (fst a) (fst b) /\ O2.eq (snd a) (snd b).

  Definition lt : t -> t -> Prop :=
    fun a b => O1.lt (fst a) (fst b) \/
      (O1.eq (fst a) (fst b) /\ O2.lt (snd a) (snd b)).

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    split; auto.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros x y H; inv H; split; auto.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z H1 H2; inv H1; inv H2; split; eauto.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z H1 H2; inv H1; inv H2.
    left; eauto.
    destruct H0; left; eauto.
    destruct H; left; eauto.
    destruct H; destruct H0; right; split; eauto.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H1 H2.
    destruct H2; destruct H1.
    eelim O1.lt_not_eq; eauto.
    destruct H1.
    eelim O2.lt_not_eq; eauto.
  Qed.
    
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    destruct (O1.compare x1 y1).
    constructor 1; left; auto.
    destruct (O2.compare x2 y2).
    constructor 1; right; split; simpl; auto.
    constructor 2; split; auto.
    constructor 3; right; split; simpl; auto.
    constructor 3; left; auto.
  Defined.
    
End MiniOrderedTypeProd.

Module OrderedTypeProd (O1 O2:OrderedType) <: OrderedType.
  Module P := MiniOrderedTypeProd O1 O2.
  Include MOT_to_OT P.
End OrderedTypeProd.

Module OP2 := OrderedTypeProd OrderedPositive OrderedPositive.
Module SSARegSet := FSetAVL.Make OP2.

Definition all_def (f:function) : SSARegSet.t :=
  PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst succ => SSARegSet.add dst s
        | Iload chunk addr args dst succ => SSARegSet.add dst s
        | Icall sig fn args dst succ => SSARegSet.add dst s
        | Ibuiltin fn args dst succ => SSARegSet.add dst s
        | _ => s
      end) (fn_code f) 
    (PTree.fold
      (fun s _ phib => 
        List.fold_left 
        (fun s (phi:phiinstruction) => let (_,dst) := phi in SSARegSet.add dst s)
        phib s) (fn_phicode f) SSARegSet.empty).

Definition param_set (f:function) : SSARegSet.t :=
  List.fold_right SSARegSet.add SSARegSet.empty (fn_params f).  

Definition all_uses (f:function) : SSARegSet.t :=
  PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst _ => fold_right SSARegSet.add s args
        | Iload chk adr args dst _ => fold_right SSARegSet.add s args
        | Icond cond args _ _ => fold_right SSARegSet.add s args
        | Ibuiltin ef args dst _ => fold_right SSARegSet.add s args
        | Istore chk adr args src _ => fold_right SSARegSet.add s args
        | Icall sig (inl r) args dst _ => fold_right SSARegSet.add s (r::args)
        | Itailcall sig (inl r) args => fold_right SSARegSet.add s (r::args)
        | Icall sig (inr id) args dst _ => fold_right SSARegSet.add s args
        | Itailcall sig (inr id) args => fold_right SSARegSet.add s args
        | Ijumptable arg tbl => SSARegSet.add arg s
        | Ireturn (Some arg) => SSARegSet.add arg s
        | _ => s
      end) (fn_code f) 
    (PTree.fold
      (fun s _ phib => 
        fold_left 
        (fun s (phi:phiinstruction) => 
          let (args,dst) := phi in 
            fold_right SSARegSet.add s args)
        phib s) (fn_phicode f) SSARegSet.empty).

Lemma In_fold_right_add1: forall x l a,
 In x l -> SSARegSet.In x (fold_right SSARegSet.add a l).
Proof.
  induction l; simpl; auto.
  intuition.
  destruct 1; subst.
  apply SSARegSet.add_1; auto.
  apply SSARegSet.add_2; auto.
Qed.

Lemma In_fold_right_add2: forall x l a,
  SSARegSet.In x a -> SSARegSet.In x (fold_right SSARegSet.add a l).
Proof.
  induction l; simpl; auto; intros.
  apply SSARegSet.add_2; auto.
Qed.

Lemma In_fold_right_add3: forall x l a,
  SSARegSet.In x (fold_right SSARegSet.add a l) -> SSARegSet.In x a \/ In x l.
Proof.
  induction l; simpl; auto; intros.
  destruct (p2eq x a); subst; auto.
  destruct (IHl a0); auto.
  eapply SSARegSet.add_3; eauto.
  destruct a; destruct x; simpl; red; destruct 1; elim n; subst; auto.
Qed.

Lemma in_all_uses1: forall x pc code s ins,
  code!pc = Some ins ->
      match ins with
        | Iop op args dst _ => In x args
        | Iload chk adr args dst _ => In x args
        | Icond cond args _ _ => In x args
        | Ibuiltin ef args dst _ => In x args
        | Istore chk adr args src _ => In x args
        | Icall sig (inl r) args dst _ => In x (r::args)
        | Itailcall sig (inl r) args => In x (r::args)
        | Icall sig (inr id) args dst _ => In x args
        | Itailcall sig (inr id) args => In x args
        | Ijumptable arg tbl => x = arg 
        | Ireturn (Some arg) => x = arg
        | _ => False
      end ->
  SSARegSet.In x 
  (PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst _ => fold_right SSARegSet.add s args
        | Iload chk adr args dst _ => fold_right SSARegSet.add s args
        | Icond cond args _ _ => fold_right SSARegSet.add s args
        | Ibuiltin ef args dst _ => fold_right SSARegSet.add s args
        | Istore chk adr args src _ => fold_right SSARegSet.add s args
        | Icall sig (inl r) args dst _ => fold_right SSARegSet.add s (r::args)
        | Itailcall sig (inl r) args => fold_right SSARegSet.add s (r::args)
        | Icall sig (inr id) args dst _ => fold_right SSARegSet.add s args
        | Itailcall sig (inr id) args => fold_right SSARegSet.add s args
        | Ijumptable arg tbl => SSARegSet.add arg s
        | Ireturn (Some arg) => SSARegSet.add arg s
        | _ => s
      end) code s).
Proof.
  intros x pc code s.
  apply PTree_Properties.fold_rec with (P:=
    (fun code s => forall ins,
      code ! pc = Some ins ->
      match ins with
        | Inop _ => False
        | Iop _ args _ _ => In x args
        | Iload _ _ args _ _ => In x args
        | Istore _ _ args _ _ => In x args
        | Icall _ (inl r) args _ _ => In x (r :: args)
        | Icall _ (inr _) args _ _ => In x args
        | Itailcall _ (inl r) args => In x (r :: args)
        | Itailcall _ (inr _) args => In x args
        | Ibuiltin _ args _ _ => In x args
        | Icond _ args _ _ => In x args
        | Ijumptable arg _ => x = arg
        | Ireturn (Some arg) => x = arg
        | Ireturn None => False
      end -> SSARegSet.In x s)).
  intros.
  rewrite <- H in H1; eauto.
  intros; rewrite PTree.gempty in *; congruence.
  intros.
  rewrite PTree.gsspec in *; destruct peq; subst.
  inv H2.  
  destruct ins; try contradiction; try (apply In_fold_right_add1; auto).
  destruct s1; apply In_fold_right_add1; auto.
  destruct s1; apply In_fold_right_add1; auto.
  subst; apply SSARegSet.add_1; auto.
  destruct o; try contradiction.
  subst; apply SSARegSet.add_1; auto.
  destruct v; try (destruct s1); try (apply In_fold_right_add2); try (apply H1 with ins; auto).
  apply SSARegSet.add_2; eauto.
  destruct o ; eauto.
  apply SSARegSet.add_2; eauto.
Qed.

Lemma in_all_uses2: forall x code s,
  SSARegSet.In x s ->
  SSARegSet.In x 
  (PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst _ => fold_right SSARegSet.add s args
        | Iload chk adr args dst _ => fold_right SSARegSet.add s args
        | Icond cond args _ _ => fold_right SSARegSet.add s args
        | Ibuiltin ef args dst _ => fold_right SSARegSet.add s args
        | Istore chk adr args src _ => fold_right SSARegSet.add s args
        | Icall sig (inl r) args dst _ => fold_right SSARegSet.add s (r::args)
        | Itailcall sig (inl r) args => fold_right SSARegSet.add s (r::args)
        | Icall sig (inr id) args dst _ => fold_right SSARegSet.add s args
        | Itailcall sig (inr id) args => fold_right SSARegSet.add s args
        | Ijumptable arg tbl => SSARegSet.add arg s
        | Ireturn (Some arg) => SSARegSet.add arg s
        | _ => s
      end) code s).
Proof.
  intros x code s0.
  apply PTree_Properties.fold_rec with (P:=
    (fun code s => SSARegSet.In x s0 -> SSARegSet.In x s)); auto.
  intros.
  destruct v; auto; try (apply In_fold_right_add2; auto).
  destruct s1; apply In_fold_right_add2; auto.
  destruct s1; apply In_fold_right_add2; auto.
  apply SSARegSet.add_2; eauto.
  destruct o ; eauto.
  apply SSARegSet.add_2; eauto.
Qed.  

Lemma in_all_uses3 : forall x code s pc phib args dst,
  code!pc = Some phib ->
  In (Iphi args dst) phib ->
  In x args ->
   SSARegSet.In x
     (PTree.fold
        (fun (s : SSARegSet.t) (_ : positive) (phib : list phiinstruction) =>
         fold_left
           (fun (s0 : SSARegSet.t) (phi : phiinstruction) =>
            let (args, _) := phi in fold_right SSARegSet.add s0 args) phib s)
        code s).
Proof.
  intros x code s.
  apply PTree_Properties.fold_rec with (P:=
    (fun code s =>  forall pc phib args dst,
      code ! pc = Some phib ->
      In (Iphi args dst) phib ->
      In x args ->
      SSARegSet.In x s)); intros; auto.
  rewrite <- H in *; eauto.
  rewrite PTree.gempty in *; congruence.
  assert (forall phib a,
    SSARegSet.In x a ->
    SSARegSet.In x
    (fold_left
      (fun (s0 : SSARegSet.t) (phi : phiinstruction) =>
        let (args0, _) := phi in fold_right SSARegSet.add s0 args0) phib a)).
    induction phib0; simpl; auto.
    intros; apply IHphib0; auto.
    destruct a0.
    apply In_fold_right_add2; auto.    
  rewrite PTree.gsspec in *; destruct peq; subst.
  inv H2.
  clear H0 H1 H.  
  generalize dependent args.
  generalize dependent dst.
  generalize dependent a.
  generalize dependent phib.
  induction phib; simpl; intuition.
  subst.
  apply H5.
  apply In_fold_right_add1; auto.    
  eapply IHphib; eauto.
  apply H5; eauto.
Qed.

Definition ext_params_list (f:function) : list reg :=
  SSARegSet.elements 
  (SSARegSet.diff (all_uses f)
    (SSARegSet.union (all_def f) (param_set f)))
++(fn_params f).

Lemma InA_In : forall x (l:list reg),
  InA (fun a b : OP2.P.t => fst a = fst b /\ snd a = snd b) x l <-> In x l.
Proof.
  induction l; simpl; split; intros; inv H.
  destruct x; destruct a; simpl in *; destruct H1; left.
  f_equal; auto.
  rewrite IHl in H1; auto.
  constructor 1 ;auto.
  constructor 2; auto.
  rewrite IHl; auto.
Qed.

Lemma In_param_set : forall f x, SSARegSet.In x (param_set f) -> In x (fn_params f).
Proof.
  unfold param_set; intros.
  elim In_fold_right_add3 with (1:=H); auto; intros.
  elim SSARegSet.empty_1 with (1:=H0).
Qed.

Lemma use_In_all_usses : forall f x pc,
  use f x pc -> SSARegSet.In x (all_uses f).
Proof.
  intros.
  inv H.
  unfold all_uses.
  inv H0;
  eapply in_all_uses1; simpl; eauto.
  simpl; auto.
  simpl; auto.
  unfold all_uses.
  eapply in_all_uses2; simpl; eauto.
  inv H0.
  eapply in_all_uses3; simpl; eauto.
  eapply nth_error_in; eauto.
Qed.

Lemma In_all_def1: forall x code s,
  SSARegSet.In x
  (PTree.fold
    (fun (s : SSARegSet.t) (_ : positive) (ins : instruction) =>
      match ins with
        | Inop _ => s
        | Iop _ _ dst _ => SSARegSet.add dst s
        | Iload _ _ _ dst _ => SSARegSet.add dst s
        | Istore _ _ _ _ _ => s
        | Icall _ _ _ dst _ => SSARegSet.add dst s
        | Itailcall _ _ _ => s
        | Ibuiltin _ _ dst _ => SSARegSet.add dst s
        | Icond _ _ _ _ => s
        | Ijumptable _ _ => s
        | Ireturn _ => s
      end) code s) ->
  SSARegSet.In x s \/
  exists pc : node, assigned_code_spec code pc x.
Proof.
  intros x code s0.
  apply PTree_Properties.fold_rec with (P:=fun code s =>
    SSARegSet.In x s ->
    SSARegSet.In x s0 \/ (exists pc : node, assigned_code_spec code pc x)).
  intros.
  destruct (H0 H1); auto.
  destruct H2 as [pc H2]; right.
  exists pc; inv H2; rewrite H in *; eauto.
  auto.
  intros.
  destruct v;try destruct (H1 H2); auto.
  destruct H3 as [pc H3]; right; exists pc.
  inv H3.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  destruct (p2eq x r).
  subst; right; exists k; econstructor; eauto.
  rewrite PTree.gss; eauto.
  elim H1; auto.
  destruct 1 as [pc T].
  right; exists pc; inv T.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  eapply SSARegSet.add_3; eauto.
  destruct r; destruct x; simpl; red; destruct 1; elim n0; subst; auto.
  destruct (p2eq x r).
  subst; right; exists k; econstructor 2; eauto.
  rewrite PTree.gss; eauto.
  elim H1; auto.
  destruct 1 as [pc T].
  right; exists pc; inv T.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  eapply SSARegSet.add_3; eauto.
  destruct r; destruct x; simpl; red; destruct 1; elim n0; subst; auto.
  destruct H3 as [pc H3]; right; exists pc.
  inv H3.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  destruct (p2eq x r).
  subst; right; exists k; econstructor 3; eauto.
  rewrite PTree.gss; eauto.
  elim H1; auto.
  destruct 1 as [pc T].
  right; exists pc; inv T.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  eapply SSARegSet.add_3; eauto.
  destruct r; destruct x; simpl; red; destruct 1; elim n0; subst; auto.
  destruct H3 as [pc H3]; right; exists pc.
  inv H3.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  destruct (p2eq x r).
  subst; right; exists k; econstructor 4; eauto.
  rewrite PTree.gss; eauto.
  elim H1; auto.
  destruct 1 as [pc T].
  right; exists pc; inv T.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  eapply SSARegSet.add_3; eauto.
  destruct r; destruct x; simpl; red; destruct 1; elim n0; subst; auto.
  destruct H3 as [pc H3]; right; exists pc.
  inv H3.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  destruct H3 as [pc H3]; right; exists pc.
  inv H3.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  destruct H3 as [pc H3]; right; exists pc.
  inv H3.
  econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
  econstructor 4; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
Qed.

Lemma In_fold_left_add1 : forall x phib s,
  SSARegSet.In x (fold_left (fun s0 (phi:phiinstruction) =>  let (_, dst) := phi in SSARegSet.add dst s0) phib s) ->
  SSARegSet.In x s \/ exists args, In (Iphi args x) phib.
Proof.
  induction phib; simpl; auto; intros.
  elim IHphib with (1:=H); clear IHphib; intros.
  destruct a.
  destruct (p2eq x r); subst; eauto.
  left; eapply SSARegSet.add_3; eauto.
  destruct r; destruct x; simpl; red; destruct 1; elim n; subst; auto.
  destruct H0; eauto.
Qed.

Lemma In_all_def2: forall x p s,
   SSARegSet.In x
     (PTree.fold
        (fun (s : SSARegSet.t) (_ : positive) (phib : list phiinstruction) =>
         fold_left
           (fun (s0 : SSARegSet.t) (phi : phiinstruction) =>
            let (_, dst) := phi in SSARegSet.add dst s0) phib s) p
        s) -> 
     SSARegSet.In x s \/
     exists pc : node, assigned_phi_spec p pc x.
Proof.
  intros x p s0.
  apply PTree_Properties.fold_rec with (P:=fun code s =>
    SSARegSet.In x s -> 
     SSARegSet.In x s0 \/
     exists pc : node, assigned_phi_spec p pc x); auto.
  intros.
  elim In_fold_left_add1 with (1:=H2); clear H2; intros H2.
  destruct H1; auto.
  right; exists k; econstructor; eauto.
Qed.

Lemma In_all_def : forall f x,
  SSARegSet.In x (all_def f) ->
  (exists pc, assigned_phi_spec (fn_phicode f) pc x)
  \/ (exists pc, assigned_code_spec (fn_code f) pc x).
Proof.
  intros; unfold all_def in *.
  destruct In_all_def1 with (1:=H); eauto.
  clear H; left.
  elim In_all_def2 with (1:=H0); auto; intros.
  elim SSARegSet.empty_1 with (1:=H).
Qed.


Lemma ext_params_list_spec : forall f x, ext_params f x -> In x (ext_params_list f).
Proof.
  unfold ext_params_list; intros f x H.
  inv H.
  auto with datatypes.
  destruct (classic (In x (fn_params f))) as [E|E].
  rewrite in_app; right; auto.
  rewrite in_app; left.
  rewrite <- InA_In.
  apply SSARegSet.elements_1.
  apply SSARegSet.diff_3.
  destruct H0; eapply use_In_all_usses; eauto.
  intro.
  elim SSARegSet.union_1 with (1:=H); clear H; intros H.
  elim In_all_def with (1:=H); intros [pc T]; intuition eauto.
  elim E.
  apply In_param_set; auto.
Qed.


Lemma unique_def_elim1: forall f pc pc' x, 
  unique_def_spec f ->
  assigned_code_spec (fn_code f) pc x ->
  assigned_phi_spec (fn_phicode f) pc' x -> 
  False.
Proof.
  intros. inv H.
  generalize (H2 x pc pc') ; intros Hcont.  
  intuition.
Qed.

  Ltac ssa_def := 
    let eq_pc pc1 pc2 := 
    assert (pc1 = pc2) by (eapply ssa_def_unique; eauto); subst
    in
    match goal with 
      | r : reg |- _ =>
            match goal with 
               id: def _ r ?x,
               id': def _ r ?y
               |- _ => eq_pc x y ; try clear id'
            end
      | x : node,
        y : node  |- _ =>
        match goal with 
              id: def _ ?r x,
              id': assigned_phi_spec_with_args _ y ?r _ |- _ => 
              assert (x = y) 
                by (repeat invh assigned_phi_spec_with_args;
                    eapply ssa_def_unique; eauto); subst
        end
      | pc1: node,
        pc2: node |- _ =>
            match goal with 
                id : def _ ?r pc1,
                id': assigned_phi_spec _ pc2 ?r |- _ =>
                eq_pc pc1 pc2
            end
      |  pc1: node,
         pc2: node |- _ =>
            match goal with 
                id: assigned_phi_spec _ pc1 ?r,
                id': assigned_phi_spec _ pc2 ?r |- _ =>
                eq_pc pc1 pc2
            end
      | id1: assigned_phi_spec_with_args _ ?pc1 ?r _,
        id2: In (Iphi _ ?r) ?phib,
        id3: _ ! ?pc2 = Some ?phib |- _  =>
        assert (pc1 = pc2) 
          by (inv id1;
              eapply ssa_def_unique; eauto); subst
      | id : _ ! ?pc1 = Some (Iop _ _ ?r _),
        id' : _ ! ?pc2 = Some (Iop _ _ ?r _)
        |- _ => 
        match pc2 with
          | pc1 => fail 1
          | _ => idtac
        end;
          eq_pc pc1 pc2
      | id : _ ! ?pc1 = Some (Iop _ _ ?r _),
        id': def _ ?r ?pc2 |- _ =>
        match pc2 with
          | pc1 => fail 1
          | _ => idtac
        end;
          eq_pc pc1 pc2
      end.

  Lemma wf_ssa_phidef_args : forall f pc x args args', 
                               wf_ssa_function f -> 
                               assigned_phi_spec_with_args (fn_phicode f) pc x args ->
                               assigned_phi_spec_with_args (fn_phicode f) pc x args' ->
                               args = args'.
  Proof.
    intros until args'.
    intros WF ARGS ARGS'.
    repeat invh assigned_phi_spec_with_args; allinv.
    exploit fn_ssa; eauto. intros UNIQ. inv UNIQ.
    exploit H3; eauto; intros; invh and; go.
  Qed.

(** ** The [is_edge] predicate *)
Inductive is_edge (tf:SSA.function) : node -> node -> Prop:=
| Edge: forall i j instr, 
  (fn_code tf)!i = Some instr ->
  In j (successors_instr instr) ->
  is_edge tf i j.

Lemma is_edge_succs_not_nil: forall tf i j, 
  is_edge tf i j ->
  exists succtfi, (successors tf)!i = Some succtfi.
Proof.
  intros. inv H.
  unfold successors. rewrite PTree.gmap1. rewrite H0. 
  simpl; eauto.
Qed.

Lemma is_edge_insuccs: forall tf i j, 
  is_edge tf i j -> 
  (exists succtfi, (successors tf) ! i = Some succtfi /\ In j succtfi).
Proof.
  intros. 
  destruct (is_edge_succs_not_nil _ _ _ H) as [succtfi Hsuccs].
  exists succtfi ; intuition.
  inv H.
  unfold successors in *. 
  rewrite PTree.gmap1 in Hsuccs. rewrite H0 in Hsuccs. 
  inv Hsuccs; auto.
Qed.

Lemma is_edge_pred: forall tf i j,
  is_edge tf i j ->
  exists k, index_pred  (make_predecessors (fn_code tf) successors_instr) i j = Some k.
Proof.
  intros. inv H. 
  eapply index_pred_instr_some ; eauto.
Qed.

Lemma mk_pred_some_in: forall tf i j ,
  In j (successors tf)!!! i ->
  exists instr, (fn_code tf)!i = Some instr /\ In j (successors_instr instr) .
Proof.  
  intros.
  unfold successors_list, successors in *.
  case_eq ((PTree.map1 successors_instr (fn_code tf)) ! i) ; intros. rewrite H0 in H at 1.
  rewrite PTree.gmap1 in H0. 
  generalize H0 ; intros Hopt.
  eapply option_map_some in H0.
  unfold option_map in Hopt. 
  destruct H0 as [instr Hinstr].
  rewrite Hinstr in Hopt. 
  exists instr; intuition; inv Hopt ; auto.
  rewrite H0 in H at 1. inv H.
Qed.

Lemma pred_is_edge_help: forall tf i j k,
  index_pred  (make_predecessors (fn_code tf) successors_instr) i j = Some k -> 
  (is_edge tf i j).
Proof.
  intros. 
  unfold index_pred in *. 
  case_eq ((make_predecessors (fn_code tf) successors_instr) !!! j); intros ; rewrite H0 in *.
  - (* cas absurde j sans predecesseurs *) 
    inv H.
  - exploit get_index_some_in ; eauto ; intros.
    rewrite <- H0 in *.
    exploit (make_predecessors_some (fn_code tf) successors_instr j); eauto.
    unfold make_preds, successors_list in *.
    destruct ((make_predecessors (fn_code tf) successors_instr) ! j).
    auto. inv H1.
    intros (ins & Hins).
    assert (Hcorr := make_predecessors_correct2 (fn_code tf) successors_instr i ins j Hins H1); auto. 
    eapply Edge; eauto. 
Qed.
  
Lemma pred_is_edge: forall tf i j k,
                      index_pred (make_predecessors (fn_code tf) successors_instr) i j = Some k -> is_edge tf i j.
Proof.
  intros. 
  exploit_dstr pred_is_edge_help; eauto.
Qed.

Inductive ssa_def : Type := 
| SDIop (pc:node)
| SDPhi (pc:node) (idx:nat).

Inductive ssa_eq : Type := 
| EqIop (op:operation) (args:list reg) (dst:reg)
| EqPhi (dst:reg) (args:list reg).

Definition ssa_eq_to_dst (eq:ssa_eq) : reg :=
  match eq with
    | EqIop _ _ dst => dst
    | EqPhi dst _ => dst
  end.

Definition get_ssa_eq (f:function) (d:ssa_def) : option ssa_eq :=
  match d with
    | SDIop pc => 
      match (fn_code f)!pc with
        | Some (Iop op args dst _) => Some (EqIop op args dst)
        | _ => None
      end
    | SDPhi pc idx =>
      match (fn_phicode f)!pc with
        | Some phi =>
          match nth_error phi idx with
            | Some (Iphi args dst) => Some (EqPhi dst args)
            | None => None
          end
        | _ => None
      end
  end.
