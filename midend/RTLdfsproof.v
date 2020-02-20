(** This file contain the proof of the RTLdfs transformation. We show
both that the transformation ensures that generated functions are
satisfying the predicate [wf_dfs_function] and that the transformation
preserves the semantics. *)

Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import Smallstep.
Require Import RTL.
Require Import RTLutils.
Require Import RTLdfs.
Require Import Kildall.
Require Import Conventions.
Require Import Integers.
Require Import Floats.
Require Import Utils.
Require Import RTLdfs.
Require Import Events.


(** * Utility lemmas *)
Section dfs.
Variable entry:node.
Variable code:code.

Definition cardinal {A} (m:PTree.t A) :=
  List.length (List.map (@fst _ _) (PTree.elements m)).

Lemma not_seen_sons_aux0 : forall l0 l1 l2 seen_set seen_set',
  fold_left
  (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
    let (new, seen) := ns in
      match seen ! j with
        | Some _ => ns
        | None => (j :: new, PTree.set j tt seen)
      end) l0 (l1, seen_set) = (l2, seen_set') ->
  forall x, In x l1 -> In x l2.
Proof.
  induction l0; simpl; intros.
  inv H; auto.
  destruct (seen_set!a); inv H; eauto.
Qed.

Lemma not_seen_sons_prop1 : forall i j seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  cfg code i j -> In j l \/ seen_set ! j = Some tt.
Proof.
  unfold not_seen_sons; intros.
  inv H0.
  rewrite HCFG_ins in *.
  assert (
   forall l0 l1 l2 seen_set seen_set',
   fold_left
     (fun (ns : prod (list node) (PTree.t unit)) (j0 : positive) =>
      let (new, seen) := ns in
      match seen ! j0 with
      | Some _ => ns
      | None => (j0 :: new, PTree.set j0 tt seen)
      end) l0 (l1, seen_set) = (l2, seen_set') ->
   In j l0 -> In j l2 \/ seen_set ! j = Some tt).
  induction l0; simpl; intros.
  intuition.
  destruct (peq a j).
  subst.
  case_eq (seen_set0!j); intros.
  destruct u; auto.
  rewrite H2 in *.
  left; eapply not_seen_sons_aux0; eauto.
  destruct H1.
  intuition.
  destruct (seen_set0!a); eauto.
  elim IHl0 with (1:=H0); auto.
  rewrite PTree.gso; auto.
  eauto.
Qed.

Lemma not_seen_sons_prop8 : forall i j seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  In j l -> cfg code i j.
Proof.
  unfold not_seen_sons; intros.
  assert (
   forall l0 l1 l2 seen_set seen_set',
   fold_left
     (fun (ns : prod (list node) (PTree.t unit)) (j0 : positive) =>
      let (new, seen) := ns in
      match seen ! j0 with
      | Some _ => ns
      | None => (j0 :: new, PTree.set j0 tt seen)
      end) l0 (l1, seen_set) = (l2, seen_set') ->
   In j l2 -> In j l0 \/ In j l1).
  induction l0; simpl; intros.
  inv H1; auto.
  case_eq (seen_set0!a); intros; rewrite H3 in *.
  elim IHl0 with (1:=H1); auto.
  elim IHl0 with (1:=H1); auto.
  simpl; destruct 1; auto.
  case_eq (code!i); intros; rewrite H2 in H.
  apply H1 in H; auto; clear H1.
  destruct H as [H|H]; try (elim H; fail).
  econstructor; eauto.
  inv H; elim H0.
Qed.

Lemma not_seen_sons_prop2 : forall i j seen_set,
  In j (fst (not_seen_sons code i seen_set)) ->
  seen_set ! j = None.
Proof.
  unfold not_seen_sons; intros.
  case_eq (code!i); [intros ins Hi|intros Hi]; rewrite Hi in *.
  assert (forall l l0 seen_set,    
    In j
        (fst
           (fold_left
              (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
               let (new, seen) := ns in
               match seen ! j with
               | Some _ => ns
               | None => (j :: new, PTree.set j tt seen)
               end) l (l0, seen_set))) ->
        In j l0\/ seen_set ! j = None).
  induction l; simpl; auto.
  intros.
  case_eq (seen_set0 ! a); intros; rewrite H1 in *; eauto.
  elim IHl with (1:=H0); auto.
  simpl; destruct 1; subst; auto.
  rewrite PTree.gsspec; destruct peq; auto.
  intros; congruence.
  elim H0 with (1:=H); auto.
  simpl; intuition.
  simpl in H; intuition.
Qed.

Lemma not_seen_sons_prop5 : forall i seen_set,
  list_norepet (fst (not_seen_sons code i seen_set)).
Proof.
  unfold not_seen_sons; intros.
  destruct (code ! i); simpl; try constructor.
  assert (forall l l0 seen_set l1 seen_set',    
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    (forall x, In x l0 -> seen_set!x = Some tt) ->
    list_norepet l0 ->
    (forall x, In x l1 -> seen_set'!x = Some tt) /\ list_norepet l1).
  induction l; simpl; intros.
  inv H ;auto.
  case_eq (seen_set0!a); intros; rewrite H2 in *; auto.
  elim IHl with (1:=H); auto.
  elim IHl with (1:=H); auto.
  simpl; destruct 1; auto.
  subst; rewrite PTree.gss; auto.
  rewrite PTree.gsspec; destruct peq; auto.
  constructor; auto.
  intro; rewrite (H0 a) in H2; auto; congruence.
  generalize (H (successors_instr i0) nil seen_set).
  destruct (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) (successors_instr i0) (nil, seen_set)); intuition.
  eelim H0; eauto.
  simpl; intuition.
  constructor.
Qed.

Lemma not_seen_sons_prop3_aux : forall l i l0 seen_set l1 seen_set',    
    seen_set!i = Some tt ->
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    seen_set'!i = Some tt.
Proof.
 induction l; simpl; intros.
 inv H0; auto.
 destruct (seen_set!a).
 rewrite (IHl _ _ _ _ _ H H0); auto.
 assert ((PTree.set a tt seen_set)! i = Some tt).
 rewrite PTree.gsspec; destruct peq; auto.
 rewrite (IHl _ _ _ _ _ H1 H0); auto.
Qed.

Lemma not_seen_sons_prop3 : forall i seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  forall i, seen_set!i = Some tt -> seen_set'!i = Some tt.
Proof.
  unfold not_seen_sons; intros.
  destruct (code!i); inv H; auto.
  apply not_seen_sons_prop3_aux with (2:=H2); auto.
Qed.


Lemma not_seen_sons_prop4 : forall i seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  forall i, In i l -> seen_set'!i = Some tt.
Proof.
  unfold not_seen_sons; intros.
  destruct (code!i); inv H; auto.
  assert (forall l i l0 seen_set l1 seen_set',    
    In i l1 ->
    (forall i, In i l0 -> seen_set !i = Some tt) ->
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    seen_set'!i = Some tt).
  induction l0; simpl; intros.
  inv H3; auto.
  case_eq (seen_set0 ! a); intros; rewrite H4 in *; inv H3.
  apply IHl0 with (3:= H6); auto.
  apply IHl0 with (3:= H6); auto.
  simpl; destruct 1; subst.
  rewrite PTree.gss; auto.
  rewrite PTree.gsspec; destruct peq; auto.
  apply H with (3:=H2); auto.
  simpl; intuition.
  elim H0.
Qed.

Lemma not_seen_sons_prop6 : forall i seen_set seen_set' l,
  not_seen_sons code i seen_set = (l,seen_set') ->
  forall i, seen_set'!i = Some tt -> seen_set!i = Some tt \/ In i l.
Proof.
  unfold not_seen_sons; intros.
  destruct (code!i); inv H; auto.
  assert (forall l i l0 seen_set l1 seen_set',    
    (fold_left
      (fun (ns : prod (list node) (PTree.t unit)) (j : positive) =>
        let (new, seen) := ns in
          match seen ! j with
            | Some _ => ns
            | None => (j :: new, PTree.set j tt seen)
          end) l (l0, seen_set)) = (l1,seen_set') ->
    seen_set'!i = Some tt ->
    seen_set !i = Some tt \/ In i l1).
  induction l0; simpl; intros.
  inv H; auto.
  case_eq (seen_set0 ! a); intros; rewrite H3 in *; inv H.
  apply IHl0 with (1:= H5); auto.
  elim IHl0 with (1:= H5) (i:=i2); auto; intros.
  rewrite PTree.gsspec in H; destruct peq; auto.
  subst.
  right.
  eapply not_seen_sons_aux0; eauto.
  apply H with (1:=H2); auto.
Qed.

Lemma iter_hh7 :  forall seen_list stack
  (HH7: forall i j, In i seen_list -> cfg code i j -> In j seen_list \/ In j stack),
  forall i j, (cfg code)** i j -> In i seen_list -> In j seen_list \/ 
    exists k, (cfg code)** i k /\ (cfg code)** k j /\ In k stack.
Proof.
  induction 2; intros; auto.
  edestruct HH7; eauto.
  right; exists y; repeat split; auto.
  edestruct IHclos_refl_trans1; eauto.
  edestruct IHclos_refl_trans2; eauto.
  destruct H3 as [k [T1 [T2 T3]]].
  right; exists k; repeat split; eauto.
  destruct H2 as [k [T1 [T2 T3]]].
  right; exists k; repeat split; eauto.
Qed.

Lemma acc_succ_prop : forall workl seen_set seen_list stack seen code'
  (HH1: In entry seen_list)
  (HH2: list_norepet stack)
  (HH3: forall i, In i stack -> seen_set ! i = Some  tt)
  (HH4: forall i, In i seen_list -> seen_set ! i = Some  tt)
  (HH5: forall i, In i seen_list -> In i stack -> False)
  (HH6: forall i, seen_set ! i = Some tt -> In i seen_list \/ In i stack)
  (HH7: forall i j, In i seen_list -> cfg code i j -> In j seen_list \/ In j stack)
  (HH8: forall i, In i seen_list -> (cfg code)** entry i)
  (HH11: forall i, In i stack -> (cfg code)** entry i)
  (HH9: acc_succ code workl (OK (seen_set,seen_list,stack)) = OK (seen, code'))
  (HH10: list_norepet seen_list),
  (forall j, (cfg code)** entry j -> In j seen /\ code ! j = code' !j)
  /\ (forall j ins, code'!j = Some ins -> In j seen)
  /\ list_norepet seen 
  /\ (forall j, In j seen -> code!j = code'!j)
  /\ (forall i j, In i seen -> cfg code i j -> In j seen)
  /\ (forall j, In j seen -> (cfg code)** entry j).
Proof.
  induction workl; simpl; intros until 11.
  destruct stack; inv HH9.
  assert (forall j : node, (cfg code **) entry j -> In j seen); intros.
  elim (iter_hh7 seen nil HH7 entry j); auto.
  destruct 1; intuition.
  split; auto.
  intros.
  rewrite gcombine; auto.
  rewrite HH4; auto.
  split; intros.
  rewrite gcombine in H0; auto.
  unfold remove_dead in *.
  case_eq (seen_set!j); intros; rewrite H1 in *; try congruence.
  elim HH6 with j; intros; auto.
  destruct u; auto.
  split; auto.
  split; auto.
  intros.
  rewrite gcombine; simpl; auto.
  rewrite HH4; auto.
  split.
  intros; exploit HH7; eauto; destruct 1; simpl; auto.
  assumption.

  destruct stack; inv HH9.
  assert (forall j : node, (cfg code **) entry j -> In j seen); intros.
  elim (iter_hh7 seen nil HH7 entry j); auto.
  destruct 1; intuition.
  split; auto.
  intros.
  rewrite gcombine; auto.
  rewrite HH4; auto.
  split; intros.
  rewrite gcombine in H0; unfold remove_dead in *.
  case_eq (seen_set!j); intros; rewrite H1 in *; try congruence.
  elim HH6 with j; intros; auto.
  destruct u; auto.
  auto.
  split; auto.
  split; auto.
  intros; rewrite gcombine; auto.
  rewrite HH4; auto.
  split.
  intros; exploit HH7; eauto; destruct 1; auto.
  assumption.

  case_eq (not_seen_sons code p (PTree.set p tt seen_set)); intros new seen_set' Hn.
  rewrite Hn in *.

  apply IHworkl with (10:=H0); auto; clear H0.

  apply list_norepet_append; auto.
  generalize (not_seen_sons_prop5 p (PTree.set p tt seen_set)); rewrite Hn; auto.
  inv HH2; auto.
  unfold list_disjoint; red; intros; subst.
  assert (seen_set!y=None).
  generalize (not_seen_sons_prop2 p y (PTree.set p tt seen_set)); rewrite Hn; simpl; intros.
  apply H1 in H.
  rewrite PTree.gsspec in H; destruct peq; try congruence.
  rewrite HH3 in H1; auto; congruence.

  simpl; intros i Hi.
  rewrite in_app in Hi; destruct Hi; auto.
  eapply not_seen_sons_prop4; eauto.
  eapply not_seen_sons_prop3; eauto.
  rewrite PTree.gsspec; destruct peq; auto.

simpl; intros i Hi.
  destruct Hi; subst.
  eapply not_seen_sons_prop3; eauto.
  rewrite PTree.gss; auto.
  eapply not_seen_sons_prop3; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  
simpl; intros i Hi1 Hi2.
  rewrite in_app in Hi2.
  destruct Hi2.
  generalize (not_seen_sons_prop2 p i (PTree.set p tt seen_set)); rewrite Hn; simpl; intros.
  apply H0 in H; clear H0.
  rewrite PTree.gsspec in H; destruct peq; try congruence.
  destruct Hi1; subst; try congruence.
  rewrite HH4 in H; congruence.
  destruct Hi1; subst.
  inv HH2; intuition.
  elim HH5 with i; auto.
  
intros i Hi.
  elim not_seen_sons_prop6 with (1:=Hn) (2:=Hi); intros.
  rewrite PTree.gsspec in H; destruct peq; auto.
  left; left; auto.
  elim HH6 with i; auto with datatypes.
  simpl; destruct 1; auto.
  right; rewrite in_app; auto.
  right; rewrite in_app; auto.

intros i j Hi1 Hi2.
  simpl in Hi1; destruct Hi1; subst.
  elim not_seen_sons_prop1 with i j (PTree.set i tt seen_set) seen_set' new; auto; intros.
  right; eauto with datatypes.
  rewrite PTree.gsspec in H; destruct peq; auto.
  left; left; auto.
  elim HH6 with j; auto.
  simpl; destruct 1; auto with datatypes.
  elim HH7 with i j; auto.
  simpl; destruct 1; auto with datatypes.

simpl; intros i Hi.
  destruct Hi; auto.
  subst; auto.

simpl; intros i Hi.
  rewrite in_app in Hi.
  destruct Hi; auto.
  exploit not_seen_sons_prop8; eauto.

  constructor; auto.
  intro HI; elim HH5 with p; auto with arith.
Qed.  
  
End dfs.

(** * Proof of the well-formedness of generated functions *)
Lemma dfs_prop_aux : forall tf seen code',
  dfs tf = OK (seen, code') ->
  (forall j, (cfg (RTL.fn_code tf))** (RTL.fn_entrypoint tf) j -> 
    In j seen /\  (RTL.fn_code tf) ! j = code' ! j)
  /\ (forall j ins, code'!j = Some ins -> In j seen)
  /\ list_norepet seen
  /\ (forall j, In j seen -> (RTL.fn_code tf)!j = code'!j)
  /\ (forall i j, In i seen -> cfg (fn_code tf) i j -> In j seen)
  /\ (forall i, In i seen -> (cfg (RTL.fn_code tf))** (RTL.fn_entrypoint tf) i).
Proof.
  unfold dfs; intros tf seen.
  destruct (map (@fst node instruction) (PTree.elements (RTL.fn_code tf))); simpl.
  intros; congruence.
  case_eq (not_seen_sons (RTL.fn_code tf) (RTL.fn_entrypoint tf)
           (PTree.set (RTL.fn_entrypoint tf) tt (PTree.empty unit)));
  intros new seen_set TT.
  intros code' T; monadInv T.
  assert (
 (forall j : node,
    (cfg (RTL.fn_code tf) **) (RTL.fn_entrypoint tf) j ->
    In j x /\ (RTL.fn_code tf) ! j = code' ! j) /\
   (forall (j : positive) (ins : instruction),
    code' ! j = Some ins -> In j x) /\ list_norepet x /\
   (forall j, In j x -> (RTL.fn_code tf)!j = code'!j) /\
   (forall i j, In i x -> cfg (fn_code tf) i j -> In j x) /\
   (forall j : positive, In j x -> (cfg (fn_code tf) **) (fn_entrypoint tf) j)
   ).
  apply acc_succ_prop with (entry:=(RTL.fn_entrypoint tf)) (10:=EQ); auto.

  apply list_norepet_append; auto.
  generalize (not_seen_sons_prop5 (RTL.fn_code tf) (RTL.fn_entrypoint tf)
         (PTree.set (RTL.fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl; auto.
  constructor.
  intro; simpl; intuition.

  intros.
  rewrite in_app in H; destruct H.
  generalize (not_seen_sons_prop4 (RTL.fn_code tf) (RTL.fn_entrypoint tf)
         (PTree.set (RTL.fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl; eauto.
  elim H.

  simpl; intuition.
  subst.
  generalize (not_seen_sons_prop3 (RTL.fn_code tf) (RTL.fn_entrypoint tf)
         (PTree.set (RTL.fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl; intros.
  eapply H; eauto.
  rewrite PTree.gss; auto.

  simpl; intuition; subst.
  rewrite in_app in H0; destruct H0.
  generalize (not_seen_sons_prop2 (RTL.fn_code tf) (RTL.fn_entrypoint tf)
    (RTL.fn_entrypoint tf)
    (PTree.set (RTL.fn_entrypoint tf) tt (PTree.empty unit))); rewrite TT; simpl.
  rewrite PTree.gss; intros.
  apply H0 in H; congruence.
  elim H.
  
  intros.
  elim not_seen_sons_prop6 with (1:=TT) (i0:=i); auto with datatypes.
  rewrite PTree.gsspec; destruct peq; subst; intros; auto.
  rewrite PTree.gempty in H0; congruence.
  
  simpl; intuition.
  elim not_seen_sons_prop1 with (j:=j) (1:=TT); auto with datatypes.
  rewrite PTree.gsspec; destruct peq; subst; intros; auto.
  rewrite PTree.gempty in H; congruence.
  rewrite H1; auto.

  simpl; destruct 1; subst.
  constructor 2.
  elim H.

  intros i; rewrite in_app; destruct 1.
  exploit not_seen_sons_prop8; eauto.
  elim H.

  repeat constructor.
  intro H; elim H.

  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  destruct H3 as [H3 H5].
  repeat split; intros.
  rewrite <- rev_alt; rewrite <- In_rev; eauto.
  elim H with j; auto.
  elim H with j; auto.
  rewrite <- rev_alt; rewrite <- In_rev; eauto.
  rewrite <- rev_alt; auto.
  apply list_norepet_rev; auto.
  rewrite <- rev_alt in H4; rewrite <- In_rev in H4; eauto.
  rewrite <- rev_alt in *; rewrite <- In_rev in *; eauto.
  rewrite <- rev_alt in *; rewrite <- In_rev in *; eauto.
Qed. 

(** Lemmas derived from the main lemma.*)
Lemma transf_function_ppoints1 : forall f tf, 
  transf_function f = OK tf ->
  (forall j, (cfg (fn_code f))** (fn_entrypoint f) j -> 
    In j (fn_dfs tf) /\  (fn_code f) ! j = (fn_code tf) ! j).
Proof.
  intros.
  monadInv H.
  eapply dfs_prop_aux ; eauto.
Qed.

Lemma transf_function_fn_entrypoint : forall f tf, 
  transf_function f = OK tf ->
  fn_entrypoint tf = fn_entrypoint f.
Proof.
  intros.
  unfold transf_function in H.
  destruct (dfs f); simpl in H; try congruence.
  destruct p; inv H.
  reflexivity.
Qed.

Lemma transf_function_ppoints1' : forall f tf, 
  transf_function f = OK tf ->
  (forall j, (cfg (fn_code f))** (fn_entrypoint f) j -> 
    (cfg (fn_code tf))** (fn_entrypoint tf) j).
Proof.
  intros.
  rewrite <- cfg_star_same.
  assert (fn_entrypoint tf = fn_entrypoint f).
    eapply transf_function_fn_entrypoint; eauto.
  apply cfg_star_same_code with (fn_code f).
  intros.
  rewrite cfg_star_same in *.
  clear H0.
  rewrite H1 in H2.
  exploit transf_function_ppoints1; eauto.
  intuition.
  rewrite cfg_star_same; rewrite H1; auto.
Qed.

Lemma transf_function_ppoints2 : forall f tf, 
  transf_function f = OK tf ->
  (forall j ins, (fn_code tf)!j = Some ins -> In j (fn_dfs tf)).
Proof.
  intros.
  monadInv H; simpl in *.
  exploit dfs_prop_aux ; eauto; intuition eauto.
Qed.

Lemma transf_function_ppoints3 : forall f tf, 
  transf_function f = OK tf ->
  list_norepet (fn_dfs tf).
Proof.
  intros.
  monadInv H.
  eapply dfs_prop_aux ; eauto.
Qed.

Lemma transf_function_ppoints4 : forall f tf, 
  transf_function f = OK tf ->
  (forall j, In j (fn_dfs tf) -> (fn_code f)!j = (fn_code tf) ! j).
Proof.
  intros.
  monadInv H.
  eapply dfs_prop_aux ; eauto. 
Qed.

Lemma transf_function_ppoints5 : forall f tf, 
  transf_function f = OK tf ->
  (forall i j, In i (fn_dfs tf) -> cfg (fn_code f) i j -> In j (fn_dfs tf)).
Proof.
  intros.
  monadInv H.
  eapply dfs_prop_aux ; eauto. 
Qed.

Lemma transf_function_ppoints6 : forall f tf, 
  transf_function f = OK tf ->
  (forall i, In i (fn_dfs tf) -> (cfg (fn_code tf))** (fn_entrypoint tf) i).
Proof.
  intros.
  eapply transf_function_ppoints1'; eauto.
  monadInv H.
  eapply dfs_prop_aux ; eauto. 
Qed.

Lemma transf_function_wf_dfs : forall f tf,
   transf_function f = OK tf ->
   wf_dfs_function tf.
Proof.
  constructor.
  eapply transf_function_ppoints2 ; eauto.
  eapply transf_function_ppoints6 ; eauto.
  eapply transf_function_ppoints3 ; eauto.
Qed.


(** All generated functions satisfy the [wf_dfs] predicate. *)
Lemma transf_program_wf_dfs : forall p tp, 
  transf_program p = OK tp ->
  wf_dfs_program tp.
Proof.
Admitted.
(*
  intros.
  unfold wf_dfs_program. intros.
  elim transform_partial_program_function with (1:=H) (2:=H0).
  intros g [F1 F2].
  destruct g; simpl in *; monadInv F2; constructor. 
  eapply transf_function_wf_dfs; eauto.
Qed.
 *)

(** * Semantics preservation *)
Section PRESERVATION.

Variable prog: RTL.program.
Variable tprog: RTL.program.
Hypothesis TRANSF_PROG: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
  
Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
Admitted.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof.
Admitted.

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof.
Admitted.

Lemma var_info_preserved:
  forall (b: block), Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
Admitted.

Lemma instr_at:
  forall f tf pc ins,
  transf_function f = OK tf ->
  (cfg (fn_code f) **) (fn_entrypoint f) pc -> 
  (RTL.fn_code f)!pc = Some ins ->  
  (RTL.fn_code tf)!pc = Some ins.
Proof.
  intros. inv H. 
  monadInv  H3; simpl.
  inv EQ. 
  elim dfs_prop_aux with f x x0; auto; intros.
  elim H with pc; auto.
  congruence.
Qed.

Lemma sig_fundef_translated:
  forall f tf,
  transf_fundef f = OK tf ->
  funsig tf = RTL.funsig f.
Proof.
  intros f tf. destruct f; simpl; intros.
  monadInv H; auto.
  monadInv EQ; auto.
  inv H. simpl; auto.
Qed.

Lemma find_function_preserved_same : forall r rs f f', 
  find_function ge (inl ident r) rs = Some f ->
  find_function tge (inl ident r) rs = Some f' ->
  funsig f = funsig f'.
Proof.
  intros. simpl in *.
  exploit (functions_translated rs#r) ; eauto.
  intros.
  destruct H1 as [tf [Htf Oktf]].
  symmetry.
  eapply sig_fundef_translated; eauto.
  rewrite Htf in H0. inv H0; auto.
Qed.

Lemma sig_function_translated:
  forall f tf,
  transf_function f = OK tf ->
  fn_sig tf = RTL.fn_sig f.
Proof.
  intros f tf. destruct f; simpl; intros.
  monadInv H; auto.
Qed. 

Lemma spec_ros_r_find_function:
  forall rs f r,
  RTL.find_function ge (inl _ r) rs = Some f ->
  exists tf,
     RTL.find_function tge (inl _ r) rs = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros.
  eapply functions_translated; eauto.
Qed.

Lemma spec_ros_id_find_function:
  forall rs f id,
  RTL.find_function ge (inr _ id) rs = Some f ->
  exists tf,
     RTL.find_function tge (inr _ id) rs = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros.
  simpl in *. 
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
| match_stackframes_nil: match_stackframes nil nil
| match_stackframes_cons: 
  forall res f sp pc rs s tf ts 
    (STACK : (match_stackframes s ts))
    (SPEC: (transf_function f = OK tf))
    (HCFG: (cfg (fn_code f) **) (fn_entrypoint f) pc),
    match_stackframes
    ((Stackframe res f sp pc rs) :: s)
    ((Stackframe res tf sp pc rs) :: ts)
    .
Hint Constructors match_stackframes.


Inductive match_states: state -> state -> Prop :=
  | match_states_intro:
      forall s ts sp pc rs m f tf
        (SPEC: transf_function f = OK tf)
        (HCFG: (cfg (fn_code f) **) (fn_entrypoint f) pc)
        (STACK: match_stackframes s ts ),
        match_states (State s f sp pc rs m) (State ts tf sp pc rs m)
  | match_states_call:
      forall s ts f tf args m
        (SPEC: transf_fundef f = OK tf)
        (STACK: match_stackframes s ts ),
        match_states (Callstate s f args m) (Callstate ts tf args m)
  | match_states_return:
      forall s ts v m 
        (STACK: match_stackframes s ts ),
        match_states (Returnstate s v m) (Returnstate ts v m).
Hint Constructors match_states.

Lemma transf_initial_states:
  forall st1, RTL.initial_state prog st1 ->
    exists st2, RTL.initial_state tprog st2 /\ match_states st1 st2.
Proof.
Admitted.
(*
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial); eauto).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  rewrite symbols_preserved.
  rewrite (transform_partial_program_main _ _ TRANSF_PROG).  auto.
  rewrite <- H3. apply sig_fundef_translated; auto.
  eapply match_states_call  ; eauto.
Qed. *)

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> RTL.final_state st1 r -> RTL.final_state st2 r.
Proof.
  intros. inv H0. inv H. 
  inv STACK.
  constructor.
Qed.

Lemma stacksize_preserved: forall f tf, 
  transf_function f = OK tf -> 
  fn_stacksize f = fn_stacksize tf.
Proof.
  intros.
  monadInv H. auto.
Qed.

Create HintDb valagree.
Hint Resolve find_function_preserved_same: valagree.
Hint Resolve symbols_preserved : valagree.
Hint Resolve eval_addressing_preserved : valagree.
Hint Resolve eval_operation_preserved : valagree.
Hint Resolve sig_function_translated : valagree.
Hint Resolve sig_fundef_translated : valagree.
Hint Resolve var_info_preserved : valagree.
Hint Resolve stacksize_preserved: valagree.

Ltac try_succ f pc pc' := 
  try (eapply Rstar_trans ; eauto) ; constructor ; 
    (eapply (CFG (fn_code f) pc pc'); eauto;  simpl; auto). 

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
Admitted.
(* Proof (Genv.senv_transf TRANSL). *)

Lemma transl_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; auto.
  
- (* inop *)
  exploit instr_at; eauto; intros.
  exists (State ts tf sp pc' rs m); split ; eauto. 
  econstructor; auto. 
  constructor; auto.  
  try_succ f pc pc'.
 
- (* iop *)
  exploit instr_at; eauto; intros.
  exists (State ts tf sp pc' (rs#res<- v) m); split ; eauto. 
  eapply exec_Iop ; eauto.
  rewrite <- H0 ; eauto with valagree. 
  constructor; auto.  
  try_succ f pc pc'.
  
- (* iload *)
  exploit instr_at; eauto; intros.
  exists (State ts tf sp pc' (rs#dst <- v) m); split ; eauto. 
  eapply exec_Iload ; eauto. 
  rewrite <- H0 ; eauto with valagree.
  econstructor ; eauto.

- (* istore *)
  exploit instr_at; eauto; intros.
  exists (State ts tf sp pc' rs m'); split ; eauto. 
  eapply exec_Istore ; eauto. 
  rewrite <- H0 ; eauto with valagree.
  constructor ; eauto.
  
- (* icall *)
  destruct ros.
  exploit spec_ros_r_find_function ; eauto.
  intros. destruct H1 as [tf' [Hfind OKtf']].

  exploit instr_at; eauto; intros.
  exists (Callstate (Stackframe res tf sp pc' rs :: ts) tf' rs ## args m) ; split ; eauto. 
  eapply exec_Icall ; eauto. 
  eauto with valagree.
  constructor; auto. 
  constructor; auto.
  try_succ f pc pc'.
  
  exploit spec_ros_id_find_function ; eauto.
  intros. destruct H1 as [tf' [Hfind OKtf']].

  exploit instr_at; eauto; intros.
  exists (Callstate (Stackframe res tf sp pc' rs :: ts) tf' rs ## args m) ; split ; eauto. 
  eapply exec_Icall ; eauto. 
  eauto with valagree.
  constructor; auto.
  constructor ; eauto.

- (* itailcall *)
  destruct ros.
  exploit spec_ros_r_find_function ; eauto.
  intros. destruct H1 as [tf' [Hfind OKtf']].

  exploit instr_at; eauto; intros.
  exploit find_function_preserved_same ; eauto.
  intros.
  exists (Callstate ts tf' rs##args m');  split ; eauto. 
  eapply exec_Itailcall ; eauto with valagree.  
  replace (fn_stacksize tf) with (fn_stacksize f); eauto with valagree.
  
  exploit spec_ros_id_find_function ; eauto.
  intros. destruct H1 as [tf' [Hfind OKtf']].

  exploit instr_at; eauto; intros.
  exists (Callstate ts tf' rs##args m');  split ; eauto. 
  eapply exec_Itailcall ; eauto with valagree.
  replace (fn_stacksize tf) with (fn_stacksize f); eauto with valagree.

- (* ibuiltin *)
  exploit instr_at; eauto; intros.
  econstructor; eauto.
  split; eauto.
  eapply exec_Ibuiltin ; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto with valagree.
   apply senv_preserved.

  constructor; auto. try_succ f pc pc'. 
  
- (* ifso *)
  
  exploit instr_at; eauto; intros.
  destruct b.
  +  exists (State ts tf sp ifso rs m); split ; eauto. 
     eapply exec_Icond ; eauto. 
     constructor; auto.  
     try_succ f pc ifso.
  + exists (State ts tf sp ifnot rs m); split ; eauto. 
    eapply exec_Icond ; eauto. 
    constructor; auto.  
    try_succ f pc ifnot.
  
- (* ijump *)
  exploit instr_at; eauto; intros.
  exists (State ts tf sp pc' rs m); split ; eauto. 
  eapply exec_Ijumptable ; eauto. 
  constructor; auto.  
  try_succ f pc pc'.
  eapply list_nth_z_in; eauto. 
  
- (* ireturn *)
  exploit instr_at; eauto; intros.
  exists (Returnstate ts (regmap_optget or Vundef rs) m'); split ; eauto. 
  eapply exec_Ireturn ; eauto.
  rewrite <- H0 ; eauto with valagree.
  rewrite stacksize_preserved with f tf ; eauto.

- (* internal *)
  simpl in SPEC. monadInv SPEC. simpl in STACK.
  exists (State ts x
    (Vptr stk Ptrofs.zero)
    x.(fn_entrypoint)
    (init_regs args x.(fn_params))
    m').
  split.
  eapply exec_function_internal; eauto.
  rewrite stacksize_preserved with f x in H ; auto.
  replace (RTL.fn_entrypoint f) with (fn_entrypoint x).
  replace (RTL.fn_params f) with (fn_params x).

  econstructor ; eauto.
  replace (RTL.fn_entrypoint x) with (fn_entrypoint f).
  eapply Rstar_refl ; eauto.
  monadInv EQ. auto.
  monadInv EQ. auto.
  monadInv EQ. auto.

- (* external *)
  inv SPEC.
  exists (Returnstate ts res m'). split. 
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto with valagree.
  apply senv_preserved; auto.
  econstructor ; eauto.
  
- (* return state *)
  inv STACK. 
  exists (State ts0 tf sp pc (rs# res <- vres) m);
    split; ( try constructor ; eauto).
Qed.
  
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
   exact transl_step_correct. 
Qed.

End PRESERVATION.
