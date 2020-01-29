Require Import Maps.
Require Import BinNums.
Require Import List.

Section TREES.
  Variable X : Type.

  Section PROPERTY.
  Variable P : positive -> X -> Prop.

  Local Definition tree := PTree.t X.
  Local Definition alist := list (positive * X).

  Definition forall_list (l : alist) :=
    forall key val,
      In (key, val) l -> (P key val).
  
  Fixpoint forall_list2 (l : alist) :=
    match l with
    | nil => True
    | (hi,hv) :: t => (P hi hv) /\ (forall_list2 t)
    end.

  Lemma forall_list_eqv: forall l : alist,
      (forall_list l) <-> (forall_list2 l).
  Proof.
    induction l; unfold forall_list in *; simpl.
    {
      split; trivial.
      contradiction.
    }
    destruct a as (key, val).
    split.
    {
      intro ALL.
      split; auto.
      apply IHl.
      auto.
    }
    {
      intro H.
      destruct H as (Pkeyval, REST).
      intros key' val'.
      intro H.
      destruct H as [EQ | OTHER].
      { congruence. }
      apply IHl; assumption.
    }
  Qed.      

  Definition forall_tree (tr : tree) :=
    forall key : positive,
    forall val : X,
      PTree.get key tr = Some val ->
      (P key val).
  
  Definition forall_tree2 (tr : tree) :=
    forall_list (PTree.elements tr).

  Lemma forall_tree_eqv :
    forall tr : tree,
      (forall_tree tr) <-> (forall_tree2 tr).
  Proof.
    unfold forall_tree, forall_tree2, forall_list.
    intro.
    split.
    {
      intros ALL key val IN.
      apply ALL.
      apply PTree.elements_complete.
      assumption.
    }
    intros ALL key val GET.
    apply ALL.
    apply PTree.elements_correct.
    assumption.
  Qed.
    
  Theorem forall_tree_set :
    forall tr : tree,
    forall key : positive,
    forall val : X,
      (P key val) ->
      (forall_tree tr) ->
      (forall_tree (PTree.set key val tr)).
  Proof.
    unfold forall_tree.
    intros until val. intros Pkeyval Palready.
    intros key' val' GET.
    destruct (PTree.elt_eq key key').
    {
      subst key'.
      rewrite PTree.gss in GET.
      congruence.
    }
    rewrite PTree.gso in GET by congruence.
    apply Palready.
    assumption.
  Qed.

  Theorem forall_tree_remove :
    forall tr : tree,
    forall key : positive,
      (forall_tree tr) ->
      (forall_tree (PTree.remove key tr)).
  Proof.
    unfold forall_tree.
    intros tr key ALL key' val' GET.
    destruct (PTree.elt_eq key key').
    {
      subst key'.
      rewrite PTree.grs in GET.
      discriminate.
    }
    rewrite PTree.gro in GET by congruence.
    apply ALL.
    assumption.
  Qed.

  Definition exists_tree (tr : tree) :=
    exists key : positive,
    exists val : X,
      PTree.get key tr = Some val /\ (P key val).

  Theorem exists_tree_set :
    forall tr : tree,
    forall key : positive,
    forall val : X,
      (P key val) ->
      (exists_tree (PTree.set key val tr)).
  Proof.
    unfold exists_tree.
    intros tr key val Pkeyval.
    exists key. exists val.
    rewrite PTree.gss.
    auto.
  Qed.

  Section PROPAGATE.
    Variable Y : Type.
    Variable valid : Y -> Prop.
    Variable f : Y -> positive -> X -> Y.
    Variable f_respects :
      forall y key val,
        (valid y) -> (P key val) -> (valid (f y key val)).

    Theorem fold_tree_propagate:
      forall tr : tree,
      forall initial : Y,
      (forall_tree tr) ->
      valid initial ->
      valid (PTree.fold f tr initial).
    Proof.
      intros tr initial.
      rewrite PTree.fold_spec.
      generalize (PTree.elements_complete tr).
      generalize (PTree.elements tr).
      intro l.
      generalize initial.
      clear initial.
      induction l; simpl.
      { trivial. }
      destruct a as [key val]; simpl.
      intros already GET ALL ALREADY.
      apply IHl; auto.
    Qed.
  End PROPERTY.

  Section PROPERTY2.
    Variable P P' : positive -> X -> Prop.
    Hypothesis IMPLIES: forall key val, (P key val) -> (P' key val).
    
    Lemma forall_tree_implies:
      forall tr : tree,
        (forall_tree P tr) -> (forall_tree P' tr).
    Proof.
      unfold forall_tree.
      auto.
    Qed.      
  End PROPERTY2.
End TREES.