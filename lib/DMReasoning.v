Require Import Maps.
Require Import BinNums.
Require Import List.

Section TREES.
  Variable X : Type.
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
    forall_list (PTree.elements tr).

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
    unfold forall_list in *.
    intros key' val' IN.
    assert (PTree.get key' (PTree.set key val tr) = Some val') as GET.
    { apply PTree.elements_complete. assumption. }
    destruct (PTree.elt_eq key key').
    { subst key'.
      rewrite PTree.gss in GET.
      congruence.
    }
    rewrite PTree.gso in GET by congruence.
    apply Palready.
    apply PTree.elements_correct.
    assumption.
  Qed.

  Theorem forall_tree_remove :
    forall tr : tree,
    forall key : positive,
      (forall_tree tr) ->
      (forall_tree (PTree.remove key tr)).
  Proof.
    unfold forall_tree, forall_list.
    intros tr key ALL key' val' IN.
    apply ALL.
    apply PTree.elements_correct.
    assert ((PTree.get key' (PTree.remove key tr)) = Some val') as GET.
    { apply PTree.elements_complete.
      assumption. }
    destruct (PTree.elt_eq key key').
    { subst key'.
      rewrite PTree.grs in GET.
      discriminate. }
    rewrite PTree.gro in GET by congruence.
    assumption.
  Qed.
End TREES.