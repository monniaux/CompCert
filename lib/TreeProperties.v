(*
Additional properties on CompCert's PTree structures.

David Monniaux, CNRS, VERIMAG
 *)

Require Import Maps.
Require Import BinNums.
Require Import BinPos.
Require Import List.
Require Import Lia.

Set Implicit Arguments.

Section TREES.
  Variable X : Type.

  Section PROPERTY.
  Variable P : positive -> X -> Prop.

  Local Definition tree := PTree.t X.
  Local Definition alist := list (positive * X).

  Definition forall_alist (l : alist) :=
    forall key val,
      In (key, val) l -> (P key val).
  
  Fixpoint forall_alist2 (l : alist) :=
    match l with
    | nil => True
    | (hi,hv) :: t => (P hi hv) /\ (forall_alist2 t)
    end.

  Lemma forall_list_eqv: forall l : alist,
      (forall_alist l) <-> (forall_alist2 l).
  Proof.
    induction l; unfold forall_alist in *; simpl.
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
    forall_alist (PTree.elements tr).

  Lemma forall_tree_eqv :
    forall tr : tree,
      (forall_tree tr) <-> (forall_tree2 tr).
  Proof.
    unfold forall_tree, forall_tree2, forall_alist.
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

  Theorem forall_tree_empty :
    (forall_tree (PTree.empty X)).
  Proof.
    unfold forall_tree.
    intros.
    rewrite PTree.gempty in *.
    discriminate.
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
    End PROPAGATE.
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

  Local Open Scope positive.
  
  Definition max_key_tree (tr : tree) :=
    PTree.fold (fun m key _ => Pos.max m key) tr 1.

  Definition bounds_tree (bound : positive) (tr : tree) :=
    forall_tree (fun key val => key <= bound) tr.

  Definition max_list (l : list positive) :=
    fold_left Pos.max l 1.

  Lemma fold_max_increase:
    forall l x y,
      x <= y ->
      (fold_left Pos.max l x) <= (fold_left Pos.max l y).
  Proof.
    induction l; simpl; trivial.
    intros.
    apply IHl.
    lia.
  Qed.

  Lemma fold_max_bigger :
    forall l x,
      (fold_left Pos.max l x) >= x.
  Proof.
    induction l; simpl; intro.
    lia.
    specialize IHl with (Pos.max x a).
    lia.
  Qed.
  
  Lemma max_list_bounds :
    forall l : list positive,
    forall x, In x l -> x <= (max_list l).
  Proof.
    unfold max_list.
    induction l; simpl.
    contradiction.
    intros x IN.
    destruct IN as [ EQ | REST ].
    { subst a.
      pose proof (fold_max_bigger l (Pos.max 1 x)) as BIG.
      lia.
    }
    pose proof (IHl x REST) as IHLx.
    assert (fold_left Pos.max l 1 <= fold_left Pos.max l (Pos.max 1 a)).
    { apply fold_max_increase.
      lia. }
    lia.
  Qed.

  Lemma fold_list_fst :
    forall f l x,
      fold_left (fun (a : positive) (p : positive * X) => f a (fst p)) l x =
      fold_left f (List.map fst l) x.
  Proof.
    induction l; simpl; trivial.
  Qed.

  Lemma forall_alist_fst :
    forall P al,
      forall_alist (fun key val => P key) al <->
      forall x, In x (List.map fst al) -> P x.
  Proof.
    unfold forall_alist.
    intros.
    split.
    {
      intros INP key IN.
      rewrite in_map_iff in IN.
      destruct IN as ((key', val'), (OK1, OK2)). simpl in *.
      apply INP with (val := val').
      congruence.
    }
    intros INP key val IN.
    apply INP.
    rewrite in_map_iff.
    exists (key, val).
    simpl.
    auto.
  Qed.
    
  Lemma max_key_bounds_tree:
    forall tr : tree,
      (bounds_tree (max_key_tree tr) tr).
  Proof.
    intro.
    unfold bounds_tree.
    rewrite forall_tree_eqv.
    unfold forall_tree2, max_key_tree.
    rewrite PTree.fold_spec.
    rewrite fold_list_fst.
    fold (max_list (map fst (PTree.elements tr))).
    rewrite forall_alist_fst.
    apply max_list_bounds.
  Qed.
End TREES.
