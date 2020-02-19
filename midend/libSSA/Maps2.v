Require Import Coqlib.
Require Import Maps.

Set Implicit Arguments.

Module MakeProdTree (M1:TREE) (M2:TREE) <: TREE.
  Definition elt: Type := (M1.elt * M2.elt)%type.
  Definition elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Proof.
    decide equality.
    apply M2.elt_eq.
    apply M1.elt_eq.
  Defined.

  Definition t (A:Type) : Type := M1.t (M2.t A).

  Definition empty (A: Type) : t A := M1.empty _.

  Definition get (A: Type) (a:elt) (m: t A) : option A :=
    let (a1,a2) := a in
      match M1.get a1 m with
        | None => None
        | Some m => M2.get a2 m
      end.

  Definition set (A: Type) (a:elt) (v: A) (m:t A) : t A :=
    let (a1,a2) := a in
      let m1 := match M1.get a1 m with
                  | None => M2.set a2 v (M2.empty _)
                  | Some m1 => M2.set a2 v m1
                end in
      M1.set a1 m1 m.

  Definition remove (A: Type) (a:elt) (m:t A) : t A :=
    let (a1,a2) := a in
      let m1 := match M1.get a1 m with
                  | None => M2.empty _
                  | Some m1 => m1
                end in
      M1.set a1 (M2.remove a2 m1) m.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Lemma gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof.
    intros A [i1 i2]; unfold get, empty.
    rewrite M1.gempty; auto.
  Qed.

  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros A [i1 i2] x m; unfold get, set.
    rewrite M1.gss; auto.
    destruct (M1.get i1 m).
    rewrite M2.gss; auto.
    rewrite M2.gss; auto.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros A [i1 i2] [j1 j2] x m H; unfold get, set.
    destruct (M1.elt_eq i1 j1); subst.
    rewrite M1.gss; auto.
    destruct (M1.get j1 m).
    rewrite M2.gso; intuition congruence.
    rewrite M2.gso; try intuition congruence.
    rewrite M2.gempty; auto.
    rewrite M1.gso; auto.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros A i j x m.
    destruct (elt_eq i j); subst.
    apply gss.
    apply gso; auto.
  Qed.

  Lemma gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    intros A [i1 i2] m v; unfold get, set.
    case_eq (M1.get i1 m); [intros m2 H2 H| intros H2 H].    
    apply M1.gsident.
    rewrite M2.gsident; auto.
    congruence.
  Qed.

  Lemma grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof.
    intros A [i1 i2] m; unfold get, remove.
    rewrite M1.gss.
    rewrite M2.grs; auto.
  Qed.

  Lemma gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros A [i1 i2] [j1 j2] m H; unfold get, remove.
    destruct (M1.elt_eq i1 j1); subst.
    rewrite M1.gss.
    rewrite M2.gro.
    destruct (M1.get j1 m); auto.
    rewrite M2.gempty; auto.
    congruence.
    rewrite M1.gso; auto.
  Qed.

  Lemma grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros A i j m.
    destruct (elt_eq i j); subst.
    apply grs.
    apply gro; auto.
  Qed.

  (** Extensional equality between trees. *)
  Definition beq (A: Type) (f:A -> A -> bool) (m1 m2: t A) : bool :=
    let mb := M1.combine
                (fun m'1 m'2 =>
                   match m'1, m'2 with
                     | Some m'1, Some m'2 => Some (M2.beq f m'1 m'2)
                     | Some m'1, None => Some (M2.beq f m'1 (M2.empty _))
                     | None, Some m'2 => Some (M2.beq f (M2.empty _) m'2)
                     | None, None => None
                   end)
                m1 m2
    in M1.fold (fun x _ y => y && x) mb true.

  Lemma beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).
  Proof.
    intros A eqA t1 t2. unfold get, beq.
    rewrite M1.fold_spec.
    rewrite <- fold_left_rev_right.
    unfold fold_right. fold (forallb (snd (A:=M1.elt))).
    rewrite forallb_forall.
    setoid_rewrite <- (in_rev).
    assert (forall (A B:Type) (P:A*B->Prop), (forall p, P p) <-> (forall a b, P (a, b))) by intuition.
    rewrite H. clear H.
    setoid_rewrite (fun A m i v => conj (@M1.elements_complete A m i v) (@M1.elements_correct A m i v) : _ <-> _).
    setoid_rewrite (@M1.gcombine _ _ _ _ eq_refl).
    split.
    - intros H [x1 x2]. specialize (H x1 false). simpl in H.
      destruct (M1.get); destruct (M1.get).
      + apply M2.beq_correct. destruct (M2.beq eqA t0 t3); auto.
      + assert (M2.beq eqA t0 (M2.empty A) = true) by (destruct M2.beq; auto).
        rewrite M2.beq_correct in H0. specialize (H0 x2). rewrite (M2.gempty) in H0. trivial.
      + assert (M2.beq eqA (M2.empty A) t0 = true) by (destruct M2.beq; auto).
        rewrite M2.beq_correct in H0. specialize (H0 x2). rewrite (M2.gempty) in H0. trivial.
      + trivial.
    - intros H x1 []. trivial.
      pose proof (fun x => H (x1, x)). clear H. simpl in H0.
      destruct (M1.get); destruct (M1.get).
      + rewrite <- M2.beq_correct in H0. congruence.
      + assert (M2.beq eqA t0 (M2.empty A) = true).
        rewrite M2.beq_correct. intro. rewrite M2.gempty. apply H0.
        congruence.
      + assert (M2.beq eqA (M2.empty A) t0 = true).
        rewrite M2.beq_correct. intro. rewrite M2.gempty. apply H0.
        congruence.
      + congruence.
  Qed.

  (** Applying a function to all data of a tree. *)
  Definition map (A B: Type) (f: elt -> A -> B) (m:t A) : t B :=
    M1.map (fun a1 => M2.map (fun a2 => f (a1,a2))) m.

  Lemma gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros A B f [i1 i2] m; unfold get, map.
    rewrite M1.gmap.
    case_eq (M1.get i1 m); intros; simpl; auto.
    rewrite M2.gmap; auto.
  Qed.

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Definition map1 (A B: Type) (f:A -> B) (m:t A) : t B :=
    M1.map1 (M2.map1 f) m.

  Lemma gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    intros A B f [i1 i2] m; unfold get, map1.
    rewrite M1.gmap1.
    case_eq (M1.get i1 m); intros; simpl; auto.
    rewrite M2.gmap1; auto.
  Qed.

  (** Applying a function pairwise to all data of two trees. *)
  Definition combine (A B C: Type) (f:option A -> option B -> option C) (m1:t A) (m2:t B) : t C :=
    M1.combine (fun om1 om2 =>
      match om1, om2 with
        | None, None => None
        | None, Some m2 => Some (M2.combine f (@M2.empty _) m2)
        | Some m2, None => Some (M2.combine f m2 (@M2.empty _))
        | Some m1, Some m2 => Some (M2.combine f m1 m2)
      end) m1 m2.

  Lemma gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros A B C f Hf m1 m2 [i1 i2]; unfold get, combine.
    rewrite M1.gcombine; auto.
    case_eq (M1.get i1 m1); intros; simpl; auto.
    case_eq (M1.get i1 m2); intros; simpl; auto.
    rewrite M2.gcombine; auto.
    rewrite M2.gcombine; auto.
    rewrite M2.gempty; auto.
    case_eq (M1.get i1 m2); intros; simpl; auto.
    rewrite M2.gcombine; auto.
    rewrite M2.gempty; auto.
  Qed.

  Lemma combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros A B f g Hf m1 m2; unfold get, combine.
    apply M1.combine_commut.
    clear m1 m2; intros m1 m2.
    destruct m1; destruct m2; auto; apply f_equal.
    apply M2.combine_commut; auto.
    apply M2.combine_commut; auto.
    apply M2.combine_commut; auto.
  Qed.

  (** Enumerating the bindings of a tree. *)
  Definition elements (A: Type) (m:t A) : list (elt * A) :=
    rev (M1.fold (fun l x1 m1 => M2.fold (fun l x2 a => ((x1,x2),a)::l) m1 l) m (@nil _)).

  Module P1 := Tree_Properties(M1).
  Module P2 := Tree_Properties(M2).

  Definition xelements (A: Type) (m:t A) : list (elt * A) :=
    let ll := List.map (fun p =>
                          let '(x1, m1) := p in
                          List.map (fun p => let '(x2, a) := p in ((x1,x2),a))
                                   (M2.elements m1))
                       (M1.elements m)
    in
    List.fold_left (@app _) ll (@nil _).

  Lemma xelements_eq : forall A (m:t A), xelements m = elements m.
  Proof.
    intros; unfold xelements, elements.
    rewrite M1.fold_spec.
    change nil with (rev (nil (A:=M1.elt * M2.elt * A))) at 1.
    generalize (nil (A:=M1.elt * M2.elt * A)).
    induction (M1.elements m); intros; simpl. auto.
    rewrite <- IHl. rewrite M2.fold_spec. f_equal. clear.
    destruct a. simpl.
    revert l0; induction (M2.elements t0); simpl; intro.
    apply app_nil_r.
    destruct a; simpl. rewrite <- IHl. simpl.
    rewrite <- app_assoc. auto.
  Qed.

  Lemma elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    unfold get, elements; intros A m [i1 i2] v.
    case_eq (M1.get i1 m); [idtac| intros H1 H; discriminate].
    intros. apply -> in_rev.
    revert t0 H H0.
    apply (P1.fold_rec _
      (fun m l => forall i1 i2 v  m2,
        M1.get i1 m = Some m2 ->
        M2.get i2 m2 = Some v ->
        In (i1, i2, v) l)); clear i1 i2 v.

    intros m' m'' l H1 H2 i1 i2 v m2 Heq1 Heq2.
    eapply H2; eauto.
    rewrite H1; auto.

    intros i1 i2 v m2 Heq1 Heq2.
    rewrite M1.gempty in *; congruence.

    assert (forall i x m2 l,
      In x l ->
      In x (M2.fold
        (fun (l0 : list (M1.elt * M2.elt * A)) (x2 : M2.elt) (a : A) =>
         (i, x2, a) :: l0) m2 l)).
      intros i x m2 l Hl.
      apply (P2.fold_rec
        (fun l0 x2 a => (i, x2, a) :: l0)
        (fun m2 l' => In x l')); auto with datatypes.

    intros m' l i m2 H1 H2 H3 i1 i2 v m0 Heq1 Heq2.
    rewrite M1.gsspec in Heq1; destruct M1.elt_eq; subst; eauto.
    inv Heq1.
    clear dependent m'.

    generalize i2 v Heq2; clear i2 v Heq2.
    apply (P2.fold_rec (fun l0 x2 a => (i, x2, a) :: l0)
      (fun m2 l => forall i2 v,
           M2.get i2 m2 = Some v ->
           In (i, i2, v) l) l); eauto.
    intros m2 m2' l1 H1 H3 i2 v.
    rewrite <- H1; auto.
    intros i2 v; rewrite M2.gempty; congruence.
    intros m1 a i2 v Heq1 Heq2 Heq3 i2' v'.
    rewrite M2.gsspec; destruct M2.elt_eq; intros T.
    inv T; left; auto.
    right; eauto.
  Qed.

  Lemma elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
        In (i, v) (elements m) -> get i m = Some v.
  Proof.
    unfold elements; intros A m.
    intros. apply in_rev in H. revert i v H.
    apply (P1.fold_rec _
      (fun m l =>
        (forall i v, In (i,v) l -> get i m = Some v))).
    intros m'' m' a Hyp1 Hyp0; auto.
    intros [i1 i2] Hv; unfold get.
    rewrite <- Hyp1 in *; apply (Hyp0 (i1,i2)).
    simpl; intuition.
    intros m1 l i v1 H1 H2 H3.
    apply (P2.fold_rec _
      (fun m l =>
        (forall i0 v, In (i0,v) l -> get i0 (M1.set i v1 m1) = Some v))); auto.
    intros [i1 i2] v Hv.
    unfold get. rewrite M1.gsspec; destruct M1.elt_eq; subst; auto.
    generalize (H3 _ _ Hv); unfold get.
    rewrite H1; congruence.
    generalize (H3 _ _ Hv); unfold get; auto.
    intros m0 a k v0 H H0 H4 [i1 i2] v; unfold get in *.
    simpl; destruct 1.
    inv H5.
    rewrite M1.gss; auto.
    rewrite M1.gsspec; destruct M1.elt_eq; subst.
    generalize (H4 _ _ H5); rewrite M1.gss; auto.
    generalize (H4 _ _ H5); rewrite M1.gso; auto.
  Qed.

  (* Lemma list_norepet_rev: *)
  (*   forall (A : Type) (l : list A), *)
  (*     list_norepet l -> list_norepet (rev l). *)
  (* Proof. *)
  (*   induction l; simpl. auto. *)
  (*   intros. *)
  (*   inv H. apply list_norepet_append; auto. *)
  (*   constructor; auto. constructor. *)
  (*   unfold list_disjoint. repeat intro. destruct H0 as [|[]]. subst. *)
  (*   apply H2. apply in_rev. auto. *)
  (* Qed. *)

  Lemma elements_keys_norepet:
    forall (A: Type) (m: t A),
      list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros A m; rewrite <- xelements_eq.
    unfold xelements.
    assert (list_norepet (List.map fst (@nil ((M1.elt * M2.elt) * A)))) by constructor.
    assert (list_disjoint (List.map (fun (p:(M1.elt * M2.elt) * A) => fst (fst p)) nil)
                          (List.map fst (M1.elements m)))
      by destruct 1.
    revert H H0. generalize (@nil ((M1.elt * M2.elt) * A)).
    generalize (M1.elements_keys_norepet m).
    induction (M1.elements); simpl.
    auto.
    destruct a.
    intros. inv H.
    apply IHl; rewrite ?rev_append_rev, ?map_app, ?map_rev.
    - auto.
    - apply list_norepet_append; auto.
      + apply PTree_Properties.list_norepet_map with (f:=snd).
        rewrite !map_map.
        rewrite list_map_exten with (f:=@fst M2.elt A).
        apply M2.elements_keys_norepet.
        destruct x; auto.
      + rewrite map_map. repeat intro.
        apply list_in_map_inv in H2. destruct H2 as [[] []].
        apply in_map with (f:=fst) in H. rewrite map_map in H.
        apply (f_equal fst) in H3. apply H1 in H3. auto. auto.
        left. subst. auto.
    - rewrite map_map. repeat intro.
      apply in_app in H. destruct H.
      + eapply H1; eauto. right; auto.
      + apply list_in_map_inv in H. destruct H as [[] []].
        subst. subst. auto.
  Qed.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Proof.
  Admitted.
  
  Definition fold (A B: Type) (f: B -> elt -> A -> B) (m: t A) (b:B) : B :=
    M1.fold
      (fun acc x1 m1 => M2.fold (fun acc x2 a => f acc (x1, x2) a) m1 acc) m b.

  Lemma fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. unfold fold, elements.
    rewrite !M1.fold_spec.
    change v with (fold_right (fun p a => f a (fst p) (snd p)) v nil) at 1.
    fold elt. generalize (nil (A:=elt * A)).
    induction (M1.elements m).
    simpl. intros. rewrite <- fold_left_rev_right. rewrite rev_involutive. auto.
    intros. destruct a. simpl. rewrite !M2.fold_spec.
    revert l0. induction (M2.elements t0); simpl. auto.
    intros. rewrite <- IHl0. simpl. auto.
  Qed.

  Definition fold1 (A B: Type) (f: B -> A -> B) (m: t A) (b:B) : B :=
    M1.fold1
      (fun acc m1 => M2.fold1 (fun acc a => f acc a) m1 acc) m b.

  Lemma fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof.
    intros. unfold fold1, elements.
    rewrite M1.fold_spec, M1.fold1_spec.
    change v with (fold_right (fun (p:elt*A) a => f a (snd p)) v nil) at 1.
    fold elt. generalize (nil (A:=elt * A)).
    induction (M1.elements m).
    simpl. intros. rewrite <- fold_left_rev_right. rewrite rev_involutive. auto.
    intros. destruct a. simpl. rewrite M2.fold_spec, M2.fold1_spec.
    revert l0. induction (M2.elements t0); simpl. auto.
    intros. rewrite <- IHl0. simpl. auto.
  Qed.

  Theorem elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.
  Proof.
  Admitted.
End MakeProdTree.

Module  MakeProdMap (M1:MAP) (M2:MAP) <: MAP.

  Definition elt: Type := (M1.elt * M2.elt)%type.

  Lemma elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Proof.
    decide equality.
    apply M2.elt_eq.
    apply M1.elt_eq.
  Qed.

  Definition t (A:Type) : Type := M1.t (M2.t A).

  Definition init (A: Type) (a: A) : t A := M1.init (M2.init a).

  Definition get (A: Type) (x:elt) (m:t A) : A :=
    let (x1,x2) := x in
      M2.get x2 (M1.get x1 m).

  Definition set (A: Type) (x:elt) (v:A) (m:t A) : t A :=
    let (x1,x2) := x in
      M1.set x1 (M2.set x2 v (M1.get x1 m)) m.

  Lemma gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Proof.
    intros A [i1 i2] x; unfold get, init.
    rewrite M1.gi.
    rewrite M2.gi; auto.
  Qed.

  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros A [i1 i2] x m; unfold get, set.
    rewrite M1.gss; rewrite M2.gss; auto.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros A [i1 i2] [j1 j2] x m H; unfold get, set.
    destruct (M1.elt_eq i1 j1); subst.
    rewrite M1.gss; rewrite M2.gso; congruence.
    rewrite M1.gso; auto.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros A i j x m.
    destruct (elt_eq i j); subst.
    apply gss.
    apply gso; auto.
  Qed.

  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros A i j m.
    destruct (elt_eq i j); subst.
    rewrite gss; auto.
    rewrite gso; auto.
  Qed.

  Definition map (A B: Type) (f: A -> B) (m: t A) : t B :=
    M1.map (M2.map f) m.

  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros A B f [i1 i2] m; unfold get, map.
    rewrite M1.gmap; rewrite M2.gmap; auto.
  Qed.

End MakeProdMap.
