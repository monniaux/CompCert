(** Utility lemmas, tactics *)

Require Import Coqlib.
Require Import Maps.
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
Require Import Integers.
Require Ascii.
Require String.
Require Import Relation_Operators.
Require Psatz.
Require Import Permutation.
Require Import Maps2.

(** * Tactics *)
Ltac exploit_dstr x := 
  let Hnew := fresh "Htmp"
    in  exploit x ; eauto ; intros Hnew  ; destruct Hnew as [] ; intuition.

Ltac boolInv :=
  match goal with
  | [ H: _ && _ = true |- _ ] => 
      destruct (andb_prop _ _ H); clear H; boolInv
  | [ H: proj_sumbool _ = true |- _ ] =>
      generalize (proj_sumbool_true _ H); clear H; 
      let EQ := fresh in (intro EQ; try subst; boolInv)
  | _ =>
      idtac
  end.

Ltac revert_arith :=
  repeat
    (match goal with
       | H : Z |- _ => generalize dependent H
       | H : positive |- _ => generalize dependent H
       | H : N   |- _ => generalize dependent H
       | H : nat  |- _ => generalize dependent H
       | H : context[?X] |- _ => match type of X with
          			   | nat => generalize dependent H
                               	   | Z => generalize dependent H
			           | N => generalize dependent H
                          	   | positive => generalize dependent H
				 end
     end	
    ) ; clear ; intros.

Ltac lia := 
  (try revert_arith) ; zify ; unfold Z.succ in * ; Psatz.lia.

(* To be used when building error messages *)
(* Eval compute in (Ascii false false false false true true false false). *)
Fixpoint get_digits (z:Z) (p:positive) : list nat :=
  match p with 
    | xH => nil
    | xO p | xI p =>  
      let digit := (z - ((z/10)*10))%Z in       
        match digit with 
          | Zpos d => (nat_of_P d)::(get_digits (z/10) p)
          | Z0 => O::(get_digits (z/10) p)
          | _ => nil
        end
  end.

Fixpoint rm_zeros l := 
  match l with 
    | nil => nil 
    | O::m => rm_zeros m
    | x::m =>  l
  end.

Definition encode_ascii (n: nat) := (n + 48)%nat.

Fixpoint digits l := 
   match l with 
     | nil => String.EmptyString 
     | d::m => String.String (Ascii.ascii_of_nat (encode_ascii d)) (digits m)
   end.
 
Definition pos_to_string (p:positive) : String.string :=
  let ldigits := rm_zeros (rev (get_digits (Zpos p) p)) in
    digits ldigits.

(** * Utilities on the [option] type *)
Definition get_opt {A B:Type} (f:A->B) (x:option A) : option B :=
  match x with
    | None => None
    | Some a => Some (f a)
  end.

Lemma option_map_some: forall A B (f:A->B) x i, 
 option_map f x = Some i -> exists i', x = Some i'.
Proof.
  intros.
  destruct x; inv H; eauto.
Qed.
Hint Resolve option_map_some.

(** * Properties about [PTree] *)
Lemma add_set_or : forall i j s,
  (PTree.set i tt s) ! j = Some tt -> i=j \/ s ! j = Some tt.
Proof.
  intros.
  rewrite PTree.gsspec in H.
  destruct peq; auto.
Qed.

Lemma xmap_assoc:
  forall (A B C: Type) (f1: positive -> A -> B) (f2: positive -> B -> C) (m: PTree.t A) (i : positive),
    PTree.xmap f2 (PTree.xmap f1 m i) i = 
    PTree.xmap (fun i x => f2 i (f1 i x)) m i.
Proof.
  induction m; intros; destruct i; simpl; auto;
  rewrite IHm1; rewrite IHm2;
  destruct o; simpl; auto.
Qed.

Lemma map_assoc:
  forall (A B C: Type) (f1: positive -> A -> B) (f2: positive -> B -> C) (m: PTree.t A),
    PTree.map f2 (PTree.map f1 m) = 
    PTree.map (fun i x => f2 i (f1 i x)) m.
Proof.
  unfold map; intros; apply xmap_assoc.
Qed.

Require Import DLib.

Lemma append_assoc : forall p1 p2 p3,
  PTree.append p1 (PTree.append p2 p3) = PTree.append (PTree.append p1 p2) p3.
Proof.
  induction p1; simpl; go.
Qed.

Lemma xmap_ext:
  forall (A B: Type) (f1 f2: positive -> A -> B) (m: PTree.t A) (i0 : positive),
    (forall i x, m!i = Some x -> f1 (PTree.append i0 i) x = f2 (PTree.append i0 i) x) ->
    PTree.xmap f1 m i0 = PTree.xmap f2 m i0.
Proof.
  induction m; intros; destruct i0; simpl; auto;
  rewrite IHm1; try rewrite IHm2; auto.
  - destruct o; simpl; try rewrite H; auto.
    generalize (H xH); simpl.
    rewrite PTree.append_neutral_r.
    intros T; auto.
    f_equal.
    rewrite T; auto.
  - intros i x.
    generalize (H (xI i)); simpl.
    rewrite <- append_assoc.
    simpl.
    auto.
  - intros i x.
    generalize (H (xO i)); simpl.
    rewrite <- append_assoc.
    simpl.
    auto.
  - destruct o; simpl; try rewrite H; auto.
    generalize (H xH); simpl.
    rewrite PTree.append_neutral_r.
    intros T; auto.
    f_equal.
    rewrite T; auto.
  - intros i x.
    generalize (H (xI i)); simpl.
    rewrite <- append_assoc.
    simpl.
    auto.
  - intros i x.
    generalize (H (xO i)); simpl.
    rewrite <- append_assoc.
    simpl.
    auto.
  - destruct o; simpl; try rewrite H; auto.
    f_equal.
    generalize (H xH); simpl.
    intros T; rewrite T; auto.
  - intros i x.
    generalize (H (xI i)); simpl.
    auto.
  - intros i x.
    generalize (H (xO i)); simpl.
    auto.
Qed.

Lemma map_ext:
  forall (A B: Type) (f1 f2: positive -> A -> B) (m: PTree.t A),
    (forall i x, m!i = Some x -> f1 i x = f2 i x) ->
    PTree.map f1 m = PTree.map f2 m.
Proof.
  unfold PTree.map; intros.
  apply xmap_ext; auto.
Qed.

Lemma xmap_map1_opt:
  forall (A B: Type) (f: A -> B) (m: PTree.t A) (i: positive),
    PTree.xmap (fun i x => f x) m i = 
    PTree.map1 f m.  
Proof.
  induction m; intros. 
  - destruct i; simpl; auto.
  - destruct i; simpl; auto;
    rewrite IHm1; rewrite IHm2;
    destruct o; simpl; auto.
Qed.

Lemma map1_opt:
  forall (A B: Type) (f: A -> B) (m: PTree.t A),
    PTree.map (fun i x => f x) m = 
    PTree.map1 f m.  
Proof.
  unfold PTree.map; intros. rewrite xmap_map1_opt.
  auto. 
Qed.
  
Lemma map1_assoc:
  forall (A B C: Type) (f1: positive -> A -> B) (f2: B -> C) (m: PTree.t A),
    PTree.map (fun i x => f2 (f1 i x)) m = 
    PTree.map1 f2 (PTree.map f1 m).
Proof.
  intros. 
  erewrite <- map1_opt ; eauto.
  unfold PTree.map.
  rewrite <- xmap_assoc at 1.
  auto. 
Qed.

Lemma PTree_xfold_none : forall (A B:Type) (f:A->positive->B->A) (m:PTree.t B) (x:A) p',
  (forall p, m!p = None) ->
  PTree.xfold f p' m x = x.
Proof.
  induction m; simpl; intros; auto.
  generalize (H xH); simpl; intros; subst.
  rewrite IHm1.
  rewrite IHm2; auto.
  intros; generalize (H (xI p)); simpl; auto.
  intros; generalize (H (xO p)); simpl; auto.
Qed.

Lemma PTree_xfold_same : forall (A B:Type) (f:A->positive->B->A) (m1 m2:PTree.t B) (x y:A) p',
  (forall p, m1!p = m2!p) ->
  x = y ->
  PTree.xfold f p' m1 x = PTree.xfold f p' m2 y.
Proof.
  induction m1; simpl; intros; auto.
  rewrite PTree_xfold_none; auto.
  intros p; rewrite <- H; auto.
  induction p; simpl; auto.
  subst; destruct m2.
  generalize (H xH); simpl; intros; subst.
  repeat rewrite PTree_xfold_none; auto.
  intros p; generalize (H (xO p)); simpl; auto.
  intros p; generalize (H (xI p)); simpl; auto.  
  generalize (H xH); simpl; intros; subst.
  destruct o0.
  apply IHm1_2.
  intros p; generalize (H (xI p)); simpl; auto.
  f_equal.
  apply IHm1_1; auto.
  intros p; generalize (H (xO p)); simpl; auto.
  apply IHm1_2.
  intros p; generalize (H (xI p)); simpl; auto.
  apply IHm1_1; auto.
  intros p; generalize (H (xO p)); simpl; auto.
Qed.

Lemma PTree_fold_same : forall (A B:Type) (f:A->positive->B->A) (m1 m2:PTree.t B) (x:A),
  (forall p, m1!p = m2!p) ->
  PTree.fold f m1 x = PTree.fold f m2 x.
Proof.
  unfold PTree.fold.
  intros; apply PTree_xfold_same; auto.
Qed.

(** * Properties of [Regmap] *)

Lemma val_eqdec: forall (v1 v2:val), {v1 = v2}+{v1 <> v2}.
Proof.
  repeat decide equality.
  apply Int.eq_dec.
  eapply Int64.eq_dec. 
  eapply Float.eq_dec. 
  apply Int.eq_dec.
Qed.
  
Definition regset := Regmap.t val.

Lemma gsregset: forall  (j: reg) (v:val) (m: regset) ,
  (m#j) = v -> (forall r, (m#j <- v)#r = m#r).
Proof.
  intros. case_eq m. intros.
  unfold PMap.set, PMap.get.
  simpl.
  rewrite PTree.gsspec; auto.  
  case (peq j r); intros. rewrite e in * ; simpl in *.
  destruct (peq r r). 
  case_eq (t!r); intros; (unfold PMap.get in *; subst; simpl; rewrite H1; auto).
  elim n ; auto.
  destruct (peq r j); [elim n; auto| reflexivity].
Qed.
  
Lemma regset_copy: forall (rs: PMap.t val) r1 r0 r,
  (rs # r0 <- (rs # r1)) # r0 <- (rs # r1)#r = 
  (rs # r0 <- (rs # r1)) # r.
Proof.
  intros.
  case_eq rs; intros. 
  unfold PMap.set, PMap.get. simpl.
  destruct (t! r1).
  rewrite PTree.gsident; auto. 
  rewrite PTree.gss; auto.
  rewrite PTree.gsident; auto.
  rewrite PTree.gss; auto.
Qed.

Lemma ptree_set_permut: forall r  r0 r1 (v0 v1:val) t ,
  r0 <> r1 ->
  (PTree.set r0 v0 (PTree.set r1 v1 t)) ! r = 
  (PTree.set r1 v1 (PTree.set r0 v0 t)) ! r.
Proof.
  induction r; intros; destruct r0; destruct r1; destruct t; simpl;
    try rewrite <- (gleaf A i); auto; try apply IHr; congruence.
Qed.

Lemma ptree_setset: forall r dst (v1 v2:val) t,
(PTree.set r v2 (PTree.set r v1 t)) ! dst = 
(PTree.set r v2 t) ! dst.
Proof.
  induction r; intros; destruct dst; destruct t; simpl;
    try rewrite <- (gleaf A i); auto; try apply IHr; congruence.
Qed.
  
Lemma regset_permut: forall rs r (v:val) r1 r0,
  r <> r0 ->  r <> r1 ->
  forall dst, (rs # r <- v) # r0 <- (rs # r1) # dst = 
              (rs # r0 <- (rs # r1)) # r <- v  # dst.
Proof.
  intros ; case_eq rs ; intros.
  unfold PMap.get, PMap.set ; simpl.
  destruct (t!r1); rewrite ptree_set_permut; eauto.
Qed.    

Lemma regset_setset: forall rs r (v1 v2:val),
  forall dst, (rs # r <- v1) # r <- v2 # dst = 
              (rs # r <- v2) # dst.
Proof.
  intros ; case_eq rs ; intros.
  unfold PMap.get, PMap.set ; simpl.
  rewrite ptree_setset; eauto.
Qed.    

Definition forall_ptree {A:Type} (f:positive->A->bool) (m:PTree.t A) : bool :=
  PTree.fold (fun (res: bool) (i: positive) (x: A) => res && f i x) m true.

Remark ptree_forall:
  forall (A: Type) (f: positive -> A -> bool) (m: PTree.t A),
  PTree.fold (fun (res: bool) (i: positive) (x: A) => res && f i x) m true = true ->
  forall i x, m!i = Some x -> f i x = true.
Proof.
  intros.
  set (f' := fun (res: bool) (i: positive) (x: A) => res && f i x).
  set (P := fun (m: PTree.t A) (res: bool) =>
              res = true -> m!i = Some x -> f i x = true).
  assert (P m true).
  rewrite <- H. fold f'. apply PTree_Properties.fold_rec.
  unfold P; intros. rewrite <- H1 in H4. auto. 
  red; intros. rewrite PTree.gempty in H2. discriminate.
  unfold P; intros. unfold f' in H4. boolInv. 
  rewrite PTree.gsspec in H5. destruct (peq i k). 
  subst. inv H5. auto.
  apply H3; auto. 
  red in H1. auto. 
Qed.

Lemma forall_ptree_true:
  forall (A: Type) (f: positive -> A -> bool) (m: PTree.t A),
    forall_ptree f m = true ->
    forall i x, m!i = Some x -> f i x = true.
Proof ptree_forall.

(** * PTrees over pairs of positive *)

Module P2Tree : TREE with Definition elt := (positive * positive)%type :=
  MakeProdTree PTree PTree.

Module P2Tree_Properties := Tree_Properties(P2Tree).

Module P2Map : MAP with Definition elt := (positive * positive)%type :=
  MakeProdMap PMap PMap.

Notation "a #2 b" := (P2Map.get b a) (at level 1).
Notation "a ##2 b" := (List.map (fun r => P2Map.get r a) b) (at level 1).
Notation "a #2 b <- c" := (P2Map.set b c a) (at level 1, b at next level).
Notation "a !2 b" := (P2Tree.get b a) (at level 1).
Notation "a !!2 b" := (P2Map.get b a) (at level 1).
Notation p2eq :=  P2Map.elt_eq.

Definition p2eqb (x y:positive * positive) : bool :=
  if p2eq x y then true else false.

Lemma p2eqb_true : forall x y, 
  p2eqb x y = true -> x = y.
Proof.
  unfold p2eqb; intros; destruct p2eq; congruence.
Qed.

Definition forall_p2tree {A: Type} (f: P2Tree.elt -> A -> bool) (m: P2Tree.t A) : bool :=
    P2Tree.fold (fun (res: bool) i (x: A) => res && f i x) m true.

Lemma ptree2_forall:
  forall (A: Type) (f: P2Tree.elt -> A -> bool) (m: P2Tree.t A),
  forall_p2tree f m = true ->
  forall i x, m!2 i = Some x -> f i x = true.
Proof.
  unfold forall_p2tree.
  intros.
  set (f' := fun (res: bool) (i: P2Tree.elt) (x: A) => res && f i x).
  set (P := fun (m: P2Tree.t A) (res: bool) =>
              res = true -> m!2 i = Some x -> f i x = true).
  assert (P m true).
  rewrite <- H. fold f'. apply P2Tree_Properties.fold_rec.
  unfold P; intros. rewrite <- H1 in H4. auto. 
  red; intros. rewrite P2Tree.gempty in H2. discriminate.
  unfold P; intros. unfold f' in H4. boolInv. 
  rewrite P2Tree.gsspec in H5. destruct (P2Tree.elt_eq i k). 
  subst. inv H5. auto.
  apply H3; auto. 
  red in H1. auto. 
Qed.

Lemma gsregset2: forall  (j: (positive * positive)) (v:val) (m: P2Map.t val) ,
  (m#2 j) = v -> (forall r, (m#2 j <- v)#2 r = m#2 r).
Proof.
  intros.
  rewrite P2Map.gsspec.
  destruct p2eq; congruence.
Qed.

Lemma regset_setset2: forall rs r (v1 v2:val),
  forall dst, (rs #2  r <- v1) #2  r <- v2 #2  dst = 
              (rs #2  r <- v2) #2  dst.
Proof.
  intros.
  repeat rewrite P2Map.gsspec.
  destruct p2eq; congruence.
Qed.

Lemma regset_permut2: forall rs r (v:val) r1 r0,
  r <> r0 ->  r <> r1 ->
  forall dst, (rs #2  r <- v) #2  r0 <- (rs #2  r1) #2  dst = 
              (rs #2  r0 <- (rs #2  r1)) #2  r <- v  #2  dst.
Proof.
  intros.
  repeat rewrite P2Map.gsspec.
  repeat destruct p2eq; try congruence.
Qed.

Definition regmap2_optget
    {A: Type} (or: option (positive * positive)) (dfl: A) (rs: P2Map.t A) : A :=
  match or with
  | None => dfl
  | Some r => P2Map.get r rs
  end.

Definition regmap2_optset
    {A: Type} (or: option (positive * positive)) (v: A) (rs: P2Map.t A) : P2Map.t A :=
  match or with
  | None => rs
  | Some r => P2Map.set r v rs
  end.

(** * Lemmas about lists *)
Lemma in_tl_in_cons: forall (A:Type) (l: list A) (a e:A), 
  In e l -> In e (a::l).
Proof.
  intros; constructor 2; auto.
Qed.

Lemma in_hd_in_cons: forall (A:Type) (l: list A) (a:A), 
  In a (a::l).
Proof.
  intros; constructor ; auto.
Qed.

Hint Resolve in_tl_in_cons.
Hint Resolve in_hd_in_cons.

Lemma app_cons_nil : forall (A:Type) (l l': list A) (n1 n2 : A), 
  n1 :: nil = l ++ n2 :: l' ->
  (l = nil) /\ (l' = nil).
Proof.
  intros.
  destruct l.
  intuition.
  simpl in H. inv H ; auto.
  simpl in H.
  inv H.
  eelim app_cons_not_nil ; eauto.
Qed.

Lemma app_cons_help2 : forall (A:Type) (l l': list A) (n0 n1 n2 : A), 
  n0 :: n1 :: nil = l ++ n2 :: l' ->
  ((l = n0::nil) /\ (l' = nil))
  \/ ((l = nil) /\ (l' = n1::nil)).
Proof.
  intros.
  destruct l. simpl in H.
  right ; intuition. inv H; auto.
  inv H.
  exploit app_cons_nil; eauto. intuition. 
  left ; intuition.
  congruence. 
Qed.

Lemma nth_error_app_length {A :Type} : forall l l' (a:A), 
  nth_error (l++a::l') (length l) = Some a.
Proof.
  induction l ; intros; simpl ; auto.
Qed.

Lemma nth_error_app_length2 : forall (A: Type) (l1 l2: list A),
  nth_error (l1 ++ l2) (S (length l1)) = 
  nth_error (l2) 1.
Proof.
  induction l1; intros.
  simpl ; auto.
  simpl length.
  rewrite <- IHl1 ; eauto.
Qed.

Lemma in_nth_error_some : forall (A: Type) (l: list A) (a: A), 
  In a l -> 
  (exists k, nth_error l k = Some a).
Proof.
  induction l ; intros; inv H.
  exists O ; auto. 
  eelim IHl ; eauto ; intros.
  exists (S x) ; auto. 
Qed.

Lemma in_nth_error_app : forall (A: Type) (l l': list A)  (a: A) k,
  In a l' ->
  nth_error (l++l') k = Some a ->
  (k >= length l)%nat ->
  (exists k', (k' <= k)%nat /\ nth_error l' k' = Some a).
Proof.
  induction l ; intros. 
    
  exists k. split ; auto. 
  simpl length in *.
  destruct k.
  inv H1.
  simpl in *.
  exploit IHl ; eauto. lia.
  intros.
  destruct H2 ; intuition.
  exists x ; auto. 
Qed.  

Lemma nth_error_app_gt_in : forall (A: Type) (l l': list A) (a: A) k, 
  nth_error (l ++ l') k = Some a ->
  (k > (length l))%nat ->
  In a l'.
Proof.
  induction l ; intros.
  simpl in *.
  eapply nth_error_in ; eauto.
  simpl in *.
  destruct k.
  lia.
  simpl in *.
  eapply IHl ; eauto. lia.
Qed.

Lemma nth_error_nil_some {A: Type} : forall k (e: A), 
  nth_error nil k = Some e -> False.
Proof.
  intros.
  destruct k ; simpl in H ; inv H.
Qed.

Lemma nth_error_some_length {A: Type} : forall (l: list A) a k, 
  nth_error l k = Some a ->
  (k < List.length l)%nat.
Proof.
  induction l ; intros.
  eelim (@nth_error_nil_some A) ; eauto.
  destruct k; simpl in *.
  omega. 
  exploit IHl ; eauto ; omega.
Qed.

Lemma nth_error_some {A:Type}: forall l k (v:A),
  nth_error l k = Some v ->
  forall dft, nth k l dft = v.
Proof.
  induction l ; intros.
  destruct k; inv H.
  destruct k. simpl in * ;  inv H; auto.
  simpl in *. 
  eapply IHl; eauto.
Qed.

Lemma nth_error_length : forall (A:Type) (l:list A) x, 
  (x < length l)%nat -> exists y, nth_error l x = Some y.
Proof.
  induction l; simpl; intros x Hx.
  apply False_ind; omega.
  destruct x.
  exists a; simpl; eauto.
  elim IHl with x.
  intros y Hy.
  exists y; simpl; auto.
  omega.
Qed.

Lemma nth_error_some_in: forall (A:Type), forall k (l:list A) r,
  nth_error l k = Some r -> In r l.
Proof.
  induction k; intros; destruct l; simpl in *.
  - inv H.
  - inv H; auto.
  - inv H.
  - right; auto.
Qed.

Lemma map_cons_inv {A B:Type} : forall (f:A->B) (l:list A) (l':list B) (b:B), 
  map f l = b :: l' ->
  exists a, exists m, b = (f a) /\ l = a::m /\ l' = map f m.
Proof.
  intros.
  destruct l. inv H. simpl in H.
  inv H. eauto.
Qed.

Lemma map_in {A B:Type}: forall (f:A->B) (l:list A) (a:A), 
  In a l -> In (f a) (map f l).
Proof.
  induction l; intros.
  inv H. simpl in *. 
  destruct H. left; inv H ; auto.
  right. eapply IHl ; eauto.
Qed.  

Lemma map_length {A B : Type} : forall (f : A -> B) (l: list A), 
  List.length l = List.length (map f l).
Proof.
  induction l ; intros ; simpl ; eauto.
Qed.


Lemma nth_error_some_same_length {A B: Type}: forall (l1: list A) (l2: list B) k e, 
  nth_error l1 k = Some e ->
  List.length l1 = List.length l2 ->
  exists e, nth_error l2 k = Some e.
Proof.
  induction l1; intros.
  destruct k ; simpl in * ; inv H.
  destruct k ; simpl in *. 
  destruct l2 ; simpl in *; try congruence.
  inv H0. inv H. eauto.
  destruct l2 ; simpl in *; try congruence.
  inv H0. eauto.  
Qed.
  
Lemma map_in_some {A B :Type} : forall (f:A -> B) l b, 
  In b (map f l) -> 
  exists a, In a l /\ f a = b.
Proof.
  induction l ; intros ; inv H.
  exists a ;  intuition.
  elim (IHl b) ; eauto. 
  intros. exists x ; intuition.
Qed.

Lemma list_map_nth_some {A B : Type} : forall (f: A -> B) l a k, 
  nth_error l k = Some a ->
  nth_error (map f l) k = Some (f a).
Proof.
  induction l ; intros.
  destruct k in H; inv H.
  destruct k.  simpl in *. inv H ; auto.
  simpl in *; eauto. 
Qed.

Lemma fold_left_inv {A : Type} : forall (f: A -> bool) (l: list A) (a : A) (res0:bool), 
    fold_left (fun (res : bool) (i : A) => res && f i) (a::l) res0 = 
    (f a) && fold_left (fun (res : bool) (i : A) => res && f i) l res0.
Proof.
  induction l ; intros.
  simpl. rewrite andb_comm; auto. 
  simpl.
  rewrite <- IHl ; eauto.  simpl. 
  assert (res0 && f a0 && f a = res0 && f a && f a0) by ring. 
  rewrite H. auto.
Qed.    

Lemma list_forall {A: Type}: forall (f: A -> bool) (l: list A), 
  fold_left (fun (res : bool) (i : A) => res && f i) l true = true ->
  forall (i : A), In i l -> f i = true.
Proof. 
  induction l ; intros.
  inv H0.
  rewrite fold_left_inv in H. 
  simpl in H. 
  case_eq (f a); intros. 
  inv H0. auto. rewrite H1 in *.  
  rewrite andb_true_l in H. eapply IHl ; eauto.
  rewrite H1 in *.  boolInv. inv H2. 
Qed. 

Fixpoint forall_list2 {A:Type} (f:A->A->bool) (l1 l2: list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | a1::q1, a2::q2 => f a1 a2 && (forall_list2 f q1 q2)
    | _, _ => false
  end.


(** * Lemmas about [positive] *)

Lemma Ple_Plt_trans:
  forall (p q r: positive), Ple p q -> Plt q r -> Plt p r.
Proof.
  unfold Plt, Ple; intros.
  zify ; omega.
Qed.

Lemma Ple_Plt_succ: forall p1 p2,
  Ple p1 p2 -> Plt p1 (Psucc p2).
Proof.
  intros.
  eapply Ple_Plt_trans ; eauto.
  eapply Plt_succ; eauto.
Qed.

(** * Lemmas about [bool] *)
Lemma negb_false : forall b, negb b = false -> b = true.
Proof.
  destruct b ; auto. 
Qed.

Lemma negb_true : forall b, negb b = true -> b = false.
Proof.
  destruct b ; auto. 
Qed.

Ltac negInv := 
  match goal with 
    | [H : negb _ = true |- _ ] => apply negb_true in H ; negInv
    | [H : negb _ = false |- _ ] => apply negb_false in H ; negInv
    | _ => idtac
  end.

(** * The [nth_okp] predicate *)

Inductive nth_okp {A:Type}: nat -> list A -> Prop :=
  | nth_okp_headO : forall l e, nth_okp 0 (e::l)
  | nth_okp_headS : forall l e n, nth_okp n l -> nth_okp (Datatypes.S n) (e::l).

Lemma nth_okp_exists {A:Type}: forall (l: list A) k, 
  nth_okp k l -> exists v, nth_error l k = Some v.
Proof.
  induction l; intros.
  inv H. 
  destruct k. exists a ; auto.
  simpl in *.  inv H. eapply IHl ; eauto.
Qed.

Lemma nth_okp_nth {A:Type} : forall (l: list A) k e v, 
  nth_okp k l -> 
  nth k l v = e ->
  nth_error l k = Some e.
Proof.
  induction l ; intros; inv H; auto.
  simpl. eapply IHl ; eauto.
Qed.

Lemma nth_okp_length : forall (A B:Type) k (l1:list A),
  nth_okp k l1 -> forall  (l2:list B), length l1 = length l2 -> nth_okp k l2.
Proof.
  induction 1; destruct l2; try constructor; simpl; try congruence.
  inv H0; auto.
Qed.

Lemma length_nth_ok {A: Type} : forall (l: list A) k, 
  (k < List.length l)%nat -> nth_okp k l.
Proof.
  induction l; intros ; simpl in *. 
  inv H. 
  destruct k ; constructor.
  assert (k < List.length l)%nat by omega; eauto.
Qed.

(** * The [inclist] predicate *)
Inductive inclist {A:Type} : list A -> list A -> Prop:=
| inclist_nil : forall l, inclist nil l
| inclist_cons1: forall l1 l2 b, inclist l1 l2 -> inclist l1 (b::l2)
| inclist_cons2: forall l1 l2 a, inclist l1 (a::l2) -> inclist (a::l1) (a::l2).

Lemma inclist_refl {A:Type} : forall (l: list A), inclist l l.
Proof.
  induction l; intros.
  constructor.
  constructor 3. constructor ; auto.
Qed.

Lemma inclist_cons_in {A:Type} : forall l1 l2 (a:A),
  inclist (a :: l2) l1 -> In a l1.
Proof.
  induction l1; intros; inv H.
  exploit IHl1; eauto.
  auto. 
Qed.

Lemma inclist_indu : forall A l2 l1 (a:A), 
  inclist (a::l1) l2 -> inclist l1 l2.
Proof.
  induction l2; intros; inv H.
  exploit IHl2; eauto; intros.
  constructor; auto.
  auto.
Qed.

(** * The [alln] predicate *)
Inductive alln {A:Type} (n:A) : list A -> Prop:=
| alln_nil : alln n nil
| alln_cons: forall m, alln n m -> alln n (n::m).

Lemma alln_is_alln {A:Type}: forall (v' n v:A) l k,
  alln n l ->
  nth_error l k = Some v ->
  nth k l v' = n.
Proof.
  induction l; intros. 
  destruct k; [idtac | simpl in H0] ; inv H0.
  destruct k. simpl in *. inv H0 ; auto.
  inv H; auto.
  simpl in *. 
  exploit IHl; eauto. inv H; auto.
Qed.

Lemma alln_is_alln2 {A:Type}: forall (n:A) l,
  alln n l -> 
  forall k, (exists r, nth_error l k = Some r) -> nth_error l k = Some n.
Proof.
  induction 1; intros.
  destruct H as [x Hx]. 
  destruct k; inv Hx.
  destruct k.  simpl; auto. 
  simpl; auto.
Qed.

Lemma alln_spec {A:Type}: forall (n:A) l, 
  (forall k a, nth_error l k = Some a -> a = n) -> alln n l.
Proof.
  induction l; intros.
  constructor.
  replace a with n.
  constructor. eapply IHl ; eauto.
  intros.
  exploit (H (Datatypes.S k)) ; eauto.
  exploit (H O) ; eauto. simpl ; auto.
Qed.

(** * Additional definitions and properties of lists *)

Lemma list_nth_z_tonat {A: Type} : forall  (l : list A) (n: Z)  (a: A),
list_nth_z l n = Some a ->
n = Z0 \/ (exists p, n = Zpos p).
Proof.
  induction l ; intros.
  inv H. 

  simpl in H.
  destruct (zeq n 0). 
  inv e; auto.
  destruct n; eauto.  
  simpl in H. exploit IHl ; eauto; intros.
  destruct H0.
  lia. 
  destruct H0; inv H0. 
Qed.
  
Lemma arith_utils: forall (n:Z) (n1: nat) , 
   Z.to_nat n = Datatypes.S n1 ->
   n1 =  (Z.to_nat (Zpred n)) .
Proof.
  induction n; intros.
  inv H. 
  rewrite Z2Nat.inj_pred. rewrite H.
  lia. 
  inv H.
Qed.

Lemma arith_utils2: forall (n:Z) (n1: nat)  , 
  n > 0 ->
  n1 =  (Z.to_nat (Zpred n)) ->
  Z.to_nat n = Datatypes.S n1.
Proof.
  induction n; intros.
  inv H.
  rewrite Z2Nat.inj_pred in H0.
  rewrite H0. 
  erewrite NPeano.Nat.lt_succ_pred with O _; eauto.
  destruct p; (simpl; lia).
  inv H.
Qed.
  
Lemma list_nth_z_nth_error {A: Type} : forall  (l : list A) (n: Z) (a: A),
list_nth_z l n = Some a ->
nth_error l (Z.to_nat n) = Some a.
Proof.
  induction l ; intros.
  inv H.
  exploit @list_nth_z_tonat ; eauto.
  intros.
  destruct H0. inv H0.
  simpl in * ; auto.  
  destruct H0. 
  
  simpl in H. case_eq (zeq n 0) ; intros.
  inv H. inv e.
  rewrite H1 in *.
  exploit IHl ; eauto.
  intros.
  case_eq (Z.to_nat n); intros.
  inv H3.  inv H5.  lia.
  simpl. 
  exploit arith_utils; eauto.
  intros. rewrite H4 ; auto.
Qed.

Lemma nth_error_list_nth_z {A: Type} : forall  (l : list A) (n: Z) (a: A),
n >= 0 ->
nth_error l (Z.to_nat n) = Some a ->
list_nth_z l n = Some a.
Proof.
  induction l ; intros.
  eelim @nth_error_nil_some ; eauto.
  destruct n.
  simpl in * ; auto.
  case_eq (Z.to_nat (Zpos p) ) ; intros.
  inv H1. lia. rewrite H1 in *. simpl in H0.
  case_eq (Zpos p); intros. inv H2. 
  exploit arith_utils ; eauto.
  intros.
  exploit arith_utils2 ; eauto. 
  lia. intros.
  inv H3 ; auto.
  exploit (IHl (Zpred (Zpos p0))) ; eauto. 
  unfold Zpred ; lia.
  simpl in *. lia. 
Qed.

Lemma list_nth_z_ge0 {A: Type} : forall (l: list A) (n:Z) (a: A), 
  list_nth_z l n = Some a ->
  n >= 0.
Proof.
  induction l; intros; auto. 
  destruct n ; try lia.
  simpl in H. inv H.
  simpl in H.
  case_eq (zeq n 0) ; intros; rewrite H0 in *. 
  inversion e ; auto.
  lia.
  assert (HH:= IHl (Zpred n) a0 H) ; eauto.
  unfold Zpred in * ; lia.
Qed.  

Lemma list_norepet_app: forall A (l1:list A), list_norepet l1 -> 
  forall l2, list_norepet l2 -> 
    (forall x, In x l1 -> In x l2 -> False) ->
    list_norepet (l1++l2).
Proof.
  induction 1; simpl; intros; auto.
  constructor; eauto with arith.
  intro.
  rewrite (in_app _ _ _) in H3.
  intuition; eauto with datatypes.
Qed.

Lemma list_norepet_rev: forall A (l:list A), list_norepet l -> list_norepet (rev l).
Proof.
  induction 1; simpl.
  constructor.
  apply list_norepet_app; auto.
  repeat constructor.
  simpl; auto.  
  simpl; intuition; subst.
  elim H; apply In_rev; auto.
Qed.

Lemma Permutation_NoDup: forall (A:Type),
  forall (l l': list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; intros.
  constructor.

  inversion H0; subst. constructor; auto.
  red; intro; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.

  inversion H; subst. inversion H3; subst. 
  constructor. simpl. simpl in H2. intuition.
  constructor. simpl in H2. intuition. auto.

  auto.
Qed.

Section FORALL1.

Variable A: Type.
Variable P: A -> Prop.

Inductive list_forall1: list A -> Prop :=
  | list_forall1_nil: list_forall1 nil 
  | list_forall1_cons: forall a al, P a -> list_forall1 al -> list_forall1 (a :: al).

Lemma list_forall1_app: forall a2 a1,
  list_forall1 a1 -> list_forall1 a2 -> 
  list_forall1 (a1 ++ a2).
Proof.
  induction 1; intros; simpl. auto. constructor; auto. 
Qed.

End FORALL1.

Set Implicit Arguments.

Lemma list_forall1_imply:
  forall (A : Type) (P1: A -> Prop) (l: list A),
  list_forall1 A P1 l ->
  forall (P2: A -> Prop),
  (forall v, In v l -> P1 v -> P2 v) ->
  list_forall1 A P2 l.
Proof.
  induction 1; intros.
  constructor.
  constructor. auto with coqlib. apply IHlist_forall1; auto. 
Qed.

Section forall3_ptree.

  Variable A B: Type.
  Variable f: positive -> option A -> option A -> option B -> bool.
  Hypothesis f_none_none: forall p x, f p None None x = true.

  Fixpoint xforall3_l (m : PTree.t A) (m3 : PTree.t B) (i : positive) : bool :=
      match m with
      | PTree.Leaf => true
      | PTree.Node l o r => 
        match m3 with
          | PTree.Leaf => 
            f i o None None && 
            (xforall3_l l PTree.Leaf (PTree.append i (xO xH))) &&
            (xforall3_l r PTree.Leaf (PTree.append i (xI xH)))
          | PTree.Node l3 o3 r3 => 
            f i o None o3 && 
            (xforall3_l l l3 (PTree.append i (xO xH))) &&
            (xforall3_l r r3 (PTree.append i (xI xH)))
        end
      end.

  Lemma xgforall3_l :
    forall i m m3 j,
      xforall3_l m m3 j = true ->
      f (PTree.append j i) (PTree.get i m) None (PTree.get i m3) = true.
  Proof.
    induction i; intros; destruct m; destruct m3; simpl in *; auto;
      repeat rewrite andb_true_iff in *.
    replace (@None B) with (@PTree.get B i PTree.Leaf).
    rewrite (PTree.append_assoc_1 j i); apply IHi; intuition.
    apply PTree.gempty.
    rewrite (PTree.append_assoc_1 j i); apply IHi; intuition.
    replace (@None B) with (@PTree.get B i PTree.Leaf).
    rewrite (PTree.append_assoc_0 j i); apply IHi; intuition.
    apply PTree.gempty.
    rewrite (PTree.append_assoc_0 j i); apply IHi; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
  Qed.

  Fixpoint xforall3_r (m : PTree.t A) (m3 : PTree.t B) (i : positive) : bool :=
      match m with
      | PTree.Leaf => true
      | PTree.Node l o r =>
        match m3 with
          | PTree.Leaf => 
            (f i None o None) && 
            (xforall3_r l PTree.Leaf (PTree.append i (xO xH))) && 
            (xforall3_r r PTree.Leaf (PTree.append i (xI xH)))
          | PTree.Node l3 o3 r3 =>
            (f i None o o3) && 
            (xforall3_r l l3 (PTree.append i (xO xH))) && 
            (xforall3_r r r3 (PTree.append i (xI xH)))
        end
      end.

  Lemma xgforall3_r :
    forall i m m3 j,
      xforall3_r m m3 j = true ->
      f (PTree.append j i) None (PTree.get i m) (PTree.get i m3) = true.
  Proof.
    induction i; intros; destruct m; destruct m3; simpl in *; auto;
      repeat rewrite andb_true_iff in *.
    replace (@None B) with (@PTree.get B i PTree.Leaf).
    rewrite (PTree.append_assoc_1 j i); apply IHi; intuition.
    apply PTree.gempty.
    rewrite (PTree.append_assoc_1 j i); apply IHi; intuition.
    replace (@None B) with (@PTree.get B i PTree.Leaf).
    rewrite (PTree.append_assoc_0 j i); apply IHi; intuition.
    apply PTree.gempty.
    rewrite (PTree.append_assoc_0 j i); apply IHi; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
  Qed.

  Fixpoint xforall3_ptree (m1 m2 : PTree.t A) (m3: PTree.t B) (i : positive) {struct m1} : bool :=
    match m1 with
    | PTree.Leaf => xforall3_r m2 m3 i
    | PTree.Node l1 o1 r1 =>
        match m2 with
        | PTree.Leaf => xforall3_l m1 m3 i
        | PTree.Node l2 o2 r2 => 
          match m3 with
            | PTree.Leaf => 
              (xforall3_ptree l1 l2 PTree.Leaf (PTree.append i (xO xH))) && 
              (f i o1 o2 None) &&
              (xforall3_ptree r1 r2 PTree.Leaf (PTree.append i (xI xH)))
            | PTree.Node l3 o3 r3 => 
              (xforall3_ptree l1 l2 l3 (PTree.append i (xO xH))) && 
              (f i o1 o2 o3) &&
              (xforall3_ptree r1 r2 r3 (PTree.append i (xI xH)))
          end
        end
    end.

  Lemma xgforall3_ptree :
    forall i m1 m2 m3 j,
      xforall3_ptree m1 m2 m3 j = true ->
      f (PTree.append j i) (PTree.get i m1) (PTree.get i m2) (PTree.get i m3) = true.
  Proof.
    induction i; intros; destruct m1; destruct m2; destruct m3; simpl in *; auto;
      repeat rewrite andb_true_iff in *.
    replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
    rewrite (PTree.append_assoc_1 j i); apply xgforall3_r; intuition.
    rewrite (PTree.append_assoc_1 j i); apply xgforall3_r; intuition.
    replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
    rewrite (PTree.append_assoc_1 j i); apply xgforall3_l; intuition.
    rewrite (PTree.append_assoc_1 j i); apply xgforall3_l; intuition.
    replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
    rewrite (PTree.append_assoc_1 j i); apply IHi; intuition.
    rewrite (PTree.append_assoc_1 j i); apply IHi; intuition.
    replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
    rewrite (PTree.append_assoc_0 j i); apply xgforall3_r; intuition.
    rewrite (PTree.append_assoc_0 j i); apply xgforall3_r; intuition.
    replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
    rewrite (PTree.append_assoc_0 j i); apply xgforall3_l; intuition.
    rewrite (PTree.append_assoc_0 j i); apply xgforall3_l; intuition.
    replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
    rewrite (PTree.append_assoc_0 j i); apply IHi; intuition.
    rewrite (PTree.append_assoc_0 j i); apply IHi; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
    rewrite (PTree.append_neutral_r j); auto; intuition.
  Qed.

  Definition forall3_ptree (m1 m2 : PTree.t A) (m3: PTree.t B) : bool :=
    xforall3_ptree m1 m2 m3 xH.

  Lemma gforall3_ptree :
    forall m1 m2 m3, forall3_ptree m1 m2 m3 = true ->
      forall i, f i (PTree.get i m1) (PTree.get i m2) (PTree.get i m3) = true.
  Proof.
    unfold forall3_ptree; intros.
    replace (f i) with (f (PTree.append xH i)).
    eapply xgforall3_ptree; eauto.
    rewrite (PTree.append_neutral_l i); auto.
  Qed.

End forall3_ptree.
Implicit Arguments forall3_ptree [A B].

  Section COMBINE.
    Import PTree.
    Variable A B C: Type.
    Variable f: option A -> option B -> option C.
    Hypothesis f_none_none: f None None = None.

  Fixpoint xcombine_l (m : t A) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)
      end.

  Lemma xgcombine_l :
          forall (m: t A) (i : positive),
          get i (xcombine_l m) = f (get i m) None.
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint xcombine_r (m : t B) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_r l) (f None o) (xcombine_r r)
      end.

  Lemma xgcombine_r :
          forall (m: t B) (i : positive),
          get i (xcombine_r m) = f None (get i m).
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint combine (m1:t A) (m2 : t B) {struct m1} : t C :=
    match m1 with
    | Leaf => xcombine_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l m1
        | Node l2 o2 r2 => Node' (combine l1 l2) (f o1 o2) (combine r1 r2)
        end
    end.

  Theorem gcombine:
      forall m1 m2 (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    induction m1; intros; simpl.
    rewrite gleaf. apply xgcombine_r.
    destruct m2; simpl.
    rewrite gleaf. rewrite <- xgcombine_l. auto. 
    repeat rewrite gnode'. destruct i; simpl; auto.
  Qed.

  End COMBINE.
Implicit Arguments combine [A B C].

(** * Relational operators *)

Notation "R **" := (@clos_refl_trans _ R) (at level 30).
Lemma Rstar_refl : forall A R (i:A), R** i i.
Proof. constructor 2. Qed.

Lemma Rstar_R : forall A (R:A->A->Prop) (i j:A), R i j -> R** i j.
Proof. constructor 1; auto. Qed.
  
Lemma Rstar_trans : forall A (R:A->A->Prop) (i j k:A), 
  R** i j -> R** j k -> R** i k.
Proof. intros A R i j k; constructor 3 with j; auto. Qed.

Hint Resolve Rstar_trans Rstar_refl Rstar_R.
 
Lemma Rstar_left_case : forall A R (i j:A), R** i j ->
  i = j \/ exists k, R i k /\ R** k j.
Proof.  induction 1; eauto. intuition; subst; auto. decompose [ex and] H1 ; eauto. Qed.

Lemma star_eq : forall A (R1 R2:A->A->Prop),
  (forall i j, R1 i j -> R2 i j) ->
  forall i j, R1** i j -> R2** i j.
Proof.
  induction 2.
  econstructor 1; eauto.
  econstructor 2; eauto.
  econstructor 3; eauto.
Qed.
