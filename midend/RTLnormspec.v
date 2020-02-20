(** Abstract specification of RTL normalization *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLnorm.
Require Import Kildall.
Require Import Utils.
 
(** * Reasoning about monadic computations *)

(** The tactics below simplify hypotheses of the form [f ... = OK x s i]
  where [f] is a monadic computation.  For instance, the hypothesis
  [(do x <- a; b) s = OK y s' i] will generate the additional witnesses
  [x], [s1], [i1], [i'] and the additional hypotheses
  [a s = OK x s1 i1] and [b x s1 = OK y s' i'], reflecting the fact that
  both monadic computations [a] and [b] succeeded.
*)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B) 
         (y: B) (s1 s3: state) (i: state_incr s1 s3),
  bind f g s1 = OK y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
Proof.
  intros until i. unfold bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s'; exists s.
  destruct (g a s'); inv H.
  exists s0; auto.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: state) (i: state_incr s1 s3),
  bind2 f g s1 = OK z s3 i ->
  exists x, exists y, exists s2, exists i1, exists i2,
  f s1 = OK (x, y) s2 i1 /\ g x y s2 = OK z s3 i2.
Proof.
  unfold bind2; intros.
  exploit bind_inversion; eauto. 
  intros [[x y] [s2 [i1 [i2 [P Q]]]]]. simpl in Q.
  exists x; exists y; exists s2; exists i1; exists i2; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (Error _ _ = OK _ _ _) =>
      discriminate
  | (ret _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (error _ _ = OK _ _ _) =>
      discriminate
  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _ _) => monadInv1 H
  | (error _ _ = OK _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); try monadInv1 H
  | (?F _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.


Lemma mfold_step {A B : Type}: forall (f: A -> B -> mon B) l b a s1 s2 b' INCR,
  mfold f (a::l) b s1 = OK b' s2 INCR ->
  exists b'' , exists s'', exists INCR'', exists INCR''',
    f a b s1 = OK b'' s'' INCR'' 
    /\ (mfold f l b'' s'' = OK b' s2 INCR''').
Proof.
  induction l ; intros; monadInv H ; simpl. 
  exists b' ; exists s2 ; exists INCR0 ; exists (state_incr_refl s2); auto.
  unfold bind.  exists x ; exists s ; exists INCR0; exists (state_incr_trans s s0 s2 INCR2 INCR3).
  split ; auto. rewrite EQ1; rewrite EQ2; auto. 
Qed.

Lemma step_mfold : forall (A B : Type) (f: A -> B -> mon B)  a b s1 b'' s'' INCR''
  l b' s2 INCR''',
  f a b s1 = OK b'' s'' INCR'' ->
  (mfold f l b'' s'' = OK b' s2 INCR''') ->
  exists INCR, mfold f (a::l) b s1 = OK b' s2 INCR.
Proof.
  intros.
  simpl. unfold bind. rewrite H. rewrite H0.
  eauto.
Qed.

Lemma mfold_unit_step: forall (A: Type) (f: A -> mon unit) l u a s1 s2 INCR,
  mfold_unit f (a::l) s1 = OK u s2 INCR ->
  exists u'' , exists s'', exists INCR'', exists INCR''',
    f a s1 = OK u'' s'' INCR'' 
    /\ (mfold_unit f l s'' = OK u s2 INCR''').
Proof.
  induction l ; intros; monadInv H ; simpl. 
  exists x ; exists s2 ; exists INCR0 ; exists (state_incr_refl s2); auto.
  unfold bind.  exists x ; exists s ; exists INCR0; exists (state_incr_trans s s0 s2 INCR2 INCR3).
  split ; auto. rewrite EQ1; rewrite EQ2; auto. 
Qed.

(** * Monotonicity properties of the state *)
Lemma instr_at_incr:
  forall s1 s2 n i,
  state_incr s1 s2 -> s1.(st_code)!n = Some i -> exists i', s2.(st_code)!n = Some i' /\ ch_succ i' i.
Proof.
  intros. inv H.
  destruct (H2 n); try congruence. 
  inv H; try congruence. 
  rewrite <- H4 in H0 ; inv H0. 
  eauto.
Qed.

Hint Resolve instr_at_incr: rtln.
Hint Resolve state_incr_refl: rtln.

(** The following tactic saturates the hypotheses with
  [state_incr] properties that follow by transitivity from
  the known hypotheses. *)

Ltac saturateTrans :=
  match goal with
  | H1: state_incr ?x ?y, H2: state_incr ?y ?z |- _ =>
      match goal with
      | H: state_incr x z |- _  =>
         fail 1
      | _ =>
         let i := fresh "INCR" in
         (generalize (state_incr_trans x y z H1 H2); intro i;
          saturateTrans)
      end
  | _ => idtac
  end.

(** * Properties of utility functions. *)
Lemma add_nop_at:
  forall s1 s2 incr i n,
  add_nop i s1 = OK n s2 incr -> 
  (s2.(st_code)!n = Some (Inop i)
    /\ (forall pc, pc <> n -> s2.(st_code)!pc = s1.(st_code)!pc)
    /\ s1.(st_code) ! n = None).
Proof.
  intros. monadInv H.
  split. 
  destruct (peq i (st_entry s1)); subst ; monadInv1 H; apply PTree.gss.
  split. 
  intros. destruct (peq i (st_entry s1)); subst ; monadInv1 H; apply PTree.gso; auto.
  destruct (peq i (st_entry s1)); subst ; monadInv1 H. 
  destruct (st_wf s1 (st_nextnode s1)).
  elim (Plt_ne (st_nextnode s1) (st_nextnode s1))  ; eauto.
  auto.
  destruct (st_wf s1 (st_nextnode s1)).
  elim (Plt_ne (st_nextnode s1) (st_nextnode s1))  ; eauto.
  auto.
Qed.
  
Hint Resolve add_nop_at: rtln.

Lemma ins_newsucc_ksucc : forall ins k succ x
(Hins : ins <> (Inop succ)),
nth_error (successors_instr ins) k = Some succ ->
nth_error (successors_instr (ins_newsucc ins x k)) k = Some x.
Proof.
  intros.
  assert (Hk : (k < (List.length (successors_instr ins)))%nat) by (eapply nth_error_some_length ; eauto).
  destruct ins;
  match goal with 
    | [ |- context [Inop _]]   => idtac
    | [ |- context [Icond _ _ _ _]]   => idtac
    | [ |- context [Ijumptable _ _ ]]  => idtac
    | _ =>     try (simpl; destruct k ; simpl; auto);
      try (simpl in H ; simpl in H; inv H); try (eelim @nth_error_nil_some ; eauto)
  end.
  (* Inop *)
  simpl in *. destruct k; simpl in *. inv H ; elim Hins ; auto.
  try (eelim @nth_error_nil_some ; eauto).

  (* Icond *)
  simpl in *. destruct k; simpl in *. auto.
  destruct k ; simpl in *. auto.
  try (eelim @nth_error_nil_some ; eauto).

  (* jumptable  *)
  simpl in *. eapply upd_nth_k ; eauto. 
Qed.

Lemma upd_succ_at:
  forall pc newsucc k s1 s2 incr k',
  upd_succ pc newsucc k s1 = OK k' s2 incr -> 
  (exists i, s1.(st_code)!pc = Some i
    /\ s2.(st_code)!pc = Some (ins_newsucc i newsucc k)
    /\ (forall s,
      (forall s', i <> Inop s') -> 
      (nth_error (successors_instr i) k = Some s) ->
      (nth_error (successors_instr (ins_newsucc i newsucc k)) k = Some newsucc)))
  /\ (forall pc', pc <> pc' -> s1.(st_code) ! pc'  = s2.(st_code)!pc')
  /\ k' = S k.  
Proof.
  unfold upd_succ; intros;
  destruct (@get_proof instruction) in H; destruct x;  inv H.
  
  split. exists i. 
  split; auto. 
  split. simpl; rewrite PTree.gss ; auto. 
  intros; eapply ins_newsucc_ksucc; eauto. 

  split; auto. 
  intros; simpl ; rewrite PTree.gso ; auto. 
Qed.

  
Hint Resolve upd_succ_at: rtln.

Lemma upd_nth_only_k {A: Type} : forall l k k' (x: A), 
  k <> k' -> nth_error (upd_nth l x k) k' = nth_error l k'.
Proof.
  induction l ; intros.
  destruct k ; simpl ; auto.
  destruct k ; simpl ; auto.
  destruct k' ; simpl.  elim H ; auto.
  auto. 
  destruct k' ; auto. 
  simpl ; eapply IHl ; eauto.
Qed.

Lemma ins_newsucc_only_k : forall k' k ins x,
  k <> k' ->
  nth_error (successors_instr (ins_newsucc ins x k)) k' =
  nth_error (successors_instr ins) k'.
Proof.
  intros.  
  destruct ins ; 
    match goal with
      | [ |- context [Ijumptable _ _ ]]   =>   simpl; eapply upd_nth_only_k ; eauto
      | [ |- context [Icond _ _ _ _]]   => 
          simpl; destruct k ; simpl ; auto;
            [(destruct k' ; simpl ; auto ; elim H; auto)
              |destruct k  ; simpl ; auto; (destruct k' ; simpl ; auto) ;  
               (destruct k' ; simpl; [elim H ; auto | destruct k' ; auto])]  
      | _ => destruct k ; simpl ; auto ; (destruct k'  ; simpl ; auto) ; try (elim H ; auto)
  end.
Qed.

Lemma ch_succ_same_length : forall i i', 
  ch_succ i i' ->  length  (successors_instr i) = length (successors_instr i').
Proof. 
  intros; inv H; simpl ; auto.
Qed.

Lemma upd_nth_app {A: Type}: forall (l:list A) a rem x, 
     upd_nth (l ++ a :: rem) x (length l) = (l ++ x :: nil) ++ rem.
Proof.
  induction l ; intros; auto.
  simpl; rewrite IHl ; eauto.
Qed.

Ltac allinv := 
  repeat 
    match goal with 
      | [ H1:   (st_code ?s) ! ?pc = Some _  ,
        H2: (st_code ?s) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   Some _ = (st_code ?s) ! ?pc  ,
        H2: (st_code ?s) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | _ => idtac
    end.

Lemma modif_ksucc_okS : forall is_jp pc a k l s1 k' l' s2 incr,
  modif_ksucc is_jp pc a (k,l) s1 = OK (k',l') s2 incr ->
  k' = S k.
Proof.
  intros.
  unfold modif_ksucc in *.
  destruct (st_code s1) ! pc. 
  destruct i; inv H; auto;
    (destruct (is_jp a); [monadInv H1;  
      exploit upd_succ_at ; eauto ; intuition | inv H1 ; auto]).
  destruct (is_jp a); [monadInv H;  
  exploit upd_succ_at ; eauto; intuition | inv H ; auto].
Qed.

Lemma modif_ksucc_ok_kl1_aux : forall is_jp pc a k l s1 k' l' s2 incr,
  k = List.length l ->
  modif_ksucc is_jp pc a (k,l) s1 = OK (k',l') s2 incr ->
  k' = List.length l'.
Proof.
  intros.
  exploit modif_ksucc_okS ; eauto. intros.
  unfold modif_ksucc in *. inv H1.
  destruct (st_code s1) ! pc. 
  destruct i; inv H0; auto; 
    (destruct (is_jp a); (monadInv H1;  rewrite app_length;  simpl ; lia)).   
  destruct (is_jp a); monadInv H0 ; (rewrite app_length;  simpl ; lia).    
Qed.

Lemma modif_ksucc_ok_kl2_aux : forall is_jp pc a k l s1 k' l' s2 incr,
  k = List.length l ->
  modif_ksucc is_jp pc a (k,l) s1 = OK (k',l') s2 incr ->
  (length l') = ((length l) + 1)%nat.
Proof.
  intros.
  exploit modif_ksucc_okS ; eauto. intros.
  inv H1.
  unfold modif_ksucc in *. 
  destruct (st_code s1) ! pc. 
  destruct i; inv H0; auto; 
    (destruct (is_jp a); (monadInv H1;  rewrite app_length;  simpl ; lia)).   
  destruct (is_jp a); monadInv H0; (  rewrite app_length;  simpl ; lia).
Qed.

(** * Specification of [modif_ksucc] *)
Inductive mks_spec (jp: node -> bool) (code code' : code) 
  (pc :node) (lnew: list node) (k:nat) : Prop :=
| mks_jp : forall ins ins' succ pcnew,
  (code ! pc = Some ins) ->
  (forall succ', ins <> Inop succ') ->
  (nth_error (successors_instr ins) k = Some succ) ->
  (code' ! pc = Some ins') ->
  (ch_succ ins' ins) ->
  (nth_error (successors_instr ins') k = Some pcnew) ->
  (nth_error lnew k = Some pcnew) ->
  (code' ! pcnew = Some (Inop succ)) ->
  mks_spec jp code code' pc lnew k
| mks_njp : forall ins ins' succ,
  (code ! pc = Some ins) ->
  (forall succ', ins <> Inop succ') ->
  (nth_error (successors_instr ins) k = Some succ) ->
  (code' ! pc = Some ins') ->
  (ch_succ ins' ins) ->
  (nth_error (successors_instr ins') k = Some succ) ->
  (nth_error lnew k = Some succ) ->
  mks_spec jp code code' pc lnew k.
  
Lemma modif_ksucc_ok : forall jp pc succ k s1 k' s2 incr ins l l',
  (st_code s1) ! pc = Some ins ->
  (nth_error (successors_instr ins) k = Some succ) ->
  k = length l ->
  modif_ksucc jp pc succ (k,l) s1 = OK (k',l') s2 incr ->
  mks_spec jp (st_code s1) (st_code s2) pc l' k.
Proof.
  intros.
  destruct ins; 
    match goal with
      | [ H : ?code = Some (Inop _ ) |- _ ]   =>
        destruct k;
          [   inv H1; unfold modif_ksucc in *; rewrite H in *; inv H2;  eapply mks_nop ; eauto
            | simpl in *; try (eelim (@nth_error_nil_some node) ; eauto)]
      | [H : ?code = Some (Itailcall _ _ _) |- _ ] => simpl in H0; eelim (@nth_error_nil_some node) ; eauto
      | [H : ?code = Some (Ireturn _ ) |- _ ] => simpl in H0; eelim (@nth_error_nil_some node) ; eauto
      | [H : ?code = Some ?ins |- _ ] => 
  unfold modif_ksucc in *; rewrite H in H2;
  (* build hypotheses *)
    (case_eq (jp succ); intros Hsucc; rewrite Hsucc in *);
    [(monadInv H2; 
      (exploit upd_succ_at ; eauto ; intros);
      (exploit add_nop_at ; eauto ; intros);
      (destruct H1 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]);
      (destruct H2 as [Hx [Huc' Hfx]]);
      (assert (Hinsi : ins = i) by (  exploit (Huc' pc) ; eauto; intro; inv H1 ; congruence); inv Hinsi));
(* constructor *)
    (eapply mks_jp with (pcnew := x) ; eauto);
    [(intros ;  discriminate)
      | (eapply ch_succ_ins_newsucc; eauto)
      | eapply ins_newsucc_ksucc; eauto; discriminate
      | eapply nth_error_app_length ; eauto
      | (rewrite <- Huc ; auto ; intro Hcont; inv Hcont; congruence)]
      |(monadInv H2; eapply mks_njp ; eauto);
        [(intros ; discriminate)
          |(eapply nth_error_app_length ; eauto)]]
    end.
Qed.

Hint Resolve modif_ksucc_ok modif_ksucc_okS : rtln. 

Lemma modif_ksucc_ok2 : forall jp pc succ k s1 k' s2 incr ins l l' pcnew ins',
  (st_code s1) ! pc = Some ins ->
  (st_code s2) ! pc = Some ins' ->
  (nth_error (successors_instr ins) k = Some succ) ->
  (nth_error (successors_instr ins') k = Some pcnew) ->
  (forall k', (k' < k)%nat -> (nth_error (successors_instr ins) k = (nth_error l k))) ->
  k = length l ->
  modif_ksucc jp pc succ (k,l) s1 = OK (k',l') s2 incr ->
  l' = (l++pcnew::nil).
Proof.
  intros.
  exploit (modif_ksucc_ok jp pc succ k s1); eauto; intros. 
  unfold modif_ksucc in H5; rewrite H in *; destruct ins;
  match goal with
    | [ H : ?code = Some (Inop _ ) |- _ ]   =>   inv H5
    | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   =>   inv H5
    | [ H : ?code = Some (Ireturn _) |- _ ]   =>   inv H5
    | [ H : ?code = Some (Icond _ _ _ _) |- _ ]   => idtac
    | [ H : ?code = Some (Ijumptable _ _) |- _ ]   => idtac            
    | [HH : ?code = Some ?ins |- _ ] => 
      try (destruct (jp succ);  monadInv H5;
  [((exploit upd_succ_at ; eauto ; intros); (destruct H4 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
  ((exploit add_nop_at ; eauto ; intros); (destruct H4 as [Hx [Huc' Hfx]]));
  destruct (peq pc x) as [Heq | Hdiff];
    [(inv Heq; rewrite Hfx in H ; inv H)
      | (exploit (Huc' pc) ; eauto);
        (intros; rewrite H4 in Hsi; rewrite Hsi in H; inv H);
        (rewrite Hs2i in H0; inv H0);
        (destruct l;  simpl in H1 ;  [inv H1; simpl in H2; inv H2 ; auto | eelim (@nth_error_nil_some node) ; eauto])]
  |
    (rewrite H in H0 ; inv H0);
    (destruct l;  simpl in H1; [inv H1; simpl in H2; inv H2 ; auto| eelim (@nth_error_nil_some node) ; eauto])])
  end;
  destruct (jp succ);  monadInv H5.
  
  (* Icond jp *)
  ((exploit upd_succ_at ; eauto ; intros); (destruct H4 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
  ((exploit add_nop_at ; eauto ; intros); (destruct H4 as [Hx [Huc' Hfx]]));
  destruct (peq pc x).
  (inv e; rewrite Hfx in H ; inv H).
  (exploit (Huc' pc) ; eauto).
  (intros; rewrite H4 in Hsi; rewrite Hsi in H; inv H).
  (rewrite Hs2i in H0; inv H0).
  simpl in H1.
  destruct l;  simpl in H1. 
  simpl in H2. inv H2 ; auto.
  simpl in H2. destruct l. simpl in H2.  inv H2 ; auto. 
  simpl in H2. eelim (@nth_error_nil_some node) ; eauto.

  (* not a join point *)
  (rewrite H in H0 ; inv H0).
  destruct l;  simpl in H1. 
  inv H1; simpl in H2; inv H2 ; auto. 
  simpl in *. 
  rewrite H1 in H2 ; inv H2 ; auto.

  (* join point *)
  ((exploit upd_succ_at ; eauto ; intros); (destruct H4 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
  ((exploit add_nop_at ; eauto ; intros); (destruct H4 as [Hx [Huc' Hfx]])).
  destruct (peq pc x).
  (inv e; rewrite Hfx in H ; inv H).
  (exploit (Huc' pc) ; eauto).
  (intros; rewrite H4 in Hsi; rewrite Hsi in H; inv H).
  (rewrite Hs2i in H0; inv H0).
  simpl in H1.  simpl in H2.
  eapply (@upd_nth_k node _ _ x) in H1 ; eauto.
  rewrite H2 in H1 ; inv H1; auto.

  (* not a join point *)
  (rewrite H in H0 ; inv H0).
  destruct l;  simpl in H1. 
  destruct l0 ; inv H1.
  simpl in H2; inv H2; auto.
  destruct l0 ; inv H1.
  simpl in H2 ; inv H2; auto.
  rewrite H4 in H1 ; inv H1 ; auto.
Qed.  


Lemma modif_ksucc_unch : forall is_jp pc a k deb s1 k' l' s2 INCR pc' ins
  (Hins : (st_code s1) ! pc' = Some ins)
  (Hmodif : modif_ksucc is_jp pc a (k, deb) s1 = OK (k', l') s2 INCR)
  (Hdiff: pc <> pc'),
  (st_code s2) ! pc' = Some ins.
Proof.
  intros.
  unfold modif_ksucc in Hmodif.
  case_eq ((st_code s1) ! pc) ; intros; rewrite H in *.
  destruct i;
  match goal with
    | [ H : ?code = Some (Inop _ ) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Ireturn _) |- _ ]   =>   inv Hmodif
    | [HH : ?code = Some ?ins |- _ ] =>       
        destruct (is_jp a);  monadInv Hmodif; auto;
          ((exploit upd_succ_at ; eauto ; intros); (destruct H0 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
          ((exploit add_nop_at ; eauto ; intros); (destruct H0 as [Hx [Huc' Hfx]]));
          (destruct (peq pc' x) as [Heq | Hd];
            [ inv Heq;  congruence 
              |(rewrite <- Huc ; eauto); (rewrite Huc' ; eauto)])
  end.
  destruct (is_jp a);  monadInv Hmodif; auto;
    ((exploit upd_succ_at ; eauto ; intros); (destruct H0 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
    ((exploit add_nop_at ; eauto ; intros); (destruct H0 as [Hx [Huc' Hfx]]));
    (destruct (peq pc' x) as [Heq | Hd];
      [ inv Heq;  congruence 
        |(rewrite <- Huc ; eauto); (rewrite Huc' ; eauto)]).
Qed.
  
Lemma modif_ksucc_onlyk : forall jp pc succ k s1 k' s2 incr ins l l'  ins' k'' n
  (Hins: (st_code s1) ! pc = Some ins)
  (Hins': (st_code s2) ! pc = Some ins')
  (Hk: k = length l)
  (Hsucc:   (nth_error (successors_instr ins) k = Some succ))
  (Hmodif: modif_ksucc jp pc succ (k,l) s1 = OK (k',l') s2 incr),
  (k'' <> k)%nat -> nth_error (successors_instr ins) k'' = Some n -> nth_error (successors_instr ins') k'' = Some n.
Proof.
  intros.
  exploit (modif_ksucc_ok jp pc succ k s1); eauto; intros. 
  unfold modif_ksucc in Hmodif; rewrite Hins in *; destruct ins;
  match goal with
    | [ H : ?code = Some (Inop _ ) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Ireturn _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Icond _ _ _ _) |- _ ]   =>   destruct (jp succ);  monadInv Hmodif; (try allinv ; auto)
    | [ H : ?code = Some (Ijumptable _ _) |- _ ]   => destruct (jp succ);  monadInv Hmodif ; (try allinv ; auto)      
    | [HH : ?code = Some ?ins |- _ ] => 
      simpl in *; destruct (length l) ; simpl in *;
        [  inv Hk ; simpl in *; inv Hsucc ;
          destruct k''; [lia | simpl in *; eelim @nth_error_nil_some ; eauto]
          | inv Hk; simpl in Hsucc; eelim @nth_error_nil_some ; eauto]
  end.
    
  (* Icond jp *)
  ((exploit upd_succ_at ; eauto ; intros) ; (destruct H2 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
  ((exploit add_nop_at ; eauto ; intros); (destruct H2 as [Hx [Huc' Hfx]])).
  destruct (peq pc x).
  (inv e; congruence).
  (exploit (Huc' pc) ; eauto).
  (intros; allinv).
  rewrite H2 in *. allinv.

  destruct l ; simpl length in *; simpl. 
  destruct k''. elim H; auto.
  simpl. simpl in Hsucc ; inv Hsucc. simpl in H0 ; auto.
  destruct l ; simpl length in * ; simpl.
  destruct k''. auto.
  simpl. simpl in Hsucc ; inv Hsucc. simpl in H0 ; auto.
  destruct k''. elim H ; auto.
  simpl in H0 ; eelim @nth_error_nil_some ; eauto.
  simpl in Hsucc. eelim @nth_error_nil_some ; eauto.

  (* Ijumptable join point *)
  ((exploit upd_succ_at ; eauto ; intros) ; (destruct H2 as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
  ((exploit add_nop_at ; eauto ; intros); (destruct H2 as [Hx [Huc' Hfx]])).
  destruct (peq pc x).
  (inv e; congruence).
  (exploit (Huc' pc) ; eauto).
  (intros; allinv).
  rewrite H2 in *. allinv. simpl in *.
  erewrite @upd_nth_only_k  ; eauto. 
Qed.  

Lemma modif_ksucc_ok3 : forall is_jp s1 s2 pc ins ins' l a rem k succ' INCR
  (Hins : (st_code s1) ! pc = Some ins)
  (Hins' : (st_code s2) ! pc = Some ins')
  (Hsucc: (successors_instr ins) = (l++a::rem))
  (Hmodif : modif_ksucc is_jp pc a (length l, l) s1 = OK (k, succ') s2 INCR),
  (successors_instr ins') = (succ'++rem).
Proof.
  intros.
  exploit modif_ksucc_okS; eauto. intros ; inv H.
  unfold modif_ksucc in Hmodif; rewrite Hins in *;
  destruct ins; 
  match goal with
    | [ H : ?code = Some (Inop _ ) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Ireturn _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Icond _ _ _ _) |- _ ]   => idtac
    | [ H : ?code = Some (Ijumptable _ _) |- _ ]   => idtac            
    | [HH : ?code = Some ?ins |- _ ] => 
        (simpl in Hsucc;
          (assert (Hnil : l = nil) by (destruct l ; [auto | simpl in Hsucc ; inv Hsucc; eelim app_cons_not_nil; eauto]));
          (inv Hnil; simpl in *; inv Hsucc)); 
        
        (destruct (is_jp a); monadInv Hmodif;
          [  ((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
            ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
            destruct (peq pc x) as [Heq | Hdiff];
              [   (inv Heq; rewrite Hfx in Hins ; inv Hins)
                | (exploit (Huc' pc) ; eauto);
                  (intros; rewrite H in Hsi; rewrite Hsi in Hins; inv Hins);
                  (rewrite Hs2i in Hins'; inv Hins');
                  (simpl ; auto)]
            |   rewrite Hins' in Hins ; inv Hins; simpl ; auto])
  end.
      
  (* Incond *)
  destruct l; simpl in Hsucc. 
  (* nil : first succ *)
  inv Hsucc.
  destruct (is_jp a); monadInv Hmodif;
    [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
      ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
      destruct (peq pc x) as [Heq | Hdiff];
        [   (inv Heq; rewrite Hfx in Hins ; inv Hins)
          | (exploit (Huc' pc) ; eauto);
            (intros; rewrite H in Hsi; rewrite Hsi in Hins; inv Hins);
            (rewrite Hs2i in Hins'; inv Hins');
            (simpl ; auto)]
      |   rewrite Hins' in Hins ; inv Hins; simpl ; auto].
  destruct l ; simpl in Hsucc.
  (* one elmt : second succ *)
  inv Hsucc.
  destruct (is_jp a); monadInv Hmodif;
    [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
      ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
      destruct (peq pc x) as [Heq | Hdiff];
        [   (inv Heq; rewrite Hfx in Hins ; inv Hins)
          | (exploit (Huc' pc) ; eauto);
            (intros; rewrite H in Hsi; rewrite Hsi in Hins; inv Hins);
            (rewrite Hs2i in Hins'; inv Hins');
            (simpl ; auto)]
      |   rewrite Hins' in Hins ; inv Hins; simpl ; auto].
  (* more than one elmt : error case *) 
  inv Hsucc;  eelim app_cons_not_nil; eauto. 
  
  (* Ijumptable *)
  simpl in Hsucc; inv Hsucc.
  destruct (is_jp a); monadInv Hmodif;
    [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
      ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
      destruct (peq pc x) as [Heq | Hdiff];
        [   (inv Heq; rewrite Hfx in Hins ; inv Hins)
          | (exploit (Huc' pc) ; eauto);
            (intros; rewrite H in Hsi; rewrite Hsi in Hins; inv Hins);
            (rewrite Hs2i in Hins'; inv Hins');
            (simpl ; auto)]
      |   rewrite Hins' in Hins ; inv Hins; simpl ; auto].
  eapply upd_nth_app ; eauto.
  rewrite app_ass ; simpl ; auto.
Qed.

Lemma modif_ksucc_succ :  forall is_jp  a l pc s1 s0 k0 INCR0 ins ins'0 deb l0
  (Hins : (st_code s1) ! pc = Some ins)
  (SUCCS : successors_instr ins = deb ++ a :: l)
  (Hins' : (st_code s0) ! pc = Some ins'0)
  (Hmodif : modif_ksucc is_jp pc a (length deb, deb) s1 = OK (k0, l0) s0 INCR0),
  (successors_instr ins'0 = l0 ++ l)
  /\ (exists l', l0 = deb++l').
Proof.
  intros.
  split. 
  exploit modif_ksucc_okS; eauto. intros ; inv H.
  unfold modif_ksucc in Hmodif; rewrite Hins in *;
  destruct ins;
  match goal with
    | [ H : ?code = Some (Inop _ ) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Ireturn _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Icond _ _ _ _) |- _ ]   => idtac
    | [ H : ?code = Some (Ijumptable _ _) |- _ ]   => idtac            
    | [HH : ?code = Some ?ins |- _ ] =>   
      (simpl in SUCCS; exploit app_cons_nil ; eauto);
      (intros; inv H; simpl in SUCCS; inv SUCCS);
      (rewrite <- app_nil_end);
      
      destruct (is_jp a); monadInv Hmodif;  
        [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
          ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
          (rewrite Hs2i in Hins' ; inv Hins');
          (simpl in Hs2i; simpl length in Hnth);
          (exploit (Huc' pc) ; eauto ; (intros Hcont ; inv Hcont ; try congruence));
          (intros; rewrite <- H0 in *; rewrite Hsi in Hins ; inv Hins; auto)
          | rewrite Hins in Hins' ; inv Hins' ; auto]
  end.
  
  (simpl in SUCCS; exploit app_cons_help2 ; eauto).
  intuition; (inv H; inv SUCCS);
    (destruct (is_jp a); monadInv Hmodif;
      [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
        ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
        (rewrite Hs2i in Hins' ; inv Hins');
        (simpl in Hs2i; simpl length in Hnth);
        (exploit (Huc' pc) ; eauto ; (intros Hcont ; inv Hcont ; try congruence));
        (intros; rewrite <- H0 in *; rewrite Hsi in Hins ; inv Hins; auto)
        | rewrite Hins in Hins' ; inv Hins' ; auto]).
  
  simpl in SUCCS. inv SUCCS.
  destruct (is_jp a); monadInv Hmodif;
    [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
      ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
      (rewrite Hs2i in Hins' ; inv Hins');
      (simpl in Hs2i; simpl length in Hnth);
      (exploit (Huc' pc) ; eauto ; (intros Hcont ; inv Hcont ; try congruence));
      (intros; rewrite <- H0 in *; rewrite Hsi in Hins ; inv Hins; auto)
      | rewrite Hins in Hins' ; inv Hins' ; auto].
  simpl. exploit @upd_nth_app ; eauto.
  simpl ; rewrite app_ass ; auto.

  exploit modif_ksucc_okS; eauto. intros ; inv H.
  unfold modif_ksucc in Hmodif; rewrite Hins in *;
  destruct ins;
  match goal with
    | [ H : ?code = Some (Inop _ ) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   => inv Hmodif
    | [ H : ?code = Some (Ireturn _) |- _ ]   =>   inv Hmodif
    | [ H : ?code = Some (Icond _ _ _ _) |- _ ]   => idtac
    | [ H : ?code = Some (Ijumptable _ _) |- _ ]   => idtac            
    | [HH : ?code = Some ?ins |- _ ] =>   
      (simpl in SUCCS; exploit app_cons_nil ; eauto);
      (intros; inv H; simpl in SUCCS; inv SUCCS);
      simpl; eauto
  end.

  (simpl in SUCCS; exploit app_cons_help2 ; eauto).
  intuition; (inv H; inv SUCCS);  
  (destruct (is_jp a); monadInv Hmodif;
      [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
        ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
        (rewrite Hs2i in Hins' ; inv Hins');
        (simpl in Hs2i; simpl length in Hnth);
        (exploit (Huc' pc) ; eauto ; (intros Hcont ; inv Hcont ; try congruence));
        (intros; rewrite <- H0 in *; rewrite Hsi in Hins ; inv Hins; auto)
        | rewrite Hins in Hins' ; inv Hins' ; auto]).
  
  exists (x::nil). simpl ; auto.
  exists (a::nil). simpl ; auto.
  exists (x::nil). simpl ; auto.
  exists (a::nil). simpl ; auto.
  
  
  simpl in SUCCS. inv SUCCS.
  destruct (is_jp a); monadInv Hmodif;
    [((exploit upd_succ_at ; eauto ; intros); (destruct H as [[i [Hsi [Hs2i Hnth]]] [Huc Hk']]));
      ((exploit add_nop_at ; eauto ; intros); (destruct H as [Hx [Huc' Hfx]]));
      (rewrite Hs2i in Hins' ; inv Hins');
      (simpl in Hs2i; simpl length in Hnth);
      (exploit (Huc' pc) ; eauto ; (intros Hcont ; inv Hcont ; try congruence));
      (intros; rewrite <- H0 in *; rewrite Hsi in Hins ; inv Hins; auto)
      | rewrite Hins in Hins' ; inv Hins' ; auto].
  exists (a::nil). simpl ; auto.
Qed.

  
(** Properties of [mfold (modif_ksucc is_jp pc)] *)
Lemma mfold_prop_chsucc : forall is_jp  l0 l pc s1 s2 k k' INCR ins l'
  (H : (st_code s1) ! pc = Some ins)
  (EQ : mfold (modif_ksucc is_jp pc) l (k,l0) s1 = OK (k',l') s2 INCR),
  exists i', (st_code s2) ! pc = Some i' /\ ch_succ ins i'.
Proof.
  induction l ; intros.
  simpl in EQ. monadInv EQ.
  exists ins ; split ; auto with rtln.
  inversion INCR. elim (H1 pc) ; intros ; try congruence ; auto.
  inv H4. rewrite <- H6 in *. inv H. 
  exists i1. split ; eauto with rtln.
  congruence. 
Qed.  
  
Lemma mfold_prop_chsucc2 : forall is_jp  l pc s1 s2 k' INCR ins ins' l'
  (Hins : (st_code s1) ! pc = Some ins)
  (EQ : mfold (modif_ksucc is_jp pc) l (O,nil) s1 = OK (k',l') s2 INCR)
  (Hins' : (st_code s2) ! pc = Some ins'),
  ch_succ ins ins'.
Proof.
  intros.
  exploit (mfold_prop_chsucc is_jp nil l  pc s1 s2 O k' INCR ins) ; eauto.
  intros.
  destruct H as [ins'' [Hcode Hchsucc]].
  rewrite Hcode in *. inv Hins'; auto.
Qed.  

Lemma mfold_prop_kl_aux : forall is_jp pc  lsucc s1 k l k' l' s2 incr,
  k = length l ->
  mfold (modif_ksucc is_jp pc) lsucc (k,l) s1 = OK (k',l') s2 incr ->
  k' = length l'.
Proof.
  induction lsucc; intros.
  simpl in H0. 
  monadInv H0 ; auto.
  monadInv H0.
  destruct x.
  exploit (modif_ksucc_ok_kl1_aux is_jp pc a k l s1 n l0 s INCR) ; eauto.
Qed.

Lemma mfold_prop_kl : forall is_jp pc  lsucc s1 k' l' s2 incr,
  mfold (modif_ksucc is_jp pc) lsucc (O,nil) s1 = OK (k',l') s2 incr ->
  k' = length l'.
Proof.
  intros. 
  assert (O = (@length node nil)) by auto.
  eapply mfold_prop_kl_aux ; eauto.
Qed.

Lemma mfold_prop_length_aux : forall is_jp pc lsucc s1 k l k' l' s2 incr,
  k = length l ->
  mfold (modif_ksucc is_jp pc) lsucc (k,l) s1 = OK (k',l') s2 incr ->
  (length l' = (length lsucc) + (length l))%nat.
Proof.
  induction lsucc; intros.
  simpl in H0. 
  monadInv H0 ; auto.
  generalize H0 ; intros Hnl0.
  monadInv H0.
  destruct x.
  exploit (modif_ksucc_ok_kl2_aux is_jp pc a k l s1 n l0 s INCR) ; eauto.
  intros.
  simpl.
  exploit (IHlsucc s n l0) ; eauto.
  eapply modif_ksucc_ok_kl1_aux  ; eauto. intros.
  lia.
Qed.

Lemma mfold_prop_length : forall is_jp pc  lsucc s1 k' l' s2 incr,
  mfold (modif_ksucc is_jp pc) lsucc (O,nil) s1 = OK (k',l') s2 incr ->
  length lsucc = length l'.
Proof.
  intros. 
  assert (O = (@length node nil)) by auto.
  exploit mfold_prop_length_aux ; eauto. lia. 
Qed.

Lemma mfold_prop_succ_aux : forall is_jp lsucc ins ins' pc  s1 k k' l l' s2 incr,
  (st_code s1) ! pc = Some ins ->
  (successors_instr ins) = l++lsucc ->
  (length l = k) ->
  mfold (modif_ksucc is_jp pc) lsucc (k,l) s1 = OK (k',l') s2 incr ->
  (st_code s2) ! pc = Some ins' ->
  (successors_instr ins') = l'.
Proof.
  induction lsucc; intros.
  
  (* nil *)
  rewrite <- app_nil_end in H0.
  monadInv H2 ; auto.
  rewrite H3 in H ; inv H ; auto.
  
  (* a::l *)
  exploit (mfold_prop_chsucc is_jp l (a::lsucc) pc s1 s2 k k') ; eauto.
  intros. destruct H4 as [i' [Hi' Hchsucc]].
  
  exploit (@mfold_step node) ; eauto.
  rewrite Hi' in H3 ; inv H3.
  intros Htmp. destruct Htmp as [k0 [s' [INCR1 [INCR2 [Hmodif Hmfold']]]]].
  destruct k0 as [k0 succ'].
  assert (exists i, (st_code s')!pc = Some i).
  inversion INCR1.
  elim (H3 pc) ; eauto. intros. congruence.
  intros. inv H6. eauto. congruence.
  destruct H1 as [i Hi].
  exploit (mfold_prop_chsucc is_jp succ' lsucc pc s' s2) ; eauto.
  intros. destruct H1 as [is2 [His2 Hchsucc2]].
  
  assert (length succ' = k0) by (exploit modif_ksucc_ok_kl1_aux ; eauto).
  eapply IHlsucc with (4:= Hmfold') ; eauto.
  exploit (modif_ksucc_ok3 is_jp s1 s' pc ins i); eauto.
Qed.

Lemma mfold_prop_succ : forall is_jp pc ins lsucc s1 k' l' s2 incr,
  (st_code s1) ! pc = Some ins ->
  (successors_instr ins) = lsucc ->
  mfold (modif_ksucc is_jp pc) lsucc (O,nil) s1 = OK (k',l') s2 incr ->
  (exists i, (st_code s2) ! pc = Some i /\ (successors_instr i) = l').
Proof.
  intros.
  exploit mfold_prop_chsucc ; eauto.
  intros. destruct H2 as [i [Hi Hchsucc]].
  exists i. split ; auto.  
  eapply (mfold_prop_succ_aux is_jp lsucc ins i pc s1 O k' nil) ; eauto. 
Qed.

(** * Specification of a normalized program point *)
Inductive norm (is_jp: node -> bool) (code code' : code) (pc: node) : Prop :=
| norm_inop : forall s, code ! pc = Some (Inop s) -> code' ! pc = Some (Inop s) -> norm is_jp code code' pc
| norm_itailcall: forall sig ros args, code ! pc = Some (Itailcall sig ros args) -> code' ! pc = Some (Itailcall sig ros args) -> norm is_jp code code' pc
| norm_ireturn: forall rov, code ! pc = Some (Ireturn rov) -> code' ! pc = Some (Ireturn rov) -> norm is_jp code code' pc
| norm_oth : forall i i', 
  (forall s, i <> Inop s) ->  (forall or, i <> Ireturn or) ->  (forall sig ros args, i <> Itailcall sig ros args) ->
  code ! pc = Some i ->   code' ! pc = Some i' ->   ch_succ i i' -> 
  (forall k succ, nth_error (successors_instr i) k = Some succ ->  mks_spec is_jp code code' pc (successors_instr i') k) ->
  norm is_jp code code' pc.

Lemma mfold_prop_spec_aux_1 : forall is_jp  l pc s1 s2 k k' INCR ins ins' deb news n succ
  (Hins : (st_code s1) ! pc = Some ins)
  (SUCCS: (successors_instr ins) = deb++l)
  (EQ : mfold (modif_ksucc is_jp pc) l (k,deb) s1 = OK (k',news) s2 INCR)
  (Hins' : (st_code s2) ! pc = Some ins')
  (Hdeb: k  = length deb),
  (n < k)%nat ->
  nth_error (successors_instr ins) n = Some succ ->
  nth_error (successors_instr ins') n = Some succ.
Proof.
Admitted.
  (*
  induction l ; intros.
  inv EQ. rewrite Hins in Hins' ; inv Hins' ; auto.
  exploit @mfold_step ; eauto; intros.
  destruct H1 as [x H1].
  destruct H1 as [s0 [INCR0 [INCR1 [Hmodif Hmfold]]]].
  destruct x as [k0 l0]. 
  assert (SPEC : mks_spec is_jp (st_code s1) (st_code s0) pc l0 k).
  eapply modif_ksucc_ok ; eauto. 
  rewrite SUCCS in *. rewrite Hdeb. eapply nth_error_app_length ; eauto.
  inv SPEC; allinv. 
  assert (k0 = length l0) by (eapply modif_ksucc_ok_kl1_aux; eauto).  
  eapply (IHl pc s0 s2 k0 k' INCR1 ins'0 ins' l0 news n) ; eauto. 
  eapply modif_ksucc_succ ; eauto.
  assert (k0 = S (length deb)) by (eapply modif_ksucc_okS ; eauto). lia.
  eapply modif_ksucc_onlyk with (5:= Hmodif) ; eauto.
  rewrite SUCCS ; eapply nth_error_app_length ; eauto.
  lia. 
  
  exploit (IHl pc s0 s2 k0 k' INCR1 ins'0 ins' l0 news n) ; eauto.  
  eapply modif_ksucc_succ ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.
  assert (k0 = S (length deb)) by (eapply modif_ksucc_okS ; eauto). lia.
  eapply modif_ksucc_onlyk with (5:= Hmodif) ; eauto.
  rewrite SUCCS ; eapply nth_error_app_length ; eauto.
  lia.
Qed.   *)

Lemma mfold_prop_spec_succsapp : forall is_jp  l pc s1 s2 k k' INCR ins ins' deb news  
  (Hins : (st_code s1) ! pc = Some ins)
  (Hins' : (st_code s2) ! pc = Some ins')
  (SUCCS: (successors_instr ins) = deb++l)
  (EQ : mfold (modif_ksucc is_jp pc) l (k,deb) s1 = OK (k',news) s2 INCR)
  (Hdeb: k  = length deb),
  exists l', news = deb++l'.
Proof.
  induction l ; intros.
  inv EQ. rewrite Hins in Hins' ; inv Hins' ; eauto.
  exists nil ; simpl ; auto. apply app_nil_end ; auto.

  exploit @mfold_step ; eauto; intros.
  destruct H as [x H].
  destruct H as [s0 [INCR0 [INCR1 [Hmodif Hmfold]]]].
  destruct x as [k0 l0]. 

  inversion INCR0.
  elim (H0 pc) ; intros; try congruence.
  inv H3; try congruence.
  exploit (modif_ksucc_succ is_jp a l pc s1 s0) ; eauto.
  intros.
  destruct H1. destruct H2. inv H2.
  exploit (IHl pc s0 s2) ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.
  intros. destruct H2. inv H2.
  exists (x++x0). rewrite app_ass ; auto.
Qed.
  

Lemma mfold_prop_spec_aux_2 : forall is_jp  l pc s1 s2 k k' INCR ins ins' deb news n succ
  (Hins : (st_code s1) ! pc = Some ins)
  (SUCCS: (successors_instr ins) = deb++l)
  (EQ : mfold (modif_ksucc is_jp pc) l (k,deb) s1 = OK (k',news) s2 INCR)
  (Hins' : (st_code s2) ! pc = Some ins')
  (Hdeb: k = length deb),
  (n >= k)%nat ->
  nth_error (successors_instr ins) n = Some succ ->
  mks_spec is_jp (st_code s1) (st_code s2) pc news n.  
Proof.

  induction l ; intros.

  (* base case *)
  rewrite SUCCS in *; rewrite <- app_nil_end in *.
  exploit (@nth_error_some_length) ; eauto; intros.
  lia. 
  
  (*   a::l induction case *)
  exploit (mfold_prop_succ_aux is_jp (a::l) ins ins' pc s1 k k') ; eauto ; intros.
  
  destruct l.
  exploit @mfold_step ; eauto; intros.
  destruct H2 as [[k0 l0] [s0 [INCR0 [INCR1 [Hmodif Hmfold]]]]].
  inv Hmfold.
  inversion H. inv H1.
  assert (Hnth : nth_error (successors_instr ins) (length deb) = Some a).
  rewrite SUCCS. eapply nth_error_app_length ; eauto.
  rewrite Hnth in H0 ; inv H0.
  eapply modif_ksucc_ok ; eauto.  
  inv H2.
  exploit @nth_error_some_length ; eauto. intros.
  rewrite SUCCS in H2. rewrite app_length in H2.
  simpl in *. lia.
   
  case (eq_nat_dec n k) ; intros. inv e. 

  exploit @mfold_step ; eauto; intros.
  destruct H1 as [[k0 l0] [s0 [INCR0 [INCR1 [Hmodif Hmfold]]]]].
  
  assert (nth_error (successors_instr ins) (length deb) = Some a) by (rewrite SUCCS ; eapply nth_error_app_length ; eauto). 
  assert (mks_spec is_jp (st_code s1) (st_code s0) pc l0 (length deb)). 
  (eapply modif_ksucc_ok with (4:= Hmodif) ; eauto). 
  
  inv H2. rewrite H3 in Hins ; inv Hins.
  econstructor 1 with (pcnew:= pcnew)  ; eauto. 
  (* Po 1 *)
  eapply ch_succ_trans ; eauto. 
  exploit mfold_prop_chsucc ; eauto; intros; destruct H2 as [ii [Hii2 Hsucc]].
  rewrite Hii2 in Hins' ; inv Hins'.
  eauto with rtln. 
  (* Po 2 *)
  rewrite H5 in H0 ; inv H0. clear H.
  exploit (modif_ksucc_succ is_jp a (n0::l) pc s1 s0) ; eauto.
  intros. destruct H. assert (k0 = S (length deb)) by (eapply modif_ksucc_okS ; eauto).
  inv H0. 
  exploit (mfold_prop_spec_aux_1 is_jp (n0::l) pc s0 s2 ) ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.
  
  (* Po 3 *)
  rewrite H5 in H0 ; inv H0. clear H.
  exploit (modif_ksucc_succ is_jp a (n0::l) pc s1 s0) ; eauto.
  intros. destruct H. assert (k0 = S (length deb)) by (eapply modif_ksucc_okS ; eauto).
  inv H0. 
  exploit (mfold_prop_spec_aux_1 is_jp (n0::l) pc s0 s2 ) ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.

  (* Po 4 *)
  inversion INCR1. elim (H11 pcnew); eauto; intros ; try congruence.
  inv H14. symmetry in H16. symmetry in H15. allinv. 
  inv H17 ; auto. 
  congruence.

  (* second case... *)
  set (ll:= (n0::l)) in *.
  allinv. rewrite H1 in *.  inv H5. 
  econstructor 2   ; eauto. 
  (* Po 1 *)
  eapply ch_succ_trans ; eauto. 
  exploit mfold_prop_chsucc ; eauto; intros; destruct H2 as [ii [Hii2 Hsucc]].
  rewrite Hii2 in Hins' ; inv Hins'.
  eauto with rtln. 
  (* Po 2 et 3 *)
  clear H.
  exploit (modif_ksucc_succ is_jp succ0 ll pc s1 s0) ; eauto.
  intros. destruct H. assert (k0 = S (length deb)) by (eapply modif_ksucc_okS ; eauto).
  inv H0. 
  exploit (mfold_prop_spec_aux_1 is_jp ll pc s0 s2 ) ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.

  clear H.
  exploit (modif_ksucc_succ is_jp succ0 ll pc s1 s0) ; eauto.
  intros. destruct H. assert (k0 = S (length deb)) by (eapply modif_ksucc_okS ; eauto).
  inv H0. 
  exploit (mfold_prop_spec_aux_1 is_jp ll pc s0 s2 ) ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.
  
  (* n <> k -> strictly greater *)
  inv H1.
  set (ll:= n0::l) in *.
  rewrite SUCCS in H0.
  assert (Hin : In succ (a::ll)) by (eapply nth_error_app_gt_in ; eauto; lia). 
  exploit in_nth_error_some ; eauto.
  intros. destruct H1.
  
  exploit @mfold_step ; eauto; intros.
  destruct H2 as [[k0 l0] [s0 [INCR0 [INCR1 [Hmodif Hmfold]]]]].
  
  (* instruction at s0 *)
  inversion INCR0 ; allinv.
  elim (H3 pc) ; intros ; try congruence.
  inv H6 ; try congruence.
  symmetry in H8. symmetry in H7 ; inv Hins. allinv.
  
  exploit (IHl pc s0 s2 k0 k' INCR1 i1 ins' l0 (successors_instr ins') n succ) ; eauto; intros.
  eapply modif_ksucc_ok3 ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.
  assert (k0 = S( length deb)) by (eapply modif_ksucc_okS ; eauto).
  
  (* here *) lia.
  eapply modif_ksucc_onlyk with (5:= Hmodif) ; eauto.
  rewrite SUCCS. eapply nth_error_app_length ; eauto.  
  rewrite <- SUCCS in H0 ; auto.
  
  assert (mks_spec is_jp (st_code s1) (st_code s0) pc l0 (length deb)).
  eapply modif_ksucc_ok ; eauto.
  rewrite SUCCS ; eapply nth_error_app_length ; eauto.
  
  assert (nth_error (successors_instr i1) n = Some succ).
  eapply modif_ksucc_onlyk with (5:= Hmodif) ; eauto.
  (rewrite SUCCS; eapply nth_error_app_length ; eauto). 
  rewrite <- SUCCS in *. auto.
  
  inv H4; allinv.
  econstructor 1 ; eauto with rtln.
  rewrite H12 in H6 ; inv H6.

  (* Po 1 *)
  elim (H3 pc) ; try congruence.
  intros. inv H4. 
  symmetry in H10. symmetry in H6. allinv.
  intro Hcont. inv Hcont. inv H9. eelim H11 ; eauto.
  congruence. 
  
  (* PO 2 *)
  rewrite H12 in H6 ; inv H6.
  rewrite <- SUCCS in H0 ; eauto.
  
  (* second case... *)
  econstructor 2   ; eauto with rtln.
  
  (* po1 *)
  elim (H3 pc) ; try congruence.
  intros. inv H4. 
  symmetry in H10. symmetry in H13. allinv. 
  intro Hcont. inv Hcont. inv H9. eelim H11 ; eauto.
  congruence. 
  
  (* PO 2 *)
  rewrite H12 in H6 ; inv H6.
  rewrite <- SUCCS in H0 ; eauto.
Qed.  


Lemma mfold_prop_spec : forall is_jp  l pc s1 s2 kend INCR ins ins' news succ
  (Hins : (st_code s1) ! pc = Some ins)
  (SUCCS: (successors_instr ins) = l)
  (EQ : mfold (modif_ksucc is_jp pc) l (O,nil) s1 = OK (kend,news) s2 INCR)
  (Hins' : (st_code s2) ! pc = Some ins'),
  (forall k,
  nth_error (successors_instr ins) k = Some succ ->
  mks_spec is_jp (st_code s1) (st_code s2) pc news k).  
Proof.
  intros is_jp  l pc s1 s2 kend INCR ins ins' news succ Hins SUCCS EQ Hins'; intros.
  exploit (mfold_prop_spec_aux_2 is_jp l pc s1 s2 O kend INCR ins ins' nil news k) ; eauto.
  lia.
Qed.

Lemma mfold_prop_unch_aux : forall is_jp l pc  pc' s1 s2 INCR ins ins' deb news  k k'
  (HUC : (st_code s1) ! pc' = Some ins')
  (Hins : (st_code s1) ! pc = Some ins)
  (Hmfold : mfold (modif_ksucc is_jp pc) l (k,deb) s1 = OK (k',news) s2 INCR)
  (SUCCS: (successors_instr ins) = deb++l)
  (Hdiff: pc' <> pc)
  (Hdeb: k = length deb),
  (st_code s2) ! pc' = Some ins'.
Proof.
  induction l ; intros.
  (* base case *)
  inv Hmfold; auto.
  
  (* a::l *)
  exploit @mfold_step ; eauto; intros.
  destruct H as [[k0 l0] [s0 [INCR0 [INCR1 [Hmodif Hmfold']]]]].
  
  (* instr at s0 *)
  inversion INCR0 ; allinv.
  elim (H0 pc) ; intros ; try congruence.
  inv H3 ; try congruence.
  symmetry in H4. symmetry in H5 ; inv Hins. allinv.
  exploit (IHl pc pc' s0 s2 INCR1 i1)  ; eauto.
  eapply modif_ksucc_unch ; eauto.
  eapply modif_ksucc_ok3 ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.
Qed.

Lemma mfold_prop_unch : forall is_jp  pc  pc' s1 s2 INCR ins ins' news k'
  (HUC : (st_code s1) ! pc' = Some ins')
  (Hins : (st_code s1) ! pc = Some ins)
  (Hmfold : mfold (modif_ksucc is_jp pc) (successors_instr ins) (O,nil) s1 = OK (k',news) s2 INCR)
  (Hdiff: pc' <> pc),
  (st_code s2) ! pc' = Some ins'.
Proof.
  intros.
  eapply mfold_prop_unch_aux ; eauto.
Qed.

Lemma modif_ksucc_opt_eq_aux : forall is_jp pc succ k k'  s1 s2  i l lend ins ins',
  modif_ksucc_opt is_jp pc succ k s1 = OK k' s2 i ->
  (st_code s1) ! pc = Some ins ->
  (st_code s2) ! pc = Some ins' ->
  k = length l ->
  (successors_instr ins) = l++(succ::lend) ->
  exists newsucc, exists i', 
    modif_ksucc is_jp pc succ (k,l) s1 = OK (k',l++(newsucc::nil)) s2 i'.
(*     /\ (successors_instr ins') = l++(newsucc::lend).     *)
Proof.
  intros.
  unfold modif_ksucc_opt, modif_ksucc in *.
  rewrite H0  in *. 
  
  
  (destruct ins) ;   (try inv H);
  (destruct (is_jp succ);
    [ ( monadInv H5);
      unfold bind ; rewrite EQ; rewrite EQ1; simpl;
        exists x ; simpl ; eauto
      | ( monadInv H5); unfold ret;
        exists succ ; simpl;  eauto]). 
  Qed.

Lemma modif_ksucc_opt_eq : forall is_jp pc succ k k'  s1 s2  i l lend ins ins',
  modif_ksucc_opt is_jp pc succ k s1 = OK k' s2 i ->
  (st_code s1) ! pc = Some ins ->
  (st_code s2) ! pc = Some ins' ->
  k = length l ->
  (successors_instr ins) = l++(succ::lend) ->
  exists newsucc, exists i', 
    modif_ksucc is_jp pc succ (k,l) s1 = OK (k',l++(newsucc::nil)) s2 i'
    /\ (successors_instr ins') = l++(newsucc::lend).
Proof.
  intros.
  exploit modif_ksucc_opt_eq_aux ; eauto.
  intros [newsucc [i' Hmodif]]. inv H3.
  exploit (modif_ksucc_ok3 is_jp s1 s2) ; eauto.
  rewrite app_ass. simpl app.
  intros ; eauto.
Qed.
  
Lemma mfold_modif_ksucc_opt_eq_aux : forall is_jp pc succs k l k' s1 s2 i incr,
  mfold (modif_ksucc_opt is_jp pc) succs k s1 = OK k' s2 incr ->
  (st_code s1) ! pc = Some i ->
  (successors_instr i) = l++succs ->
  k = length l ->
  exists l', exists i', mfold (modif_ksucc is_jp pc) succs (k,l) s1 = OK (k',l') s2 i'.
Proof.
  induction succs ; intros.

  inv H. exists l. 
  exists (state_incr_refl s2). simpl ; unfold ret ; auto.
  
  exploit @mfold_step ; eauto; intros.
  destruct H3 as [ x [s0 [INCR0 [INCR1 [Hmodif Hmfold']]]]].
  
  (* instr at s0 *)
  inversion INCR0 ; allinv.
  elim (H4 pc) ; intros ; try congruence.
  inv H7 ; try congruence.
  symmetry in H8. symmetry in H9 ; inv H0. allinv.
  
  exploit modif_ksucc_opt_eq ; eauto.
  intros [l0 [incr' [Hmodif' Hsucc]]].
  
  exploit (IHsuccs x (l++l0::nil)) ; eauto.
  eapply modif_ksucc_ok3 ; eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.  
  intros [l' [i' Hmfold]].
  
  exists l'. 
  eapply step_mfold ; eauto.
Qed.

Lemma mfold_modif_ksucc_opt_eq : forall ins is_jp pc k' s1 s2  i ,
  (st_code s1) ! pc = Some ins ->
  mfold (modif_ksucc_opt is_jp pc) (successors_instr ins) O s1 = OK k' s2 i ->
  exists l', exists i', mfold (modif_ksucc is_jp pc) (successors_instr ins) (O,nil) s1 = OK (k',l') s2 i'.
Proof.
  intros.
  eapply mfold_modif_ksucc_opt_eq_aux ; eauto.  
Qed.

Lemma add_nop_after_ins_opt_eq : forall is_jp pc ins s1 s2 incr,
  (st_code s1) ! pc = Some ins ->
  add_nop_after_instruction_opt is_jp (pc,ins) s1 = OK tt s2 incr ->
  exists incr', add_nop_after_instruction is_jp (pc,ins) s1 = OK tt s2 incr'.
Proof.
  intros.
  unfold add_nop_after_instruction_opt, add_nop_after_instruction in *.
  destruct ins;  
    match goal with
      | [ H : ?code = Some (Inop _ ) |- _ ]   => eauto
      | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   => eauto
      | [ H : ?code = Some (Ireturn _) |- _ ]   => eauto
      | [HH : ?code = Some ?ins |- _ ] =>   (monadInv H0); (destruct x);
  (unfold bind); (exploit mfold_modif_ksucc_opt_eq ; eauto);
  (intros);
  (destruct H0 as [l' [i' H0]]; rewrite H0; simpl ; eauto)
    end.
Qed.

(** * Correctness of [add_nop_after_instruction]  *)
Lemma add_nop_after_ins : forall is_jp pc ins s1 s2 incr,
  (st_code s1) ! pc = Some ins ->
  add_nop_after_instruction is_jp (pc,ins) s1 = OK tt s2 incr ->
  norm is_jp (st_code s1) (st_code s2) pc.
Proof.
  intros.
  unfold add_nop_after_instruction in H0. 
  destruct ins; 
    match goal with
      | [ H : ?code = Some (Inop _ ) |- _ ]   => inv H0; econstructor 1 ; eauto
      | [ H : ?code = Some (Itailcall _ _ _) |- _ ]   => inv H0; econstructor 2 ; eauto
      | [ H : ?code = Some (Ireturn _) |- _ ]   =>   inv H0; econstructor 3; eauto
      | [HH : ?code = Some ?ins |- _ ] => 
          (monadInv1 H0;  destruct x);
          (eelim (mfold_prop_chsucc) ; eauto ; intros);
          (destruct H0 as [Hx Hchsucc]; inv H);
          (econstructor 4; eauto; (try (intros ; discriminate)) ; intros);
          (exploit mfold_prop_spec ; eauto ; intros);  
          (exploit_dstr mfold_prop_succ ; eauto);
          (rewrite H3 in Hx ; inv Hx; auto)
    end.
Qed.

Lemma add_nop_unch : forall is_jp pc i pc' s1 s2 INCR ins
  (Han: add_nop_after_instruction is_jp (pc,i) s1 = OK tt s2 INCR)
  (Hins: (st_code s1) ! pc = Some i)
  (HUC : (st_code s1) ! pc' = Some ins)
  (Hdiff: pc <> pc'),
  (st_code s2) ! pc' = Some ins.
Proof.
  intros.
  unfold add_nop_after_instruction in Han.
  case_eq i ; intros ; rewrite H in * ; (try monadInv Han ; eauto);
  destruct x; eapply mfold_prop_unch with (3:= EQ); eauto.  
Qed.

(** * Specification for the entry point of the generated function *)
Inductive reach_nops (code : code) : node -> node -> list node -> Prop :=
| rp_nil : forall pc pc', 
  code ! pc = Some (Inop pc') -> 
  reach_nops code pc pc' nil
| rp_cons : forall pc0 pc1 pc2 l, 
  reach_nops code pc1 pc2 l -> 
  code ! pc0 = Some (Inop pc1) -> 
  reach_nops code pc0 pc2 (pc1::l).  

Lemma rp_nop : forall code l n1 n2, 
  reach_nops code n1 n2 l ->
  exists s, code ! n1 = Some (Inop s).
Proof.
  induction 1.
  eauto.
  eelim IHreach_nops ; eauto.
Qed.

Lemma rp_nop_1 : forall l code n1 n2 a, 
  reach_nops code n1 n2 l ->
  In a l -> 
  exists s, code ! a = Some (Inop s).
Proof.
  induction 1 ; intros.
  inv H0.
  inv H1.
  inv H; eauto.
  eelim IHreach_nops ; eauto.
Qed.
  
Lemma rp_nop_2 : forall l code n1 n2 nentry i,
  (forall a, In a l -> a <> n2) ->
  n1 <> n2 ->
  reach_nops code n1 nentry l ->
  reach_nops (PTree.set n2 i code) n1 nentry l.
Proof.
  induction 3 ; intros.
  constructor ; auto.
  rewrite PTree.gso ; auto.
  
  constructor 2 ; eauto.
  rewrite PTree.gso ; eauto.
Qed.
  
Lemma add_nop_nentry : forall s1 s2 incr i n aux nentry,
  add_nop i s1 = OK n s2 incr -> 
  reach_nops (st_code s1) (st_entry s1) nentry aux ->
  exists aux', reach_nops (st_code s2) (st_entry s2) nentry aux'.
Proof.
  intros.
  inv H0.
  monadInv H.
  case (peq i (st_entry s1)); intros ; subst.  
  rewrite peq_true in *.
  inv H ; simpl. 
  exists ((st_entry s1)::nil). 
  econstructor 2 ; eauto.
  econstructor 1 ; eauto.
  rewrite PTree.gso ; eauto.
  elim (st_wf s1 (st_entry s1)) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.
  rewrite PTree.gss ; auto.
  
  rewrite peq_false in *; auto.
  inv H ; simpl.
  exists nil.
  constructor ; auto.
  rewrite PTree.gso ; eauto.
  elim (st_wf s1 (st_entry s1)) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.

  monadInv H.
  case (peq i (st_entry s1)); intros ; subst.  
  rewrite peq_true in *.
  inv H ; simpl. 
  
  exists ((st_entry s1)::pc1::l). 
  econstructor 2 ; eauto.
  econstructor 2 ; eauto.
  eapply rp_nop_2 ; eauto.
  intros.
  exploit rp_nop_1 ; eauto.
  intros. destruct H0.
  elim (st_wf s1 a) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.
  exploit rp_nop ; eauto. intros. destruct H.
  elim (st_wf s1 pc1) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.
  
  
  rewrite PTree.gso ; eauto.
  elim (st_wf s1 (st_entry s1)) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.
  rewrite PTree.gss ; auto.

  rewrite peq_false in *; auto.
  inv H ; simpl.
  exists (pc1::l).
  econstructor 2 ; eauto.
  
  eapply rp_nop_2 ; eauto.
  intros.
  exploit rp_nop_1 ; eauto.
  intros. destruct H0.
  elim (st_wf s1 a) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.
  exploit rp_nop ; eauto. intros. destruct H.
  elim (st_wf s1 pc1) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.

  rewrite PTree.gso ; eauto.
  elim (st_wf s1 (st_entry s1)) ; eauto.
  intros.    
  intro Hcont. rewrite  Hcont in *. eelim Plt_ne ; eauto.
  intros. congruence.
Qed.

Lemma rp_nop3 : forall aux code n1 n2 nentry i, 
  reach_nops code n1 nentry aux ->
  code ! n2 = Some i ->
  reach_nops (PTree.set n2 i code) n1 nentry aux.
Proof.
  induction aux ; intros.
  inv H.
  constructor 1 ; auto.
  case (peq n1 n2) ; intros.
  inv e. rewrite PTree.gss ; eauto. congruence.
  rewrite PTree.gso ; eauto.
  
  constructor 2 ; auto.
  eapply IHaux ; eauto.
  inv H ; auto.
  inv H.
    case (peq n1 n2) ; intros.
  inv e. rewrite PTree.gss ; eauto. congruence.
  rewrite PTree.gso ; eauto.
Qed.

Lemma rp_nop4 : forall aux code n1 n2 nentry i, 
  reach_nops code n1 nentry aux ->
  (PTree.set n2 i code) ! n1 = code ! n1 ->
  (forall a, In a aux -> (PTree.set n2 i code) ! a = code ! a) ->
  reach_nops (PTree.set n2 i code) n1 nentry aux.
Proof.
  induction aux ; intros.
  inv H.
  constructor 1 ; auto.
  rewrite H2 in H0 ; auto.
  
  constructor 2 ; auto.
  eapply IHaux ; eauto.
  inv H ; auto. 
  inv H ; auto. rewrite H7 in H0 ; auto.
Qed.

Lemma upd_succ_nentry:
  forall pc newsucc k s1 s2 incr k' s aux,
  upd_succ pc newsucc k s1 = OK k' s2 incr -> 
  reach_nops (st_code s1) (st_entry s1) s aux ->
  exists aux', reach_nops (st_code s2) (st_entry s2) s aux'.
Proof.
  unfold upd_succ; intros.
  destruct (@get_proof instruction) in H; destruct x ; inv H.
  simpl. 
  case (peq pc (st_entry s1)) ; intros.
  inv e0.
  exists aux. eapply rp_nop3 ; eauto.
  exploit rp_nop ; eauto.
  intros. destruct H. allinv.
  simpl. destruct k ; auto.
  
  inversion incr; simpl in *.
  exploit rp_nop ; eauto. intros. destruct H4.  
  elim (H1 (st_entry s1)) ; intros ; try congruence.
  inv H5; try congruence. symmetry in H6 ; symmetry in H7 ; allinv.
  inv H8. exists aux. 
  eapply rp_nop4 ; eauto.
  rewrite <- H4 in H6 ; auto.
  intros.
  exploit rp_nop_1 ; eauto.
  intros. destruct H3.
  elim (H1 a) ; intros ; try congruence.
  inv H5 ; try congruence.
  symmetry in H7 ; symmetry in H8 ; allinv.
  inv H9 ; auto.
Qed.  

Lemma modif_ksucc_ok_entry : forall is_jp pc a k l s1 k' l' s2 incr nentry aux,
  modif_ksucc is_jp pc a (k,l) s1 = OK (k',l') s2 incr ->
  (reach_nops (st_code s1) (st_entry s1) nentry aux) ->
  exists auxnops, reach_nops (st_code s2) (st_entry s2) nentry auxnops.  
Proof.
  intros.
  unfold modif_ksucc in *;
  (destruct (st_code s1) ! pc).
  (destruct i; inv H; auto);
  (destruct (is_jp a);  
    monadInv H2; auto ;
    [((exploit add_nop_nentry ; eauto; intros);
    (destruct H; (exploit upd_succ_nentry ; eauto)))
    | exists aux ; auto]).
  (destruct (is_jp a);  
    monadInv H; auto ;
    [((exploit add_nop_nentry ; eauto; intros);
    (destruct H; (exploit upd_succ_nentry ; eauto)))
    | exists aux ; auto]).
Qed.
  
Lemma mfold_prop_entry_aux : forall is_jp l pc s1 s2 INCR ins  deb news  k k' nentry aux
  (Hins: (st_code s1) ! pc = Some ins)
  (Hmfold : mfold (modif_ksucc is_jp pc) l (k,deb) s1 = OK (k',news) s2 INCR)
  (SUCCS: (successors_instr ins) = deb++l)
  (Hdeb: k = length deb),
  (reach_nops (st_code s1) (st_entry s1) nentry aux) ->
  exists nopsaux, reach_nops (st_code s2) (st_entry s2) nentry nopsaux.
Proof.
  induction l ; intros.
  (* base case *)
  inv Hmfold; auto.
  exists aux ; auto.
  
  (* a::l *)
  exploit  @mfold_step ; eauto; intros.
  destruct H0 as [ [k0 l0] [s0 [INCR0 [INCR1 [Hmodif Hmfold']]]]].
  
  (* instr at s0 *)
  inversion INCR0 ; allinv.
  elim (H1 pc) ; intros ; try congruence.
  inv H4 ; try congruence.
  symmetry in H5. symmetry in H6 ; inv Hins. allinv.
  
  exploit modif_ksucc_ok_entry ; eauto.
  intros. destruct H2.
  
  exploit (IHl pc s0 s2 INCR1 i1)  ; eauto.
  eapply modif_ksucc_ok3 with (4:= Hmodif); eauto.
  eapply modif_ksucc_ok_kl1_aux ; eauto.
Qed.

Lemma mfold_prop_entry : forall is_jp  l pc s1 s2 kend INCR ins  news  nentry aux
  (Hins : (st_code s1) ! pc = Some ins)
  (SUCCS: (successors_instr ins) = l)
  (EQ : mfold (modif_ksucc is_jp pc) l (O,nil) s1 = OK (kend,news) s2 INCR)
  (Hins' : reach_nops (st_code s1) (st_entry s1) nentry aux),
  exists nopsaux, reach_nops (st_code s2) (st_entry s2) nentry nopsaux.
Proof.
  intros.
  exploit (mfold_prop_entry_aux is_jp l pc s1 s2 INCR) ; eauto.
Qed.

Lemma add_nop_prop_entry : forall is_jp  pc ins s1 s2 nentry INCR aux
  (Hins : (st_code s1) ! pc = Some ins)
  (Han: add_nop_after_instruction is_jp (pc,ins) s1 = OK tt s2 INCR),
  reach_nops (st_code s1) (st_entry s1) nentry aux ->
  exists aux', reach_nops (st_code s2) (st_entry s2) nentry aux'.  
Proof.
  intros.
  unfold add_nop_after_instruction in Han;
    case_eq ins ; intros ; rewrite H0 in *; (try monadInv Han ; eauto);
      ((destruct x);
        (eapply mfold_prop_entry with (3:= EQ) ; eauto)).
Qed.  

Lemma mfold_add_nop_unch : forall is_jp elts s1 u s2 INCR  pc ins, 
  (forall ins, ~ In (pc,ins) elts) ->
  (st_code s1) ! pc = Some ins ->
  list_norepet (map (@fst node instruction) elts) ->
  (forall pc ins, In (pc,ins) elts -> (st_code s1) ! pc = Some ins) ->
  mfold_unit (add_nop_after_instruction is_jp) elts s1 = OK u s2 INCR ->
  (st_code s2) ! pc = Some ins.
Proof.
  induction elts ; intros.
  simpl in H3. inv H3; auto.
  
  exploit mfold_unit_step ; eauto.
  intros. destruct H4 as [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
  destruct u'.
  
  exploit (IHelts s0) ; eauto.
  intros. intro Hcont. eelim H ; eauto.
  
  destruct a.
  exploit (add_nop_unch is_jp p i pc) ; eauto.
  intro. inv H4. eelim H ; eauto.
  
  inv H1 ; auto.

  intros.
  destruct (peq pc pc0).
  inv e. eelim H ; eauto.
  destruct a.
  exploit (H2 pc0 ins0) ; eauto.
  intros.
  exploit (add_nop_unch is_jp p i pc0) ; eauto.
  intro.  inv H5.
  
  assert (In (pc0,i) ((pc0,i)::elts)) by (econstructor ; eauto).
  inv H1. elim H9. 
  replace (pc0) with (fst (pc0,ins0)) by auto. 
  eapply in_map ; eauto.
Qed.

Lemma mfold_unit_prop_entry : forall is_jp l s1 s2 INCR nentry pc ins aux,
  (st_code s1) ! pc = Some ins ->
  list_norepet (map (@fst node instruction) l) ->
  (forall pc ins, In (pc,ins) l -> (st_code s1) ! pc = Some ins) ->
  mfold_unit (add_nop_after_instruction is_jp) l s1 = OK tt s2 INCR ->
  reach_nops (st_code s1) (st_entry s1) nentry aux ->
  exists aux', reach_nops (st_code s2) (st_entry s2) nentry aux'.
Proof.
  induction l ; intros ; inv H2.
  exists aux. auto.
    
  exploit mfold_unit_step ; eauto.
  intros. destruct H2 as [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
  destruct u'.
  destruct a.
  
  inv H0.
  exploit (add_nop_prop_entry is_jp n i) ; eauto.
  intros. destruct H0.  
    
  inversion INCR0.
  eelim (H4 pc) ; eauto ; try congruence.
  intros. inv H10. symmetry in H11 ; allinv. symmetry in H12. allinv.
  eapply (IHl s0 s2 INCR1 nentry pc) ; eauto.
  intros. 

  exploit (H1 pc0 ins) ; eauto.
  intros. rewrite <- H9.
  exploit add_nop_unch ; eauto.
  intro. inv H10.
  replace (pc0) with (fst (pc0,ins)) in H6 by auto. 
  eapply in_map in H8 ; eauto.
  congruence.
  congruence.
Qed.

Lemma mfold_add_nop_spec : forall is_jp elts s1 u s2 INCR  pc ins, 
  list_norepet (map (@fst node instruction) elts) ->
  In (pc,ins) elts ->
  (st_code s1) ! pc = Some ins ->
  (forall pc ins, In (pc,ins) elts -> (st_code s1) ! pc = Some ins) ->
  mfold_unit (add_nop_after_instruction is_jp) elts s1 = OK u s2 INCR ->
  norm is_jp (st_code s1) (st_code s2) pc.
Proof.
  induction elts ; intros ; inv H0.
  
  exploit mfold_unit_step ; eauto.
  intros. destruct H0 as [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
  destruct u'.
  exploit add_nop_after_ins ; eauto; intros.
  simpl in H ; inv H.
  
  inversion INCR0.
  elim (H4 pc) ; intros ; try congruence.
  inv H9 ; try congruence.
  symmetry in H10. symmetry in H11. allinv.
  exploit (mfold_add_nop_unch is_jp elts s0) ; eauto.
  intros. intro. elim H6.
  replace pc with (fst (pc,ins)) by auto.
  eapply in_map ; eauto.
  
  intros.
  destruct (peq pc pc0).
  inv e. elim H6 ; eauto. replace (pc0) with (fst (pc0,ins)) by auto. 
  eapply in_map ; eauto.
  
  exploit (H2 pc0 ins) ; eauto. 
  intros.
  exploit (add_nop_unch is_jp pc i2 pc0) ; eauto.
  intros.
  
  inv H0; allinv. 
  econstructor ; eauto.
  econstructor 2 ; eauto.
  econstructor 3 ; eauto.
  econstructor 4 ; eauto.
  
  intros.
  exploit H16 ; eauto; intros.
  inv H13 ; allinv.
  
  rewrite H0 in H18 ; inv H18.
  econstructor 1 ; eauto.
  inversion INCR1 ; allinv.
  elim (H14 pcnew) ; intros ; try congruence.
  inv H24 ; try congruence.
  symmetry in H26. symmetry in H25 ; allinv.
  inv H27; auto. 
  
  rewrite H0 in H18 ; inv H18.
  econstructor 2 ; eauto.
  
  exploit mfold_unit_step ; eauto.
  intros. destruct H0 as [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
  destruct u'.

  destruct a.
  assert (n <> pc). intro. inv H0. inv H. elim H6 ; eauto.
  replace pc with (fst (pc,ins)) by auto.
  eapply in_map ; eauto.  
  exploit add_nop_unch ; eauto.
  intros.

  exploit (IHelts s0) ; eauto.
  inv H ; auto.
  
  intros.
  exploit (H2 pc0) ; eauto.
  intros.
  exploit (add_nop_unch is_jp n i pc0) ; eauto.
  intro. inv H8.
  inv H.  elim H10. 
  replace pc0 with (fst (pc0,ins0)) by auto.
  eapply in_map ; eauto.  
  intros.
  
  inv H6; allinv. 
  econstructor ; eauto.
  econstructor 2 ; eauto.
  econstructor 3 ; eauto.
  econstructor 4 ; eauto.
  
  intros.
  exploit H13 ; eauto; intros.
  inv H10 ; allinv.
  
  rewrite H6 in H16 ; inv H16.
  econstructor 1 ; eauto.
    
  rewrite H6 in H16 ; inv H16.
  econstructor 2 ; eauto.
Qed.

Lemma mfold_add_nop_opt_eq : forall is_jp elts s1 s2 INCR  , 
  list_norepet (map (@fst node instruction) elts) ->
  (forall pc ins, In (pc,ins) elts -> (st_code s1) ! pc = Some ins) ->
  mfold_unit (add_nop_after_instruction_opt is_jp) elts s1 = OK tt s2 INCR ->
  exists incr, mfold_unit (add_nop_after_instruction is_jp) elts s1 = OK tt s2 incr.
Proof.
  induction elts ; intros.
  simpl in H1. simpl. eauto.
  
  exploit mfold_unit_step ; eauto.
  intros. destruct H2 as [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
  destruct u'.
  
  simpl. unfold bind.
  destruct a. exploit (H0 n i) ; eauto.
  intros.
  exploit add_nop_after_ins_opt_eq ; eauto; intros.
  destruct H3.
  
  exploit (IHelts s0) ; eauto.
  inv H; auto.
  intros.
  exploit (H0 pc ins) ; eauto. intros.
  assert (n <> pc). intro. inv H6. allinv. inv H. elim H7 ; eauto.
  replace pc with (fst (pc,i)) by auto.
  eapply in_map ; eauto. 
  exploit add_nop_unch ; eauto.
  
  intros. destruct H4.
  case_eq (add_nop_after_instruction is_jp (n, i) s1) ; intros.
  rewrite H3 in H5 at 1. inv H5.
  rewrite H3 in H5 at 1. inv H5.
  case_eq ( mfold_unit (add_nop_after_instruction is_jp) elts s' ) ; intros.
  rewrite H5 in H4 at 1. inv H4.
  rewrite H5 in H4 at 1. inv H4.
  eauto.
Qed.  

(** * Relational specification of the translation *)

Inductive tr_function: RTL.function -> RTL.function -> Prop :=
  | tr_function_intro:
      forall f s1 i1 s2 i2 nentry code_elts is_jp u,
        add_nop_entry (fn_entrypoint f) (init_state f) = OK nentry s1 i1 ->
        code_elts = PTree.elements s1.(st_code) ->
        is_jp = RTLnorm.is_joinpoint (make_predecessors (fn_code f) successors_instr) ->
        mfold_unit (add_nop_after_instruction is_jp) code_elts s1 = OK u s2 i2 ->
        tr_function f (RTL.mkfunction
                f.(RTL.fn_sig)
                f.(RTL.fn_params)
                f.(RTL.fn_stacksize)
                s2.(st_code)
                s2.(st_entry)
                f.(RTL.fn_dfs)).

(** Correctness proof of the both translations *)
Lemma transl_function_opt_eq : forall f tf, 
  transl_function_opt f = Errors.OK tf ->
  transl_function f = Errors.OK tf.
Proof.
  intros.
  unfold transl_function_opt, transl_function in *.
  destruct (add_nop_entry (fn_entrypoint f) (init_state f)).
  auto.
  case_eq (mfold_unit
          (add_nop_after_instruction_opt
             (is_joinpoint (make_predecessors (fn_code f) successors_instr)))
          (PTree.elements (st_code s')) s'); intros; rewrite H0 in *;  inv H.
  destruct u.
  exploit mfold_add_nop_opt_eq ; eauto.
  eapply PTree.elements_keys_norepet ; eauto.
  eapply PTree.elements_complete ; eauto.
  intros. destruct H.
  rewrite H. auto.
Qed.  

Lemma transl_function_charact:
  forall f tf,
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof.
  intros.
  unfold transl_function in H.
  case_eq (add_nop_entry (fn_entrypoint f) (init_state f)); intros ; rewrite H0 in *. 
  inv H.
  case_eq (mfold_unit  (add_nop_after_instruction  
                          (is_joinpoint (make_predecessors (fn_code f) successors_instr )))
    (PTree.elements (st_code s')) s'); intros; rewrite H1 in *.
  inv H.
  inv H.
  eapply tr_function_intro ; eauto.
Qed.

Lemma transl_function_opt_charact:
  forall f tf,
  transl_function_opt f = Errors.OK tf ->
  tr_function f tf.
Proof.
  intros.
  exploit transl_function_opt_eq; eauto. intros.
  eapply transl_function_charact ; eauto.
Qed.

Inductive transl_function_spec: RTL.function -> RTL.function -> Prop :=
  | transl_function_spec_intro: forall f tf is_jp,
    is_jp = RTLnorm.is_joinpoint (make_predecessors (fn_code f) successors_instr) ->
    (forall pc ins, (fn_code f) ! pc = Some ins -> norm is_jp (fn_code f) (fn_code tf) pc) ->
    transl_function_spec f tf.

Lemma get_max_code_none : forall f,  
  (fn_code f) ! (Psucc (get_max (fn_code f))) = None.
Proof.
  intros.
  elim (init_state_wf f (Psucc (get_max (fn_code f)))) ; eauto. 
  intros.
  eelim Plt_ne ; eauto. 
Qed.

Lemma transl_function_spec_ok : forall f tf, 
  tr_function f tf -> 
  transl_function_spec f tf.
Proof.
  intros. inv H.
  eapply transl_function_spec_intro ; eauto. 
  intros.
  simpl.

  assert (norm (is_joinpoint (make_predecessors (fn_code f) successors_instr)) (st_code s1) (st_code s2) pc).
  unfold init_state in *.
  inversion i1; simpl in *.
  elim (H2 pc); intros. 
  congruence.
  inversion H6.
  symmetry in H7. symmetry in H8. allinv.
  eapply mfold_add_nop_spec  with 
  (is_jp := (is_joinpoint (make_predecessors (fn_code f) successors_instr))) (5:= H3) ; eauto.
  eapply PTree.elements_keys_norepet ; eauto.
  eapply PTree.elements_correct ; eauto.
  eapply PTree.elements_complete ; eauto.
  congruence.

  replace (fn_code f) with (st_code (init_state f)) by (unfold init_state in * ; simpl in * ; auto).
  clear H3.

  assert (pc <> (Psucc (get_max (fn_code f)))).
  assert (Hcont := get_max_code_none f).
  intro Heq ; inv Heq ; congruence.

  unfold init_state; simpl.
  unfold add_nop_entry in  H0; simpl in *.
  inv H0 ; simpl in *.
  inv H1; simpl in *; rewrite PTree.gso in * ; auto.
  econstructor 1 ; eauto.
  econstructor 2 ; eauto.
  econstructor 3 ; eauto.
  econstructor 4 ; eauto.
  
  intros.
  exploit H8 ; eauto ; intros.
  inv H9 ; allinv ; simpl in *.

  econstructor 1 ; eauto with rtln.
  rewrite PTree.gso in * ; auto. 
  rewrite H5 in H10 ; inv H10.  
  rewrite H1 in H12 ; inv H12 ; auto.
  
  econstructor 2; eauto with rtln.
  rewrite PTree.gso in * ; auto. 
  rewrite H5 in H10 ; inv H10.  
  rewrite H1 in H12 ; inv H12 ; auto.
  rewrite PTree.gso in * ; auto. 
  rewrite H10 in H5 ; inv H5.
  rewrite H1 in H12 ; inv H12 ; auto.
Qed.
