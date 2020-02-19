(** Proof of the DeSSA transformation.  This file starts with some
   monadic machinery.  Then, we prove that the implementation of DeSSA
   satisfies its specification.  Finally, we show that the
   specification of DeSSA preserves the semantics. *)

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
Require Import SSA.
Require Import SSAutils.
Require Import DeSSA.
Require Import DeSSAspec.
Require Import Kildall.
Require Import Conventions.
Require Import Utils.
Require Import NArith.
Require Import Events.
Require Import Bijection.
Require Import Permutation.
Require Import Utilsvalidproof.

Ltac sz := unfold Plt, Ple in * ; (zify; omega).
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

(** * Reasoning about monadic computations *)
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

(** Monotonicity properties of the state *)
Lemma instr_at_incr:
  forall s1 s2 n i,
  state_incr s1 s2 -> s1.(st_code)!n = Some i -> s2.(st_code)!n = Some i.
Proof.
  intros. inv H.
  destruct (H4 n); congruence. 
Qed.

Hint Resolve instr_at_incr: dessa.
Hint Resolve state_incr_refl: dessa.
Hint Resolve state_incr_trans : dessa.

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

Ltac expl_incr pc := 
  match goal with 
    | [ H : forall pc : positive,
       (st_code ?s0) ! pc = None \/ (st_code ?s0) ! pc = (st_code ?s2) ! pc |- _ ] =>
    eelim (H pc) ; eauto ; (intros ; congruence)
  end.

(** * The implementation of DeSSA satisfies its specification *)

(** ** Properties of auxiliary functions *)
Lemma copy_ins_at:
  forall s1 s2 incr pc max i code u,
  copy_ins pc max i code s1 = OK u s2 incr -> 
  (s2.(st_code)! pc = Some i
    /\ (forall pc', pc' <> pc -> s2.(st_code)!pc' = s1.(st_code)!pc')
    /\ s1.(st_code) ! pc = None).  
Proof.
  intros.
  unfold copy_ins in H. 
  destruct plt in H.
  destruct peq in H.
  inv e. monadInv1 H; simpl in *.  
  split. rewrite PTree.gss ; auto.
  split. intros. rewrite PTree.gso ; auto.
  destruct (st_wf s1 (st_nextnode_cp s1)).
  apply Plt_ne in H ; auto. congruence.
  intuition.
  generalize (st_wf_next_fs s1) (st_wf_next s1) ; intros.
  unfold Plt, Ple, Psucc in *. zify ; omega. 
  inv H. 
  inv H. 
Qed.

Lemma add_nop_pc_at:
  forall s1 s2 incr i n,
  add_nop_pc i s1 = OK n s2 incr -> 
  (s2.(st_code)!(st_nextnode_fs s1) = Some i
    /\ (forall pc', pc' <> (st_nextnode_fs s1) -> s2.(st_code)!pc' = s1.(st_code)!pc')
    /\ s1.(st_code) ! (st_nextnode_fs s1) = None).
Proof.
  intros. unfold add_nop_pc in H. 
  monadInv1 H; simpl in *.  
  split. rewrite PTree.gss ; auto.
  split. intros. rewrite PTree.gso ; auto.
  destruct (st_wf s1 (st_nextnode_fs s1)).
  generalize (st_wf_next_fs s1) (st_wf_next s1) ; intros.  
  unfold Plt, Ple in *. zify ; omega. 
  intuition.
  unfold Plt, Ple, Psucc in *. zify ; omega. 
Qed.

Hint Resolve copy_ins_at: dessa.

Lemma empty_block_at : forall size s1 s2 k args dst_r dst_i n incr pc, 
  empty_block size k (Iphi args (dst_r,dst_i)) pc s1 = OK n s2 incr ->
  pc = (st_nextnode_fs s1) ->
  (exists arg, nth_error args k = Some arg
    /\ (st_code s2) ! pc = Some (RTL.Iop Omove ((Bij.pamr size arg)::nil) (Bij.pamr size (dst_r,dst_i)) n))
    /\ (st_code s1) ! pc = None 
    /\ (forall pc',  pc' <> pc -> (st_code s2) ! pc' = (st_code s1) ! pc')
    /\ n = (st_nextnode_fs s2)
    /\ (is_valid_phi size (dst_r,dst_i) args) .
Proof.
  intros.
  unfold empty_block in H.
  destruct (nth_error args k) ; try inv H; simpl in *.  destruct r.
  case_eq (valid_ind size (dst_r, dst_i) && forallb (valid_ind size) args); intros Hif ; rewrite Hif in *.    
  split. 
  exists (r,p). split ; auto.  
  inv H2; simpl.
  rewrite PTree.gss ; auto.
  generalize (st_wf s1) (st_wf_next s1) (st_wf_next_fs s1) ; intros.
  eelim (H (st_nextnode_fs s1)) ; auto ; intros.
  sz.
  inv H2; simpl in *. intuition.  
  sz.
  rewrite PTree.gso ; auto.
  boolInv. unfold is_valid_phi. 
  intros. inv H6.
  unfold valid_ind in H2 ; simpl ; auto.  
  eapply forallb_forall in H5 ; eauto.
  rewrite PTree.gso ; auto.
  boolInv. unfold is_valid_phi.   
  intros.  inv H5. unfold valid_ind in H3 ; simpl ; auto.  
  eapply forallb_forall in H4 ; eauto. 
  inv H2.
  case_eq (valid_ind size (dst_r, dst_i) && forallb (valid_ind size) args); intros Hif ; rewrite Hif in *.    
  inv H2. inv H2.
Qed.

Lemma reach_moves_incr : forall size lnew s1 s2 k  succ' lastnew block ,
  reach_moves size (st_code s1) k succ' lastnew block lnew ->
  state_incr s1 s2 ->
  reach_moves size (st_code s2) k succ' lastnew block lnew.
Proof.
  induction 1 ; intros.
  econstructor ; eauto.
  exploit IHreach_moves ; eauto. intros HH.
  econstructor 2 with (succ:= succ) ; eauto.
  
  inversion H2 ; simpl in *.
  expl_incr from.
Qed.

Lemma transl_function_charact:
  forall f tf,
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof.
  intros.
  unfold transl_function, transl_function_v1 in H.
  case_eq (init_state f) ; intros.  rewrite H0 in *.
  case_eq p ; intros.
  rewrite H1 in *. 
  case_eq (check_para_block (fn_phicode f)) ; intros ; rewrite H2 in *.
  case_eq (mfold_unit
           (copy_wwo_add (fn_max_indice f) (make_predecessors (fn_code f) successors_instr) 
              (fn_code f) (fn_phicode f) p0) (sort_pp l) s); intros; rewrite H3 in *.
  inv H.  
  inv H.
  destruct u.  
  case_eq (forallb (valid_ind (fn_max_indice f)) (fn_params f)) ; intros;  rewrite H in *; inv H5. 
  eapply tr_function_intro ; eauto.
  eapply check_para_block_ok ; eauto.
  intros ; eapply forallb_forall in H ; eauto.
  inv H.
Qed.

Lemma empty_the_block_valid: forall size k block s n s' INCR,  
  empty_the_block size k block s = OK n s' INCR ->
  forall args dst, In (Iphi args dst) block -> is_valid_phi size dst args.
Proof.
  unfold empty_the_block.  
  induction block ; intros; inv H0.
  
  exploit (@mfold_step phiinstruction) ; eauto.
  intros [k0 [s'' [INCR1 [INCR2 [Hempty Hmfold']]]]].
  unfold empty_block in Hempty. destruct dst.
  unfold is_valid_phi. 
  case_eq (forallb (valid_ind size) ((r,p)::args)) ; intros Hif ; rewrite Hif in *.
  intros. inv H0; (eapply forallb_forall in Hif ; eauto).
  congruence. 
  
  exploit (@mfold_step phiinstruction) ; eauto.
  intros [k0 [s'' [INCR1 [INCR2 [Hempty Hmfold']]]]].
  destruct a.  destruct r. 
  exploit empty_block_at ; eauto. intros. intuition.
  inv H4.
  eapply IHblock ; eauto.
Qed.
  
Lemma empty_the_block_reach_moves : forall size k block s1 s2 psuccnew incr,
  empty_the_block size k block s1 = OK psuccnew s2 incr ->
  psuccnew = (st_nextnode_fs s2) /\
  exists lnew, 
    reach_moves size (st_code s2) k (st_nextnode_fs s1) psuccnew block lnew.
Proof.
  unfold empty_the_block.
  
  induction block ; intros.
  simpl in H. inv H. split ; auto. exists nil ; econstructor ; eauto.

  exploit (@mfold_step phiinstruction) ; eauto.
  intros [k0 [s' [INCR1 [INCR2 [Hempty Hmfold']]]]].

  destruct a. destruct r.
  exploit empty_block_at ; eauto.
  intros [ [arg [Hnth Hcode]] [Hs1 [Huch Hnextfs]]].
  inv Hnextfs.
  exploit IHblock ; eauto. intros [Heq [lnew Hlnew]].
  
  split ; auto.  
  exists ((st_nextnode_fs s1)::lnew).  
  econstructor 2 ; eauto.
  inversion INCR2. expl_incr (st_nextnode_fs s1).
Qed.
  
Lemma copy_ins_next_fs : forall s1 s x pc max ins code INCR,
  copy_ins pc max ins code s1 = OK x s INCR ->
  (st_nextnode_fs s1) = (st_nextnode_fs s).
Proof.
  intros.
  unfold copy_ins in H.
  destruct plt.
  destruct (peq pc (st_nextnode_cp s1)).
  inv e.
  inv H ; simpl in *. auto.
  inv H. 
  inv H.
Qed.
Hint Constructors is_valid.

Lemma forallb_forall_1 : forall (A : Type) (f : A -> bool) (l : list A),
   forallb f l = true -> (forall x : A, In x l -> f x = true).
Proof.
  intros.
  eapply forallb_forall ; eauto.
Qed.  

Ltac kick_aux :=
  match goal with 
    | [h0: Bij.valid_index ?size (snd _) = true |- _] => solve [auto]
    | [h1 : valid_ind ?size ?rr = true |- _ ] => solve [inv h1 ; eauto]
    | [h2 : forallb _ _ = true |- _ ] => solve [eapply forallb_forall in h2 ; eauto]
  end.

Ltac kick := 
  match goal with 
    | [ H: (fn_code ?f) ! _ = Some (Itailcall _ (inl ident _) _) |- _] =>
      econstructor 8 ; eauto
    | [ H: (fn_code ?f) ! _ = Some (Icall _ (inl ident _) _ _ _) |- _] =>
      econstructor 6 ; eauto
    | _ =>      
      (econstructor ; eauto)
  end ; 
  (intros rr Hrr; try inv Hrr); kick_aux.

Lemma ros_pamr_true : forall size s r, 
  ros_pamr size (inl ident s) = Errors.OK r ->
  Bij.valid_index size (snd s) = true.
Proof.
  intros.
  simpl in *. 
  destruct Bij.valid_index; auto.
  inv H.
Qed.

Lemma opt_pamr_true : forall size s r, 
  opt_pamr size (Some s) = Errors.OK r ->
  Bij.valid_index size (snd s) = true.
Proof.
  intros.
  simpl in *. 
  destruct Bij.valid_index; auto.
  inv H.
Qed.

(** ** Correctness of [copy_wwo_add] *)
Lemma copy_wwo_add_dssa_spec: forall f size pc max s1 s2 incr ins, 
  (fn_code f) ! pc = Some ins ->
  copy_wwo_add size (make_predecessors (fn_code f) successors_instr) (fn_code f) (fn_phicode f) max pc s1 = OK tt s2 incr ->
  dssa_spec size (make_predecessors (fn_code f) successors_instr) (fn_code f) (fn_phicode f) (st_code s2) pc.
Proof.
  intros.
  unfold copy_wwo_add in H0.
  rewrite H in *.
  destruct ins;  
    (try match goal with 
       | [H: (fn_code ?f) ! ?pc = Some ?ins  |- _ ] => 
         case_eq (map_pamr size ins) ; intros i Hi ; rewrite Hi in * ; 
           generalize Hi ; inv Hi ; intros Hi ; try congruence
     end;
    try match goal with 
      | [H : (if ?t_if then _ else _) = _ |- _ ] => 
        case_eq t_if ; intros Hif ; rewrite Hif in * ; boolInv ; try congruence
    end;
    try  match goal with 
           | [ros: (reg + ident)%type |- _ ] => 
             case_eq (ros_pamr size ros) ; intros ros' Hros ; rewrite Hros in *;
               [(destruct ros ; [ (exploit ros_pamr_true ; eauto) ; intros Hvalid |])|] ; 
               try congruence
           | _ => idtac  
         end;
    try solve [((econstructor 3 ; eauto ; try kick ; try congruence);
      (exploit copy_ins_at ; eauto ; (intros ; intuition ; (inv H2 ; eauto) )))]).

  Focus 2.  
  econstructor 3 ; eauto.
  econstructor 6 ; eauto.
  intros. inv H4 ; try kick_aux. inv H5 ; kick_aux.
  congruence.
  (exploit copy_ins_at ; eauto ; (intros ; intuition ; (inv H2 ; eauto) )). 

  Focus 2.
  
  case_eq (opt_pamr size o) ; intros ros' Hros ; rewrite Hros in *;
  [(destruct o ; [ (exploit opt_pamr_true ; eauto) ; intros Hvalid |])|].
  econstructor 3 ; eauto. congruence. 
  (exploit copy_ins_at ; eauto ; (intros ; intuition ; (inv H2 ; eauto) )). 
  econstructor 3 ; eauto. congruence. 
  (exploit copy_ins_at ; eauto ; (intros ; intuition ; (inv H2 ; eauto) )). 
  inv H2.
    
  case_eq (fn_phicode f) ! n ; intros; rewrite H1 in *.
  
  case_eq (index_pred (make_predecessors (fn_code f) successors_instr) pc n) ; intros ;  rewrite H2 in *.
  monadInv H0.
  
  unfold copy_inop in EQ. 
  exploit (empty_the_block_reach_moves) ; eauto. intros [Heq [lnew Hlnew]]. 
  exploit (reach_moves_incr size lnew s0 s2) ; eauto.  intros.
  
  erewrite <- (copy_ins_next_fs s1 s) in H0 ; eauto.  
  econstructor 2 ; eauto.    
  eapply empty_the_block_valid ; eauto.
  inv EQ. exploit copy_ins_at ; eauto.
  intros. intuition. inversion INCR0. expl_incr pc.
  exploit add_nop_pc_at ; eauto. intros.  intuition ; auto.
  inv Heq. auto.
  inv H0.
  econstructor ; eauto.
  exploit copy_ins_at ; eauto.
  intros ; intuition. 
Qed.

Lemma mfold_dssa_spec : forall f size l max s1 s2 incr, 
  mfold_unit (copy_wwo_add size (make_predecessors (fn_code f) successors_instr) (fn_code f) (fn_phicode f) max) l s1 = OK tt s2 incr ->
  (list_norepet l) ->
  forall pc ins, 
    In pc l -> (fn_code f) ! pc = Some ins ->
    dssa_spec size (make_predecessors (fn_code f) successors_instr) (fn_code f) (fn_phicode f) (st_code s2) pc. 
Proof.
  induction l ; intros.
  inv H1.
  inv H1.
  
  exploit mfold_unit_step ; eauto.
  intros. destruct H1 as [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
  destruct u'.
  
  exploit copy_wwo_add_dssa_spec ; eauto.
  intros.
  inversion INCR1. 
  
  inv H1.
  econstructor ; eauto.
  expl_incr pc.
  
  econstructor 2 with (succ':= succ') (lastnew :=lastnew) (lnew:= lnew); eauto.
  expl_incr pc. 
  expl_incr lastnew.
  eapply reach_moves_incr;  eauto.
  
  econstructor 3 ; eauto.
  expl_incr pc. 
    
  exploit mfold_unit_step ; eauto.
  intros. destruct H1 as [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
  destruct u'.  
  
  exploit IHl ; eauto. inv H0 ; auto.
Qed.  

Lemma NoDup_list_norepet : forall (A: Type) (l:list A), NoDup l -> list_norepet l.
Proof.
  induction 1; intros; (constructor ; eauto).
Qed.  

Lemma list_norepet_NoDup : forall (A: Type) (l:list A), list_norepet l -> NoDup l.
Proof.
  induction 1; intros; (constructor ; eauto).
Qed.

Lemma get_max_fold''' : forall l maxacc lacc,
  NoDup (l++lacc) ->
  NoDup (snd (fold_left (fun (al: positive * list positive) pc => let (a,l) := al in if plt a pc then (pc,pc::l) else (a,pc::l)) l (maxacc,lacc))).
Proof.
  induction l ; intros ; inv H.
  simpl in H0. inv H0. simpl. constructor.
  simpl in *. inv H2. econstructor ; eauto. 
  simpl in *.
  destruct (plt maxacc a); eapply IHl ; eauto;
    ((eapply NoDup_list_norepet in H3);
      (eapply Coqlib.list_norepet_app in H3; intuition);
      (eapply list_norepet_NoDup ; eauto);
      (eapply Coqlib.list_norepet_app; intuition ; auto);
      [ (constructor ; auto; (intro Hcont ; elim H2; eapply in_app ; eauto))
        | (unfold list_disjoint; intros; intro Hcont; inv Hcont;
          inv H4 ;  [ (elim H2; eapply in_app ; eauto) | exploit H3 ; eauto])]).
Qed.

Lemma get_max_nodup : forall (A: Type) t, 
  NoDup (snd (@get_max A t)).
Proof.
  unfold get_max.
  intros. eapply get_max_fold''' ; eauto.
  rewrite <- app_nil_end.
  apply list_norepet_NoDup.
  apply PTree.elements_keys_norepet.
Qed.
  
(** ** Specification compliancy of the implementation *)
Lemma transl_function_spec_ok : forall f tf, 
  tr_function f tf -> 
  transl_function_spec f tf.
Proof.
  intros.
  inv H.
  econstructor ; eauto. intros.    
  unfold sort_pp in *.
  
  generalize (PosSort.Permuted_sort pl)  ; intros.
  assert (pl = snd (get_max (fn_code f))).
  unfold init_state in H0. 
  congruence.  
  inv H3. 

  exploit mfold_dssa_spec ; eauto.

  apply Permutation_NoDup in H1 ; eauto.
  eapply NoDup_list_norepet ; auto.
  apply get_max_nodup.
  
  exploit get_max_in ; eauto.
  eapply Permutation_in ; eauto.
Qed.

(** * Semantic preservation *)
(** We show here that the specification of DeSSA is correct *)

Section PRESERVATION.

Variable prog: SSA.program.
Variable tprog: RTL.program.
Hypothesis TRANSF_PROG: transl_program prog = Errors.OK tprog.
Hypothesis WF_PROG : wf_ssa_program prog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
  
Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with transl_fundef.
  exact TRANSF_PROG.
Qed.

Lemma functions_translated:
  forall (v: val) (f: SSA.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf 
    /\ transl_fundef f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_transf_partial transl_fundef). 
  exact TRANSF_PROG.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: SSA.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_ptr_transf_partial transl_fundef).
  exact TRANSF_PROG.
Qed.

Lemma var_info_preserved:
  forall (b: block), Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_var_info_transf_partial with transl_fundef.
  exact TRANSF_PROG.
Qed.

Lemma sig_fundef_translated:
  forall f tf,
    transl_fundef f = Errors.OK tf ->
    RTL.funsig tf = SSA.funsig f.
Proof.
  intros f tf. intros.
  case_eq f ; intros;  inv H0.
  simpl in *. Errors.monadInv H.
  eapply transl_function_charact in EQ ; eauto.
  inv EQ. 
  simpl; auto. 
  inv H.
  simpl; auto.
Qed.

Lemma find_function_preserved_same : forall size r rs rs' (f:SSA.fundef) (f':RTL.fundef), 
  find_function ge (inl ident r) rs = Some f ->
  RTL.find_function tge (inl ident (Bij.pamr size r)) rs' = Some f' ->
  rs#2 r = rs'#(Bij.pamr size r) ->
  funsig f = RTL.funsig f'.
Proof.
  intros. simpl in *. 
  exploit (functions_translated rs#2 r) ; eauto.
  intros.
  destruct H2 as [tf [Htf Oktf]].
  symmetry.
  eapply sig_fundef_translated; eauto.
  rewrite H1 in Htf. rewrite Htf in H0. inv H0; auto.
Qed.

Lemma sig_function_translated:
  forall f tf,
    transl_function f = Errors.OK tf ->
    RTL.fn_sig tf = fn_sig f.
Proof.
  intros f tf. destruct f; simpl; intros.
  eapply transl_function_charact in H ; eauto.
  inv H.
  simpl; auto.
Qed. 

Lemma spec_ros_r_find_function:
  forall size rs rs' f r,
  SSA.find_function ge (inl _ r) rs = Some f ->
  rs#2 r = rs'#(Bij.pamr size r) ->
  exists tf,
     RTL.find_function tge (inl _ (Bij.pamr size r)) rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  eapply functions_translated; eauto. inv H. 
  rewrite H0 ; auto.
Qed.

Lemma spec_ros_id_find_function:
  forall rs rs' f id,
  SSA.find_function ge (inr _ id) rs = Some f ->
  exists tf,
     RTL.find_function tge (inr _ id) rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  simpl in *. 
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Lemma stacksize_preserved: forall f tf, 
  transl_function f = Errors.OK tf -> 
  fn_stacksize f = RTL.fn_stacksize tf.
Proof.
  intros.
  eapply transl_function_charact in H ; eauto. inv H. auto.
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

Ltac allinv := 
  repeat 
    match goal with 
      | [H: value ?s = Some ?s' |- _ ] => inv H
      | [ H1:   (fn_code ?tf) ! ?pc = Some _  ,
        H2: (fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   (RTL.fn_code ?tf) ! ?pc = Some _  ,
        H2: (RTL.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   (fn_phicode ?tf) ! ?pc = Some _  ,
        H2: (fn_phicode ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | _ => idtac
    end.


(** ** Simulating the execution of a unindexed phi-block *)
Definition phi_store_e := 
fun (size: nat) (k : nat) (phib : list phiinstruction) (rs : RTL.regset) =>
fold_left
  (fun (rs0 : PMap.t val) (phi : phiinstruction) =>
   match phi with
   | Iphi args dst =>
       match nth_error args k with
       | Some r => rs0 # (Bij.pamr size dst) <- (rs0 !! (Bij.pamr size r))
       | None => rs0
       end
   end) phib rs.

Lemma phi_store_e_notin_preserved_aux: forall size k block r v dst rs,
  (Bij.valid_index size (snd dst)) = true ->
  (forall args dst, In (Iphi args dst) block -> 
    (Bij.valid_index size (snd dst)) = true) ->
  (forall args, ~ In (Iphi args dst) block) ->
  r <> (Bij.pamr size dst) ->
  (phi_store_e size k block (rs# r <- v))# (Bij.pamr size dst) = rs# (Bij.pamr size dst).
Proof.
  induction block; intros; simpl.
  (* *) eapply PMap.gso; eauto. 
  (* *) destruct a; simpl. 
        case_eq (nth_error l k); intros ; eauto. 
        (**) rewrite IHblock ; eauto.
             eapply PMap.gso ; auto.  
             intro Hcont. 
             destruct r0 ; destruct dst. 
             eapply Bij.INJ' in Hcont ; eauto. inv Hcont. exploit H1 ; eauto.
             exploit H0 ; eauto.
Qed.
    
Lemma phi_store_e_notin_preserved: forall size k block rs dst,
  (forall args, ~ (In (Iphi args dst) block)) ->
  (forall args dst, 
    In (Iphi args dst) block ->
    (Bij.valid_index size (snd dst)) = true) ->
  (Bij.valid_index size (snd dst)) = true  ->
    (phi_store_e size k block rs)# (Bij.pamr size dst) = rs# (Bij.pamr size dst).
Proof.
  induction block; intros.
  (* *) simpl; auto.
  (* *) destruct a; simpl. 
        case_eq (nth_error l k); intros; eauto.
        (* case some *)
        eapply phi_store_e_notin_preserved_aux; eauto.
        intros. intro Hcont. 
        destruct r ; destruct dst. 
        eapply Bij.INJ' in Hcont ; eauto. inv Hcont. 
        exploit H ; eauto. exploit H0 ; eauto.
Qed.

Lemma phistore_e_compat: forall size k block (rs1 rs2: RTL.regset), 
  (forall r, rs1# r = rs2# r) ->
  (forall r, (phi_store_e size k block rs1)# r = (phi_store_e size k block rs2)# r).
Proof.
  induction block; intros.
  (* *) simpl; auto.
  (* *) destruct a; simpl.
        destruct (nth_error l k); eauto. 
        (* case some *) 
        eapply IHblock; eauto. 
        intros; rewrite H. 
        case_eq (peq r2 (Bij.pamr size r0)); intros ; auto. 
           (* case eq *)
           rewrite PMap.gsspec. rewrite H0.
           case_eq (peq (Bij.pamr size r1) r2); intros; auto.
               (* case eq *)  rewrite <- e0 in *. symmetry; eapply gsregset; eauto; congruence.
               (* case diff *) rewrite e in *. rewrite PMap.gss; eauto.
           (* case diff *)
           repeat (rewrite PMap.gso; eauto).
Qed.

Lemma phi_store_e_copy_preserved: forall size k block rs dst arg , 
  (forall (args : list reg) (dst0 : reg),
   In (Iphi args dst0) block -> Bij.valid_index size (snd dst0) = true) ->
  (Bij.valid_index size (snd dst) = true) ->
  (forall args, not (In (Iphi args dst) block)) ->
  (phi_store_e size k block rs # (Bij.pamr size dst) <- (rs # (Bij.pamr size arg))) # (Bij.pamr size dst) = rs # (Bij.pamr size arg).
Proof.
  intros. 
  case (p2eq arg dst); intros.
  (* case eq *) 
  inv e.
  assert (Hrs: (forall r, (rs# (Bij.pamr size dst) <- (rs# (Bij.pamr size dst)))#r = rs# r)) by (eapply gsregset; eauto).
  rewrite (phistore_e_compat _ _ _ (rs# (Bij.pamr size dst)<- (rs# (Bij.pamr size dst))) rs); eauto.
  rewrite phi_store_e_notin_preserved; eauto.  
  (* case diff *)
  rewrite phi_store_e_notin_preserved; eauto.
  eapply PMap.gss ; eauto.
Qed.

Lemma phi_store_e_one_step: forall size k block rs r args dst arg,
(forall argss, not (In (Iphi argss r) ((Iphi args dst)::block))) -> 
(nth_error args k) = Some arg ->
(phi_store_e size k ((Iphi args dst)::block) rs)# (Bij.pamr size r) = 
(phi_store_e size k block (rs# (Bij.pamr size dst) <- (rs# (Bij.pamr size arg))))# (Bij.pamr size r).
Proof.
  intros.
  destruct block; simpl; rewrite H0; auto.
Qed.  

Lemma phi_store_e_not_modified: forall size k block rs dst r v
  (HVALID: forall (args : list reg) (dst0 : reg),
   In (Iphi args dst0) block -> Bij.valid_index size (snd dst0) = true)
  (DSTVALID : Bij.valid_index size (snd dst) = true) 
  (RVALID : Bij.valid_index size (snd r) = true) 
  (HVALID': forall (args : list reg) (dst0 : reg) (arg: reg),
   In (Iphi args dst0) block -> In arg args -> Bij.valid_index size (snd arg) = true)
  (DIFF : dst <> r) 
  (RNOTUSED: forall dst args, (In (Iphi args dst) block) -> ~ In r args) 
  (PRMNOTUSED: para_block block)
  (NODUP: NoDup block)
  (NODUP': forall r args args', 
    In (Iphi args r) block -> In (Iphi args' r) block -> args = args'),
  (phi_store_e size k block rs) # (Bij.pamr size dst) = (phi_store_e size k block rs # (Bij.pamr size  r) <- v) # (Bij.pamr size dst).
Proof.
  induction block; intros.
  (* nil *)
  simpl; rewrite PMap.gso; eauto.
  intros Hcont. destruct dst ; destruct r. 
  apply Bij.INJ' in Hcont; eauto. 
  (* a::block *)
  destruct a; case_eq (nth_error l k).
  (* nth_error l k = Some r1 *)
  intros r1 Hnth.  
  simpl; rewrite Hnth. 
  assert (r1 <> r) by (intro H; inv H; exploit (RNOTUSED r0 l); auto; try (constructor; auto); eapply nth_error_some_in; eauto). 
  rewrite PMap.gso; auto.
  case (p2eq r0 r); intro Hinv. 
       (* r0 = r *)
       inv Hinv. 
       symmetry ; rewrite phistore_e_compat with (rs2:= (rs # (Bij.pamr size  r) <- (rs # (Bij.pamr size r1)))) at 1 ; eauto.
       eapply regset_setset; eauto.
       (* r0 <> r*)
       symmetry; rewrite phistore_e_compat with (rs2:= (rs # (Bij.pamr size  r0) <- (rs # (Bij.pamr size  r1))) # (Bij.pamr size r) <- v) ; eauto; symmetry.
       eapply IHblock ; eauto;
         [ unfold para_block; intros;  intro;
           assert (Hcont := PRMNOTUSED dst0 args); assert (Hcont' := Hcont arg); eauto; clear Hcont;
           exploit Hcont' ; eauto
           | inv NODUP; auto].
       symmetry; eapply regset_permut; auto.
  intros Hcont. destruct r0 ; destruct r. eapply Bij.INJ' in Hcont; eauto. 
  exploit HVALID ; eauto.
  intros Hcont. destruct r1 ; destruct r. eapply Bij.INJ' in Hcont ; eauto. 
  exploit (HVALID' l r0 (r1,p)) ; eauto.
  eapply nth_error_some_in ; eauto.  
  intros Hcont. destruct r1 ; destruct r. 
  eapply Bij.INJ' in Hcont; eauto. 
  exploit (HVALID' l r0 (r1,p)) ; eauto.
  eapply nth_error_some_in ; eauto.  
  
  (* nth_error l k = None *)
  intros; simpl. rewrite H. eapply IHblock; eauto;
         [  unfold para_block; intros;  intro;   
            assert (Hcont := PRMNOTUSED dst0 args); assert (Hcont' := Hcont arg); eauto; clear Hcont;
            exploit Hcont' ; eauto
           |  inv NODUP; auto].
Qed.

Lemma phi_store_e_copy: forall size k block rs dst arg args
  (PRMNOTUSED: para_block block)
  (NODUP: NoDup block)
  (NODUP': (forall r args args', 
    In (Iphi args r) block -> In (Iphi args' r) block -> args = args'))
  (HVALID: (forall r args , 
    In (Iphi args r) block -> Bij.valid_index size (snd r) = true))
  (HVALID': (forall r args arg , 
    In (Iphi args r) block -> In arg args -> Bij.valid_index size (snd arg) = true))
  (IN: In (Iphi args dst) block /\ nth_error args k = Some arg),
  (phi_store_e size k block rs)# (Bij.pamr size dst) = rs# (Bij.pamr size arg).
Proof.
  induction block; intros; destruct IN as [Hargs Hnth]. 
  inv Hargs.
  destruct a; inv Hargs. 
  (* (Iphi args dst)  is the head element of the block *)
  inv H; simpl.
  rewrite Hnth.
  assert (~ In (Iphi args dst) block) by (inv NODUP; auto). 
  eapply phi_store_e_copy_preserved; eauto. 

  intros; intro; exploit (NODUP' dst args0 args); eauto. 
  intros. inv H1. elim H; auto.
  (* (Iphi args dst) is in the tail of the block *)
  case_eq (nth_error l k); intros; simpl; rewrite H0.
  (* case Some *) 
  assert (dst <> r) by (intro; inv H1; inv NODUP; exploit (NODUP' r args l); eauto; intro;
    inv H1; elim H3 ; auto). 
  symmetry; rewrite <- IHblock with (dst:= dst) (arg:= arg) (args:= args) at 1 ; eauto. 
  eapply phi_store_e_not_modified; eauto.
  (* rest of lemma hyps *)
  (**) intros; intro ; exploit (PRMNOTUSED  dst0 args0) ; eauto.
  intro. inv H4. exploit (NODUP' r l args0); eauto. intros ; inv H4 ; inv NODUP;  contradiction.
  eapply para_block_cons; eauto.
       inv NODUP; auto.
  (**) eapply para_block_cons; eauto.
  (**) inv NODUP; auto.  
  (* case None *)  
  eapply IHblock ; eauto; [eapply para_block_cons | inv NODUP] ; eauto.
Qed.  


(** ** Simulation relation *)
Inductive match_regset (size:nat) : SSA.regset -> RTL.regset -> Prop := 
| mrg_intro : forall rs rs', 
  (forall r, 
    Bij.valid_index size (snd r) = true ->  
    rs#2 r = rs'#(Bij.pamr size r)) ->
    match_regset size rs rs'.

Lemma match_regset_args : forall size args rs rs' , 
  match_regset size rs rs' ->
  (forall arg, In arg args -> Bij.valid_index size (snd arg) = true) ->
  rs##2 args = rs'## (map (Bij.pamr size) args).
Proof.
  induction args ; intros.
  simpl ; auto.
  simpl.
  exploit IHargs ; eauto. intros. rewrite H1.
  inv H. rewrite (H2 a). auto.
  exploit H0 ; eauto.
Qed.

Lemma match_regset_phistore : forall size k phib rs rs' ,
  forall
    (HVALID: forall r args , 
      In (Iphi args r) phib -> Bij.valid_index size (snd r) = true)
    (HVALID': (forall r args arg , 
      In (Iphi args r) phib -> In arg args -> Bij.valid_index size (snd arg) = true)),
    forall (PARA: para_block phib)
      (NODUP: NoDup phib)
      (ARGS : (forall r2 args args',
        In (Iphi args r2) phib -> In (Iphi args' r2) phib -> args = args'))
      (PHIARGS: forall args dst, 
        In (Iphi args dst) phib -> (exists arg, nth_error args k = Some arg)),
      match_regset size rs rs' ->  
      match_regset size (phi_store k phib rs)
      (phi_store_e size k phib rs').
Proof.
  induction phib ; intros.
  simpl ; auto.
  
  case_eq a; intros. inv H0.
  assert (forall l, ~ In (Iphi l r) phib). 
  intros. intro Hcont.  exploit (ARGS r l0) ; eauto.
  intros. inv H0. inv NODUP. intuition.
  simpl. case_eq (nth_error l k); intros. 
  Focus 2.
  eapply IHphib; auto.
  (* po0 *) exploit HVALID ; eauto.
  (* po0' *) intros. exploit (HVALID' r0 args arg) ; eauto.
  (* po1 *) eapply para_block_cons ; eauto.
  (* po2 *) inv NODUP ; auto.
  (* po3 *) intros. exploit ARGS ; eauto.
  (* po4 *) intros ; exploit PHIARGS ; eauto.

  constructor. intros. 
  replace (rs !!2 r0) with (rs' # (Bij.pamr size r0)).
  Focus 2. inv H ; eauto. rewrite (H3 r0) ; eauto. 
  exploit HVALID' ; eauto. eapply nth_error_some_in ; eauto.
  Require Import Classical.
  destruct (classic (assigned r1 phib)).  inv H.
  Focus 2.
  (* r1 is not assigned in phib *)
  rewrite phi_store_e_notin_preserved ; eauto. 
  destruct (p2eq r r1). inv e.
  rewrite P2Map.gss. rewrite PMap.gss. auto.
  rewrite P2Map.gso ; auto. rewrite PMap.gso. 
  rewrite phi_store_notin_preserved at 1 ; eauto.
  inv H ; auto.
  intros. intro Hcont. elim H3 ; eauto. exists args; auto.    
  destruct r1 ; destruct r. intro Hcont.
  eapply Bij.INJ' in Hcont ; eauto. exploit HVALID ; eauto. 
  intros. intro Hcont. elim H3 ; eauto. exists args; auto.
  
  (* r1 is assigned in phib *)
  destruct (p2eq r r1). inv e.
  inv H3. exploit H0 ; eauto. intuition.
  inv H3. exploit (PHIARGS x) ; eauto. intros [arg Harg].  
  erewrite phi_store_e_copy; eauto. 
  rewrite P2Map.gso; auto. 
  destruct (p2eq arg r).
  inv e.
  unfold para_block in  PARA.
  exploit (PARA r1 x) ; eauto. eapply nth_error_some_in in Harg ; eauto. 
  intuition.
  
  erewrite phi_store_copy ; eauto.
  rewrite PMap.gso ; eauto.
  rewrite H4 ; auto. 
  exploit (HVALID' r1) ; eauto. eapply nth_error_some_in ; eauto.
  destruct arg ; destruct r. intro Hcont.
  eapply Bij.INJ' in Hcont; eauto. 
  exploit (HVALID' r1 x (r2,p)) ; eauto. eapply nth_error_some_in ; eauto.
  exploit (HVALID) ; eauto.   
  inv NODUP ; auto.
  eapply para_block_cons ; eauto.
  inv NODUP ; auto.    
Qed.

    
Lemma reach_moves_star :  forall size ts phib sp rs  m tf  succ' lnew k lastnew,
  reach_moves size (RTL.fn_code tf) k succ' lastnew phib lnew ->
  star RTL.step tge (RTL.State ts tf sp succ' rs m) E0 (RTL.State ts tf sp lastnew 
    (phi_store_e size k phib rs) m).
Proof.
  induction phib; intros.
  simpl in *.  inv H.
  eapply star_refl ; eauto.
  
  inv H. 
  eapply star_step 
    with  (s2 := (RTL.State ts tf sp succ 
      rs # (Bij.pamr size dst) <- 
      (rs# (Bij.pamr size arg))) m) (t2:= E0) (t1:= E0) ; eauto.
  eapply RTL.exec_Iop ; eauto. 
  simpl. rewrite H5 at 1. 
  eapply IHphib ; eauto. 
Qed.

Lemma elim_structural : forall tf,
  wf_ssa_function tf ->
  forall pc pc' instr instr' block,
    (fn_code tf)! pc = Some instr ->
    (fn_code tf)! pc' = Some instr' ->
    (fn_phicode tf)!pc' = Some block ->
    In pc' (successors_instr instr) ->
    instr = Inop pc'.
Proof.
  intros.
  inv H0. 
  assert (Hjp : join_point pc' tf).
  eapply fn_phicode_inv1 with (phib := block); eauto.
  exploit (fn_code_inv2 tf H pc' pc) ; eauto ; intros.
  unfold successors_list.
  unfold successors.
  rewrite PTree.gmap1.
  unfold option_map. rewrite H5. auto.
  congruence.
Qed.


Lemma init_reg_match_regset : forall size params args,
  (forall p, In p params -> Bij.valid_index size (snd p) = true) ->
  forall r,    
   (Bij.valid_index size (snd r) = true) ->
   (init_regs args params) !!2 r =
   (RTL.init_regs args (map (Bij.pamr size) params)) # (Bij.pamr size r).
Proof.
  induction params ; intros ; eauto; simpl. 
  rewrite Regmap.gi; rewrite P2Map.gi ; auto.
  
  destruct args.
  rewrite Regmap.gi; rewrite P2Map.gi ; auto.
  destruct (p2eq a r).
  inv e. rewrite P2Map.gss; rewrite PMap.gss ; auto.
  rewrite P2Map.gso ; auto.
  rewrite PMap.gso ; auto.
  intro Hcont. destruct r ; destruct a. 
  eapply Bij.INJ' in Hcont; eauto.
  exploit  H ; eauto. 
Qed.  

Hint Resolve match_regset_args : valagree.  

Inductive match_stackframes : list stackframe -> list RTL.stackframe -> Prop :=
| match_stackframes_nil: match_stackframes nil nil
| match_stackframes_cons: 
  forall res f sp pc rs rs' s tf ts
    (STACK : (match_stackframes s ts ))
    (SPEC: (transl_function f = Errors.OK tf))
    (WFF: wf_ssa_function f)
    (MREG: match_regset (fn_max_indice f) rs rs')
    (MREG: Bij.valid_index (fn_max_indice f) (snd res) = true),
    match_stackframes
    ((Stackframe res f sp pc rs) :: s)
    ((RTL.Stackframe (Bij.pamr (fn_max_indice f) res) tf sp pc rs') :: ts).

Hint Constructors match_stackframes.

Set Implicit Arguments.

Inductive match_states: SSA.state -> RTL.state -> Prop :=
  | match_states_intro:
      forall s ts sp pc rs rs' m f tf
        (SPEC: transl_function f = Errors.OK tf)
        (STACK: match_stackframes s ts)
        (WFF: wf_ssa_function f)
        (MREG: match_regset (fn_max_indice f) rs rs'),
        match_states (State s f sp pc rs m) (RTL.State ts tf sp pc rs' m)
  | match_states_call:
      forall s ts f tf args m 
        (SPEC: transl_fundef f = Errors.OK tf)
        (STACK: match_stackframes s ts)
        (WFF: wf_ssa_fundef f),        
        match_states (Callstate s f args m) (RTL.Callstate ts tf args m)
  | match_states_return:
      forall s ts v m 
        (STACK: match_stackframes s ts ),
        match_states (Returnstate s v m) (RTL.Returnstate ts v m).

Hint Constructors match_states.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
    exists st2, RTL.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial); eauto).
  exists (RTL.Callstate nil tf nil m0); split.
  econstructor; eauto.
  rewrite symbols_preserved.
  rewrite (transform_partial_program_main _ _ TRANSF_PROG).  auto.
  rewrite <- H3. apply sig_fundef_translated; auto.
  eapply match_states_call  ; eauto.
  eapply Genv.find_funct_ptr_prop; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> RTL.final_state st2 r.
Proof.
  intros. inv H0. inv H. 
  inv STACK.
  constructor.
Qed.


Ltac error_struct tf pc pc' :=
  (match goal with
     | [ H1 : (fn_code tf) ! pc = Some _ ,
         H2 : (fn_phicode tf) ! pc' = Some _,
         HWF: wf_ssa_function tf
       |- _ ] =>
     let Hcont := fresh "Hcont" in
     ((exploit (elim_structural tf HWF pc pc'); eauto) ;
       [ (simpl) ; (left ; auto) | (intros Hcont; inv Hcont)])
   end).

Ltac kick_valid := 
  match goal with 
    | [H : is_valid _ _ |- _ ] => inv H ; eauto
  end;
  try match goal with 
        | [H: forall r0 : Registers.reg * Bij.index,
          In r0 ((?r, ?p0) :: _) ->
          Bij.valid_index _ (snd _) = true |- _ ] => eapply (H (r,p0)) ; eauto
      end.

Ltac normalized pc :=
  match goal with
    | [NORM : forall (pc: positive) (ins: instruction), _ -> dssa_spec ?size ?preds ?code1 ?pcode1 ?code2 pc |- _] =>
      let Hpc := fresh "Hpc" in
        let Hnorm := fresh "Hnorm" in
        assert (Hpc := NORM pc); clear NORM ;
          exploit Hpc ; eauto ; clear Hpc ; intro Hnorm ; inv Hnorm ; allinv ; try congruence
  end;
  try match goal with 
        | [H: map_pamr ?size ?ins = Errors.OK ?ins' |- _ ] => 
          inv H
      end;
  try match goal with 
        | [H: (if ?t_if then _ else _) = _ |- _ ] => destruct t_if ; try congruence ; inv H
      end.

(** ** This relation is indeed a simulation *)
Lemma transl_step_correct:
  forall s1 t s2,
    step ge s1 t s2 ->
    forall s1' (MS: match_states s1 s1'),
      exists s2', plus RTL.step tge s1' t s2' /\ match_states s2 s2'.
Proof.    
  induction 1; intros; inv MS; auto;
  match goal with 
    | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
    | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
    | [  |- context [RTL.Returnstate ?ts ?vres ?m]] => idtac
    | _ => 
      ( (exploit transl_function_charact ; eauto; intros);
        (exploit transl_function_spec_ok ; eauto; intros))
  end; 
  match goal with 
    | [SPEC: transl_function_spec ?f ?tf |- _ ] => 
      inv SPEC
    | _ => try (generalize (wf_ssa f) ; intros HWF)
  end. 
  
  (* inop without *)
  normalized pc. 
  exists (RTL.State ts tf sp succ rs' m). split.
  eapply plus_one ; eauto.
  econstructor 1 ; eauto.
  constructor ; auto.
  exploit (fn_code_closed f WFF pc succ) ; eauto. simpl ; auto.
  intros [ins Hins]. 
  exploit (fn_phicode_inv1 f) ; eauto. intro Hcont. elim H0 ; auto.
  (* inop with block *)  
  normalized pc.
  rewrite H9 in H2 ; inv H2.
  exists  (RTL.State ts tf sp succ (phi_store_e (fn_max_indice f) k phib rs') m). split.
  eapply plus_left with (s2 := (RTL.State ts tf sp succ' rs' m)) (t1:=E0) (t2:=E0) ; eauto.
  econstructor ; eauto.
  
  eapply star_right with (s2 := (RTL.State ts tf sp lastnew (phi_store_e (fn_max_indice f) k phib rs') m)) (t1:= E0) (t2:= E0) ; eauto.
  eapply reach_moves_star  ; eauto.
  econstructor ; eauto. 
    
  econstructor 1 ; eauto. 
  eapply match_regset_phistore ; eauto.
  intros.  exploit H6 ; eauto. 
  intros.  generalize (H6 args r H1). intros Hvalid. unfold is_valid_phi in Hvalid.
  exploit Hvalid ; eauto.
  (* po1 *)  inv H3. eapply H4 ; eauto.   
  eapply check_udef_spec_no_dup ; eauto. inv WFF ; auto.  
  (* po2 *) 
  intros. destruct (list_eq_dec p2eq args args') ; auto. 
  destruct (fn_ssa f) as [_ Hssa]; eauto.
  exploit Hssa ; eauto. intuition.
  exploit H12 ; eauto.
  (* po3 *) intros. 
  exploit fn_phiargs ; eauto.   

  (* iop *)
  normalized pc.
  exists  (RTL.State ts tf sp pc' (rs' # (Bij.pamr (fn_max_indice f) res) <- v) m). split.
  eapply plus_one ; eauto. 
  econstructor 2 ; eauto.
  rewrite <- H0 ; eauto.
  erewrite match_regset_args ; eauto with valagree.   
  kick_valid.
  econstructor 1 ; auto.  
  constructor; intros. 
  destruct (p2eq res r).
  inv e. rewrite P2Map.gss. rewrite PMap.gss; auto.
  rewrite P2Map.gso; auto. rewrite PMap.gso ; auto. inv MREG ; auto.
  intro Hcont. destruct r ; destruct res.
  eapply Bij.INJ' in Hcont ; eauto. 
  kick_valid.
  
  (* iload *)
  normalized pc.   
  exists  (RTL.State ts tf sp pc' (rs'#(Bij.pamr (fn_max_indice f) dst) <- v) m). split.
  eapply plus_one ; eauto. 
  econstructor 3 ; eauto.
  rewrite <- H0 ; eauto.
  erewrite match_regset_args ; eauto with valagree. 
  kick_valid. 
  econstructor 1 ; auto.
  constructor. intros. destruct (p2eq dst r).
  inv e. rewrite P2Map.gss. rewrite PMap.gss; auto.
  rewrite P2Map.gso; auto. rewrite PMap.gso; auto. inv MREG ; auto.
  intro Hcont. destruct r ; destruct dst.
  eapply Bij.INJ' in Hcont ; eauto. kick_valid. 

  (* istore *)
  normalized pc. 
  exists  (RTL.State ts tf sp pc' rs' m'). split.
  eapply plus_one ; eauto. 
  econstructor 4 with (a:= a) ; eauto. 
  rewrite <- H0 ; eauto with valagree.
  erewrite match_regset_args ; eauto with valagree.
  kick_valid. 
  inv MREG.  rewrite <- H3 ; eauto.
  kick_valid. 
  econstructor 1 ; auto. 
  
  (* icall *)
  normalized pc. 
  destruct ros.
  exploit (spec_ros_r_find_function (fn_max_indice f) rs rs') ; eauto.
  inv MREG ; auto. eapply H2 ; eauto. kick_valid. 
  ((intros [tf' [Hfind OKtf']]);
    (exists (RTL.Callstate (RTL.Stackframe (Bij.pamr (fn_max_indice f) res) tf sp pc' rs' :: ts) tf' rs' ## (map (Bij.pamr (fn_max_indice f)) args) m) ; split;
      [(eapply plus_one ; eauto);
        (eapply RTL.exec_Icall  ; eauto); 
        (eauto with valagree)
        | ])).
  case_eq (ros_pamr (fn_max_indice f) (inl ident r)); intros i Heq ; rewrite Heq in *; inv H5.  
  unfold ros_pamr in Heq.
  match goal with 
    | [H: (if ?t_if then _ else _) = _ |- _ ] => destruct t_if ; try congruence ; inv H
  end. 
  replace (RTL.funsig tf') with (funsig fd).
  auto. symmetry. eapply sig_fundef_translated ; eauto. 
  
  erewrite match_regset_args ; eauto.
  econstructor ; eauto. 
  econstructor ; eauto. kick_valid.
  (eapply Genv.find_funct_prop ; eauto).
  kick_valid.
   
  exploit (spec_ros_id_find_function  rs rs') ; eauto.
  ((intros [tf' [Hfind OKtf']]);
    (exists (RTL.Callstate (RTL.Stackframe (Bij.pamr (fn_max_indice f) res) tf sp pc' rs' :: ts) tf' rs' ## (map (Bij.pamr (fn_max_indice f)) args) m) ; split;
      [(eapply plus_one ; eauto);
        (eapply RTL.exec_Icall  ; eauto); 
        (eauto with valagree)
        | ])).
  case_eq (ros_pamr (fn_max_indice f) (inr reg i)); intros i' Heq ; rewrite Heq in *; inv H5.  
  unfold ros_pamr in Heq. inv Heq.
  replace (RTL.funsig tf') with (funsig fd).
  auto. symmetry. eapply sig_fundef_translated ; eauto. 
  erewrite match_regset_args ; eauto.  
  econstructor ; eauto. 
  econstructor ; eauto. kick_valid.
  simpl in H0.
  destruct Genv.find_symbol in H0.
  eapply Genv.find_funct_ptr_prop ; eauto.
  congruence.
  kick_valid.

  (* itailcall *)
    normalized pc.
    destruct ros.
    case_eq (ros_pamr (fn_max_indice f) (inl ident r)); intros i' Heq ; rewrite Heq in *; inv H6.  
    unfold ros_pamr in Heq. 
    match goal with 
      | [H: (if ?t_if then _ else _) = _ |- _ ] => destruct t_if ; try congruence ; inv H
    end.    
    
    exploit (spec_ros_r_find_function (fn_max_indice f) rs rs') ; eauto.
    inv MREG ; eauto. eapply H3 ; eauto. 
    kick_valid. 
    
    (intros [tf' [Hfind OKtf']]);
    (exploit (sig_function_translated f tf) ; eauto ; intros);
    ((exists (RTL.Callstate ts tf' rs'##(map (Bij.pamr (fn_max_indice f)) args) m');  split);
      [  (eapply plus_one ; eauto); 
        (eapply RTL.exec_Itailcall ; eauto with valagree);
        (replace (RTL.fn_stacksize tf) with (fn_stacksize f); eauto with valagree)
        | ]).

    replace (rs' ## (map (Bij.pamr (fn_max_indice f)) args)) with (rs##2 args).
    econstructor ; eauto.
    simpl in H0.
    eapply Genv.find_funct_prop ; eauto.
    simpl in H0.
    eapply match_regset_args ; eauto. 
    kick_valid. 
    
    case_eq (ros_pamr (fn_max_indice f) (inr reg i)); intros i' Heq ; rewrite Heq in *; inv H6.  
    unfold ros_pamr in Heq. inv Heq.
    
    exploit (spec_ros_id_find_function  rs rs') ; eauto.    
    (intros [tf' [Hfind OKtf']]);
    (exploit (sig_function_translated f tf) ; eauto ; intros);
    ((exists (RTL.Callstate ts tf' rs'##(map (Bij.pamr (fn_max_indice f)) args) m');  split);
      [  (eapply plus_one ; eauto); 
        (eapply RTL.exec_Itailcall ; eauto with valagree);
        (replace (RTL.fn_stacksize tf) with (fn_stacksize f); eauto with valagree)
        | ]).
    
    replace (rs' ## (map (Bij.pamr (fn_max_indice f)) args)) with (rs##2 args).
    econstructor ; eauto.
    simpl in H0.    
    destruct Genv.find_symbol in H0.
    eapply Genv.find_funct_ptr_prop ; eauto.
    congruence.
    eapply match_regset_args ; eauto.
    kick_valid.
    
  (* ibuiltin *)
  normalized pc. 
  exists  (RTL.State ts tf sp pc' (rs'#(Bij.pamr (fn_max_indice f) res) <- v) m'). split.
  eapply plus_one ; eauto. 
  eapply RTL.exec_Ibuiltin ; eauto.
  erewrite <- match_regset_args ; eauto .
  eapply external_call_symbols_preserved; eauto with valagree.
  kick_valid.
  econstructor 1 ; eauto. 
  
  constructor. intros.
  destruct (p2eq res r).
  inv e. rewrite P2Map.gss. rewrite PMap.gss; auto.
  rewrite P2Map.gso; auto. rewrite PMap.gso; auto. inv MREG ; auto.
  intro Hcont. destruct r ; destruct res.
  eapply Bij.INJ' in Hcont ; eauto. kick_valid. 
    
  (* ifso *)
  normalized pc.
  exists (RTL.State ts tf sp ifso rs' m); split ; eauto. 
  eapply plus_one ; eauto.  
  eapply RTL.exec_Icond ; eauto. 
  erewrite <- match_regset_args ; eauto with valagree.
  kick_valid. reflexivity.

  (* ifnot *)
  normalized pc.
  exists (RTL.State ts tf sp ifnot rs' m); split ; eauto. 
  eapply plus_one ; eauto. 
  eapply RTL.exec_Icond ; eauto. 
  erewrite <- match_regset_args ; eauto with valagree.
  kick_valid. reflexivity.

  (* ijump *)
  normalized pc.
  exists (RTL.State ts tf sp pc' rs' m); split ; eauto. 
  eapply plus_one ; eauto.
  eapply RTL.exec_Ijumptable ; eauto.
  inv MREG. erewrite <- H3 ; eauto.
  kick_valid.
    
  (* ireturn *)
  (exploit transl_function_charact ; eauto; intros).
  (exploit transl_function_spec_ok ; eauto; intros).
  normalized pc.
  case_eq (opt_pamr (fn_max_indice f) or) ; intros opt Hopt; rewrite Hopt in *; inv H9. 
  exists (RTL.Returnstate ts (regmap_optget opt Vundef rs') m'); split ; eauto. 
  eapply plus_one ; eauto.
  eapply RTL.exec_Ireturn ; eauto.
  rewrite <- H0 ; eauto with valagree.
  rewrite stacksize_preserved with f tf ; eauto.
  destruct or ; simpl; eauto.
  inv MREG. rewrite H4 ; eauto. 
  simpl in Hopt. destruct Bij.valid_index; inv Hopt. eauto.
  kick_valid.
  simpl in Hopt. inv Hopt. eauto.  

  (* internal *)
  simpl in SPEC. Errors.monadInv SPEC. simpl in STACK.
  exists (RTL.State ts x
    (Vptr stk Int.zero)
    f.(fn_entrypoint)
    (RTL.init_regs args x.(RTL.fn_params))
    m').
  split.
  eapply plus_one ; eauto.
  replace (fn_entrypoint f) with (RTL.fn_entrypoint x).  
  eapply RTL.exec_function_internal; eauto.
  rewrite stacksize_preserved with f x in H ; auto.
  exploit transl_function_charact ; eauto.
  intros. inv H0.  auto.  
  constructor ; eauto.
  exploit transl_function_charact ; eauto.
  intros. inv H0.  auto.  
  inv WFF ; auto.
  constructor ; eauto.  
  exploit transl_function_charact ; eauto. intros SPEC.
  inv SPEC ; auto. simpl.
  intros ; eapply init_reg_match_regset ; eauto.
  
  
  (* external *)
  inv SPEC.
  exists (RTL.Returnstate ts res m'). split. 
  eapply plus_one ; eauto.
  eapply RTL.exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto with valagree.
  econstructor ; eauto.
  
  (* return state *)
  inv STACK. 
  exists (RTL.State ts0 tf sp pc (rs'# (Bij.pamr (fn_max_indice f) res) <- vres) m).
  split. eapply plus_one ; eauto. constructor ; eauto.
  constructor ; auto.
  constructor. intros. 
  destruct (p2eq res r).
  inv e. rewrite P2Map.gss. rewrite PMap.gss; auto.
  rewrite P2Map.gso; auto. rewrite PMap.gso; auto. inv MREG ; auto.
  intro Hcont. destruct r ; destruct res.
  eapply Bij.INJ' in Hcont; eauto. 
Qed.

(** * Semantics preservation *)  
Theorem transf_program_correct:
  forward_simulation (SSA.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus with (match_states := match_states). 
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transl_step_correct.
Qed.

End PRESERVATION.