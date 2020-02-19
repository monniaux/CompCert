(** Destruction of the SSA form : translation from SSA back to RTL. *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import CminorSel.
Require Import RTL.
Require Import Kildall. 
Require Import Utils.
Require Import SSA.
Require Import SSAutils.
Require Import Bijection.

Local Open Scope string_scope.

(** * Monad state for the transformation *)
Record state : Type := mkstate {
  st_nextnode_cp:   node;        (** next point to copy *)
  st_first_fs:      node;        (** the least fresh node where to add a move, constant *)
  st_nextnode_fs:   node;        (** the next node where to add *)
  st_code:          RTL.code;
  st_wf_next:       Plt st_nextnode_cp st_first_fs ; (** copied nodes and fresh nodes are diff *)
  st_wf_next_fs :   Ple st_first_fs st_nextnode_fs ; (** first fresh comes before the next fresh *)
  st_wf: forall (pc: node), 
    Plt pc st_nextnode_cp                            (** node already copied *)
    \/ (Plt pc st_nextnode_fs /\ Ple st_first_fs pc) (** a move node has already been added *)
    \/ st_code!pc = None                             (** no instruction yet *)    
}.


Inductive state_incr: state -> state -> Prop :=
| state_incr_intro : forall (s1 s2: state),
  Ple (st_nextnode_cp s1) (st_nextnode_cp s2) ->
  Ple (st_nextnode_fs s1) (st_nextnode_fs s2) ->
  (st_first_fs s1 = st_first_fs s2) ->
  (forall pc, s1.(st_code)!pc = None \/ s1.(st_code)!pc = s2.(st_code)!pc) ->
  state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. 
  econstructor ; eauto. 
  apply Ple_refl.
  apply Ple_refl.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0 ; intuition.
  econstructor ; eauto.
  apply Ple_trans with (st_nextnode_cp s2); assumption.
  apply Ple_trans with (st_nextnode_fs s2); assumption.  
  congruence.
  intros.
  generalize (H4 pc) (H7 pc). intuition.
  left ; congruence.
  right ; congruence.
Qed.

(** ** Additional Monadic machinery *)
Inductive res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> forall (s': state), state_incr s s' -> res A s.

Implicit Arguments OK [A s].
Implicit Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret (A: Type) (x: A) : mon A :=
  fun (s: state) => OK x s (state_incr_refl s).

Implicit Arguments ret [A].

Definition error (A: Type) (msg: Errors.errmsg) : mon A := fun (s: state) => Error msg.

Implicit Arguments error [A].

Definition bind (A B: Type) (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i'  => OK b s'' (state_incr_trans s s' s'' i i')
        end
    end.

Implicit Arguments bind [A B].

Definition bind2 (A B C: Type) (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Implicit Arguments bind2 [A B C].

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Fixpoint mfold_unit {A: Type} (f: A -> mon unit) (l: list A) : mon unit :=
  match l with
    | nil => ret tt
    | hd :: tl => (do rhd <- f hd ; mfold_unit f tl)
  end.

Fixpoint mfold {A B: Type} (f: A -> B -> mon B) (l: list A) (b: B) : mon B :=
  match l with
    | nil => ret b
    | hd :: tl =>
      do rhd <- f hd b;
      mfold f tl rhd
  end.

(** * DeSSA transformation *)

(** ** Getting the code boundaries *)
Definition get_max {A: Type} (t: PTree.t A) : (positive * list positive) :=
  let elts := map (@fst positive A) (PTree.elements t) in
    fold_left (fun (al: positive * list positive) pc => 
      let (a,l) := al in if plt a pc then (pc,pc::l) else (a,pc::l)) elts (xH,nil).

Definition get_min {A: Type} (t: PTree.t A) (max: positive) : positive :=
  let elts := map (@fst positive A) (PTree.elements t) in
    fold_left (fun acc pc => if plt pc acc then pc else acc) elts max.

Lemma get_max_fold_aux' : forall l e maxacc lacc, 
  In e l \/ In e lacc ->
  In e (snd (fold_left (fun (al: positive * list positive) pc => 
    let (a,l) := al in 
    if plt a pc then (pc, pc::l) else (a, pc::l)) l (maxacc,lacc))).
Proof.
  induction l ; intros; inv H; try inv H0; simpl; auto;
    [ destruct (plt maxacc e) ;  eapply IHl ; eauto
      | destruct (plt maxacc a) ;  eapply IHl ; eauto
      | destruct (plt maxacc a) ;  eapply IHl ; eauto]. 
Qed.   

Lemma get_max_fold_aux : forall l maxacc lacc,
  Ple maxacc (fst (fold_left (fun (al: positive * list positive) pc => 
    let (a,l) := al in 
    if plt a pc then (pc, pc::l) else (a, pc::l)) l (maxacc,lacc))).
Proof.
  induction l ; intros.
  simpl. apply Ple_refl.
  simpl.
  destruct (plt maxacc a).
  assert (Ha := IHl a).
  eapply Plt_Ple in p.  
  eapply (Ple_trans maxacc a (fst (fold_left (fun (al : positive * list positive) (pc : positive) =>
                let (a, l) := al in
                if plt a pc then (pc, pc :: l) else (a, pc :: l)) l (a,a::lacc)))); eauto.
  eapply IHl ; eauto.
Qed.
Lemma get_max_fold : forall l pc maxacc lacc,
  In pc l ->
  Ple pc (fst (fold_left (fun (al: positive * list positive) pc => let (a,l) := al in if plt a pc then (pc,pc::l) else (a,pc::l)) l (maxacc,lacc))).
Proof.
  induction l ; intros ; inv H.
  simpl.
  destruct (plt maxacc pc).
  eapply get_max_fold_aux ; eauto.
  assert (Ple pc maxacc) by (unfold Plt, Ple in * ;  zify ; omega).
  assert (Htr:= get_max_fold_aux l maxacc).
  eapply Ple_trans ; eauto.
  simpl.
  destruct (plt maxacc a); eapply IHl ; eauto.
Qed.

Lemma get_max_in : forall (A: Type) t pc (a:A), 
  t ! pc = Some a -> In pc (snd (get_max t)).
Proof.
  unfold get_max ; intros.
  exploit PTree.elements_correct ; eauto. intros.
  assert (Hinpc : In (fst (pc,a)) (map (@fst positive A) (PTree.elements t))) by (eapply in_map ; eauto).
  simpl in Hinpc. 
  eapply (get_max_fold_aux'); eauto.
Qed.  

Lemma get_max_lt {A: Type} : forall t pc (a:A),
    t ! pc = Some a -> Plt pc (Psucc (Psucc (fst (get_max t)))).
Proof.
  unfold get_max ; intros.
  exploit PTree.elements_correct ; eauto. intros.
  assert (Hinpc : In (fst (pc,a)) (map (@fst positive A) (PTree.elements t))) by (eapply in_map ; eauto).
  simpl in Hinpc.
  eapply Ple_Plt_succ ; eauto.
  eapply Plt_Ple ; eauto.
  eapply Ple_Plt_succ ; eauto.
  eapply get_max_fold ; eauto.  
Qed.

Ltac sz := unfold Plt, Ple in * ; zify ; omega.

Notation plus_2 :=  (fun p => (Psucc (Psucc p))). 

Lemma get_min_fold_aux : forall l minacc,
  Ple (fold_left (fun a pc => if plt pc a then pc else a) l minacc) minacc.
Proof.
  induction l ; intros.
  simpl. apply Ple_refl.
  simpl.
  destruct (plt a minacc).
  assert (Ha := IHl a).
  eapply Plt_Ple in p.
  eapply (Ple_trans (fold_left (fun a pc => if plt pc a then pc else a) l a) a minacc ); eauto.
  eapply IHl ; eauto.
Qed.

Lemma min_max : forall (code:code), 
  Ple (get_min code (fst (get_max code))) (fst (get_max code)).
Proof.
  intros. generalize get_min_fold_aux; intros.
  unfold get_min. eauto.
Qed.

(** ** Initial state of the monad *)
Lemma init_state_wf_next : forall f,
  Plt (get_min (fn_code f) (fst (get_max (fn_code f)))) (plus_2 (fst (get_max (fn_code f)))).
Proof.
intros. 
generalize (min_max (fn_code f)) ; intros ; sz ; omega.
Qed.

Lemma init_state_wf :
  forall f,
    let max := fst (get_max (fn_code f)) in
      forall  pc,
        Plt pc (get_min (fn_code f) max)
        \/ (Plt pc (plus_2 max)) /\ (Ple (plus_2 max) pc)
    \/ (PTree.empty RTL.instruction) ! pc = None.
Proof.
  intros.
  right ; right.
  apply PTree.gempty.
Qed.

Definition init_state (f: SSA.function) : (state * positive * list positive) :=
  let maxlp := (get_max (fn_code f)) in 
    ((mkstate 
      (get_min (fn_code f) (fst maxlp))
      (plus_2 (fst maxlp))
      (plus_2 (fst maxlp))
      (PTree.empty RTL.instruction)
      (init_state_wf_next _ )
      (Ple_refl (plus_2 (fst maxlp)))
      (init_state_wf f)) , fst maxlp, snd maxlp).

(** ** Auxiliary functions *)
(** [next code pc diff] gets the next copy point in code [code] starting from [pc]. Should terminate after [diff] steps of recursion *)
Fixpoint next (code : code) (pc:node) (diff: nat)  : node := 
  match code ! pc with 
    | Some _ => pc
    | None => 
      match diff with 
        | O => pc (* corner case when pc = max *)
        | S k => next code (Psucc pc) k
      end
  end.
  
Lemma next_lt : forall code  diff pc,
  Plt pc (next code (Psucc pc) diff).
Proof.
  induction diff ; intros.
  simpl. destruct (code ! (Psucc pc)) ; apply Plt_succ.  
  simpl. destruct (code ! (Psucc pc)).
  apply Plt_succ.
  assert (HH:= IHdiff (Psucc pc)).
  exploit Plt_succ; eauto. 
Qed.  

(** [copy_ins pc max ins code] copies the instruction [ins] at program point [pc] that should be in the code [code]. *)
  
Lemma copy_ins_wf : forall s i code diff pc ,
  Plt pc (next code (Psucc (st_nextnode_cp s)) diff)  \/
  Plt pc (st_nextnode_fs s) /\ Ple (st_first_fs s) pc \/
  (PTree.set (st_nextnode_cp s) i (st_code s)) ! pc = None.
Proof.
  intros.
  destruct (peq pc (st_nextnode_cp s)).
  subst. left. apply next_lt ; auto.
  destruct (st_wf s pc).
  left.
  generalize (next_lt code diff (st_nextnode_cp s)) ; intros.
  eapply Plt_trans in H0; eauto. 
  intuition.
  right. right. rewrite PTree.gso ; auto.
Qed.

Lemma copy_ins_incr : forall code diff  s ins
  (H : Plt (next code (Psucc (st_nextnode_cp s)) diff) (st_first_fs s)),
  state_incr s
  (mkstate
    (next code (Psucc (st_nextnode_cp s)) diff)
    (st_first_fs s)
    (st_nextnode_fs s)
    (PTree.set (st_nextnode_cp s) ins (st_code s))
    H
    (st_wf_next_fs s)
    (copy_ins_wf s ins code diff)).
Proof.
  intros.
  econstructor ; eauto ; simpl.
  apply Plt_Ple. apply next_lt.
  apply Ple_refl.
  intros.
  destruct (st_wf s pc) ; simpl in *.
  rewrite PTree.gso ; auto ; sz.
  intuition.
  rewrite PTree.gso ; auto.
  generalize (next_lt code diff (st_nextnode_cp s)) ; intros.
  sz.
Qed.

Definition copy_ins (pc max: node) (ins: RTL.instruction) (code: code) : mon unit := 
  fun s => 
    let nx_cp := st_nextnode_cp s in 
      let nxt := (next code (Psucc nx_cp) (((nat_of_P max) - (S (nat_of_P pc)))%nat)) in
        match plt nxt (st_first_fs s) with 
          | left H =>
            match peq pc nx_cp with 
              | left H' =>
                OK tt 
                (mkstate 
                  nxt
                  (st_first_fs s)
                  (st_nextnode_fs s)
                  (PTree.set nx_cp ins (st_code s))
                  H
                  (st_wf_next_fs s)
                  (copy_ins_wf s ins _ _ ))
                (copy_ins_incr _ _ _ _ H)
              | right _ => Error (Errors.msg (pos_to_string pc)) 
            end
          | right _ => Error (Errors.msg "")
        end.

(** [incr_next_cp] just goes to the next program point to copy *)
Lemma incr_next_cp_wf : forall s (H : Plt (Psucc (st_nextnode_cp s)) (st_first_fs s)), 
  forall pc : node,
             Plt pc (Psucc (st_nextnode_cp s)) \/
             Plt pc (st_nextnode_fs s) /\ Ple (st_first_fs s) pc \/
             (st_code s) ! pc = None.
Proof.
  intros.
  destruct (st_wf s pc).
  left ; sz.
  intuition.
Qed. 

Lemma incr_next_cp_incr : forall s H, 
  state_incr s (mkstate 
    (Psucc (st_nextnode_cp s))
    (st_first_fs s)
    (st_nextnode_fs s)
    (st_code s)
    H
    (st_wf_next_fs s) 
    (incr_next_cp_wf s H)).
Proof.
  intros.
  constructor ; auto; simpl in *; sz.
Qed.

(** Adding a [Inop] *)
Lemma add_nop_pc_wf : forall s ins pc,
             Plt pc (st_nextnode_cp s) \/
             Plt pc (Psucc (st_nextnode_fs s)) /\ Ple (st_first_fs s) pc \/
             (PTree.set (st_nextnode_fs s)  ins (st_code s)) ! pc = None.
Proof.
  intros.
  destruct (peq pc (st_nextnode_fs s)). 
  inv e. right ; left. split. apply Plt_succ ; auto.
  generalize (st_wf_next_fs s) (st_wf_next s) ; intros. auto.
  
  destruct (st_wf s pc).
  left. auto. 
  intuition.
  right ; left.
  split ; auto. eapply Plt_trans ; eauto. eapply Plt_succ.
  
  right. right. rewrite PTree.gso ; auto.
Qed.

Lemma add_nop_pc_incr : forall s ins, 
  state_incr s (mkstate 
      (st_nextnode_cp s)
      (st_first_fs s)
      (Psucc (st_nextnode_fs s))
      (PTree.set (st_nextnode_fs s) ins (st_code s))
      (st_wf_next s)
      (Ple_trans _ _ _ (st_wf_next_fs s) (Ple_succ (st_nextnode_fs s)) )
      (add_nop_pc_wf s ins)).
Proof.
  intros.
  econstructor ; eauto ; simpl in *.
  apply Ple_refl.
  apply Ple_succ.
  
  intros.
  destruct (st_wf s (st_nextnode_fs s)).
  generalize (st_wf_next_fs s) (st_wf_next s); intros.
  apply False_ind. sz.

  intuition.
  generalize (st_wf_next_fs s) (st_wf_next s); intros.
  apply False_ind. sz.
  
  destruct (peq pc (st_nextnode_fs s)).
  inv e. auto.
  rewrite PTree.gso ; auto ; sz.
Qed.
  
Definition add_nop_pc (ins: RTL.instruction) : mon unit := 
  fun s => 
    OK tt 
    (mkstate 
      (st_nextnode_cp s)
      (st_first_fs s)
      (Psucc (st_nextnode_fs s))
      (PTree.set (st_nextnode_fs s) ins (st_code s))
      (st_wf_next s)
      (Ple_trans _ _ _ (st_wf_next_fs s) (Ple_succ (st_nextnode_fs s)))
      (add_nop_pc_wf s ins))
    (add_nop_pc_incr _ _).


(** Replacing phi-instructions with copies *)
Lemma empty_block_wf : forall s size arg_r arg_i dst_r dst_i pc,
  Plt pc (st_nextnode_cp s) \/
  Plt pc (Psucc (st_nextnode_fs s)) /\ Ple (st_first_fs s) pc \/
  (PTree.set (st_nextnode_fs s) (RTL.Iop Omove ((Bij.pamr size (arg_r,arg_i))::nil) (Bij.pamr size (dst_r, dst_i)) (Psucc (st_nextnode_fs s))) (st_code s)) ! pc = None.
Proof.
  intros.
  destruct (peq pc (st_nextnode_fs s)). 
  inv e. right ; left. 
  split. apply Plt_succ ; auto.
  apply (st_wf_next_fs s).
  destruct (st_wf s pc) as [Hcase1 | [ [Hcase21 Hcase22] | Hcase3]].  
  left ; auto.
  right ; left. intuition.
  apply Ple_Plt_succ ; eauto.
  apply Plt_Ple ; auto.
  right ; right.
  rewrite PTree.gso ; auto.
Qed.

Lemma empty_block_incr : forall s size dst_r dst_i arg_r arg_i, 
  state_incr s 
  (mkstate 
    (st_nextnode_cp s)
    (st_first_fs s)
    (Psucc (st_nextnode_fs s) )
    (PTree.set (st_nextnode_fs s) (RTL.Iop Omove ((Bij.pamr size (arg_r,arg_i))::nil) (Bij.pamr size (dst_r,dst_i)) (Psucc (st_nextnode_fs s))) (st_code s))
    (st_wf_next s)
    (Ple_trans _ _ _ (st_wf_next_fs s) (Ple_succ (st_nextnode_fs s)))
    (empty_block_wf s size arg_r arg_i dst_r dst_i)).
Proof.
  intros.
  econstructor ; eauto ; simpl in *.
  apply Ple_refl.
  apply Ple_succ.
  intros.
  destruct (st_wf s pc) ; simpl in *.
  generalize (st_wf_next_fs s) ; intros.
  generalize (st_wf_next s) ; intros.
  right. rewrite PTree.gso; auto. intro Hcont. inv Hcont. sz.
  
  intuition. 
  right. rewrite PTree.gso ; auto.
Qed.

Definition valid_ind (size:nat) (r : SSA.reg) : bool := 
  Bij.valid_index size (snd r).
  
Definition empty_block (size : nat) (k: nat) (phi : phiinstruction) (pc:node): mon node := 
  fun s =>     
    match phi with 
      | Iphi args (dst_r,dst_i) =>
        if (forallb (valid_ind size) ((dst_r,dst_i)::args)) then
          let nx_fs := st_nextnode_fs s in 
            match nth_error args k with 
              | None => Error (Errors.msg "") 
              | Some (arg_r,arg_i) => 
                OK (Psucc nx_fs) 
                (mkstate 
                  (st_nextnode_cp s)
                  (st_first_fs s)
                  (Psucc nx_fs)
                  (PTree.set nx_fs (RTL.Iop Omove ((Bij.pamr size (arg_r,arg_i))::nil) (Bij.pamr size (dst_r,dst_i)) (Psucc nx_fs)) (st_code s))
                  (st_wf_next s)
                  (Ple_trans _ _ _ (st_wf_next_fs s) (Ple_succ nx_fs))
                  (empty_block_wf s size arg_r arg_i dst_r dst_i))
                (empty_block_incr _ _ _ _ _ _)
            end
          else Error (Errors.msg "") 
    end.    


Definition empty_the_block (size: nat) (k: nat) (block : phiblock) : mon node :=
  fun s => 
    mfold (empty_block size k) block (st_nextnode_fs s) s.

(** Unindexing register in the code *)
Definition ros_pamr (size: nat) (ros : reg + ident) : Errors.res (Registers.reg + ident) :=
  match ros with 
    | inl r => 
      if (Bij.valid_index size (snd r)) then Errors.OK (inl ident (Bij.pamr size r))
        else Errors.Error (Errors.msg "")
    | inr id => Errors.OK (inr Registers.reg id) 
  end.

Definition opt_pamr (size: nat) (rop : option reg) : Errors.res (option Registers.reg) :=
  match rop with 
    | Some r => 
      if (Bij.valid_index size (snd r)) then 
        Errors.OK (Some (Bij.pamr size r))
        else  Errors.Error (Errors.msg " ")
    | _ => Errors.OK None 
  end.

Definition map_pamr (size: nat) (ins : instruction) : Errors.res RTL.instruction :=
  match ins with 
    | Inop s =>  Errors.OK (RTL.Inop s)

    | Iop op args dst s => 
      if (forallb (valid_ind size) (dst::args))
        then Errors.OK (RTL.Iop op (map (Bij.pamr size) args) (Bij.pamr size dst) s)
        else Errors.Error (Errors.msg "")

    | Iload ch ad args dst s =>  
      if (forallb (valid_ind size) (dst::args))
        then Errors.OK (RTL.Iload ch ad (map (Bij.pamr size) args) (Bij.pamr size dst) s)
        else Errors.Error (Errors.msg "")
          
    | Istore ch ad args src s => 
      if (forallb (valid_ind size) (src::args))
        then Errors.OK (RTL.Istore ch ad (map (Bij.pamr size) args) (Bij.pamr size src) s)
        else Errors.Error (Errors.msg "")

    | Icall sig ros args dst s => 
      if (forallb (valid_ind size) (dst::args))
        then 
          match (ros_pamr size ros) with 
            | Errors.Error _ => Errors.Error (Errors.msg "")
            | Errors.OK optg => Errors.OK (RTL.Icall sig optg (map (Bij.pamr size) args) (Bij.pamr size dst) s)       
          end
        else Errors.Error (Errors.msg "")

    | Itailcall sig ros args => 
      if (forallb (valid_ind size) args)
        then 
          match (ros_pamr size ros) with 
            | Errors.Error _ => Errors.Error (Errors.msg "")
            | Errors.OK optg => Errors.OK (RTL.Itailcall sig optg (map (Bij.pamr size) args)) 
          end
        else Errors.Error (Errors.msg "")

    | Ibuiltin ef args dst s => 
      if (forallb (valid_ind size) (dst::args))
        then Errors.OK (RTL.Ibuiltin ef (map (Bij.pamr size) args) (Bij.pamr size dst) s)
        else Errors.Error (Errors.msg "")

    | Icond cond args ifso ifnot => 
      if (forallb (valid_ind size) args)
        then Errors.OK (RTL.Icond cond (map (Bij.pamr size) args) ifso ifnot)
        else Errors.Error (Errors.msg "")

    | Ijumptable arg tbl => 
      if (valid_ind size arg)
        then Errors.OK (RTL.Ijumptable (Bij.pamr size arg) tbl)
        else Errors.Error (Errors.msg "")

    | Ireturn rop => 
      match (opt_pamr size rop) with 
        | Errors.Error _ => Errors.Error (Errors.msg "")
        | Errors.OK optg => Errors.OK (RTL.Ireturn optg)
      end
  end.

(** ** Copying the code of the function, whilst performing unindexing and replacement of phi-blocks *)
Definition copy_inop (pc max: node) (code:code) : mon unit :=
  fun s => copy_ins pc max (RTL.Inop (st_nextnode_fs s)) code s.

Definition copy_wwo_add (size: nat) (preds: PTree.t (list node)) (code : code) (pcode : phicode) (max pc: node) : mon unit :=
  fun s =>
    match code ! pc with 
      | None => 
        match plt (Psucc (st_nextnode_cp s)) (st_first_fs s) with 
          | left H =>
            OK tt (mkstate 
              (Psucc (st_nextnode_cp s))
              (st_first_fs s)
              (st_nextnode_fs s)
              (st_code s)
              H
              (st_wf_next_fs s) 
              (incr_next_cp_wf s H))
            (incr_next_cp_incr s H)
          | right _ => Error (Errors.msg "") 
        end
      | Some (Inop succ) => 
        match pcode ! succ with 
          | None => copy_ins pc max (RTL.Inop succ) code s
          | Some block => 
            match index_pred preds pc succ with
              | None => Error (Errors.msg "") 
              | Some k => (* ajout du nop avec modif succ, puis vider le block, puis nop *)
                (do u <- copy_inop pc max code ; 
                 do n <- empty_the_block size k block ; 
                 do u' <- add_nop_pc (RTL.Inop succ) ; 
                 ret tt) s              
          end
      end
    | Some ins => 
      match (map_pamr size ins) with 
        | Errors.Error _ => Error (Errors.msg "")
        | Errors.OK ins => copy_ins pc max ins code s
      end
  end.

(** ** Sorting a list *)
Lemma Ple_total : forall p1 p2, Ple p1 p2 \/ Ple p2 p1.
Proof.
  intros.
  unfold Ple. zify ; omega.
Qed.

Lemma Ple_dec : forall p1 p2, {Ple p1 p2} + {~ Ple p1 p2}.
Proof.
  intros.
  unfold Ple in *.
  generalize (zle (Zpos p1) (Zpos p2)) ; eauto; intros.
  case H; intros ; eauto.
Qed.

Require Import List Setoid Permutation Sorted Orders.

Module PosOrder <: TotalLeBool.
  Definition t := positive.
  Definition leb x y := 
    match Ple_dec x y with 
      | left _ => true
      | right _ => false
    end.
  Infix "<=?" := leb (at level 70).
  Theorem leb_total : forall a1 a2, a1 <=? a2 = true \/ a2 <=? a1 = true.
    Proof. 
      intros.
      unfold leb.
      destruct (Ple_total a1 a2); (destruct (Ple_dec); intuition).
      right. destruct (Ple_dec); intuition.
    Qed.
End PosOrder.

Require Import Sorting.
Module Import PosSort := Mergesort.Sort PosOrder.

Definition sort_pp (l : list node) := sort l.

(** ** Checking that phi-blocks are parallelizable *)
(** The DeSSA transformation fails on non-parallel blocks *)
Require Import GVNopt.

Definition phi_uses (phib:phiblock) : list (reg * SSARegSet.t) :=
  List.map (fun phi:phiinstruction =>
    let (args,dst) := phi in (dst,fold_right SSARegSet.add SSARegSet.empty args))
  phib.

Lemma phi_uses_In1: forall phib dst args,
  In (Iphi args dst) phib -> exists s, In (dst,s) (phi_uses phib).
Proof.
  induction phib; simpl.
  intuition.
  destruct 1; subst; eauto.
  eelim IHphib; eauto.
Qed.

Lemma phi_uses_In2: forall phib dst args arg,
  In (Iphi args dst) phib -> In arg args ->  
  exists s, In (dst,s) (phi_uses phib) /\ SSARegSet.In arg s.
Proof.
  induction phib; simpl.
  intuition.
  destruct 1; subst; intros.
  econstructor; split.
  left; eauto.
  apply In_fold_right_add1; auto.
  eelim IHphib; eauto.
  intros s [S1 S2].
  exists s; split; auto.
Qed.

Definition check_para_block (phic:phicode) : bool :=
  PTree.fold (fun res pc phib =>
    res &&
    let uses := phi_uses phib in
      List.forallb
      (fun du:reg*SSARegSet.t => let (d,_) := du in
        List.forallb
        (fun du':reg*SSARegSet.t => let (d',uses') := du' in
          p2eq d d' || negb (SSARegSet.mem d uses'))
        uses)
      uses)
  phic true.

Lemma check_para_block_ok : forall f, 
  check_para_block (fn_phicode f) = true ->
  forall pc block,
    (fn_phicode f) ! pc = Some block ->
    para_block block.
Proof.
  unfold check_para_block; intros.
  generalize (ptree_forall _ _ _ H _ _ H0); clear H; intros.
  rewrite forallb_forall in H.
  intros d args arg H1 H2 H3 args' H4.
  elim phi_uses_In1 with (1:=H4); intros s Hs.
  generalize (H _ Hs); clear H; intros.
  rewrite forallb_forall in H.
  elim phi_uses_In2 with (1:=H1) (2:=H2); intros s' [Hs' Hs''].
  generalize (H _ Hs'); clear H; intros.
  destruct p2eq; simpl in *.
  intuition.
  case_eq (SSARegSet.mem arg s'); intros.
  rewrite H5 in *; inv H.
  assert (~(SSARegSet.mem arg s'=true)) by congruence.
  elim H6; apply SSARegSet.mem_1; auto.
Qed.

(** ** Alltogether: Transformation from an SSA function to RTL function. *)
Definition transl_function_v1 (f: SSA.function) : Errors.res RTL.function :=
  let '(init,max,lp) := init_state f in 
    let preds := make_predecessors (fn_code f) successors_instr in
      if (check_para_block (fn_phicode f)) then 
        match mfold_unit (copy_wwo_add (fn_max_indice f) preds (fn_code f) (fn_phicode f) max) (sort_pp lp) init with
          | Error m => Errors.Error m
          | OK u s'' H => 
            if (forallb (valid_ind (fn_max_indice f)) f.(SSA.fn_params)) then
              Errors.OK (RTL.mkfunction
                f.(SSA.fn_sig)
                (map (Bij.pamr (fn_max_indice f)) f.(SSA.fn_params))
                f.(SSA.fn_stacksize)
                s''.(st_code)
                f.(SSA.fn_entrypoint)
                nil)
              else Errors.Error (Errors.msg "")
        end
        else Errors.Error (Errors.msg "").

Definition transl_function := transl_function_v1.

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p: SSA.program) : Errors.res RTL.program :=
  transform_partial_program transl_fundef p.