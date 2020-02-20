
(** Translation of RTL that normalizes the function code: it ensures
that only a [Inop] can lead to a junction point, and that the entry
point of the function both (i) holds a [Inop] instruction and (ii)
does not have any predecessor. *)

(** We recommend to read the specification of the transformation in
the [RTLnormspec] module. *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall. 
Require Import Utils.
Local Open Scope string_scope.

(** * Predicates used in the state of the monad *)
(** They essentially handle the program point mapping between the initial and transformed function. *)

Inductive ch_succ : instruction -> instruction -> Prop :=
|cs_inop : forall s, ch_succ (Inop s) (Inop s)
|cs_iop: forall s1 s2 op args dst, ch_succ (Iop op args dst s1)  (Iop op args dst s2)
|cs_iload: forall s1 s2 chunk addr args dst, ch_succ (Iload chunk addr args dst s1) (Iload chunk addr args dst s2)
|cs_istore: forall s1 s2 chunk addr args src, ch_succ (Istore chunk addr args src s1) (Istore chunk addr args src s2)
|cs_icall: forall s1 s2 sig fn args dst, ch_succ (Icall sig fn args dst s1) (Icall sig fn args dst s2)
|cs_itailcall: forall sig fn args, ch_succ (Itailcall sig fn args) (Itailcall sig fn args)
|cs_ibuiltin : forall s1 s2 ef args dst, ch_succ (Ibuiltin ef args dst s1) (Ibuiltin ef args dst s2)
|cs_icond : forall cond args i1 i2 n1 n2, ch_succ (Icond cond args i1 n1) (Icond cond args i2 n2)
|cs_ijump: forall arg tbl1 tbl2, List.length tbl1 = List.length tbl2 -> ch_succ (Ijumptable arg tbl1) (Ijumptable arg tbl2)
|cs_iret : forall ret, ch_succ (Ireturn ret) (Ireturn ret).

Lemma ch_succ_trans : forall ins1 ins2 ins3, 
  ch_succ ins1 ins2 ->
  ch_succ ins2 ins3 ->
  ch_succ ins1 ins3.
Proof.
  intros.
  inv H; inv H0; constructor. 
  congruence.
Qed.

Lemma ch_succ_sym : forall ins ins', ch_succ ins ins' ->  ch_succ ins' ins.
Proof.
  induction 1; auto; constructor.
  auto.
Qed.

Lemma ch_succ_refl: forall ins, ch_succ ins ins.
Proof.
  intros. destruct ins ; constructor ; auto.
Qed. 

Hint Resolve ch_succ_trans : rtln.
Hint Resolve ch_succ_sym : rtln. 
Hint Resolve ch_succ_refl : rtln. 

Inductive ch_succ_o : option instruction -> option instruction -> Prop :=
| cso_some : forall i1 i2, ch_succ i1 i2 -> ch_succ_o (Some i1) (Some i2)
| cso_none : ch_succ_o None None.

Hint Constructors ch_succ_o ch_succ.

Lemma ch_succ_o_refl : forall oi, ch_succ_o oi oi.
Proof.
  intros.
  destruct oi; constructor.
  destruct i ; constructor.
  auto.
Qed.

(** * State monad used in the transformation *)

Record state: Type := mkstate {
  st_nextnode: positive;
  st_entry: positive;
  st_code: code;
  st_wf: forall (pc: positive), Plt pc st_nextnode \/ st_code!pc = None
}.

Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
    Ple s1.(st_nextnode) s2.(st_nextnode) ->
    (forall pc,
      s1.(st_code)!pc = None \/ (ch_succ_o (s2.(st_code)!pc) (s1.(st_code)!pc))) ->
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl.
  intros. right ; auto.
  apply ch_succ_o_refl.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextnode s2); assumption.
  intros.
  generalize (H3 pc) (H2 pc). intuition.
  inv H0. right ; eauto.
  inv H7; congruence.
  left ; auto.
  inv H5; try congruence.
  inv H0; try congruence.
  rewrite <- H6 in H5.  inv H5.
  right ; auto.
  inv H7; inv H9; econstructor; auto.
  constructor; congruence. 
  inv H0. 
  congruence.
  auto.
Qed.

(** * Monadic machinery *)
Inductive res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> forall (s': state), state_incr s s' -> res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s: state) => OK x s (state_incr_refl s).

Definition error {A: Type} (msg: Errors.errmsg) : mon A := fun (s: state) => Error msg.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i'  => OK b s'' (state_incr_trans s s' s'' i i')
        end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

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

(** * Utility functions used in the transformation *)

(** [add_nop] adds a [Inop] between an instruction and one
   of its successor [pc']. *)
Lemma add_instr_wf: forall s i pc,
  let n:= s.(st_nextnode) in
  Plt pc (Pos.succ n) \/
   (PTree.set n i (st_code s)) ! pc = None.
Proof.
  intros.
  destruct (peq pc n).
  inv e ; left ; apply Plt_succ.
  destruct (st_wf s pc); unfold n in *.
  left. apply Plt_trans_succ; auto.
  right. rewrite PTree.gso ; auto.
Qed.

Remark add_instr_incr:
  forall s i e,
  let n := s.(st_nextnode) in
  state_incr s (mkstate
                (Pos.succ n)
                e
                (PTree.set n i s.(st_code))
                (add_instr_wf s i)).
Proof.
  constructor; simpl.
  apply Ple_succ.
  intros. destruct (st_wf s pc). right.
  rewrite PTree.gso.
  apply ch_succ_o_refl.
  apply Plt_ne; auto. auto.
Qed.

Definition add_nop (pc':node) : mon node :=
  fun s =>
    let pc_new := s.(st_nextnode) in
      if peq pc' s.(st_entry)
        then
          OK pc_new
          (mkstate (Pos.succ pc_new) pc_new (PTree.set pc_new (Inop pc') s.(st_code)) (add_instr_wf _ _))
          (add_instr_incr s _ _)
        else
          OK pc_new
          (mkstate (Pos.succ pc_new) s.(st_entry) (PTree.set pc_new (Inop pc') s.(st_code)) (add_instr_wf _ _))
          (add_instr_incr s _ _).

Fixpoint upd_nth {A: Type} (l: list A) (a: A) (k: nat) : (list A) :=
  match k with
    | O => match l with
             | nil => nil
             | x::m => a::m
           end
    | Datatypes.S p => match l with
                         | nil => nil
                         | x::m => x::(upd_nth m a p)
                       end
  end.


Lemma upd_nth_same_length {A: Type} : forall  (l: list A) k x, 
  List.length (upd_nth l x k) = List.length l. 
Proof.
  induction l ; intros; (simpl; destruct k ; simpl ; auto).
Qed.

Lemma upd_nth_k {A: Type} : forall k (l: list A) x a, 
  nth_error l k = Some a ->
  nth_error (upd_nth l x k) k = Some x.
Proof.
  induction k; intros.
  destruct l; [ (eelim (@nth_error_nil_some A) ; eauto) | auto].
  destruct l; [ (eelim (@nth_error_nil_some A) ; eauto) | simpl ; eapply IHk ; eauto ].  
Qed.

Definition ins_newsucc (ins: instruction) (newsucc: node) (k : nat) : instruction :=
  match ins with
    | (Itailcall _ _ _)
    | (Ireturn _) => ins
    | (Icond cond args ifso ifnot) =>
      match k with
        | O  => Icond cond args newsucc ifnot
        | Datatypes.S O => Icond cond args ifso newsucc
        | _ => ins
      end
    | (Ijumptable arg tbl) => Ijumptable arg (upd_nth tbl newsucc k)
    | _ =>
      match k with
        | O =>
          match ins with
            | (Iop op args dst succ) => (Iop op args dst newsucc)
            | (Iload chunk addr args dst succ) => (Iload chunk addr args dst newsucc)
            | (Istore chunk addr args src succ) => (Istore chunk addr args src newsucc)
            | (Icall sig fn args dst succ) => (Icall sig fn args dst newsucc)
            | (Ibuiltin ef args dst succ) => (Ibuiltin ef args dst newsucc)
            | _ => ins
          end
        | _ => ins
      end
  end.

Lemma ch_succ_ins_newsucc : forall i x k, ch_succ (ins_newsucc i x k) i.
Proof.
  intros. 
  destruct i ; simpl; (try destruct k) ; try constructor. 
  destruct k ; constructor. 
  (eapply upd_nth_same_length ; eauto).
  eapply upd_nth_same_length ; eauto.
Qed.  

Definition get_proof {A:Type} (t: PTree.t A) (p: positive) : {x : option A | (t ! p = x)}.
Proof.
intros; case_eq (t!p); intros. 
exists (Some a); auto.
exists None; auto.
Qed.
  
Lemma upd_succ_wf :
forall s pc i i',
  (s.(st_code)!pc = Some i) ->
  (forall pc0, Plt pc0 (s.(st_nextnode)) \/ (PTree.set pc i' s.(st_code))!pc0 = None).
Proof.
  intros.
  elim (st_wf s pc0) ; intros.
  left ; auto.
  destruct (peq pc pc0).
  inv e. congruence.
  rewrite PTree.gso ; auto.
Qed.

Lemma upd_succ_incr:
  forall s pc ins newsucc k H,
    state_incr s
    (mkstate
      s.(st_nextnode)
      s.(st_entry)
      (PTree.set pc (ins_newsucc ins newsucc k) s.(st_code))
      (upd_succ_wf s pc ins (ins_newsucc ins newsucc k) H)).
Proof.
  intros.
  constructor; simpl.
  apply Ple_refl.
  intros.
  destruct (peq pc pc0).
  inv e. right.  rewrite PTree.gss. rewrite H. constructor.
  apply ch_succ_ins_newsucc.
  rewrite PTree.gso ; auto. right. apply ch_succ_o_refl.
Qed.

(** [upd_succ pc newsucc k] changes the [k]th successor of the
instruction at [pc] for the new sucessors given by [newsucc] *)
Definition upd_succ (pc: node) (newsucc:node) (k: nat): mon nat :=
  fun s =>
    match get_proof (st_code s) pc with
      | exist (Some i) H => (OK (S k)
        (mkstate
          s.(st_nextnode)
          s.(st_entry)
          (PTree.set pc (ins_newsucc i newsucc k) s.(st_code))
          (upd_succ_wf s pc i (ins_newsucc i newsucc k) H))
        (upd_succ_incr s pc i newsucc k H))
      | exist None H => (Error (Errors.msg ""))
    end.

(** [modif_ksucc is_jp pc succ kl] changes the instruction at [pc]
concerning its [k]th successor [succ]. It either does nothing, or add
a [Inop] and update the successors. *)

Definition modif_ksucc (is_jp:node->bool) (pc: node) (succ:node) (kl: nat * list node) : mon (nat * list node) :=
  let (k,l) := kl in 
    fun s => 
      match (st_code s) ! pc with
        | Some (Inop _)  
        | Some (Ireturn _) 
        | Some (Itailcall _ _ _) => (Error (Errors.msg ""))
        | _ => 
          if is_jp succ
            then
              (do n <- add_nop succ ;
               do k' <- upd_succ pc n k ;
                 ret (k',(l++(n::nil))%list)) s
              else ret ((Datatypes.S k),(l++(succ::nil))%list) s
        end.

(**  [modif_ksucc_opt] is the same as [modif_ksucc] except it is not instrumented with a list of [nat * list node] *)
Definition modif_ksucc_opt (is_jp:node->bool) (pc: node) (succ:node) (k: nat) : mon nat :=
    fun s => 
      match (st_code s) ! pc with
        | Some (Inop _)  
        | Some (Ireturn _) 
        | Some (Itailcall _ _ _) => (Error (Errors.msg ""))
        | _ => 
          if is_jp succ
            then
              (do n <- add_nop succ ;
               do k' <- upd_succ pc n k ;
                 ret k') s
              else ret (Datatypes.S k) s
        end.

  
  
(** [add_nop_after_instruction isjp (pc,ins)] adds a [Inop] after
instruction [ins] that stands at node [pc]. *)
Definition add_nop_after_instruction (is_jun_point:node->bool) (pcins : node * instruction) : mon unit :=
  let (pc, ins) := pcins in
    match ins with  
      | Inop _
      | Ireturn _ 
      | Itailcall _ _ _ => ret tt
      | _ => 
        (do k <- mfold (modif_ksucc is_jun_point pc) (successors_instr ins) (O,nil) ;
         ret tt)
    end.

(** [add_nop_after_instruction_opt] is a non-instrumented version of [add_nop_after_instruction]. *)
Definition add_nop_after_instruction_opt (is_jun_point:node->bool) (pcins : node * instruction) : mon unit :=
  let (pc, ins) := pcins in
    match ins with  
      | Inop _
      | Ireturn _ 
      | Itailcall _ _ _ => ret tt
      | _ => 
        (do k <- mfold (modif_ksucc_opt is_jun_point pc) (successors_instr ins) O ;
         ret tt)
    end.

(** Adding the [Inop] at the entry point [pc] of the function.  
   It returns the value of the new entrypoint of function. *)
Definition add_nop_entry (pc : node) : mon node :=
  fun s =>
    let pc_new := s.(st_nextnode) in
      OK pc_new
      (mkstate (Pos.succ pc_new) pc_new (PTree.set pc_new (Inop pc) s.(st_code)) (add_instr_wf _ _))
      (add_instr_incr _ _ _).

Definition get_max {A: Type} (t: PTree.t A) : positive :=
  let elts := map (@fst positive A) (PTree.elements t) in
    fold_left (fun a pc => if plt a pc then pc else a) elts xH.

Lemma get_max_fold_aux : forall l acc,
  Ple acc (fold_left (fun a pc => if plt a pc then pc else a) l acc).
Proof.
  induction l ; intros.
  simpl. apply Ple_refl.
  simpl.
  destruct (plt acc a).
  assert (Ha := IHl a).
  eapply Plt_Ple in p.
  eapply (Ple_trans acc a (fold_left (fun a pc : positive => if plt a pc then pc else a) l a)); eauto.
  eapply IHl ; eauto.
Qed.

Lemma get_max_fold : forall l pc acc,
  In pc l ->
  Ple pc (fold_left (fun a pc => if plt a pc then pc else a) l acc).
Proof.
  induction l ; intros ; inv H.
  simpl.
  destruct (plt acc pc).
  eapply get_max_fold_aux ; eauto.
  assert (Ple pc acc). { unfold Plt, Ple in * . zify ; omega. }
  assert (Htr:= get_max_fold_aux l acc).
  eapply Ple_trans ; eauto.
  simpl.
  destruct (plt 1 a);  eapply IHl ; eauto.
Qed.
      
Lemma get_max_lt {A: Type} : forall t pc (a:A),
    t ! pc = Some a -> Plt pc (Pos.succ (get_max t)).
Proof.
  unfold get_max ; intros.
  exploit PTree.elements_correct ; eauto. intros.
  assert (Hinpc : In (fst (pc,a)) (map (@fst positive A) (PTree.elements t))) by (eapply in_map ; eauto).
  simpl in Hinpc.
  eapply Ple_Plt_succ ; eauto.
  eapply get_max_fold ; eauto.
Qed.

(** * Initial state of the monad *)
Lemma init_state_wf :
  forall f pc, Plt pc (Pos.succ (get_max (fn_code f))) \/ (fn_code f)!pc = None.
Proof.
  intros.
  case_eq ((fn_code f) ! pc); intros.
  left ; eapply get_max_lt ; eauto.
  right ; eauto.
Qed.

Definition init_state (f: RTL.function) : state :=
  mkstate (Pos.succ (get_max (fn_code f))) (fn_entrypoint f) (fn_code f) (init_state_wf _).

Definition succ_code (code: code) :=
  PTree.map (fun (_ : positive) (i : instruction) => successors_instr i)
  code.

Definition is_joinpoint (preds: PTree.t (list positive)) : node -> bool :=
  fun pc =>  match preds ! pc with
               | Some (x::y::m) => true
               | _ => false
             end.

(** * Actual code of the transformation. Instrumented version. *)
Definition transl_function (f: RTL.function) : Errors.res RTL.function :=
  match add_nop_entry (fn_entrypoint f) (init_state f) with
    | Error m => Errors.Error m
    | OK nentry s' H1 =>
      let code_elts := PTree.elements s'.(st_code) in
        let is_jun_point := is_joinpoint (make_predecessors (fn_code f) successors_instr) in
          match mfold_unit (add_nop_after_instruction is_jun_point) code_elts s' with
            | Error m => Errors.Error m
            | OK u s'' H => 
              Errors.OK (RTL.mkfunction
                f.(RTL.fn_sig)
                f.(RTL.fn_params)
                f.(RTL.fn_stacksize)
                s''.(st_code)
                s''.(st_entry)
                f.(RTL.fn_dfs)
              )
          end
  end.

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p: RTL.program) : Errors.res RTL.program :=
  transform_partial_program transl_fundef p.


(** * Actual code of the transformation. Non-instrumented version. *)
Definition transl_function_opt (f: RTL.function) : Errors.res RTL.function :=
  match add_nop_entry (fn_entrypoint f) (init_state f) with
    | Error m => Errors.Error m
    | OK nentry s' H1 =>
      let code_elts := PTree.elements s'.(st_code) in
        let is_jun_point := is_joinpoint (make_predecessors (fn_code f) successors_instr) in
          match mfold_unit (add_nop_after_instruction_opt is_jun_point) code_elts s' with
            | Error m => Errors.Error m
            | OK u s'' H => 
              Errors.OK (RTL.mkfunction
                f.(RTL.fn_sig)
                f.(RTL.fn_params)
                f.(RTL.fn_stacksize)
                s''.(st_code)
                s''.(st_entry)
                f.(RTL.fn_dfs))
          end
  end.

Definition transl_fundef_opt := transf_partial_fundef transl_function_opt.

Definition transl_program_opt (p: RTL.program) : Errors.res RTL.program :=
  transform_partial_program transl_fundef_opt p.
