(*
Replace available expressions by the register containing their value.

David Monniaux, CNRS, VERIMAG
 *)

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL Maps.

(* Static analysis *)

Inductive sym_val : Type :=
| SMove (src : reg)
| SOp (op : operation) (args : list reg)
| SLoad (chunk : memory_chunk) (addr : addressing) (args : list reg).
                                                   
Definition eq_args (x y : list reg) : { x = y } + { x <> y } :=
  list_eq_dec peq x y.

Definition eq_sym_val : forall x y : sym_val,
    {x = y} + { x <> y }.
Proof.
  generalize eq_operation.
  generalize eq_args.
  generalize peq.
  generalize eq_addressing.
  generalize chunk_eq.
  decide equality.
Defined.

Definition pset := PTree.t unit.

Definition pset_inter : pset -> pset -> pset :=
  PTree.combine_null
    (fun ov1 ov2 => Some tt).

Definition pset_empty : pset := PTree.empty unit.
Definition pset_add (i : positive) (s : pset) := PTree.set i tt s.
Definition pset_remove (i : positive) (s : pset) := PTree.remove i s.

Record relmap := mkrel {
   var_to_sym : PTree.t sym_val ;
   mem_used : pset
 }.

Module RELATION.

Definition t := relmap.

Definition eq (r1 r2 : t) :=
  forall x, (PTree.get x (var_to_sym r1)) = (PTree.get x (var_to_sym r2)).

Definition top : t := mkrel (PTree.empty sym_val) pset_empty.

Lemma eq_refl: forall x, eq x x.
Proof.
  unfold eq.
  intros; reflexivity.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq.
  intros; eauto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq.
  intros; congruence.
Qed.

Definition sym_val_beq (x y : sym_val) :=
  if eq_sym_val x y then true else false.

Definition beq (r1 r2 : t) := PTree.beq sym_val_beq (var_to_sym r1) (var_to_sym r2).

Lemma beq_correct: forall r1 r2, beq r1 r2 = true -> eq r1 r2.
Proof.
  unfold beq, eq. intros r1 r2 EQ x.
  pose proof (PTree.beq_correct sym_val_beq (var_to_sym r1) (var_to_sym r2)) as CORRECT.
  destruct CORRECT as [CORRECTF CORRECTB].
  pose proof (CORRECTF EQ x) as EQx.
  clear CORRECTF CORRECTB EQ.
  unfold sym_val_beq in *.
  destruct ((var_to_sym r1) ! x) as [R1x | ] in *;
    destruct ((var_to_sym r2) ! x) as [R2x | ] in *;
    trivial; try contradiction.
  destruct (eq_sym_val R1x R2x) in *; congruence.
Qed.

Definition ge (r1 r2 : t) :=
  forall x,
    match PTree.get x (var_to_sym r1) with
    | None => True
    | Some v => (PTree.get x (var_to_sym r2)) = Some v
    end.

Lemma ge_refl: forall r1 r2, eq r1 r2 -> ge r1 r2.
Proof.
  unfold eq, ge.
  intros r1 r2 EQ x.
  pose proof (EQ x) as EQx.
  clear EQ.
  destruct ((var_to_sym r1) ! x).
  - congruence.
  - trivial.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge.
  intros r1 r2 r3 GE12 GE23 x.
  pose proof (GE12 x) as GE12x; clear GE12.
  pose proof (GE23 x) as GE23x; clear GE23.
  destruct ((var_to_sym r1) ! x); trivial.
  destruct ((var_to_sym r2) ! x); congruence.
Qed.

Definition lub (r1 r2 : t) :=
  mkrel
  (PTree.combine
    (fun ov1 ov2 =>
       match ov1, ov2 with
       | (Some v1), (Some v2) =>
         if eq_sym_val v1 v2
         then ov1
         else None
       | None, _
       | _, None => None
       end)
    (var_to_sym r1) (var_to_sym r2))
  (pset_inter (mem_used r1) (mem_used r2)).

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub.
  intros r1 r2 x. simpl.
  rewrite PTree.gcombine by reflexivity.
  destruct (_ ! _); trivial.
  destruct (_ ! _); trivial.
  destruct (eq_sym_val _ _); trivial.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub.
  intros r1 r2 x. simpl.
  rewrite PTree.gcombine by reflexivity.
  destruct (_ ! _); trivial.
  destruct (_ ! _); trivial.
  destruct (eq_sym_val _ _); trivial.
  congruence.
Qed.

End RELATION.

Module Type SEMILATTICE_WITHOUT_BOTTOM.

  Parameter t: Type.
  Parameter eq: t -> t -> Prop.
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Parameter beq: t -> t -> bool.
  Axiom beq_correct: forall x y, beq x y = true -> eq x y.
  Parameter ge: t -> t -> Prop.
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Parameter lub: t -> t -> t.
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End SEMILATTICE_WITHOUT_BOTTOM.

Module ADD_BOTTOM(L : SEMILATTICE_WITHOUT_BOTTOM).
  Definition t := option L.t.
  Definition eq (a b : t) :=
    match a, b with
    | None, None => True
    | Some x, Some y => L.eq x y
    | Some _, None | None, Some _ => False
    end.
  
  Lemma eq_refl: forall x, eq x x.
  Proof.
    unfold eq; destruct x; trivial.
    apply L.eq_refl.
  Qed.

  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    unfold eq; destruct x; destruct y; trivial.
    apply L.eq_sym.
  Qed.
  
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    unfold eq; destruct x; destruct y; destruct z; trivial.
    - apply L.eq_trans.
    - contradiction.
  Qed.
  
  Definition beq (x y : t) :=
    match x, y with
    | None, None => true
    | Some x, Some y => L.beq x y
    | Some _, None | None, Some _ => false
    end.
  
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    unfold beq, eq.
    destruct x; destruct y; trivial; try congruence.
    apply L.beq_correct.
  Qed.
  
  Definition ge (x y : t) :=
    match x, y with
    | None, Some _ => False
    | _, None => True
    | Some a, Some b => L.ge a b
    end.
  
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge.
    destruct x; destruct y; trivial.
    apply L.ge_refl.
  Qed.
  
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge.
    destruct x; destruct y; destruct z; trivial; try contradiction.
    apply L.ge_trans.
  Qed.
  
  Definition bot: t := None.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot.
    destruct x; trivial.
  Qed.
  
  Definition lub (a b : t) :=
    match a, b with
    | None, _ => b
    | _, None => a
    | (Some x), (Some y) => Some (L.lub x y)
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold ge, lub.
    destruct x; destruct y; trivial.
    - apply L.ge_lub_left.
    - apply L.ge_refl.
      apply L.eq_refl.
  Qed.
  
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold ge, lub.
    destruct x; destruct y; trivial.
    - apply L.ge_lub_right.
    - apply L.ge_refl.
      apply L.eq_refl.
  Qed.
End ADD_BOTTOM.

Module RB := ADD_BOTTOM(RELATION).
Module DS := Dataflow_Solver(RB)(NodeSetForward).

Definition kill_sym_val (dst : reg) (sv : sym_val) :=
  match sv with
  | SMove src => if peq dst src then true else false
  | SOp op args => List.existsb (peq dst) args
  | SLoad chunk addr args => List.existsb (peq dst) args
  end.
                                                 
Definition kill_reg (dst : reg) (rel : RELATION.t) : RELATION.t :=
  mkrel (PTree.filter1 (fun x => negb (kill_sym_val dst x))
                       (PTree.remove dst (var_to_sym rel)))
        (pset_remove dst (mem_used rel)).

Definition kill_sym_val_mem (sv: sym_val) :=
  match sv with
  | SMove _ => false
  | SOp op _ => op_depends_on_memory op
  | SLoad _ _ _ => true
  end.

Definition kill_mem (rel : RELATION.t) :=
  mkrel
    (PTree.filter1 (fun x => negb (kill_sym_val_mem x)) (var_to_sym rel))
    pset_empty.


Definition forward_move (rel : RELATION.t) (x : reg) : reg :=
  match (var_to_sym rel) ! x with
  | Some (SMove org) => org
  | _ => x
  end.

Definition move (src dst : reg) (rel : RELATION.t) :=
  mkrel (PTree.set dst (SMove (forward_move rel src)) (var_to_sym (kill_reg dst rel)))
        (mem_used rel).

Definition find_op_fold op args (already : option reg) x sv :=
                match already with
                | Some found => already
                | None =>
                  match sv with
                  | (SOp op' args') =>
                    if (eq_operation op op') && (eq_args args args')
                    then Some x
                    else None
                  | _ => None
                  end
                end.

Definition find_op (rel : RELATION.t) (op : operation) (args : list reg) :=
  PTree.fold (find_op_fold op args) (var_to_sym rel) None.

Definition find_load_fold chunk addr args (already : option reg) x sv :=
                match already with
                | Some found => already
                | None =>
                  match sv with
                  | (SLoad chunk' addr' args') =>
                    if (chunk_eq chunk chunk') &&
                       (eq_addressing addr addr') &&
                       (eq_args args args')
                    then Some x
                    else None
                  | _ => None
                  end
                end.

Definition find_load (rel : RELATION.t) (chunk : memory_chunk) (addr : addressing) (args : list reg) :=
  PTree.fold (find_load_fold chunk addr args) (var_to_sym rel) None.

Definition oper2 (op: operation) (dst : reg) (args : list reg)
           (rel : RELATION.t) : RELATION.t :=
  let rel' := kill_reg dst rel in
  mkrel (PTree.set dst (SOp op (List.map (forward_move rel') args)) (var_to_sym rel'))
        (mem_used rel).

Definition oper1 (op: operation) (dst : reg) (args : list reg)
           (rel : RELATION.t) : RELATION.t :=
  if List.in_dec peq dst args
  then kill_reg dst rel
  else oper2 op dst args rel.

Definition oper (op: operation) (dst : reg) (args : list reg)
           (rel : RELATION.t) : RELATION.t :=
  match find_op rel op (List.map (forward_move rel) args) with
  | Some r => move r dst rel
  | None => oper1 op dst args rel
  end.

Definition gen_oper (op: operation) (dst : reg) (args : list reg)
           (rel : RELATION.t) : RELATION.t :=
  match op, args with
  | Omove, src::nil => move src dst rel
  | _, _ => oper op dst args rel
  end.

Definition load2 (chunk: memory_chunk) (addr : addressing)
           (dst : reg) (args : list reg) (rel : RELATION.t) : RELATION.t :=
  let rel' := kill_reg dst rel in
  mkrel (PTree.set dst (SLoad chunk addr (List.map (forward_move rel') args)) (var_to_sym rel'))
        (pset_add dst (mem_used rel)).

Definition load1 (chunk: memory_chunk) (addr : addressing)
           (dst : reg) (args : list reg) (rel : RELATION.t) :=
  if List.in_dec peq dst args
  then kill_reg dst rel
  else load2 chunk addr dst args rel.

Definition load (chunk: memory_chunk) (addr : addressing)
           (dst : reg) (args : list reg) (rel : RELATION.t) :=
  match find_load rel chunk addr (List.map (forward_move rel) args) with
  | Some r => move r dst rel
  | None => load1 chunk addr dst args rel
  end.

(* NO LONGER NEEDED
Fixpoint list_represents { X : Type } (l : list (positive*X)) (tr : PTree.t X) : Prop :=
  match l with
  | nil => True
  | (r,sv)::tail => (tr ! r) = Some sv /\ list_represents tail tr
  end.

Lemma elements_represent :
  forall { X : Type },
  forall tr : (PTree.t X),
    (list_represents (PTree.elements tr) tr).
Proof.
  intros.
  generalize (PTree.elements_complete tr).
  generalize (PTree.elements tr).
  induction l; simpl; trivial.
  intro COMPLETE.
  destruct a as [ r sv ].
  split.
  {
    apply COMPLETE.
    left; reflexivity.
  }
  apply IHl; auto.
Qed.
*)
    
Definition apply_instr instr (rel : RELATION.t) : RB.t :=
  match instr with
  | Inop _
  | Icond _ _ _ _
  | Ijumptable _ _ => Some rel
  | Istore _ _ _ _ _ => Some (kill_mem rel)
  | Iop op args dst _ => Some (gen_oper op dst args rel)
  | Iload chunk addr args dst _ => Some (load chunk addr dst args rel)
  | Icall _ _ _ dst _ => Some (kill_reg dst (kill_mem rel))
  | Ibuiltin _ _ res _ => Some (RELATION.top) (* TODO (kill_builtin_res res x) *)
  | Itailcall _ _ _ | Ireturn _ => RB.bot
  end.

Definition apply_instr' code (pc : node) (ro : RB.t) : RB.t :=
  match ro with
  | None => None
  | Some x =>
    match code ! pc with
    | None => RB.bot
    | Some instr => apply_instr instr x
    end
  end.

Definition forward_map (f : RTL.function) := DS.fixpoint
  (RTL.fn_code f) RTL.successors_instr
  (apply_instr' (RTL.fn_code f)) (RTL.fn_entrypoint f) (Some RELATION.top).

Definition forward_move_b (rb : RB.t) (x : reg) :=
  match rb with
  | None => x
  | Some rel => forward_move rel x
  end.

Definition subst_arg (fmap : option (PMap.t RB.t)) (pc : node) (x : reg) : reg :=
  match fmap with
  | None => x
  | Some inv => forward_move_b (PMap.get pc inv) x
  end.

Definition subst_args fmap pc := List.map (subst_arg fmap pc).

(* Transform *)
Definition find_op_in_fmap fmap pc op args :=
  match fmap with
  | None => None
  | Some map =>
    match PMap.get pc map with
    | Some rel => find_op rel op args
    | None => None
    end
  end.

Definition find_load_in_fmap fmap pc chunk addr args :=
  match fmap with
  | None => None
  | Some map =>
    match PMap.get pc map with
    | Some rel => find_load rel chunk addr args
    | None => None
    end
  end.

Definition transf_instr (fmap : option (PMap.t RB.t))
           (pc: node) (instr: instruction) :=
  match instr with
  | Iop op args dst s =>
    let args' := subst_args fmap pc args in
    match find_op_in_fmap fmap pc op args' with
    | None => Iop op args' dst s
    | Some src => Iop Omove (src::nil) dst s
    end
  | Iload chunk addr args dst s =>
    let args' := subst_args fmap pc args in
    match find_load_in_fmap fmap pc chunk addr args' with
    | None => Iload chunk addr args' dst s
    | Some src => Iop Omove (src::nil) dst s
    end
  | Istore chunk addr args src s =>
    Istore chunk addr (subst_args fmap pc args) src s
  | Icall sig ros args dst s =>
    Icall sig ros (subst_args fmap pc args) dst s
  | Itailcall sig ros args =>
    Itailcall sig ros (subst_args fmap pc args)
  | Icond cond args s1 s2 =>
    Icond cond (subst_args fmap pc args) s1 s2
  | Ijumptable arg tbl =>
    Ijumptable (subst_arg fmap pc arg) tbl
  | Ireturn (Some arg) =>
    Ireturn (Some (subst_arg fmap pc arg))
  | _ => instr
  end.

Definition transf_function (f: function) : function :=
  {| fn_sig := f.(fn_sig);
     fn_params := f.(fn_params);
     fn_stacksize := f.(fn_stacksize);
     fn_code := PTree.map (transf_instr (forward_map f)) f.(fn_code);
     fn_entrypoint := f.(fn_entrypoint) |}.


Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.
