Require Import Coqlib Maps AST Registers Op RTL Conventions Integers Values Floats.
Require Parmov.

Definition funenv := PTree.t function.

Definition add_globdef (fenv: funenv) (idg: ident * globdef fundef unit) : funenv :=
  match idg with
  | (id, Gfun (Internal f)) => PTree.set id f fenv
  | (id, _) =>
      PTree.remove id fenv
  end.

Definition funenv_program (p : program) : funenv :=
  List.fold_left add_globdef p.(prog_defs) (PTree.empty function).

Definition reg_ident_eq (a b : reg+ident) :  { a=b} + {a <> b}.
Proof.
  generalize Pos.eq_dec.
  generalize ident_eq.
  decide equality.
Defined.

Definition builtin_res_eq (a b : builtin_res reg) :  { a=b} + {a <> b}.
Proof.
  generalize Pos.eq_dec.
  induction a; destruct b; decide equality.
Defined.

Definition builtin_arg_eq (a b : builtin_arg reg) :  { a=b} + {a <> b}.
Proof.
  generalize Int.eq_dec.
  generalize Int64.eq_dec.
  generalize Ptrofs.eq_dec.
  generalize Float.eq_dec.
  generalize Float32.eq_dec.
  generalize Pos.eq_dec.
  generalize chunk_eq.
  decide equality.
Defined.

Definition builtin_args_eq (a b : list (builtin_arg reg)) :  { a=b} + {a <> b}.
Proof.
  apply list_eq_dec.
  apply builtin_arg_eq.
Defined.

Definition list_reg_eq (a b : list reg) :  { a=b} + {a <> b}.
Proof.
  apply list_eq_dec.
  apply Pos.eq_dec.
Defined.

Definition instruction_eq (a b : instruction) : { a=b} + {a <> b}.
Proof.
  generalize Pos.eq_dec.
  generalize eq_operation.
  generalize eq_addressing.
  generalize eq_condition.
  generalize chunk_eq.
  generalize signature_eq.
  generalize reg_ident_eq.
  generalize builtin_args_eq.
  generalize builtin_res_eq.
  generalize list_reg_eq.
  generalize external_function_eq.
  decide equality.
  decide equality.
Defined.

Definition code_eq (a b : code) : {a = b} + { a <> b}.
Proof.
  apply PTree.phys_eq.
  apply instruction_eq.
Defined.

Definition function_eq (f g : function) : { f=g} + { f <> g}.
Proof.
  generalize signature_eq.
  generalize Z.eq_dec.
  generalize Pos.eq_dec.
  generalize code_eq.
  generalize list_reg_eq.
  decide equality.
Defined.

Definition is_self_tailcall (fenv : funenv) (cur_fn : function) (instr : instruction) :=
  match instr with
  | Itailcall sig (inr symb) args =>
    match PTree.get symb fenv with
    | Some f =>
      if function_eq f cur_fn
      then Some args
      else None
    | _ => None
      end
  | _ => None
  end.

Definition move (dst : reg) (src : reg) (next : node) : instruction :=
  if Pos.eq_dec dst src
  then Inop next
  else Iop Omove (src :: nil) dst next.

Fixpoint generate_moves (pc : node) (moves : list (reg * reg))
           (jump_point : node) (already : code*node) : code*node :=
  let (prevcode, nextnode) := already in 
  match moves with
  | nil => ((PTree.set pc (Inop jump_point) prevcode),
            nextnode)
  | (arg0, dst0) :: nil =>
    ((PTree.set pc (Iop Omove (arg0 :: nil) dst0 jump_point) prevcode),
     nextnode)
  | (arg0, dst0) :: rest =>
    generate_moves (snd already) rest jump_point
      ((PTree.set pc (Iop Omove (arg0 :: nil) dst0 (snd already)) prevcode),
       (Pos.succ nextnode))            
  end.

Definition transf_instr (fenv : funenv) (cur_fn : function)
           (tmpalready : reg*(code*node))
           (pc: node) (instr: instruction) : reg*(code*node) :=
  let (tmp, already) := tmpalready in
  let (prevcode, nextnode) := already in 
  match is_self_tailcall fenv cur_fn instr with
  | None => (tmp, ((PTree.set pc instr prevcode), nextnode))
  | Some args =>
     ((Pos.succ tmp),
      generate_moves pc
                     (Parmov.parmove reg Pos.eq_dec (fun _ => tmp)
                                     (List.combine args (fn_params cur_fn)))
                     (fn_entrypoint cur_fn) already)
  end.

(* fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B *)

Definition transf_function (fenv : funenv) (f : function) : function :=
    mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
        (fst (snd (PTree.fold (transf_instr fenv f) (fn_code f)
                         ((Pos.succ (max_reg_function f)),
                          ((PTree.empty instruction),
                           (Pos.succ (max_pc_function f)))))))
    f.(fn_entrypoint).

Definition transf_fundef (fenv : funenv) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function fenv) fd.

Definition transf_program (p: program): program :=
  AST.transform_program (transf_fundef (funenv_program p)) p.
