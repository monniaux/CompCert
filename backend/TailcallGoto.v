Require Import Coqlib Maps AST Registers Op RTL Conventions Integers Values Floats.

Require Inlining.

Definition funenv := Inlining.funenv.
Definition funenv_program : program -> funenv := Inlining.funenv_program.

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

Definition transf_instr (fenv : funenv) (cur_fn : function) (pc: node) (instr: instruction) :=
  match instr with
  | Itailcall sig (inr symb) args =>
    match PTree.get symb fenv with
    | Some f =>
      if function_eq f cur_fn
      then
        match args with
        | nil => Inop (fn_entrypoint cur_fn)
        | _ => instr
        end
      else instr
    | _ => instr
      end
  | _ => instr
  end.

Definition transf_function (fenv : funenv) (f : function) : function :=
    mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map (transf_instr fenv f) f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (fenv : funenv) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function fenv) fd.

Definition transf_program (p: program): program :=
  AST.transform_program (transf_fundef (Inlining.funenv_program p)) p.
