Require Import Coqlib Maps AST Registers Op RTL Conventions.

Definition transf_instr (cur_fn_id: ident) (cur_fn : function) (pc: node) (instr: instruction) :=
  match instr with
  | Itailcall sig (inr symb) args =>
    if ident_eq symb cur_fn_id
    then
      match args with
      | nil => Inop (fn_entrypoint cur_fn)
      | _ => Itailcall sig (inr symb) args
      end
    else Itailcall sig (inr symb) args
  | _ => instr
  end.

Definition transf_function (id : ident) (f : function) : function :=
    mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map (transf_instr id f) f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (id : ident) (fd: RTL.fundef): RTL.fundef :=
  match fd with
  | Internal f => Internal (transf_function id f)
  | _ => fd
  end.

Definition transform_program_globdef (idg : ident * globdef fundef unit) :=
  match idg with
  | (id, Gfun f) => (id, Gfun (transf_fundef id f))
  | (id, Gvar v) => (id, Gvar v)
  end.

Definition transform_program (p: program) : program :=
  mkprogram
    (List.map transform_program_globdef p.(prog_defs))
    p.(prog_public)
    p.(prog_main).
