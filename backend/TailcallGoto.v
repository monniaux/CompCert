Require Import Coqlib Maps AST Registers Op RTL Conventions.

Definition defmap_t := PTree.t (globdef fundef unit).

Axiom function_eq_dec : forall f g : function, { f=g } + { f<>g }.

Definition transf_instr (defmap : defmap_t) (cur_fn : function) (pc: node) (instr: instruction) :=
  match instr with
  | Itailcall sig (inr symb) args =>
    match PTree.get symb defmap with
    | Some (Gfun (Internal f)) =>
      if function_eq_dec f cur_fn
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

Definition transf_function (defmap : defmap_t) (f : function) : function :=
    mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map (transf_instr defmap f) f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (defmap : defmap_t) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function defmap) fd.

Definition transf_program (p: program): program :=
  AST.transform_program (transf_fundef (prog_defmap p)) p.

