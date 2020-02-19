
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import RTL.
Require Import SSA.
Require Import Utils.
Require Import SSAvalid.
Require RTLnorm.
Require RTLdfs.

Local Open Scope error_monad_scope.

(** Generation algorithm of SSA: we first normalize the RTL input
code, then remove all unreachable code from it. Finally, we call the
main generation algorithm [SSAvalid.transf_function]. *)

Definition transf_function (f: RTL.function) : res SSA.function := 
 do rtl_normalized <- RTLnorm.transl_function_opt f;
 do rtl_dfs <- RTLdfs.transf_function rtl_normalized;
 SSAvalid.transf_function rtl_dfs.

Definition transf_fundef (fd: RTL.fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: RTL.program) : res program :=
  transform_partial_program transf_fundef p.


