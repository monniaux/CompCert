Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions TailcallGoto.


Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef (prog_defmap p) f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

