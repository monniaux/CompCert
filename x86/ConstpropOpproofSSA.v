(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for simple sparse constant propagation (processor-dependent part). *)

Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Op.
Require Import SSAtool.
Require Import ConstpropOp.

(** * Correctness of the static analysis *)
(* DD: Diff to ConstpropOpproof : the type of genv... *)

Section ANALYSIS.

Variable ge: genv.
Variable sp: val.

(** We first show that the dataflow analysis is correct with respect
  to the dynamic semantics: the approximations (sets of values) 
  of a register at a program point predicted by the static analysis
  are a superset of the values actually encountered during concrete
  executions.  We formalize this correspondence between run-time values and
  compile-time approximations by the following predicate. *)

Definition val_match_approx (a: approx) (v: val) : Prop :=
  match a with
  | Unknown => True
  | I p => v = Vint p
  | F p => v = Vfloat p
  | L p => v = Vlong p
  | G symb ofs => v = symbol_address ge symb ofs
  | S ofs => v = Val.add sp (Vint ofs)
  | Novalue => False
  end.

Inductive val_list_match_approx: list approx -> list val -> Prop :=
  | vlma_nil:
      val_list_match_approx nil nil
  | vlma_cons:
      forall a al v vl,
      val_match_approx a v ->
      val_list_match_approx al vl ->
      val_list_match_approx (a :: al) (v :: vl).

Ltac SimplVMA :=
  match goal with
  | H: (val_match_approx (I _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (F _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (L _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (G _ _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | H: (val_match_approx (S _) ?v) |- _ =>
      simpl in H; (try subst v); SimplVMA
  | _ =>
      idtac
  end.

Ltac InvVLMA :=
  match goal with
  | H: (val_list_match_approx nil ?vl) |- _ =>
      inv H
  | H: (val_list_match_approx (?a :: ?al) ?vl) |- _ =>
      inv H; SimplVMA; InvVLMA
  | _ =>
      idtac
  end.

(** We then show that [eval_static_operation] is a correct abstract
  interpretations of [eval_operation]: if the concrete arguments match
  the given approximations, the concrete results match the
  approximations returned by [eval_static_operation]. *)

Lemma eval_static_condition_correct:
  forall cond al vl m b,
  val_list_match_approx al vl ->
  eval_static_condition cond al = Some b ->
  eval_condition cond vl m = Some b.
Proof.
  intros until b.
  unfold eval_static_condition. 
  case (eval_static_condition_match cond al); intros;
  InvVLMA; simpl; congruence.
Qed.

Remark shift_symbol_address:
  forall symb ofs n,
  symbol_address ge symb (Int.add ofs n) = Val.add (symbol_address ge symb ofs) (Vint n).
Proof.
  unfold symbol_address; intros. destruct (Genv.find_symbol ge symb); auto. 
Qed.

Lemma eval_static_addressing_correct:
  forall addr al vl v,
  val_list_match_approx al vl ->
  eval_addressing ge sp addr vl = Some v ->
  val_match_approx (eval_static_addressing addr al) v.
Proof.
  intros until v. unfold eval_static_addressing.
  case (eval_static_addressing_match addr al); intros;
  InvVLMA; simpl in *; FuncInv; try subst v; auto.
  rewrite shift_symbol_address; auto.
  rewrite Val.add_assoc. auto.
  repeat rewrite shift_symbol_address. auto.
  fold (Val.add (Vint n1) (symbol_address ge id ofs)).
  repeat rewrite shift_symbol_address. repeat rewrite Val.add_assoc. rewrite Val.add_permut. auto.
  repeat rewrite Val.add_assoc. decEq; simpl. rewrite Int.add_assoc. auto.
  fold (Val.add (Vint n1) (Val.add sp (Vint ofs))).
  rewrite Val.add_assoc. rewrite Val.add_permut. rewrite Val.add_assoc. 
  simpl. rewrite Int.add_assoc; auto.
  rewrite shift_symbol_address. auto.
  rewrite Val.add_assoc. auto. 
  rewrite shift_symbol_address. auto.
  rewrite shift_symbol_address. rewrite Int.mul_commut; auto. 
Qed.

Lemma eval_static_operation_correct:
  forall op al vl m v,
  val_list_match_approx al vl ->
  eval_operation ge sp op vl m = Some v ->
  val_match_approx (eval_static_operation op al) v.
Proof.
  intros until v.
  unfold eval_static_operation. 
  case (eval_static_operation_match op al); intros;
  InvVLMA; simpl in *; FuncInv; try subst v; auto.
  destruct (propagate_float_constants tt); simpl; auto.
  rewrite Int.sub_add_opp. rewrite shift_symbol_address. rewrite Val.sub_add_opp. auto.
  destruct (Int.eq n2 Int.zero). inv H0. 
    destruct (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); inv H0; simpl; auto.
  destruct (Int.eq n2 Int.zero); inv H0; simpl; auto.
  destruct (Int.eq n2 Int.zero). inv H0. 
    destruct (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); inv H0; simpl; auto.
  destruct (Int.eq n2 Int.zero); inv H0; simpl; auto.
  destruct (Int.ltu n2 Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  destruct (Int.ltu n2 Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  destruct (Int.ltu n (Int.repr 31)); inv H0. simpl; auto.
  destruct (Int.ltu n2 Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize); simpl; auto.
  destruct (Int.ltu n Int.iwordsize);
  destruct (Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize); simpl; auto.
  eapply eval_static_addressing_correct; eauto.
  unfold eval_static_intoffloat.
  destruct (Float.intoffloat n1) eqn:?; simpl in H0; inv H0.
  simpl; auto.
  destruct (propagate_float_constants tt); simpl; auto.
  unfold eval_static_condition_val. destruct (eval_static_condition c vl0) as [b|] eqn:?.
  rewrite (eval_static_condition_correct _ _ _ m _ H Heqo). 
  destruct b; simpl; auto.
  simpl; auto.
Qed.

(*
(** * Correctness of strength reduction *)
*)
End ANALYSIS.
