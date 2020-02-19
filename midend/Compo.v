
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Kildall.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import SSA.
Require Import Integers.
Require Import Floats.
Require Import Utils.
Require Import Smallstep.

Local Open Scope error_monad_scope.

Section SIMULATION.


Variable state1 : Type.
Variable genv1 : Type.
Variable step1: genv1 -> state1 -> Events.trace -> state1 -> Prop.

Variable genv2 : Type.
Variable state2 : Type.
Variable step2: genv2 -> state2 -> Events.trace -> state2 -> Prop.

Variable  match_states: state1 -> state2 -> Prop.

Variable genv: genv1.
Variable genv': genv2.

Hypothesis simulation : 
  forall s1 t s2,
    step1 genv s1 t s2 ->
    forall s1', match_states s1 s1' ->
      exists s2',
        Smallstep.plus step2 genv' s1' t s2' /\
        match_states s2 s2'.

Lemma simulation_star_star : 
  forall s1 t s2,
    star step1 genv s1 t s2 ->
    forall s1', match_states s1 s1' ->
      exists s2',
        star step2 genv' s1' t s2' /\  match_states s2 s2'.
Proof.
  induction 1 ; intros;  auto.
  exists s1'. split.
  apply star_refl. 
  auto.
  
  eapply simulation in H ; eauto. destruct H as [s2' [Hplus' Hma]].  
  exploit IHstar ; eauto. intros. destruct H as [s2'' [Hstar'' Hma'']].
  exists s2''. split.
  eapply star_trans ; eauto. 
  eapply plus_star ; eauto.
  auto.
Qed.

Lemma simulation_plus_plus :
  forall s1 t s2,
    plus step1 genv s1 t s2 ->
    forall s1', match_states s1 s1' ->
      exists s2',
        plus step2 genv' s1' t s2' /\
        match_states s2 s2'.
Proof.
  induction 1 ; intros;  auto.
  eapply simulation in H ; eauto. destruct H as [s2' [Hplus' Hma]].
  exploit simulation_star_star ; eauto. intros [s2'' [Hstar' Hma']].
  exists s2''. split.
  inv Hstar'.
  rewrite Events.E0_right ; auto.
  eapply plus_trans ; eauto. 
  eapply plus_left in H3 ; eauto.
  auto.
Qed.  

End SIMULATION.

(* Local Variables: *)
(* eval : (load-file "../config.el") *)
(* End: *)


