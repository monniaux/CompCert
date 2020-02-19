(** Specification of the DeSSA transformation *)
Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import SSA.
Require Import SSAutils.
Require Import DeSSA.
Require Import Kildall.
Require Import Utils.
Require Import Permutation. 
Require Import Bijection.

(** * Checking that the bijection can be applied *)
Inductive is_valid (size: nat) : SSA.instruction ->  Prop := 
| valid_inop : forall s, is_valid size (Inop s)
| valid_iop : forall op args dst s, 
  (forall r, In r (dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Iop op args dst s)
| valid_iload : forall ch ad args dst s, 
  (forall r, In r (dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Iload ch ad args dst s)
| valid_istore : forall ch ad args src s, 
  (forall r, In r (src::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Istore ch ad args src s)
| valid_icall : forall sig id args dst s, 
  (forall r, In r (dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Icall sig (inr reg id) args dst s)
| valid_icall' : forall sig rfun args dst s, 
  (forall r, In r (rfun::dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Icall sig (inl ident rfun) args dst s)
| valid_itailcall : forall sig id args, 
  (forall r, In r args -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Itailcall sig (inr reg id) args)
| valid_itailcall' : forall sig rfun args, 
  (forall r, In r (rfun::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Itailcall sig (inl ident rfun) args)
| valid_ibuiltin : forall ef args dst s, 
  (forall r, In r (dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Ibuiltin ef args dst s)
| valid_icond : forall cond args ifso ifnot, 
  (forall r, In r args -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Icond cond args ifso ifnot) 
| valid_ijump : forall arg tbl, 
  Bij.valid_index size (snd arg) = true -> 
  is_valid size (Ijumptable arg tbl)
| valid_return : forall r, 
  Bij.valid_index size (snd r) = true ->
  is_valid size (Ireturn (Some r))
| valid_return' : is_valid size (Ireturn None).

Definition is_valid_phi (size: nat) (dst: reg) (args: list reg) : Prop := 
  (forall r, (In r (dst::args) -> Bij.valid_index size (snd r) = true)).

Inductive reach_moves (size : nat) (code : RTL.code) (k: nat) :  node -> node -> phiblock -> list node -> Prop := 
| reach_moves_nil : forall from, reach_moves size code k from from nil nil
| reach_moves_cons : forall from succ to args arg dst block l,
  code ! from = Some (RTL.Iop Omove ((Bij.pamr size arg)::nil) (Bij.pamr size dst) succ) ->
  nth_error args k = Some arg ->
  reach_moves size code k succ to block l ->
  reach_moves size code k from to ((Iphi args dst) :: block) (from::l).

(** * Specification of DeSSA *)
Inductive dssa_spec (size : nat) (preds : (PTree.t (list node))) (code1: code) (pcode1: phicode) (code2: RTL.code) (pc: node) : Prop := 
| dspec_noblock : forall succ,
  code1 ! pc = Some (Inop succ) ->
  pcode1 ! succ = None ->
  code2 ! pc = Some (RTL.Inop succ) ->
  dssa_spec size preds code1 pcode1 code2 pc
| dspec_block : forall succ succ' block lastnew lnew k ,
  code1 ! pc = Some (Inop succ) ->
  pcode1 ! succ = Some block ->
  (forall args dst, In (Iphi args dst) block -> is_valid_phi size dst args) ->
  code2 ! pc = Some (RTL.Inop succ') ->
  code2 ! lastnew = Some (RTL.Inop succ) ->
  index_pred preds pc succ = Some k ->
  reach_moves size code2 k succ' lastnew block lnew ->
  dssa_spec size preds code1 pcode1 code2 pc
| dspec_copy : forall ins ins', 
  code1 ! pc = Some ins -> 
  (is_valid size ins) ->
  (forall succ, ins <> Inop succ) ->
  (map_pamr size ins) = Errors.OK ins' ->
  code2 ! pc = Some ins' ->
  dssa_spec size preds code1 pcode1 code2 pc.  

Inductive tr_function: SSA.function -> RTL.function -> Prop :=
  | tr_function_intro:
    forall f s  init max preds pl  incr,
      (init,max,pl) = init_state f ->
      preds = (make_predecessors (fn_code f) successors_instr) ->
      (forall pc b, (fn_phicode f) ! pc = Some b -> para_block b) ->
      mfold_unit (copy_wwo_add (fn_max_indice f) preds (fn_code f) (fn_phicode f) max) (sort_pp pl) init = OK tt s incr  ->
      (forall p, In p f.(SSA.fn_params) -> Bij.valid_index (fn_max_indice f) (snd p) = true) ->
      tr_function f (RTL.mkfunction
        f.(SSA.fn_sig)
        (map (Bij.pamr (fn_max_indice f)) f.(SSA.fn_params))
        f.(SSA.fn_stacksize)
        s.(st_code)
        f.(SSA.fn_entrypoint)
        nil).

Inductive transl_function_spec: SSA.function -> RTL.function -> Prop :=
| transl_function_spec_intro: forall f tf preds,
  preds = (make_predecessors (fn_code f) successors_instr) ->
  (forall pc ins, (fn_code f) ! pc = Some ins -> dssa_spec (fn_max_indice f) preds (fn_code f) (fn_phicode f) (RTL.fn_code tf) pc) ->
  transl_function_spec f tf.
