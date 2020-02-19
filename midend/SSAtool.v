
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Utils.
Require Import SSAvalid.
Require Import SSAvalidator_proof.
Require Import SSAgen.
Require Import DLib.
Require Import RTLdfsproof.
Require Import Globalenvs.
Require Import Values.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Floats.
Require Import Maps.
Require Import Kildall.
Require Import RTL.
Require Import SSA.
Require Import DomTest.
Require Import SSAutils.

(** This file defines an extended version of SSA functions.  Apart
 from the regular information (from [SSA] module), SSAtool functions:

- are well-formed 

- include a toolbox [ssa_tool] (made of a dominance test, and a list
  of used but undefined variables). The toolbox is used for efficiency
  reasons

The rest of the file is defining the semantics of this extended
language, but is essentially the same as in the [SSA] module.

 *)

Record function := {
  func :> SSA.function;
  wf : wf_ssa_function func;
  tool :> ssa_tool func
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Local Open Scope error_monad_scope.

(* Integration avec SSAtool (note to self) *)
Program Definition complements_function (f:SSA.function) : ssa_tool f :=
  match (compute_test_dom f) with 
    | Some test => Build_ssa_tool f (ext_params_list f) test _ _
    | None => Build_ssa_tool f (ext_params_list f) (fun n d => false) _ _
  end
.
Next Obligation.
  apply ext_params_list_spec; auto.
Qed.
Next Obligation.
  eapply dom_test_correct ; eauto.  
Qed.
Next Obligation.
  eapply ext_params_list_spec ; eauto.  
Qed.


Program Definition transf_function_rich (f: RTL.function) : 
  res { tf: function | exists ssa, SSAgen.transf_function f = OK ssa /\ func tf = ssa}  := 
 match SSAgen.transf_function f with
   | Error msg => Error msg
   | OK ssa => OK (Build_function ssa _ (complements_function ssa))
 end.
Next Obligation.
  unfold SSAgen.transf_function in Heq_anonymous.
  unfold bind in *.
  flatten Heq_anonymous.
  eapply transf_function_wf_ssa_function; eauto.
  eapply transf_function_wf_dfs; eauto.
Qed.
Next Obligation.
  go.
Qed.

Definition transf_function (f: RTL.function) : res function := 
  do tf_rich <- transf_function_rich f;
  let (tf,_) := tf_rich in
  OK tf.

Definition transf_fundef (fd: RTL.fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: RTL.program) : res program :=
  transform_partial_program transf_fundef p.


Definition genv := Genv.t fundef unit.

Inductive stackframe : Type :=
  | Stackframe:
      forall (res: reg)        (**r where to store the result *)
             (f: function)     (**r calling function *)
             (sp: val)         (**r stack pointer in calling function *)
             (pc: node)        (**r program point in calling function *)
             (rs: regset),     (**r register state in calling function *)
      stackframe.

Inductive state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val)         (**r arguments to the call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val)                 (**r return value for the call *)
             (m: mem),                (**r memory state *)
      state.


Section RELSEM.


Variable ge: genv.

Definition find_function 
      (ros: SSA.reg + ident) (rs: regset) : option fundef :=
      match ros with
        | inl r => Genv.find_funct ge (rs #2 r)
        | inr symb =>
          match Genv.find_symbol ge symb with
            | None => None
            | Some b => Genv.find_funct_ptr ge b
          end
      end.

(** Definition of the effect of a phi-block on a register set, when
   the control flow comes from the k-th predecessor of the current
   program point. Phi-blocks are given a parallel semantics *)
Fixpoint phi_store k phib (rs:regset) :=
  match phib with
    | nil => rs
    | (Iphi args dst)::phib =>
      match nth_error args k with
        | None => (phi_store k phib rs)
        | Some arg => (phi_store k phib rs)#2 dst <- (rs #2 arg)
      end
  end.

            
(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => P2Map.set r1 v1 (init_regs vs rs)
  | _, _ => P2Map.init Vundef
  end.

Definition fn_code (f:function) := SSA.fn_code f.
Definition fn_stacksize (f:function) := SSA.fn_stacksize f.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Inductive step: state -> trace -> state -> Prop :=
| exec_Inop_njp:
  forall s f sp pc rs m pc',
    (fn_code f)!pc = Some(Inop pc') ->
    ~ join_point pc' f ->
    step (State s f sp pc rs m)
    E0 (State s f sp pc' rs m)
| exec_Inop_jp:
  forall s f sp pc rs m pc' phib k,
    (fn_code f)!pc = Some(Inop pc') ->
    join_point pc' f ->
    (fn_phicode f)!pc' = Some phib ->
    index_pred (make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
    step  (State s f sp pc rs m)
    E0 (State s f sp pc' (phi_store k phib rs) m)
| exec_Iop:
  forall s f sp pc rs m op args res pc' v,
    (fn_code f)!pc = Some(Iop op args res pc') ->
    eval_operation ge sp op rs##2 args m = Some v ->
    step (State s f sp pc rs m)
    E0 (State s f sp pc' (rs#2 res <- v) m)
| exec_Iload:
  forall s f sp pc rs m chunk addr args dst pc' a v,
    (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
    eval_addressing ge sp addr rs##2 args = Some a ->
    Mem.loadv chunk m a = Some v ->
    step (State s f sp pc rs m)
    E0 (State s f sp pc' (rs#2 dst <- v) m)
| exec_Istore:
  forall s f sp pc rs m chunk addr args src pc' a m',
    (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
    eval_addressing ge sp addr rs##2 args = Some a ->
    Mem.storev chunk m a rs#2 src = Some m' ->
    step (State s f sp pc rs m)
    E0 (State s f sp pc' rs m')
| exec_Icall:
  forall s f sp pc rs m sig ros args res pc' fd,
    (fn_code f)!pc = Some(Icall sig ros args res pc') ->
    find_function ros rs = Some fd ->
    funsig fd = sig ->
    step (State s f sp pc rs m)
    E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##2 args m)
| exec_Itailcall:
  forall s f stk pc rs m sig ros args fd m',
    (fn_code f)!pc = Some(Itailcall sig ros args) ->
    find_function ros rs = Some fd ->
    funsig fd = sig ->
    Mem.free m stk 0 (fn_stacksize f) = Some m' ->
    step (State s f (Vptr stk Int.zero) pc rs m)
    E0 (Callstate s fd rs##2 args m')
| exec_Ibuiltin:
  forall s f sp pc rs m ef args res pc' t v m',
    (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
    external_call ef ge rs##2 args m t v m' ->
    step (State s f sp pc rs m)
    t (State s f sp pc' (rs#2 res <- v) m')
| exec_Icond_true:
  forall s f sp pc rs m cond args ifso ifnot,
    (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
    eval_condition cond rs##2 args m = Some true ->
    step (State s f sp pc rs m)
    E0 (State s f sp ifso rs m)
| exec_Icond_false:
  forall s f sp pc rs m cond args ifso ifnot,
    (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
    eval_condition cond rs##2 args m = Some false ->
    step (State s f sp pc rs m)
    E0 (State s f sp ifnot rs m)
| exec_Ijumptable:
  forall s f sp pc rs m arg tbl n pc',
    (fn_code f)!pc = Some(Ijumptable arg tbl) ->
    rs#2 arg = Vint n ->
    list_nth_z tbl (Int.unsigned n) = Some pc' ->
    step (State s f sp pc rs m)
    E0 (State s f sp pc' rs m)
| exec_Ireturn:
  forall s f stk pc rs m or m',
    (fn_code f)!pc = Some(Ireturn or) ->
    Mem.free m stk 0 (fn_stacksize f) = Some m' ->
    step (State s f (Vptr stk Int.zero) pc rs m)
    E0 (Returnstate s (regmap2_optget or Vundef rs) m')
| exec_function_internal:
  forall s f args m m' stk,
    Mem.alloc m 0 (fn_stacksize f) = (m', stk) ->
    step (Callstate s (Internal f) args m)
    E0 (State s
      f
      (Vptr stk Int.zero)
      f.(fn_entrypoint)
      (init_regs args f.(fn_params))
      m')
| exec_function_external:
  forall s ef args res t m m',
    external_call ef ge args m t res m' ->
    step (Callstate s (External ef) args m)
    t (Returnstate s res m')
| exec_return:
  forall res f sp pc rs s vres m,
    step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
    E0 (State s f sp pc (rs#2 res <- vres) m).

Hint Constructors step. 

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f nil m0).

(** A final state is a [Returnstate] with an empty call stack. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m, final_state (Returnstate nil (Vint r) m) r.

(** The small-step semantics for a program. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).



