
(** The SSA intermediate language: abstract syntax and semantics.

  SSA is the SSA form of RTL.  *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Floats.

Require Import Kildall. 
Require Import Utils.
Require Import Relation_Operators.
Require Import Classical.
Require Import Relations.Relation_Definitions.
Require Import DLib.
Require Import Dom.

(** * Abstract syntax *)

(** SSA is organized as instructions and phi-blocks, functions and
  programs.  Instructions are those of RTL, phi-blocks are sequences
  of phi-instructions, that manipulates pseudo-registers, as in RTL.

  Instructions are organized as a control-flow graph: a function is
  a finite map from ``nodes'' (abstract program points) to instructions,
  and each instruction lists explicitly the nodes of its successors.
*)

Definition node := positive.

Definition reg := (reg * positive)%type.

Inductive instruction: Type :=
  | Inop: node -> instruction
      (** No operation -- just branch to the successor. *)
  | Iop: operation -> list reg -> reg -> node -> instruction
      (** [Iop op args dst succ] performs the arithmetic operation [op]
          over the values of registers [args], stores the result in [dst],
          and branches to [succ]. *)
  | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Iload chunk addr args dst succ] loads a [chunk] quantity from
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, stores the quantity just read
          into [dst], and branches to [succ]. *)
  | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Istore chunk addr args src succ] stores the value of register
          [src] in the [chunk] quantity at the
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, then branches to [succ]. *)
  | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
      (** [Icall sig fn args dst succ] invokes the function determined by
          [fn] (either a function pointer found in a register or a
          function name), giving it the values of registers [args] 
          as arguments.  It stores the return value in [dst] and branches
          to [succ]. *)
  | Itailcall: signature -> reg + ident -> list reg -> instruction
      (** [Itailcall sig fn args] performs a function invocation
          in tail-call position.  *)
  | Ibuiltin: external_function -> list reg -> reg -> node -> instruction
      (** [Ibuiltin ef args dst succ] calls the built-in function
          identified by [ef], giving it the values of [args] as arguments.
          It stores the return value in [dst] and branches to [succ]. *)
  | Icond: condition -> list reg -> node -> node -> instruction
      (** [Icond cond args ifso ifnot] evaluates the boolean condition
          [cond] over the values of registers [args].  If the condition
          is true, it transitions to [ifso].  If the condition is false,
          it transitions to [ifnot]. *)
  | Ijumptable: reg -> list node -> instruction
      (** [Ijumptable arg tbl] transitions to the node that is the [n]-th
          element of the list [tbl], where [n] is the signed integer
          value of register [arg]. *)
  | Ireturn: option reg -> instruction.
      (** [Ireturn] terminates the execution of the current function
          (it has no successor).  It returns the value of the given
          register, or [Vundef] if none is given. *)

Inductive phiinstruction: Type :=
| Iphi: list reg -> reg -> phiinstruction.
(** [Iphi args dst] copies the value of the k-th register of [args], 
   where k is the index of the predecessor of the current point. *)

(** Phi blocks are lists of phi-instructions *)
Definition phiblock:= list phiinstruction.


(** A function description comprises a control-flow graph (CFG)
    [fn_code] (a partial finite mapping from nodes to instructions)
    and a phi-block graph (a partial finite mapping from nodes to
    phi-blocks. As in Cminor, [fn_sig] is the function signature and
    [fn_stacksize] the number of bytes for its stack-allocated
    activation record.  [fn_params] is the list of registers that are
    bound to the values of arguments at call time.  [fn_entrypoint] is
    the node of the first instruction of the function in the CFG.
    [fn_max_indice] is a meta information (i.e. it doesn't influence
    the semantics of the program), representing the maximum index used
    for temporary variables. *)

Definition code: Type := PTree.t instruction.

Definition phicode: Type := PTree.t phiblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  
  fn_code: code;
  fn_phicode: phicode;

  fn_max_indice: nat;
  fn_entrypoint: node
}.
  
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop s => s :: nil
  | Iop op args res s => s :: nil
  | Iload chunk addr args dst s => s :: nil
  | Istore chunk addr args src s => s :: nil
  | Icall sig ros args res s => s :: nil
  | Itailcall sig ros args => nil
  | Ibuiltin ef args res s => s :: nil
  | Icond cond args ifso ifnot => ifso :: ifnot :: nil
  | Ijumptable arg tbl => tbl
  | Ireturn optarg => nil
  end.

Definition successors_map (f: function) : PTree.t (list node) :=
  PTree.map1 successors_instr f.(fn_code).

Notation preds := 
  (fun f pc => (make_predecessors (fn_code f) successors_instr) !!! pc).

Inductive join_point (jp: node) (f:function) : Prop :=
  | jp_cons : forall l,
              forall (Hpreds: (make_predecessors (fn_code f) successors_instr) ! jp = Some l)
                     (Hl: (length l > 1)%nat), 
                join_point jp f.


Fixpoint get_index_acc (l:list node) (a:node) acc : option nat :=
  match l with 
    | nil => None
    | x::m => if (peq x a) 
      then Some acc
      else get_index_acc m a (acc+1)%nat
  end.

Definition get_index (l:list node) (a:node) :=
  get_index_acc l a O.

Definition index_pred (predsf: PTree.t (list node)):=
  fun (i:node) (j:node)  => 
    let predsj := predsf !!! j in  
      match  predsj with
        | nil => None 
        | _ => get_index predsj i 
      end.

(** * Use and definition of registers *)
Section UDEF.

(** [assigned_code_spec code pc r] holds if the register [r] is
assigned at point [pc] in the code [code] *)
Inductive assigned_code_spec (code:code) (pc:node) : reg -> Prop :=
| AIop: forall op args dst succ,
  code!pc = Some (Iop op args dst succ)  ->
  assigned_code_spec code pc dst
| AIload: forall chunk addr args dst succ,
  code!pc = Some (Iload chunk addr args dst succ) ->
  assigned_code_spec code pc dst
| AIcall: forall sig fn args dst succ,
  code!pc = Some (Icall sig fn args dst succ) ->
  assigned_code_spec code pc dst
| AIbuiltin: forall fn args dst succ,
  code!pc = Some (Ibuiltin fn args dst succ) ->
  assigned_code_spec code pc dst.

(** [assigned_phi_spec phicode pc r] holds if the register [r] is
assigned at point [pc] in the phi-code [phicode] *)
Inductive assigned_phi_spec (phicode: phicode) (pc: node): reg -> Prop :=
  APhi: forall phiinstr dst, 
    (phicode!pc) = Some phiinstr ->
    (exists args, List.In (Iphi args dst) phiinstr) -> 
    assigned_phi_spec phicode pc dst.

Inductive assigned_phi_spec_with_args (phicode: phicode) (pc: node): reg -> list reg -> Prop :=
 | APhiA: forall phiinstr dst args, 
    (phicode!pc) = Some phiinstr ->
    List.In (Iphi args dst) phiinstr -> 
    assigned_phi_spec_with_args phicode pc dst args.


Variable f : function.
  
(** [use_code r pc] holds whenever register [r] is used at [pc] in the regular code of [f] *)
Inductive use_code : reg -> node -> Prop := 
| UIop: forall pc arg op args dst s, 
  (fn_code f) !pc = Some (Iop op args dst s)  -> In arg args -> use_code arg pc
| UIload: forall pc arg chk adr args dst s,
  (fn_code f) !pc = Some (Iload chk adr args dst s) -> In arg args -> use_code arg pc
| UIcond: forall pc arg cond args s s',
  (fn_code f) !pc = Some (Icond cond args s s') -> In arg args -> use_code arg pc 
| UIbuiltin: forall pc arg ef args dst s,
  (fn_code f) !pc = Some (Ibuiltin ef args dst s) -> In arg args -> use_code arg pc
| UIstore: forall pc arg chk adr args src s,
  (fn_code f) !pc = Some (Istore chk adr args src s) -> In arg args -> use_code arg pc
| UIcall: forall pc arg sig r args dst s,
  (fn_code f) !pc = Some (Icall sig (inl ident r) args dst s) -> In arg (r::args) -> use_code arg pc
| UItailcall: forall pc arg sig r args,
  (fn_code f) !pc = Some (Itailcall sig (inl ident r) args) -> In arg (r::args) -> use_code arg pc
| UIcall2: forall pc arg sig id args dst s,
  (fn_code f) !pc = Some (Icall sig (inr reg id) args dst s) -> In arg args -> use_code arg pc
| UItailcall2: forall pc arg sig id args,
  (fn_code f) !pc = Some (Itailcall sig (inr reg id) args) -> In arg args -> use_code arg pc
| UIjump: forall pc arg tbl, 
  (fn_code f) !pc = Some (Ijumptable arg tbl) -> use_code arg pc
| UIret: forall pc arg,
  (fn_code f) !pc = Some (Ireturn (Some arg)) -> use_code arg pc.

(** [use_phicode r pc] holds whenever register [r] is used at [pc] in the phi-code of [f] *)
Inductive use_phicode : reg -> node -> Prop := 
| upc_intro : forall pc pred k arg args dst phib
  (PHIB: (fn_phicode f) ! pc = Some phib)
  (ASSIG : In (Iphi args dst) phib)
  (KARG : nth_error args k = Some arg)
  (KPRED : index_pred (make_predecessors (fn_code f) successors_instr) pred pc = Some k),
  use_phicode arg pred.

(** A register is used either in the code or in the phicode of a function *)  
Inductive use : reg -> node -> Prop := 
| u_code : forall x pc, use_code x pc -> use x pc
| u_phicode : forall x pc, use_phicode x pc -> use x pc.

(** Special definition point for function parameters and registers that are used in the function without having been defined anywhere in the function *)
Inductive ext_params (x: reg) : Prop :=
| ext_params_params : 
  In x (fn_params f) -> ext_params x
| ext_params_undef : 
  (exists pc, use x pc) ->
  (forall pc, ~ assigned_phi_spec (fn_phicode f) pc x) ->
  (forall pc, ~ assigned_code_spec (fn_code f) pc x) ->
  ext_params x.
Hint Constructors ext_params.

(** [def r pc] holds if register [r] is defined at node [pc] *)
Inductive def : reg -> node -> Prop := 
| def_params : forall x,
  ext_params x -> def x (fn_entrypoint f)
| def_code : forall x pc, assigned_code_spec (fn_code f) pc x -> def x pc
| def_phicode : forall x pc, assigned_phi_spec (fn_phicode f) pc x -> def x pc.

End UDEF.

Hint Constructors ext_params def assigned_code_spec assigned_phi_spec.

(** * Formalization of Dominators *)
Section DOMINATORS.  
  
  Variable f : function.

  Definition entry := (fn_entrypoint f).
  Notation code := (fn_code f).
  
  (** [cfg i j] holds if [j] is a successor of [i] in the code of [f] *)
  Inductive _cfg (i j:node) : Prop :=
  | CFG : forall ins
    (HCFG_ins: code !i = Some ins)
    (HCFG_in : In j (successors_instr ins)),
    _cfg i j.

  Definition exit (pc: node) : Prop :=
  match code ! pc with
  | Some (Itailcall _ _ _) 
  | Some (Ireturn _) => True
  | _ => False
  end.

  Definition cfg := _cfg.
  
  Definition dom := dom cfg exit entry.

End DOMINATORS.

Notation SSApath := (fun f => Dom.path (cfg f) (exit f) (entry f)).

(** * Well-formed SSA functions *)

(** Every variable is assigned as most once *)
Definition unique_def_spec (f : function) :=
  (forall (r:reg) (pc pc':node), 
    (assigned_code_spec (f.(fn_code)) pc r ->
      assigned_code_spec (f.(fn_code)) pc' r ->
      pc = pc')
    /\
    (assigned_phi_spec (f.(fn_phicode)) pc r ->
      assigned_phi_spec (f.(fn_phicode)) pc' r ->
      pc = pc')
    /\
    ((assigned_code_spec (f.(fn_code)) pc r ->
      ~ assigned_phi_spec (f.(fn_phicode)) pc' r)
    /\ (assigned_phi_spec (f.(fn_phicode)) pc r ->
      ~ assigned_code_spec (f.(fn_code)) pc' r)))
  /\ 
  (forall pc phiinstr, 
    (f.(fn_phicode))!pc = Some phiinstr ->
    ( (NoDup phiinstr)
      /\ (forall r args args', 
          In (Iphi args r) phiinstr -> In (Iphi args' r) phiinstr -> args = args'))
  ).


(** All phi-instruction have the right numbers of phi-arguments *)
Definition block_nb_args (f: function) : Prop :=
  forall pc block args  x, 
    (fn_phicode f) ! pc = Some block -> 
    In (Iphi args x) block ->
    (length (preds f pc)) = (length args).

Definition successors (f: function) : PTree.t (list positive) :=
  PTree.map1 successors_instr (fn_code f).

Notation succs := (fun f pc => (successors f) !!! pc).

(** Well-formed SSA functions *)  

Notation reached := (fun f => (reached (cfg f) (entry f))).
Notation sdom := (fun f => (sdom (cfg f) (exit f) (entry f))).

Record wf_ssa_function (f:function) : Prop := {
  fn_ssa : unique_def_spec f; 
  
  fn_ssa_params : forall x, In x (fn_params f) -> 
    (forall pc, ~ assigned_code_spec (fn_code f) pc x) /\ 
    (forall pc, ~ assigned_phi_spec (fn_phicode f) pc x);
    
  fn_strict : forall x u d, use f x u -> def f x d -> dom f d u; 
      
  fn_use_def_code : forall x pc, 
    use_code f x pc -> 
    assigned_code_spec (fn_code f) pc x -> False; 

  fn_wf_block: block_nb_args f;
  
  fn_normalized: forall jp pc, 
                   (join_point jp f) ->
                   In jp (succs f pc) -> (fn_code f) ! pc = Some (Inop jp); 
  
  fn_phicode_inv: forall jp,
    join_point jp f <->
    f.(fn_phicode) ! jp <> None;
    
  fn_code_reached: forall pc ins, (fn_code f) ! pc = Some ins -> reached f pc;

  fn_code_closed:
    forall pc pc' instr, (fn_code f) ! pc = Some instr ->
    In pc' (successors_instr instr) -> 
    exists instr', (fn_code f) ! pc' = Some instr'; 

  fn_entry : exists s, (fn_code f) ! (fn_entrypoint f) = Some (Inop s); 
  fn_entry_pred: forall pc, ~ cfg f pc (fn_entrypoint f) 

}.

 Record ssa_tool (f:function) := {
  fn_ext_params : list reg; (* parameter or regs that are used but not def *)
  fn_dom_test: node -> node -> bool;

  fn_ext_params_correct: forall r,
    ext_params f r -> In r fn_ext_params;

  fn_dom_test_correct : forall n d,
    reached f n -> fn_dom_test d n = true -> dom f d n                           
  }.

Lemma assigned_phi_spec_same_with_args : forall f pc pc' x args,
  wf_ssa_function f ->
  assigned_phi_spec (fn_phicode f) pc x ->
  assigned_phi_spec_with_args (fn_phicode f) pc' x args -> pc=pc'.
Proof.
  intros.
  inv H.
  destruct fn_ssa0 as [HH1 HH2].
  generalize (HH1 x pc pc') ;eauto.
  intros. intuition.
  inv H1 ; eauto.
Qed.  

Require Import KildallComp.

Lemma no_assigned_phi_spec_fn_entrypoint: forall f,
  wf_ssa_function f -> forall x,
    ~ assigned_phi_spec (fn_phicode f) (fn_entrypoint f) x.
Proof.
  red; intros.
  inv H0.
  assert (join_point (fn_entrypoint f) f).
  { rewrite fn_phicode_inv; auto.
    congruence.
  }
  inv H0. 
  destruct l.
  simpl in Hl; apply False_ind; omega.
  exploit @make_predecessors_some; eauto. intros [pins Hpins].  
  assert (In (fn_entrypoint f) (successors_instr pins)).
  { 
    eapply @make_predecessors_correct2; eauto.
    unfold Kildall.successors_list.
    unfold make_preds.
    rewrite Hpreds.
    left; auto.
  }   
  elim (fn_entry_pred _ H p).
  econstructor; eauto.
Qed.

(** Well-formed SSA function definitions *)
Inductive wf_ssa_fundef: fundef -> Prop :=
  | wf_ssa_fundef_external: forall ef,
      wf_ssa_fundef (External ef)
  | wf_ssa_function_internal: forall f,
      wf_ssa_function f ->
      wf_ssa_fundef (Internal f).

(** Well-formed SSA programs *)
Definition wf_ssa_program (p: program) : Prop := 
  forall f id, In (id, Gfun f) (prog_defs p) -> wf_ssa_fundef f.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.

(** The dynamic semantics of SSA is given in small-step style for
  basic instructions, as a set of transitions between states, and in a
  big step style for phi-blocks.  A state captures the current point
  in the execution. Three kinds of states appear in the transitions:

- [State cs f sp pc rs m] describes an execution point within a
  function, after the potential execution of a phi-block.  
  [f] is the current function. 
  [sp] is the pointer to the
  stack block for its current activation (as in Cminor). 
  [pc] is the current program point (CFG node) within the code [c].  
  [rs] gives the current values for the pseudo-registers.  
  [m] is the current memory state.  

- [Callstate cs f args m] is an intermediate state that appears during 
  function calls. 
  [f] is the function definition that we are calling.  
  [args] (a list of values) are the arguments for this call.  
  [m] is the current memory state. 

- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.  
  [v] is the return value and 
  [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res f sp pc rs].  Each frame represents
a function call in progress.  
[res] is the pseudo-register that will receive the result of the call.
[f] is the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

Definition regset := P2Map.t val.

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
      (ros: reg + ident) (rs: regset) : option fundef :=
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
    Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
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
    Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
    step (State s f (Vptr stk Int.zero) pc rs m)
    E0 (Returnstate s (regmap2_optget or Vundef rs) m')
| exec_function_internal:
  forall s f args m m' stk,
    Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
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

(** Transformation of a SSA function instruction by instruction.
  This applies given transformation functions to all instructions and
  phi-instructions of a function and constructs a transformed function
  from that. *)

Section TRANSF.

Variable transf: node -> instruction -> instruction.
Variable transfphi: node -> phiblock -> phiblock.

Definition transf_function (f: function) : function :=
  mkfunction
  f.(fn_sig)
  f.(fn_params)
  f.(fn_stacksize)
  (PTree.map transf f.(fn_code))
  (PTree.map transfphi f.(fn_phicode))
  f.(fn_max_indice)
  f.(fn_entrypoint).
End TRANSF.

(** Missing condition for blocks in a SSA function to be
   parallelizable.  The generation algorithm only generate
   parallelizable blocks. The DeSSA transformation will fail on
   non-parallelizable blocks.  *)
Definition para_block block := forall dst args arg,
  (In (Iphi args dst) block) -> In arg args -> dst <> arg ->
  forall args', ~ (In (Iphi args' arg) block).

Lemma para_block_cons: forall a block,
  para_block (a :: block) -> para_block block.
Proof.
  intros.
  unfold para_block in *; intros.
  intro.
  exploit (H dst args arg); eauto.
Qed.

