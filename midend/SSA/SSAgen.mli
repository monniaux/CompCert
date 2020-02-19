open BinPos
open Registers
open RTL

val ssa: fundef -> 
  (SSA.reg list *                       (* param *)
     code *                         (* code *)
     SSA.phicode *           (* phicode *)
     (node -> reg -> positive) *       (* gamma *)
     (node -> reg -> positive list) )  (* delta *)
    option

val genSSA : fundef -> SSA.fundef option

val genSSA_V2 : coq_function ->   Datatypes.nat * reg Maps.PTree.t * reg Maps.PTree.t Maps.PTree.t

val ssa_function_to_function_wo_inv : SSA.coq_function -> SSAvalid.function_wo_inv 

val remove_dead_node : coq_function -> coq_function
