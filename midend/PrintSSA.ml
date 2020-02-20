open Printf
open Camlcoq
open Datatypes

open Maps
open AST
open Integers

open SSA

open PrintAST
open PrintOp

let reg pp r =
  let (r,i) = r in
    fprintf pp "x%ld_%ld" (P.to_int32 r) (P.to_int32 i)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = P.to_int32 s in
    if s <> dfl then fprintf pp "\tgoto %ld\n" s

let rec print_phi_args_aux pp = function
    [] -> ()
  | x::q -> fprintf pp ",%a%a" reg x print_phi_args_aux q

let print_phi_args pp = function
    [] -> ()
  | x::q -> fprintf pp "%a%a" reg x print_phi_args_aux q

let print_phi phi (pc : P.t) pp = 
  match PTree.get pc phi with
    | None -> ()
    | Some phi_asgnts ->
	List.iter 
	  (fun (SSA.Iphi (args,res)) ->
	     fprintf pp "%a = ϕ(%a)\n     "
               reg res print_phi_args args)
	  phi_asgnts

let print_instruction phi pp (pc, pc_pos, i) =
  fprintf pp "%5ld:\t" pc;
  print_phi phi pc_pos pp;
  match i with
    | Inop s ->
	let s = P.to_int32 s in
	  if s = Int32.pred pc
	  then fprintf pp "nop\n"
	  else fprintf pp "goto %ld\n" s
    | Iop(op, args, res, s) ->
	fprintf pp "%a = %a\n"
          reg res (PrintOp.print_operation reg) (op, args);
	print_succ pp s (Int32.pred pc)
    | Iload(chunk, addr, args, dst, s) ->
	fprintf pp "%a = %s[%a]\n"
          reg dst (name_of_chunk chunk)
          (PrintOp.print_addressing reg) (addr, args);
	print_succ pp s (Int32.pred pc)
    | Istore(chunk, addr, args, src, s) ->
	fprintf pp "%s[%a] = %a\n"
          (name_of_chunk chunk)
          (PrintOp.print_addressing reg) (addr, args)
          reg src;
	print_succ pp s (Int32.pred pc)
    | Icall(sg, fn, args, res, s) ->
	fprintf pp "%a = %a(%a)\n"
          reg res ros fn regs args;
	print_succ pp s (Int32.pred pc)
    | Itailcall(sg, fn, args) ->
	fprintf pp "tailcall %a(%a)\n"
          ros fn regs args
    | Ibuiltin(ef, args, res, s) ->
        fprintf pp "%a = %s(%a)\n"
          reg res (name_of_external ef) regs args;
        print_succ pp s (Int32.pred pc)
    | Icond(cond, args, s1, s2) ->
	fprintf pp "if (%a) goto %ld else goto %ld\n"
          (PrintOp.print_condition reg) (cond, args)
          (P.to_int32 s1) (P.to_int32 s2)
    | Ijumptable(arg, tbl) ->
	      let tbl = Array.of_list tbl in
      fprintf pp "jumptable (%a)\n" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\t\tcase %d: goto %ld\n" i (P.to_int32 tbl.(i))
      done
    | Ireturn None ->
	fprintf pp "return\n"
    | Ireturn (Some arg) ->
	fprintf pp "return %a\n" reg arg


let print_function pp id f =
  fprintf pp "%s(%a) {\n" (extern_atom id) regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _, _) (pc2, _, _) -> Pervasives.compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int32 pc, pc, i))
        (PTree.elements f.fn_code)) in
  print_succ pp f.fn_entrypoint 
    (match instrs with 
    |  (pc1, _, _) :: _ -> pc1 
    | [] -> Int32.minus_one);
  List.iter (print_instruction f.fn_phicode pp) instrs;
  fprintf pp "}\n\n"

let rec print_pp_list pp = function
    [] -> ()
  | x::q -> fprintf pp "%3ld " (P.to_int32 x) ; () ;  print_pp_list pp q ; ()

let rec print_stdout_list = function
    [] -> ()
  | x::q -> printf "%3ld " (P.to_int32 x) ; () ;  print_stdout_list q ; ()

let print_error pp msg =
  let print_one_error = function
    | Errors.MSG s -> fprintf pp ">>>> %s@ " (Camlcoq.camlstring_of_coqstring s) 
    | Errors.CTX i -> fprintf pp ">>>> %s@ " (Camlcoq.extern_atom i)
    | _ -> assert false
  in
    fun l -> 
      List.iter print_one_error msg;
      print_pp_list pp l ; fprintf pp "@\n " ; ()

let print_error_stdout msg =
  let print_one_error = function
    | Errors.MSG s -> printf ">>>> %s\n" (Camlcoq.camlstring_of_coqstring s) 
    | Errors.CTX i -> printf ">>>> %s\n" (Camlcoq.extern_atom i)
    | _ -> assert false
  in
    List.iter print_one_error msg

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: SSA.program) =
  List.iter (print_globdef pp) prog.prog_defs

let print_if optdest prog =
  match !optdest with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program oc prog;
      close_out oc

let destination_ssa : string option ref = ref None
let print_ssa = print_if destination_ssa 

let destination_rtl_norm : string option ref = ref None
let destination_dssa : string option ref = ref None

let destination_gvn : string option ref = ref None
let print_gvn = print_if destination_gvn
