(* Positive and adversarial tests of the production extracted scheduler.
   INRIA Non-Commercial License Agreement, as in the parent repository. *)
open AST
open BinNums
open Maps
open Integers
open Op

let p = Camlcoq.P.of_int
let int n = Int.repr (Camlcoq.Z.of_sint n)
let checks = ref []
let check name value =
  if not value then failwith ("schedule test failed: " ^ name);
  checks := name :: !checks
let tree entries = List.fold_left (fun t (k,v) -> PTree.set (p k) v t) PTree.empty entries
let signature = { sig_args = [Xint;Xint]; sig_res = Xint; sig_cc = cc_default }
let source : RTL.coq_function = {
  fn_sig = signature; fn_params = [p 1;p 2]; fn_stacksize = Z0; fn_entrypoint = p 1;
  fn_code = tree [
    1,RTL.Iop (Oadd,[p 1;p 2],p 3,p 2);
    2,RTL.Iop (Osub,[p 1;p 2],p 4,p 3);
    3,RTL.Iop (Omul,[p 3;p 4],p 5,p 4);
    4,RTL.Ireturn (Some (p 5))]
}
let set pc instr f = { f with RTL.fn_code = PTree.set (p pc) instr f.RTL.fn_code }
let rejected name f a b =
  check (name ^ " candidate rejected") (Schedule.validate_candidate f (p a) (p b) = None);
  check (name ^ " untransformable function retained") (Schedule.transf_function f = f)

(* The test driver only follows the fixture's Iop/return CFG, but operations
   themselves use production Op.eval_operation with the CompCert memory model. *)
let execute f x y =
  let program : RTL.program = { prog_defs = []; prog_public = []; prog_main = p 1 } in
  let ge = Globalenvs.Genv.globalenv program in
  let regs = PMap.set (p 2) (Values.Vint y) (PMap.set (p 1) (Values.Vint x) (PMap.init Values.Vundef)) in
  let rec run fuel pc regs =
    if fuel = 0 then failwith "unexpected fixture nontermination";
    match PTree.get pc f.RTL.fn_code with
    | Some (RTL.Iop (op,args,dst,next)) ->
        let values = List.map (fun r -> PMap.get r regs) args in
        begin match Op.eval_operation ge Values.Vundef op values Memory.Mem.empty with
        | Some value -> run (fuel-1) next (PMap.set dst value regs)
        | None -> failwith "fixture operation failed"
        end
    | Some (RTL.Ireturn (Some r)) -> PMap.get r regs
    | _ -> failwith "unexpected fixture instruction"
  in run 8 f.RTL.fn_entrypoint regs

let () =
  let scheduled = Schedule.transf_function source in
  check "independent pair accepted" (Schedule.validate_candidate source (p 1) (p 2) <> None);
  check "first operation really reordered"
    (PTree.get (p 1) scheduled.RTL.fn_code = Some (RTL.Iop (Osub,[p 1;p 2],p 4,p 2)));
  check "second operation really reordered"
    (PTree.get (p 2) scheduled.RTL.fn_code = Some (RTL.Iop (Oadd,[p 1;p 2],p 3,p 3)));
  check "unchanged function metadata"
    (scheduled.RTL.fn_sig = source.RTL.fn_sig && scheduled.RTL.fn_params = source.RTL.fn_params &&
     scheduled.RTL.fn_stacksize = source.RTL.fn_stacksize && scheduled.RTL.fn_entrypoint = source.RTL.fn_entrypoint);
  check "control flow after pair retained"
    (PTree.get (p 3) scheduled.RTL.fn_code = PTree.get (p 3) source.RTL.fn_code &&
     PTree.get (p 4) scheduled.RTL.fn_code = PTree.get (p 4) source.RTL.fn_code);
  rejected "read-after-write dependency"
    (set 2 (RTL.Iop (Osub,[p 3;p 2],p 4,p 3)) source) 1 2;
  rejected "write-after-read dependency"
    (set 1 (RTL.Iop (Oadd,[p 4;p 2],p 3,p 2)) source) 1 2;
  rejected "equal destinations"
    (set 2 (RTL.Iop (Osub,[p 1;p 2],p 3,p 3)) source) 1 2;
  rejected "extra predecessor, even when disconnected"
    (set 5 (RTL.Inop (p 2)) source) 1 2;
  rejected "function entry at second node"
    { source with RTL.fn_entrypoint = p 2 } 1 2;
  rejected "single-node self edge"
    (set 1 (RTL.Iop (Oadd,[p 1;p 2],p 3,p 1)) source) 1 1;
  rejected "load is not a pure scheduling candidate"
    (set 2 (RTL.Iload (Mint32,Aindexed Z0,[p 1],p 4,p 3)) source) 1 2;
  rejected "candidate does not follow actual edge"
    (set 1 (RTL.Iop (Oadd,[p 1;p 2],p 3,p 3)) source) 1 2;
  rejected "second node self edge"
    (set 2 (RTL.Iop (Osub,[p 1;p 2],p 4,p 2)) source) 1 2;
  check "missing candidate node rejected" (Schedule.validate_candidate source (p 999) (p 2) = None);
  let cycle = set 2 (RTL.Iop (Osub,[p 1;p 2],p 4,p 1)) source in
  check "backedge to first node is allowed" (Schedule.validate_candidate cycle (p 1) (p 2) <> None);
  let edges = List.map int [-2147483648;-2147483647;-1;0;1;2;31;2147483646;2147483647] in
  let cases = ref 0 in
  let compare x y =
    let before = execute source x y and after = execute scheduled x y in
    if before <> after then failwith "reordered production operations changed value";
    incr cases
  in
  List.iter (fun x -> List.iter (compare x) edges) edges;
  let random = Random.State.make [|0x534348;2026;11;4|] in
  let value () = int (Random.State.bits random lor (Random.State.int random 4 lsl 30)) in
  for _ = 1 to 4096 do compare (value ()) (value ()) done;
  check "integer edge and random executions retain results" (!cases = 4177);
  Printf.printf "{\"success\":true,\"execution_cases\":%d,\"checks\":[%s]}\n"
    !cases (String.concat "," (List.map (Printf.sprintf "%S") (List.rev !checks)))
