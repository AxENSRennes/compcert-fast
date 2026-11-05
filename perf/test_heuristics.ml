(* Native tests of real experimental oracles and existing extracted validators.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)

open AST
open BinNums
open Maps
open Integers
open Op

let p = Camlcoq.P.of_int
let int n = Int.repr (Camlcoq.Z.of_sint n)
let passed = ref []
let check name condition =
  if not condition then failwith ("heuristic test failed: " ^ name);
  passed := name :: !passed
let tree entries =
  List.fold_left (fun t (key, value) -> PTree.set (p key) value t)
    PTree.empty entries
let require_ok label = function
  | Errors.OK value -> value
  | Errors.Error _ -> failwith (label ^ " failed")

let check_graphs () =
  let cases = [
    "empty graph", [], [];
    "acyclic graph", [1,[2];2,[3];3,[]], [];
    "self loop", [1,[1]], [1];
    "two-node cycle", [1,[2];2,[1]], [1;2];
    "loop with acyclic exit", [1,[2];2,[3];3,[2;4];4,[]], [2;3];
    "disconnected cycles", [1,[1];2,[3];3,[2];4,[]], [1;2;3];
    "undefined target", [1,[999]], [];
    "duplicate edges", [1,[2;2];2,[1;1]], [1;2];
  ] in
  List.iter (fun (name, graph, expected) ->
    check name (ExperimentalOptions.cyclic_nodes graph = expected)) cases;
  let chain = List.init 10000 (fun i -> i, if i = 9999 then [] else [i+1]) in
  check "deep acyclic graph avoids recursive DFS stack overflow"
    (ExperimentalOptions.cyclic_nodes chain = [])

let check_costs () =
  let variable i = XTL.V (p i, Tint) in
  let f : XTL.xfunction = {
    XTL.fn_sig = signature_main; fn_stacksize = Z0; fn_entrypoint = p 1;
    fn_code = tree [
      1, [XTL.Xop (Oadd, [variable 1; variable 2], variable 3); XTL.Xbranch (p 2)];
      2, [XTL.Xreload (variable 7, variable 8);
          XTL.Xop (Oadd, [variable 4; variable 5], variable 6);
          XTL.Xcond (Ccompimm (Cne, int 0), [variable 6], p 2, p 3)];
      3, [XTL.Xreturn []]] } in
  let stats = Regalloc.spill_costs f in
  let cold = (stats (p 1)).IRC.cost in
  let hot = (stats (p 4)).IRC.cost in
  check "cold block spill cost remains unchanged" (cold = 10);
  check "cyclic block finite spill cost is weighted only when enabled"
    (hot = if ExperimentalOptions.enabled "loop-spill" then 80 else 10);
  check "mandatory register cost remains infinite" ((stats (p 8)).IRC.cost = max_int)

let check_layout () =
  let f : LTL.coq_function = {
    LTL.fn_sig = signature_main; fn_stacksize = Z0; fn_entrypoint = p 8;
    fn_code = tree [
      8, [LTL.Lcond (Ccompimm (Cne, int 0), [Machregs.R0], p 6, p 4)];
      6, [LTL.Lbranch (p 2)]; 4, [LTL.Lbranch (p 2)]; 2, [LTL.Lreturn]] } in
  let reach = Linearize.reachable f in
  let blocks = Linearizeaux.basic_blocks f (Linearizeaux.join_points f) in
  let baseline = Linearizeaux.flatten_blocks blocks in
  let candidate = Linearizeaux.enumerate_aux f reach in
  check "layout actually changes the fixture only when enabled"
    ((candidate <> baseline) = ExperimentalOptions.enabled "trace-layout");
  check "layout preserves every reachable block without duplication"
    (List.sort compare candidate = List.sort compare (List.map p [8;6;4;2]));
  let checked = require_ok "production layout validation" (Linearize.enumerate f) in
  check "production proved validator accepts the chosen order unchanged" (checked = candidate)

let pressure_function () =
  let signature = { sig_args = [Xint; Xint]; sig_res = Xint; sig_cc = cc_default } in
  let body = ref [1, RTL.Iop (Ointconst (int 0), [], p 3, p 2)] in
  for i = 0 to 47 do
    let pc = 2 + i in
    body := (pc, RTL.Iop (Oaddimm (int (i + 1)), [p 2], p (5+i),
                         p (if i = 47 then 1000 else pc+1))) :: !body
  done;
  body := (1000, RTL.Icond (Ccompimm (Cgt, int 0), [p 1], p 1001, p 2000)) :: !body;
  for i = 0 to 23 do
    body := (1001+i, RTL.Iop (Oadd, [p 3; p (5+i)], p 3, p (1002+i))) :: !body
  done;
  body := (1025, RTL.Iop (Oaddimm (int (-1)), [p 1], p 1, p 1000)) :: !body;
  for i = 0 to 23 do
    body := (2000+i, RTL.Iop (Oadd, [p 3; p (29+i)], p 3, p (2001+i))) :: !body
  done;
  body := (2024, RTL.Ireturn (Some (p 3))) :: !body;
  { RTL.fn_sig = signature; fn_params = [p 1; p 2]; fn_stacksize = Z0;
    fn_entrypoint = p 1; fn_code = tree !body }

let check_allocator () =
  let rtl = pressure_function () in
  let env = require_ok "pressure fixture typing" (RTLtyping.type_function rtl) in
  let candidate = require_ok "production allocation oracle" (Allocation.regalloc rtl) in
  ignore (require_ok "production allocation validator" (Allocation.check_function rtl candidate env));
  check "register-pressure candidate passes the production extracted validator" true;
  let fingerprint fn = Digest.to_hex (Digest.string (Marshal.to_string fn [Marshal.No_sharing])) in
  let baseline = require_ok "production baseline allocation" (Allocation.regalloc_baseline rtl) in
  ignore (require_ok "baseline allocation validator" (Allocation.check_function rtl baseline env));
  check "baseline retry allocation remains validated" true;
  check "baseline retry disables only experimental spill weighting"
    ((fingerprint baseline <> fingerprint candidate) = ExperimentalOptions.enabled "loop-spill");
  let restored = require_ok "allocation after baseline retry" (Allocation.regalloc rtl) in
  check "baseline retry restores the previous weighting setting"
    (fingerprint restored = fingerprint candidate);
  fingerprint candidate

let () =
  ExperimentalOptions.start_trace ();
  check_graphs ();
  check_costs ();
  check_layout ();
  let fingerprint = check_allocator () in
  Printf.printf "{\"success\":true,\"allocation_fingerprint\":%S,\"checks\":[%s],\"counters\":[%s]}\n"
    fingerprint
    (String.concat "," (List.map (Printf.sprintf "%S") (List.rev !passed)))
    (String.concat "," (List.map (fun (pass,event,count) ->
       Printf.sprintf "{\"pass\":%S,\"event\":%S,\"count\":%d}" pass event count)
       (ExperimentalOptions.summary ())))
