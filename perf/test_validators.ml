(* Negative tests of production, Coq-extracted validators. These are tests,
   not substitutes for the kernel-checked correctness proofs. Distributed
   under the repository's INRIA Non-Commercial License Agreement. *)

open AST
open BinNums
open Errors
open Maps
open Machregs
open Op

let passed = ref []

let check name condition =
  if not condition then failwith ("validator test failed: " ^ name);
  passed := name :: !passed

let is_ok = function OK _ -> true | Error _ -> false
let is_error result = not (is_ok result)
let p = Camlcoq.P.of_int

let tree entries =
  List.fold_left (fun t (key, value) -> PTree.set (p key) value t)
    PTree.empty entries

(* Invoke the actual two extracted checks independently of the fallback. *)
let raw_enumeration_valid f reach candidate =
  match Linearize.nodeset_of_list candidate Linearize.Nodeset.empty with
  | Error _ -> false
  | OK nodes -> Linearize.check_reachable f reach nodes

let rec insertions x = function
  | [] -> [[x]]
  | head :: tail as items ->
      (x :: items) :: List.map (fun rest -> head :: rest) (insertions x tail)

let rec permutations = function
  | [] -> [[]]
  | head :: tail -> List.concat (List.map (insertions head) (permutations tail))

let check_linearization () =
  let f : LTL.coq_function =
    { fn_sig = signature_main; fn_stacksize = Z0;
      fn_entrypoint = p 1;
      fn_code = tree [1, [LTL.Lbranch (p 2)];
                      2, [LTL.Lbranch (p 7)];
                      7, [LTL.Lbranch (p 42)];
                      42, [LTL.Lreturn];
                      100, [LTL.Lreturn]] } in
  let reach = Linearize.reachable f in
  let reachable_nodes = List.map p [1; 2; 7; 42] in
  let fallback = List.map fst (PTree.elements f.LTL.fn_code) in
  check "reachability excludes the disconnected defined block"
    (List.for_all (fun node -> PMap.get node reach) reachable_nodes &&
     not (PMap.get (p 100) reach));
  check "deterministic fallback enumerates every defined block"
    (Linearize.fallback_enumeration f = fallback);
  check "fallback itself passes production uniqueness and coverage checks"
    (raw_enumeration_valid f reach fallback);
  List.iteri (fun index candidate ->
    check (Printf.sprintf "valid permutation %d passes the original checks" index)
      (raw_enumeration_valid f reach candidate);
    check (Printf.sprintf "valid permutation %d retains its order" index)
      (Linearize.enumerate_with f reach candidate = candidate))
    (permutations reachable_nodes);
  let invalid =
    ["empty candidate", [];
     "missing reachable entry", List.map p [2; 7; 42];
     "missing reachable internal block", List.map p [1; 7; 42];
     "missing reachable return", List.map p [1; 2; 7];
     "duplicate reachable node", List.map p [1; 2; 7; 42; 7];
     "duplicate unreachable node", List.map p [1; 2; 7; 42; 100; 100];
     "duplicate undefined node", List.map p [1; 2; 7; 42; 999; 999]] in
  List.iter (fun (name, candidate) ->
    check (name ^ " is rejected by the original checks")
      (not (raw_enumeration_valid f reach candidate));
    let repaired = Linearize.enumerate_with f reach candidate in
    check (name ^ " selects the deterministic fallback") (repaired = fallback);
    check (name ^ " repair satisfies the production checks")
      (raw_enumeration_valid f reach repaired)) invalid;
  (* Upstream only requires uniqueness and coverage of reachable defined
     blocks: extra nonduplicate labels are deliberately not rejected. *)
  let extra = reachable_nodes @ [p 999] in
  check "harmless extra label meets the actual upstream requirements"
    (raw_enumeration_valid f reach extra);
  check "accepted extra label is preserved without broadening the validator"
    (Linearize.enumerate_with f reach extra = extra);
  let cyclic = { f with LTL.fn_code =
      tree [1, [LTL.Lbranch (p 2)]; 2, [LTL.Lbranch (p 1)]] } in
  let cyclic_reach = Linearize.reachable cyclic in
  let repaired = Linearize.enumerate_with cyclic cyclic_reach [] in
  check "cycle with invalid candidate uses a valid finite fallback"
    (repaired = Linearize.fallback_enumeration cyclic &&
     raw_enumeration_valid cyclic cyclic_reach repaired);
  let empty = { f with LTL.fn_code = PTree.empty } in
  let empty_reach = Linearize.reachable empty in
  check "empty code map repairs duplicate candidate to empty enumeration"
    (Linearize.enumerate_with empty empty_reach [p 1; p 1] = []);
  check "public enumeration still validates on a normal graph"
    (match Linearize.enumerate f with
     | OK candidate -> raw_enumeration_valid f reach candidate
     | Error _ -> false)

let require_ok label = function
  | OK value -> value
  | Error _ -> failwith (label ^ " unexpectedly failed")

let check_allocation () =
  let signature =
    { sig_args = [Xint; Xint]; sig_res = Xint; sig_cc = cc_default } in
  let rtl : RTL.coq_function =
    { fn_sig = signature; fn_params = List.map p [1; 2];
      fn_stacksize = Z0; fn_entrypoint = p 1;
      fn_code = tree [1, RTL.Iop (Osub, List.map p [1; 2], p 3, p 2);
                      2, RTL.Ireturn (Some (p 3))] } in
  let env = require_ok "RTL type inference" (RTLtyping.type_function rtl) in
  let valid = require_ok "production allocator" (Allocation.regalloc rtl) in
  check "production register allocation passes the extracted validator"
    (is_ok (Allocation.check_function rtl valid env));
  check "public allocation plus validation accepts the valid RTL function"
    (is_ok (Allocation.transf_function rtl));
  let mutate_op replacement =
    let found = ref false in
    let fn_code = PTree.map1 (List.map (function
      | LTL.Lop (Osub, args, dst) ->
          found := true; replacement args dst
      | instr -> instr)) valid.LTL.fn_code in
    if not !found then failwith "expected subtraction in allocator output";
    { valid with LTL.fn_code } in
  let rejected name candidate =
    check name (is_error (Allocation.check_function rtl candidate env)) in
  let wrong_opcode = mutate_op (fun args dst -> LTL.Lop (Oadd, args, dst)) in
  rejected "allocator validator rejects a changed arithmetic opcode"
    wrong_opcode;
  let baseline_calls = ref 0 in
  let baseline () =
    incr baseline_calls;
    Allocation.regalloc_baseline rtl in
  let accepted = Allocation.validate_with_fallback rtl env (OK valid) baseline in
  check "accepted allocation does not evaluate the lazy baseline"
    (!baseline_calls = 0 && accepted = OK valid);
  let repaired = Allocation.validate_with_fallback rtl env (OK wrong_opcode) baseline in
  check "invalid candidate invokes the baseline exactly once" (!baseline_calls = 1);
  check "invalid candidate is replaced by a validated production baseline"
    (match repaired with OK tf -> is_ok (Allocation.check_function rtl tf env) | Error _ -> false);
  baseline_calls := 0;
  let repaired_error = Allocation.validate_with_fallback rtl env
    (Error [MSG "injected candidate oracle error"]) baseline in
  check "candidate oracle error invokes baseline once" (!baseline_calls = 1);
  check "candidate oracle error is recovered through production validation"
    (match repaired_error with OK tf -> is_ok (Allocation.check_function rtl tf env) | Error _ -> false);
  baseline_calls := 0;
  let bad_baseline () = incr baseline_calls; OK wrong_opcode in
  check "malformed baseline is rejected by the same production validator"
    (is_error (Allocation.validate_with_fallback rtl env (OK wrong_opcode) bad_baseline));
  check "malformed baseline is attempted exactly once" (!baseline_calls = 1);
  baseline_calls := 0;
  let failing_baseline () = incr baseline_calls; Error [MSG "injected baseline oracle error"] in
  check "errors from both oracles remain compilation errors"
    (is_error (Allocation.validate_with_fallback rtl env
      (Error [MSG "injected candidate oracle error"]) failing_baseline) && !baseline_calls = 1);
  rejected "allocator validator rejects reversed subtraction operands"
    (mutate_op (fun args dst -> LTL.Lop (Osub, List.rev args, dst)));
  rejected "allocator validator rejects a corrupted result register"
    (mutate_op (fun args dst ->
      let wrong = if dst = R2 then R3 else R2 in
      LTL.Lop (Osub, args, wrong)));
  rejected "allocator validator rejects an incompatible result signature"
    { valid with LTL.fn_sig = { signature with sig_res = Xlong } };
  rejected "allocator validator rejects an incompatible stack size"
    { valid with LTL.fn_stacksize = Zpos (p 16) };
  rejected "allocator validator rejects a missing entry block"
    { valid with LTL.fn_code = PTree.remove valid.LTL.fn_entrypoint valid.LTL.fn_code };
  rejected "allocator validator rejects a missing reachable return block"
    { valid with LTL.fn_code = PTree.remove (p 2) valid.LTL.fn_code };
  let literal : RTL.coq_function =
    { rtl with fn_sig = signature_main; fn_params = [];
      fn_code = tree [1, RTL.Iop (Ointconst (Integers.Int.repr (Camlcoq.Z.of_sint 42)), [], p 1, p 2);
                      2, RTL.Ireturn (Some (p 1))] } in
  let literal_env = require_ok "constant RTL typing" (RTLtyping.type_function literal) in
  let literal_ltl = require_ok "constant allocation" (Allocation.regalloc literal) in
  check "constant-return allocation is accepted"
    (is_ok (Allocation.check_function literal literal_ltl literal_env));
  let tampered = { literal_ltl with LTL.fn_code =
    PTree.map1 (List.map (function
      | LTL.Lop (Ointconst _, args, dst) ->
          LTL.Lop (Ointconst (Integers.Int.repr (Camlcoq.Z.of_sint 43)), args, dst)
      | instr -> instr)) literal_ltl.LTL.fn_code } in
  check "allocator validator rejects silently changing a return constant"
    (is_error (Allocation.check_function literal tampered literal_env))

let () =
  check_linearization ();
  check_allocation ();
  let names = List.rev !passed in
  Printf.printf "{\"success\":true,\"checks\":[%s]}\n"
    (String.concat "," (List.map (Printf.sprintf "%S") names))
