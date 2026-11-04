(* Explicit packed integer NEON builtin tests against production semantics.
   INRIA Non-Commercial License Agreement, as in this repository. *)
open AST
open Asm
open Values
open Builtins1

let checks = ref []
let check name value =
  if not value then failwith ("packed NEON test failed: " ^ name);
  checks := name :: !checks

let reference op a b =
  let mask = 0xffff_ffffL in
  let lane x = Int64.logand x mask in
  let low = lane (op (lane a) (lane b)) in
  let high = lane (op (Int64.shift_right_logical a 32)
                      (Int64.shift_right_logical b 32)) in
  Int64.logor low (Int64.shift_left high 32)

let builtins = [
  "__builtin_cc_neon_add_u32x2", BI_neon_add_u32x2, Int64.add;
  "__builtin_cc_neon_sub_u32x2", BI_neon_sub_u32x2, Int64.sub;
  "__builtin_cc_neon_mul_u32x2", BI_neon_mul_u32x2, Int64.mul
]

let () =
  let enabled = ExperimentalOptions.packed_neon_enabled () in
  let cases = ref 0 in
  let edges = [0L; 1L; 2L; 0xffff_ffffL; 0x1_0000_0000L;
    0x7fff_ffff_8000_0000L; 0x8000_0000_7fff_ffffL;
    0xffff_ffff_0000_0000L; -1L] in
  let state = ref 0x6a09e667f3bcc909L in
  let random () =
    state := Int64.add (Int64.mul !state 6364136223846793005L) 1442695040888963407L;
    !state in
  List.iter (fun (name, builtin, op) ->
    check (name ^ " C registration follows gate")
      (List.mem_assoc name CBuiltins.builtins.C.builtin_functions = enabled);
    let signature = platform_builtin_sig builtin in
    let ef = EF_builtin (name, signature) in
    check (name ^ " signature is two 64-bit integers to one 64-bit integer")
      (signature.sig_args = [Xlong;Xlong] && signature.sig_res = Xlong && signature.sig_cc = cc_default);
    check (name ^ " exact scratch clobbers")
      (Machregs.destroyed_by_builtin ef = [Machregs.F16;Machregs.F17]);
    check (name ^ " branch relaxation accounts four instructions")
      (Asmexpand.BInfo.instr_size (Pbuiltin(ef,[BA(IR X0);BA(IR X1)],BR(IR X0))) = 16);
    let instr = Pbuiltin(ef,[BA(IR X0);BA(IR X1)],BR(IR X0)) in
    let fn = {fn_sig=signature;fn_code=[instr]} in
    check (name ^ " valid register operands preserved through production expansion")
      (match Asmexpand.expand_function (Camlcoq.P.of_int 1) fn with
       | Errors.OK tf -> tf.fn_code = [instr]
       | Errors.Error _ -> false);
    check (name ^ " builtin lookup requires the specified signature")
      (Builtins.lookup_builtin_function name signature = Some (Builtins.BI_platform builtin));
    check (name ^ " malformed operand classes rejected by expansion")
      (try Asmexpand.expand_instruction (Pbuiltin(ef,[BA(FR D0);BA(IR X1)],BR(IR X0)));
           false with Asmexpand.Error _ -> true);
    List.iter (fun (label, wrong_signature) ->
      check (name ^ " rejects " ^ label ^ " signature at expansion")
        (try Asmexpand.expand_instruction
               (Pbuiltin(EF_builtin(name,wrong_signature),[BA(IR X0);BA(IR X1)],BR(IR X0)));
             false with Asmexpand.Error _ -> true)
    ) ["argument", {signature with sig_args=[Xint;Xlong]};
       "result", {signature with sig_res=Xint};
       "calling convention", {signature with sig_cc={cc_default with cc_unproto=true}}];
    let test a b =
      incr cases;
      let actual = platform_builtin_sem builtin
        [Vlong(Camlcoq.coqint_of_camlint64 a);Vlong(Camlcoq.coqint_of_camlint64 b)] in
      let expected = Some(Vlong(Camlcoq.coqint_of_camlint64 (reference op a b))) in
      if actual <> expected then failwith (name ^ " numerical semantics mismatch") in
    List.iter (fun a -> List.iter (test a) edges) edges;
    for _ = 1 to 10000 do let a = random () in let b = random () in test a b done;
    check (name ^ " exact lane arithmetic on edges and deterministic random pairs") true
  ) builtins;
  let target = Camlcoq.P.of_int 1 in
  let signature = platform_builtin_sig BI_neon_add_u32x2 in
  let ef = EF_builtin("__builtin_cc_neon_add_u32x2", signature) in
  let instr = Pbuiltin(ef,[BA(IR X0);BA(IR X1)],BR(IR X0)) in
  let branch = Ptbz(X,X0,Integers.Int.zero,target) in
  let fn count = {fn_sig=signature;
    fn_code=branch :: (List.init count (fun _ -> instr) @ [Plabel target])} in
  let near = fn 2047 and far = fn 2048 in
  check "short branch remains short below packed-builtin displacement boundary"
    ((Asmexpand.BRelax.relaxation near).fn_code = near.fn_code);
  check "short branch is relaxed across 32768 bytes of packed builtins"
    (match (Asmexpand.BRelax.relaxation far).fn_code with
     | Ptbnz _ :: Pb label :: _ -> label = target
     | _ -> false);
  check "existing unrelated builtin scratch behavior unchanged"
    (Machregs.destroyed_by_builtin(EF_builtin("__builtin_bswap64", platform_builtin_sig BI_neon_add_u32x2)) = []);
  Printf.printf "{\"success\":true,\"enabled\":%b,\"semantic_cases\":%d,\"checks\":[%s]}\n"
    enabled !cases (String.concat "," (List.map (Printf.sprintf "%S") (List.rev !checks)))
