(* Native constructor checks for the proved ARM64 alternate combinations.
   INRIA Non-Commercial License Agreement, as in this repository. *)
open CminorSel
open Op

let checks = ref []
let check name value =
  if not value then failwith ("instruction selection test failed: " ^ name);
  checks := name :: !checks
let p = Camlcoq.P.of_int
let x = Evar (p 1)
let y = Evar (p 2)
let operands = Econs (x, Econs (y, Enil))

let () =
  let enabled = ExperimentalOptions.select_enabled () in
  let original32 = Eop (Omul, operands) in
  let expected32 =
    if enabled then Eop (Omulsub, Econs (Eop (Ointconst Integers.Int.zero, Enil), operands))
    else Eop (Oneg, Econs (original32, Enil)) in
  check "32-bit product negation uses the selected gated constructor"
    (SelectOp.negint original32 = expected32);
  let original64 = Eop (Omull, operands) in
  let expected64 =
    if enabled then Eop (Omullsub, Econs (SelectLong.longconst Integers.Int64.zero, operands))
    else Eop (Onegl, Econs (original64, Enil)) in
  check "64-bit product negation uses the selected gated constructor"
    (SelectLong.negl original64 = expected64);
  let three32 = Eop (Ointconst (Integers.Int.repr (Camlcoq.Z.of_sint 3)), Enil) in
  check "constant folding remains unchanged"
    (SelectOp.negint three32 = Eop (Ointconst (Integers.Int.repr (Camlcoq.Z.of_sint (-3))), Enil));
  check "non-product integer expressions retain the ordinary negation"
    (SelectOp.negint x = Eop (Oneg, Econs (x,Enil)));
  check "non-product long expressions retain the ordinary negation"
    (SelectLong.negl x = Eop (Onegl, Econs (x,Enil)));
  let malformed = Eop (Omul, Econs (x,Enil)) in
  check "nonmatching argument arity does not fuse"
    (SelectOp.negint malformed = Eop (Oneg,Econs(malformed,Enil)));
  Printf.printf "{\"success\":true,\"enabled\":%b,\"checks\":[%s]}\n" enabled
    (String.concat "," (List.map (Printf.sprintf "%S") (List.rev !checks)))
