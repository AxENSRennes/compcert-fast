(* Differential checks of the executable Coq model against actual NEON.
   No timing series, no claim that testing is a hardware correctness proof. *)
module Big = Z
open Neon_model
external hardware_eval : int -> int -> bytes -> bytes -> bytes = "compcert_neon_eval"
external scalar_u64_mul : bytes -> bytes -> bytes = "compcert_scalar_u64_mul"

let widths = [8,W8; 16,W16; 32,W32; 64,W64]
let operations = [0,"add",Vadd; 1,"sub",Vsub; 2,"mul",Vmul; 3,"and",Vand; 4,"or",Vorr; 5,"xor",Veor]
let seed = ref 0x4d595df4d0f33173L
let next () =
  let open Int64 in
  let x = logxor !seed (shift_left !seed 13) in
  let x = logxor x (shift_right_logical x 7) in
  let x = logxor x (shift_left x 17) in
  seed := x; x
let random_bytes n =
  let result = Bytes.create n in
  for i = 0 to n-1 do
    Bytes.set result i (Char.chr (Int64.to_int (Int64.logand (next ()) 255L)))
  done;
  result
let lane_values bits bytes =
  let width = bits / 8 in
  List.init (Bytes.length bytes / width)
    (fun index -> Big.of_bits (Bytes.sub_string bytes (index * width) width))
let pairs bits a b = List.combine (lane_values bits a) (lane_values bits b)
let equal_values left right = List.length left = List.length right && List.for_all2 Big.equal left right
let vector_cases = ref 0
let lane_comparisons = ref 0
let tail_cases = ref 0
let boundary_cases = ref 0
let plan_checks = ref 0
let unsupported_checks = ref 0
let scalar_fallback_cases = ref 0

let compare_vector bits w opid opname op a b =
  let model = eval_vector w op (pairs bits a b) in
  let actual = lane_values bits (hardware_eval bits opid a b) in
  if not (equal_values model actual) then
    failwith (Printf.sprintf "NEON/model mismatch: %s u%d case %d" opname bits !vector_cases);
  incr vector_cases;
  lane_comparisons := !lane_comparisons + List.length model

let check_boundaries bits w opid opname op =
  let bound = Big.shift_left Big.one bits in
  let values = [Big.zero; Big.one; Big.of_int 2; Big.pred bound;
                Big.sub bound (Big.of_int 2); Big.shift_right bound 1;
                Big.pred (Big.shift_right bound 1)] in
  let repeat value =
    let encoded = Big.to_bits value in
    Bytes.init 16 (fun index ->
      let lane_offset = index mod (bits / 8) in
      if lane_offset < String.length encoded then encoded.[lane_offset] else '\000') in
  List.iter (fun x -> List.iter (fun y ->
    compare_vector bits w opid opname op (repeat x) (repeat y);
    incr boundary_cases) values) values

let check_tails bits w opid opname op =
  let count = lanes w in
  let lengths = List.init (count * 3 + 2) (fun n -> n) @ [63;64;65;127;128;129;255;256;257] in
  List.iter (fun n ->
    let a = random_bytes (n * (bits / 8)) and b = random_bytes (n * (bits / 8)) in
    let inputs = pairs bits a b in
    let plan = plan_for w n in
    if not (validate_plan w n plan) then failwith "generated plan rejected";
    incr plan_checks;
    if checked_plan w n plan <> plan then failwith "valid vector plan changed";
    incr plan_checks;
    let bad = { vector_chunks = n + 100; scalar_tail = 0 } in
    if validate_plan w n bad then failwith "invalid vector plan accepted";
    incr plan_checks;
    if checked_plan w n bad <> plan then failwith "invalid plan was not repaired";
    incr plan_checks;
    if compile_loop w op n bad <> Some plan then failwith "checked vectorizer did not produce the valid supported plan";
    incr plan_checks;
    if compile_plan w op n bad <> Neon_plan plan then failwith "supported operation did not select a NEON plan";
    incr plan_checks;
    let scalar = scalar_loop w op inputs in
    let vector = vectorize w op inputs bad in
    let actual = lane_values bits (hardware_eval bits opid a b) in
    if not (equal_values scalar vector && equal_values scalar actual) then
      failwith (Printf.sprintf "vector/tail mismatch: %s u%d length %d" opname bits n);
    incr tail_cases;
    lane_comparisons := !lane_comparisons + n) lengths

let check_scalar_fallback () =
  List.iter (fun n ->
    let a = random_bytes (n * 8) and b = random_bytes (n * 8) in
    let input = pairs 64 a b in
    let plan = compile_plan W64 Vmul n { vector_chunks = n + 10; scalar_tail = 999 } in
    if plan <> Scalar_plan then failwith "unsupported operation requested a NEON plan";
    let expected = scalar_loop W64 Vmul input in
    let actual = lane_values 64 (scalar_u64_mul a b) in
    if not (equal_values expected actual && equal_values expected (run_compiled W64 Vmul input plan))
    then failwith "unsupported-operation scalar fallback mismatch";
    incr scalar_fallback_cases;
    lane_comparisons := !lane_comparisons + n)
    (List.init 18 (fun n -> n) @ [31;32;33;63;64;65;127;128;129;255;256;257])

let () =
  let rounds = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 50000 in
  if rounds < 1 then invalid_arg "positive randomized rounds required";
  List.iter (fun (bits,w) -> List.iter (fun (opid,opname,op) ->
    if not (bits = 64 && opid = 2) then begin
      check_boundaries bits w opid opname op;
      check_tails bits w opid opname op;
      for _ = 1 to rounds do
        compare_vector bits w opid opname op (random_bytes 16) (random_bytes 16)
      done
    end) operations) widths;
  (try
     ignore (hardware_eval 64 2 (Bytes.make 16 '\000') (Bytes.make 16 '\000'));
     failwith "unsupported 64-bit vector multiply unexpectedly accepted"
   with Invalid_argument _ -> incr unsupported_checks);
  if compile_loop W64 Vmul 10 { vector_chunks = 5; scalar_tail = 0 } <> None
  then failwith "vectorizer accepted unsupported 64-bit vector multiply";
  incr unsupported_checks;
  check_scalar_fallback ();
  (try
     ignore (hardware_eval 32 0 (Bytes.make 3 '\000') (Bytes.make 3 '\000'));
     failwith "mis-sized input unexpectedly accepted"
   with Invalid_argument _ -> incr unsupported_checks);
  Printf.printf "{\"success\":true,\"performance_measured\":false,\"random_rounds_per_configuration\":%d,\"random_vector_cases\":%d,\"boundary_vector_cases\":%d,\"tail_loop_cases\":%d,\"scalar_fallback_cases\":%d,\"lane_comparisons\":%d,\"plan_checks\":%d,\"negative_hardware_api_checks\":%d,\"seed\":\"4d595df4d0f33173\",\"unsupported\":[\"ordinary 64-bit lane vector multiplication\"]}\n"
    rounds (!vector_cases - !boundary_cases) !boundary_cases !tail_cases !scalar_fallback_cases !lane_comparisons !plan_checks !unsupported_checks
