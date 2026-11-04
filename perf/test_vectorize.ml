(* Production-extracted automatic SLP checks. Distributed under the
   repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Values
open Op

let p = Camlcoq.P.of_int
let int n = Int.repr (Camlcoq.Z.of_sint n)
let checks = ref []
let cases = ref 0
let check name value = if not value then failwith name else checks := name :: !checks
let tree items = List.fold_left (fun t (pc,i) -> PTree.set (p pc) i t) PTree.empty items
let program f = {prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let count pred f = List.length (List.filter (fun (_,i) -> pred i) (PTree.elements f.RTL.fn_code))
let packed = function
  | RTL.Ibuiltin(EF_builtin(name,_),_,_,_) -> name="__builtin_cc_neon_add_u32x2"
  | _ -> false
let fixture a b : RTL.coq_function =
  {fn_sig={sig_args=[Xint];sig_res=Xint;sig_cc=cc_default};fn_params=[p 1];
   fn_stacksize=Z0;fn_entrypoint=p 1;fn_code=tree [
     1,RTL.Iop(Oaddimm a,[p 1],p 2,p 2);
     2,RTL.Iop(Oaddimm b,[p 1],p 3,p 3);
     3,RTL.Iop(Omul,[p 2;p 3],p 4,p 4);
     4,RTL.Ireturn(Some(p 4))]}

(* All numerical operations and builtin semantics below come from production
   extraction. This bounded executor is a test, not the preservation proof. *)
let execute f inputs =
  let ge=Globalenvs.Genv.globalenv(program f) in
  let rec step fuel pc regs vectors =
    if fuel=0 then failwith "vector fixture exhausted execution fuel";
    let args values = List.map (fun r -> PMap.get r regs) values in
    match PTree.get pc f.RTL.fn_code with
    | Some(RTL.Inop next) -> step (fuel-1) next regs vectors
    | Some(RTL.Iop(op,rl,dst,next)) ->
      begin match Op.eval_operation ge Vundef op (args rl) Memory.Mem.empty with
      | Some v -> step (fuel-1) next (PMap.set dst v regs) vectors
      | None -> failwith "undefined operation in vector fixture" end
    | Some(RTL.Ibuiltin(EF_builtin(name,sg),rl,BR dst,next)) ->
      let values=List.map (function BA r -> PMap.get r regs | _ -> failwith "nonregister vector argument") rl in
      begin match Builtins.lookup_builtin_function name sg with
      | Some bf -> begin match Builtins.builtin_function_sem bf values with
        | Some v -> step (fuel-1) next (PMap.set dst v regs) (vectors+1)
        | None -> failwith "rejected generated numeric builtin" end
      | None -> failwith "unknown generated vector builtin" end
    | Some(RTL.Icond(cond,rl,yes,no)) ->
      begin match Op.eval_condition cond (args rl) Memory.Mem.empty with
      | Some take -> step (fuel-1) (if take then yes else no) regs vectors
      | None -> failwith "undefined vector fixture condition" end
    | Some(RTL.Ireturn(Some r)) -> PMap.get r regs,regs,vectors
    | _ -> failwith "unsupported vector fixture instruction"
  in step 200000 f.RTL.fn_entrypoint (RTL.init_regs inputs f.RTL.fn_params) 0

let compare f inputs =
  let source,rs,_ = execute f inputs in
  let vectorized=Vectorize.transf_function f in
  let target,trs,vectors = execute vectorized inputs in
  let lowered,lrs,lowered_vectors=execute (LowerLong.transf_function vectorized) inputs in
  incr cases;
  if source<>target || source<>lowered || vectors<>lowered_vectors then
    failwith "automatic SLP or supported-operation lowering result mismatch";
  for r=1 to Camlcoq.P.to_int (RTL.max_reg_function f) do
    if PMap.get (p r) rs <> PMap.get (p r) trs || PMap.get (p r) rs <> PMap.get (p r) lrs then
      failwith "automatic SLP changed an original register"
  done;
  vectors

let () =
  let f=fixture (int 3) (int 7) in
  let plan=match Vectorize.selected_pair f with Some plan->plan | None->failwith "no automatic pair selected" in
  let tf=Vectorize.transf_function f in
  check "ordinary scalar affine pair is selected without source builtin"
    (plan.Vectorize.source_reg=p 1 && plan.Vectorize.first_pc=p 1 && plan.Vectorize.second_pc=p 2);
  check "actual transformation inserts exactly one packed builtin" (count packed f=0 && count packed tf=1);
  check "three fresh graph nodes are added" (List.length(PTree.elements tf.RTL.fn_code)=7);
  let lowered=LowerLong.transf_function tf in
  check "packing lowering adds suffixes only for the two expanded operations"
    (List.length(PTree.elements lowered.RTL.fn_code)=9);
  check "the actual supported-operation lowering removes both generic packing operations"
    (count (function RTL.Iop((Omakelong|Ohighlong),_,_,_)->true|_->false) lowered=0);
  check "signature, params, stack and entry remain identical"
    (tf.RTL.fn_sig=f.RTL.fn_sig && tf.RTL.fn_params=f.RTL.fn_params &&
     tf.RTL.fn_stacksize=f.RTL.fn_stacksize && tf.RTL.fn_entrypoint=f.RTL.fn_entrypoint);
  check "both source lanes are duplicated into a fresh input register"
    (PTree.get(p 1)tf.RTL.fn_code=Some(RTL.Iop(Omakelong,[p 1;p 1],Vectorize.input_reg f,Vectorize.constant_pc f)));
  check "input, constants and result have distinct fresh registers"
    (Vectorize.input_reg f<>Vectorize.constant_reg f && Vectorize.input_reg f<>Vectorize.result_reg f &&
     Vectorize.constant_reg f<>Vectorize.result_reg f &&
     Camlcoq.P.to_int(Vectorize.input_reg f)>Camlcoq.P.to_int(RTL.max_reg_function f));
  let edges=[0;1;2;-1;0x7fffffff;0x80000000;0x55555555;0xaaaaaaaa;0xffffffff] in
  List.iter(fun a -> List.iter(fun b -> List.iter(fun x ->
    ignore(compare(fixture(int a)(int b))[Vint(int x)]))edges)edges)edges;
  check "all 729 edge-value and lane-constant combinations preserve every original register" true;
  let random=Random.State.make [|0x3a71;0x15ab|] in
  for _=1 to 10000 do
    let x=(Random.State.bits random lsl 2) lor (Random.State.bits random land 3) in
    ignore(compare f [Vint(int x)])
  done;
  check "10000 deterministic random input values preserve scalar results" true;
  let nonints=[Vundef;Vlong(Int64.repr(Camlcoq.Z.of_sint 13));
    Vfloat(Floats.Float.of_bits(Int64.repr(Camlcoq.Z.of_sint 0)));
    Vsingle(Floats.Float32.of_bits(Int.zero));Vptr(p 9,Ptrofs.zero)] in
  List.iter(fun value -> check "all noninteger value forms preserve both undefined lanes"
    (compare f [value]=1))nonints;
  let reject name candidate =
    check name (Vectorize.selected_pair candidate=None && Vectorize.transf_function candidate=candidate) in
  reject "rejects independent inputs whose lanes might be defined separately"
    {f with RTL.fn_code=PTree.set(p 2)(RTL.Iop(Oaddimm(int 7),[p 5],p 3,p 3))f.RTL.fn_code};
  check "negative control: packing separate undefined/defined lanes would lose a defined result"
    (Val.longofwords Vundef (Vint(int 2))=Vundef && Val.add (Vint(int 2))(Vint(int 7))=Vint(int 9));
  let separate={f with RTL.fn_code=tree [
    1,RTL.Iop(Oaddimm(int 3),[p 1],p 2,p 2);
    2,RTL.Iop(Oaddimm(int 7),[p 5],p 3,p 3);3,RTL.Ireturn(Some(p 2))]} in
  check "a defined live lane survives an unrelated undefined unused lane via refusal"
    (Vectorize.selected_pair separate=None && compare separate [Vint(int 2)]=0 &&
     let value,_,_=execute separate [Vint(int 2)] in value=Vint(int 5));
  reject "rejects overwrite of shared source by the first scalar operation"
    {f with RTL.fn_code=PTree.set(p 1)(RTL.Iop(Oaddimm(int 3),[p 1],p 1,p 2))f.RTL.fn_code};
  reject "rejects coincident result registers"
    {f with RTL.fn_code=PTree.set(p 2)(RTL.Iop(Oaddimm(int 7),[p 1],p 2,p 3))f.RTL.fn_code};
  reject "rejects second operation as function entry" {f with RTL.fn_entrypoint=p 2};
  reject "rejects even an unreachable extra predecessor of the second operation"
    {f with RTL.fn_code=PTree.set(p 10)(RTL.Inop(p 2))f.RTL.fn_code};
  reject "rejects a missing second instruction" {f with RTL.fn_code=PTree.remove(p 2)f.RTL.fn_code};
  reject "rejects other arithmetic operators"
    {f with RTL.fn_code=PTree.set(p 2)(RTL.Iop(Osub,[p 1;p 2],p 3,p 3))f.RTL.fn_code};
  reject "rejects malformed scalar argument lists"
    {f with RTL.fn_code=PTree.set(p 1)(RTL.Iop(Oaddimm(int 3),[],p 2,p 2))f.RTL.fn_code};
  let big={f with RTL.fn_code=List.fold_left(fun code n->PTree.set(p(n+10))(RTL.Ireturn None)code)
    f.RTL.fn_code (List.init 600 Fun.id)} in
  reject "functions over the conservative 512-node budget remain byte-for-byte unchanged" big;
  let overwrite={f with RTL.fn_code=tree [
    1,RTL.Iop(Oaddimm(int 3),[p 1],p 2,p 2);
    2,RTL.Iop(Oaddimm(int 7),[p 1],p 1,p 3);3,RTL.Ireturn(Some(p 1))]} in
  check "second result may overwrite shared input after both lanes are packed"
    (Vectorize.selected_pair overwrite<>None && compare overwrite [Vint(int 11)]=1);
  let loop={f with RTL.fn_sig={f.RTL.fn_sig with sig_args=[Xint;Xint]};fn_params=[p 1;p 5];
    fn_code=tree [
      1,RTL.Iop(Ointconst(int 0),[],p 4,p 2);
      2,RTL.Icond(Ccompimm(Cgt,int 0),[p 5],p 3,p 9);
      3,RTL.Iop(Oaddimm(int 3),[p 1],p 2,p 4);
      4,RTL.Iop(Oaddimm(int 7),[p 1],p 3,p 5);
      5,RTL.Iop(Oadd,[p 2;p 3],p 4,p 6);
      6,RTL.Iop(Oaddimm(int(-1)),[p 5],p 5,p 2);
      9,RTL.Ireturn(Some(p 4))]} in
  List.iter(fun bound -> List.iter(fun value ->
    let vectors=compare loop [value;Vint(int bound)] in
    check (Printf.sprintf "loop bound %d executes vector pair only when reached" bound)
      (vectors=max 0 bound)) [Vundef;Vint(int 0);Vint(int(-1));Vint(int 123456789)]) [-2;0;1;2;7;33];
  let tprog=Vectorize.transf_program(program f) in
  check "whole-program wrapper applies the actual automatic transformation"
    (match List.assoc(p 1)tprog.prog_defs with Gfun(Internal fn)->fn=tf | _->false);
  Printf.printf "{\"success\":true,\"semantic_cases\":%d,\"checks\":[%s]}\n"
    !cases (String.concat "," (List.map(Printf.sprintf "%S")(List.rev !checks)))
