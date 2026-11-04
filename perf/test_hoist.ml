(* Native checks of the production extracted integer-constant hoisting pass.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Op
let p = Camlcoq.P.of_int
let int n = Int.repr (Camlcoq.Z.of_sint n)
let passed = ref []
let check name test = if not test then failwith name else passed := name :: !passed
let tree items = List.fold_left (fun m (k,v) -> PTree.set (p k) v m) PTree.empty items
let program f = {prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let counter = p 2
let result = p 3
let value1 = p 4
let value2 = p 5
let loop () : RTL.coq_function =
  {fn_sig={sig_args=[Xint;Xint];sig_res=Xint;sig_cc=cc_default};
   fn_params=[counter;p 100];fn_stacksize=Z0;fn_entrypoint=p 1;
   fn_code=tree [
     1,RTL.Iop(Ointconst(int 7),[],result,p 2);
     2,RTL.Icond(Ccompimm(Cgt,int 0),[counter],p 3,p 9);
     3,RTL.Iop(Ointconst(int 42),[],value1,p 4);
     4,RTL.Iop(Ointconst(int 42),[],value2,p 6);
     6,RTL.Iop(Oadd,[value1;value2],value1,p 7);
     7,RTL.Iop(Oadd,[result;value1],result,p 8);
     8,RTL.Iop(Oaddimm(int(-1)),[counter],counter,p 2);
     9,RTL.Ireturn(Some result);
     129,RTL.Iop(Oaddimm(int 1),[p 200],p 300,p 9)]}

(* Bounded differential execution using the production RTL operation and
   condition evaluators. The proof, rather than this fixture interpreter,
   establishes preservation for all RTL instructions and executions. *)
let execute f values =
  let ge=Globalenvs.Genv.globalenv(program f) in
  let rec step fuel pc regs selected_evaluations =
    if fuel=0 then failwith "constant-hoisting fixture exceeded execution fuel";
    match PTree.get pc f.RTL.fn_code with
    | Some(RTL.Inop next) -> step (fuel-1) next regs selected_evaluations
    | Some(RTL.Iop(op,args,dst,next)) ->
      let selected_evaluations=match op with
        | Ointconst n when n=int 42 -> selected_evaluations+1
        | _ -> selected_evaluations in
      begin match Op.eval_operation ge Values.Vundef op
          (List.map(fun r -> PMap.get r regs) args) Memory.Mem.empty with
      | Some v -> step (fuel-1) next (PMap.set dst v regs) selected_evaluations
      | None -> None,selected_evaluations end
    | Some(RTL.Icond(cond,args,yes,no)) ->
      begin match Op.eval_condition cond (List.map(fun r -> PMap.get r regs) args) Memory.Mem.empty with
      | Some take -> step (fuel-1) (if take then yes else no) regs selected_evaluations
      | None -> None,selected_evaluations end
    | Some(RTL.Ireturn(Some r)) -> Some(PMap.get r regs),selected_evaluations
    | _ -> failwith "unsupported constant-hoisting fixture instruction"
  in step 10000 f.RTL.fn_entrypoint (RTL.init_regs values f.RTL.fn_params) 0

let () =
  let f=loop () in
  check "cyclic constant preferred to the entry constant" (HoistConst.chosen f=Some(int 42));
  let tf=HoistConst.transf_function f in
  let temporary=HoistConst.fresh_reg f in
  let entry=HoistConst.fresh_node f in
  check "new temporary is above original definitions, uses and parameters" (temporary=p 301);
  check "new entry node is above all original labels" (entry=p 130);
  check "entrypoint is the fresh preheader" (tf.RTL.fn_entrypoint=entry);
  check "metadata is preserved"
    (tf.RTL.fn_sig=f.RTL.fn_sig && tf.RTL.fn_params=f.RTL.fn_params && tf.RTL.fn_stacksize=f.RTL.fn_stacksize);
  check "exactly one new graph node is added"
    (List.length(PTree.elements tf.RTL.fn_code)=1+List.length(PTree.elements f.RTL.fn_code));
  check "new entry computes the constant only into the fresh temporary"
    (PTree.get entry tf.RTL.fn_code=Some(RTL.Iop(Ointconst(int 42),[],temporary,f.RTL.fn_entrypoint)));
  check "first loop literal becomes a temporary move"
    (PTree.get(p 3)tf.RTL.fn_code=Some(RTL.Iop(Omove,[temporary],value1,p 4)));
  check "second identical loop literal becomes a temporary move"
    (PTree.get(p 4)tf.RTL.fn_code=Some(RTL.Iop(Omove,[temporary],value2,p 6)));
  check "different literal stays in its original location"
    (PTree.get(p 1)tf.RTL.fn_code=PTree.get(p 1)f.RTL.fn_code);
  check "unrelated instruction is preserved"
    (PTree.get(p 129)tf.RTL.fn_code=PTree.get(p 129)f.RTL.fn_code);
  List.iter(fun count ->
    let inputs=[Values.Vint(int count);Values.Vundef] in
    let actual,original_evaluations=execute f inputs in
    let transformed,hoisted_evaluations=execute tf inputs in
    check (Printf.sprintf "same result for loop bound %d" count) (actual=transformed);
    check (Printf.sprintf "expected arithmetic for loop bound %d" count)
      (actual=Some(Values.Vint(int(7+84*max 0 count))));
    check (Printf.sprintf "one fresh-entry evaluation replaces repeated literals for bound %d" count)
      (original_evaluations=2*max 0 count && hoisted_evaluations=1))
    [-2;0;1;2;7;17];
  let zero_values=[Values.Vint(int 0);Values.Vundef] in
  check "zero-iteration path retains the original destination value"
    (fst(execute tf zero_values)=Some(Values.Vint(int 7)));
  let no_literal={f with RTL.fn_code=tree [1,RTL.Ireturn(Some counter)]} in
  check "function with no supported constant is unchanged"
    (HoistConst.chosen no_literal=None && HoistConst.transf_function no_literal=no_literal);
  let malformed={no_literal with RTL.fn_code=tree [
    1,RTL.Iop(Ointconst(int 42),[counter],result,p 2);2,RTL.Ireturn(Some result)]} in
  check "literal operation with nonempty arguments is not selected"
    (HoistConst.chosen malformed=None && HoistConst.transf_function malformed=malformed);
  let acyclic={no_literal with RTL.fn_code=tree [
    1,RTL.Iop(Ointconst(int 42),[],result,p 2);2,RTL.Ireturn(Some result)]} in
  check "pure acyclic literal has the documented safe fallback selection"
    (HoistConst.chosen acyclic=Some(int 42));
  check "acyclic fallback retains its result"
    (fst(execute acyclic zero_values)=fst(execute (HoistConst.transf_function acyclic)zero_values));
  let tprog=HoistConst.transf_program(program f) in
  check "whole-program wrapper actually transforms the internal function"
    (match List.assoc(p 1)tprog.prog_defs with Gfun(Internal actual)->actual=tf | _->false);
  Printf.printf "{\"success\":true,\"checks\":[%s]}\n"
    (String.concat "," (List.map(Printf.sprintf "%S")(List.rev !passed)))
