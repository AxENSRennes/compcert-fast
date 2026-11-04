(* Native checks of the production extracted unswitch transformation.
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
let nodes f = List.length (PTree.elements f.RTL.fn_code)
let flag = p 1
let counter = p 2
let result = p 3
let loop () : RTL.coq_function =
  {fn_sig={sig_args=[Xint;Xint];sig_res=Xint;sig_cc=cc_default};
   fn_params=[flag;counter];fn_stacksize=Z0;fn_entrypoint=p 1;
   fn_code=tree [
     1,RTL.Iop(Ointconst(int 0),[],result,p 2);
     2,RTL.Icond(Ccompimm(Cgt,int 0),[counter],p 3,p 9);
     3,RTL.Icond(Ccompimm(Cne,int 0),[flag],p 4,p 5);
     4,RTL.Iop(Oaddimm(int 1),[result],result,p 6);
     5,RTL.Iop(Oaddimm(int 3),[result],result,p 6);
     6,RTL.Iop(Oaddimm(int(-1)),[counter],counter,p 2);
     9,RTL.Ireturn(Some result)]}

(* The transition interpreter is deliberately bounded and uses CompCert's
   production operation/condition evaluators. It is differential testing,
   not the preservation proof. None records an undefined evaluated condition. *)
let execute f values =
  let ge=Globalenvs.Genv.globalenv(program f) in
  let rec step fuel pc regs flag_reads =
    if fuel=0 then failwith "unswitch fixture exceeded execution fuel";
    match PTree.get pc f.RTL.fn_code with
    | Some(RTL.Inop next) -> step (fuel-1) next regs flag_reads
    | Some(RTL.Iop(op,args,dst,next)) ->
      begin match Op.eval_operation ge Values.Vundef op
          (List.map(fun r -> PMap.get r regs) args) Memory.Mem.empty with
      | Some v -> step (fuel-1) next (PMap.set dst v regs) flag_reads
      | None -> None,flag_reads end
    | Some(RTL.Icond(cond,args,yes,no)) ->
      let flag_reads=if args=[flag] then flag_reads+1 else flag_reads in
      begin match Op.eval_condition cond (List.map(fun r -> PMap.get r regs) args) Memory.Mem.empty with
      | Some take -> step (fuel-1) (if take then yes else no) regs flag_reads
      | None -> None,flag_reads end
    | Some(RTL.Ireturn(Some r)) -> Some(PMap.get r regs),flag_reads
    | _ -> failwith "unsupported unswitch fixture instruction"
  in step 10000 f.RTL.fn_entrypoint (RTL.init_regs values f.RTL.fn_params) 0

let () =
  let f=loop () in
  let selected=match Unswitch.chosen f with Some b->b | None->failwith "no loop branch selected" in
  check "cyclic immutable flag condition is selected" (selected.Unswitch.branch_pc=p 3 && selected.Unswitch.branch_reg=flag);
  check "immutable parameter accepted" (Unswitch.immutable f flag);
  check "modified loop counter is not an immutable candidate" (not(Unswitch.immutable f counter));
  let tf=Unswitch.transf_function f in
  check "three real CFG phases are generated" (nodes tf = 3*nodes f);
  check "entry uses unlearned Normal phase" (tf.RTL.fn_entrypoint=Unswitch.tag Unswitch.Normal f.RTL.fn_entrypoint);
  check "metadata preserved" (tf.RTL.fn_sig=f.RTL.fn_sig && tf.RTL.fn_params=f.RTL.fn_params && tf.RTL.fn_stacksize=f.RTL.fn_stacksize);
  check "Normal phase retains the original comparison"
    (match PTree.get (Unswitch.tag Unswitch.Normal (p 3)) tf.RTL.fn_code with
     | Some(RTL.Icond(Ccompimm(Cne,n),args,yes,no)) -> n=int 0 && args=[flag] &&
         yes=Unswitch.tag(Unswitch.Known true)(p 4) && no=Unswitch.tag(Unswitch.Known false)(p 5)
     | _->false);
  List.iter(fun answer ->
    let mode=Unswitch.Known answer in
    check (Printf.sprintf "specialized phase %b removes the repeated branch" answer)
      (PTree.get(Unswitch.tag mode(p 3)) tf.RTL.fn_code =
       Some(RTL.Inop(Unswitch.tag mode (p(if answer then 4 else 5)))))) [false;true];
  List.iter(fun flag_value -> List.iter(fun count ->
    let input=[Values.Vint(int flag_value);Values.Vint(int count)] in
    let actual,original_reads=execute f input in
    let transformed,learned_reads=execute tf input in
    check (Printf.sprintf "same result for flag %d and loop bound %d" flag_value count) (actual=transformed);
    check (Printf.sprintf "expected arithmetic for flag %d and loop bound %d" flag_value count)
      (actual=Some(Values.Vint(int(max 0 count * (if flag_value=0 then 3 else 1)))));
    check (Printf.sprintf "comparison learned only once for flag %d and bound %d" flag_value count)
      (original_reads=max 0 count && learned_reads=(if count>0 then 1 else 0)))
    [-1;0;1;2;7;17]) [-7;0;1;42];
  let zero=[Values.Vundef;Values.Vint(int 0)] in
  check "source zero-iteration loop never evaluates uninitialized flag" (execute f zero=(Some(Values.Vint(int 0)),0));
  check "transformed zero-iteration loop does not speculate uninitialized flag" (execute tf zero=(Some(Values.Vint(int 0)),0));
  let undefined=[Values.Vundef;Values.Vint(int 1)] in
  check "undefined flag remains undefined at its first actual evaluation"
    (execute f undefined=(None,1) && execute tf undefined=(None,1));
  let mutable_flag={f with RTL.fn_code=PTree.set(p 4)(RTL.Iop(Oaddimm(int 1),[flag],flag,p 6)) f.RTL.fn_code} in
  check "mutable tested register is rejected" (Unswitch.chosen mutable_flag=None);
  check "rejected mutable flag leaves function unchanged" (Unswitch.transf_function mutable_flag=mutable_flag);
  let memory_condition={f with RTL.fn_code=PTree.set(p 3)
    (RTL.Icond(Ccompuimm(Cne,int 0),[flag],p 4,p 5)) f.RTL.fn_code} in
  check "memory-dependent unsigned condition is outside supported certificate" (Unswitch.chosen memory_condition=None);
  let dead_write={f with RTL.fn_code=PTree.set(p 100)
    (RTL.Iop(Ointconst(int 0),[],flag,p 9)) f.RTL.fn_code} in
  check "even an unreachable flag definition conservatively rejects candidate" (Unswitch.chosen dead_write=None);
  let empty={f with RTL.fn_code=PTree.empty} in
  check "empty graph falls back unchanged" (Unswitch.transf_function empty=empty);
  let tprog=Unswitch.transf_program(program f) in
  check "whole-program wrapper actually transforms the internal function"
    (match List.assoc(p 1)tprog.prog_defs with Gfun(Internal actual)->actual=tf | _->false);
  Printf.printf "{\"success\":true,\"checks\":[%s]}\n"
    (String.concat "," (List.map(Printf.sprintf "%S")(List.rev !passed)))
