(* Exercise production extracted RTL transformations, not test replacements.
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
  if not condition then failwith name;
  passed := name :: !passed
let tree entries = List.fold_left (fun t (k,v) -> PTree.set (p k) v t) PTree.empty entries
let signature args = {sig_args=args; sig_res=Xint; sig_cc=cc_default}
let program f = {prog_defs=[p 1, Gfun (Internal f)]; prog_public=[p 1]; prog_main=p 1}
let function_after prog =
  match List.assoc (p 1) prog.prog_defs with Gfun (Internal f) -> f | _ -> failwith "lost function"
let require_ok = function Errors.OK x -> x | Errors.Error _ -> failwith "cleanup refused fixture"
let count pred f = List.length (List.filter (fun (_,i) -> pred i) (PTree.elements f.RTL.fn_code))
let nodes f = List.length (PTree.elements f.RTL.fn_code)
let load = function RTL.Iload _ -> true | _ -> false
let store = function RTL.Istore _ -> true | _ -> false

(* This interpreter calls the real RTL operation/condition evaluators. It is a
   bounded differential test for finite pure fixtures, not the compiler proof. *)
let execute f input =
  let ge = Globalenvs.Genv.globalenv (program f) in
  let rec step fuel pc rs =
    if fuel=0 then failwith "fixture exhausted execution fuel";
    match PTree.get pc f.RTL.fn_code with
    | Some (RTL.Inop next) -> step (fuel-1) next rs
    | Some (RTL.Iop (op,args,dst,next)) ->
        let values = List.map (fun r -> PMap.get r rs) args in
        begin match Op.eval_operation ge Values.Vundef op values Memory.Mem.empty with
        | Some v -> step (fuel-1) next (PMap.set dst v rs)
        | None -> failwith "undefined pure fixture operation" end
    | Some (RTL.Icond (cond,args,yes,no)) ->
        begin match Op.eval_condition cond (List.map (fun r -> PMap.get r rs) args) Memory.Mem.empty with
        | Some take -> step (fuel-1) (if take then yes else no) rs
        | None -> failwith "undefined fixture condition" end
    | Some (RTL.Ireturn (Some r)) -> PMap.get r rs
    | _ -> failwith "unsupported pure fixture instruction"
  in step 10000 f.RTL.fn_entrypoint (RTL.init_regs [Values.Vint (int input)] f.RTL.fn_params)

let loop () : RTL.coq_function =
  {fn_sig=signature [Xint]; fn_params=[p 1]; fn_stacksize=Z0; fn_entrypoint=p 6;
   fn_code=tree [6,RTL.Iop(Ointconst(int 0),[],p 2,p 5);
                 5,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 4,p 1);
                 4,RTL.Iop(Oaddimm(int 7),[p 2],p 2,p 3);
                 3,RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 5);
                 1,RTL.Ireturn(Some(p 2))]}
let visits f n =
  let ge=Globalenvs.Genv.globalenv(program f) in
  let rec walk fuel pc rs first stable =
    if fuel=0 then failwith "loop fixture fuel";
    let first=first+(if pc=Experimental.tagged false (p 4) then 1 else 0) in
    let stable=stable+(if pc=Experimental.tagged true (p 4) then 1 else 0) in
    match PTree.get pc f.RTL.fn_code with
    | Some(RTL.Iop(op,args,dst,next)) ->
        let value=match Op.eval_operation ge Values.Vundef op (List.map(fun r->PMap.get r rs)args) Memory.Mem.empty with Some v->v|_->failwith "op" in
        walk(fuel-1)next(PMap.set dst value rs)first stable
    | Some(RTL.Icond(cond,args,yes,no)) ->
        let take=match Op.eval_condition cond (List.map(fun r->PMap.get r rs)args) Memory.Mem.empty with Some b->b|_->failwith "cond" in
        walk(fuel-1)(if take then yes else no)rs first stable
    | Some(RTL.Ireturn _) -> first,stable
    | _ -> failwith "unexpected instruction"
  in walk 10000 f.RTL.fn_entrypoint (RTL.init_regs[Values.Vint(int n)]f.RTL.fn_params)0 0
let () =
  let f=loop() in let tf=LoopPeel.transf_function f in
  check "cover candidate accepted" (LoopPeel.accepted f);
  check "actual graph peeling creates two copies" (nodes tf=2*nodes f);
  List.iter(fun n ->
    check(Printf.sprintf "same result at trip count %d" n)(execute f n=execute tf n);
    let a,b=visits tf n in
    check(Printf.sprintf "first body executes exactly once at count %d" n)(a=(if n>0 then 1 else 0));
    check(Printf.sprintf "remaining iterations stay in stable copy at count %d" n)(b=max 0(n-1)))
    [-1;0;1;2;3;4;7;8;31;100];
  let acyclic={f with RTL.fn_entrypoint=p 2; RTL.fn_code=tree[2,RTL.Inop(p 1);1,RTL.Ireturn(Some(p 1))]} in
  check "postorder acyclic graph is retained exactly" (LoopPeel.transf_function acyclic=acyclic);
  let broken={f with RTL.fn_code=tree[6,RTL.Inop(p 999)]} in
  check "malformed candidate rejected" (not(LoopPeel.accepted broken));
  check "invalid candidate falls back exactly" (LoopPeel.transf_function broken=broken);
  let oversized={f with RTL.fn_code=tree(List.init 600(fun i->i+1,RTL.Inop(p 1)))} in
  check "large graph is retained byte-for-byte" (LoopPeel.transf_function oversized=oversized);
  let invalid={tf with RTL.fn_code=PTree.remove tf.RTL.fn_entrypoint tf.RTL.fn_code} in
  check "missing entry rejected by production checker" (not(Experimental.check_function f invalid Experimental.project));
  let invalid={tf with RTL.fn_sig=signature []} in
  check "signature corruption rejected by production checker" (not(Experimental.check_function f invalid Experimental.project));
  Printf.printf "{\"success\":true,\"checks\":[%s]}\n" (String.concat "," (List.map(Printf.sprintf "%S")(List.rev !passed)))
