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
  {fn_sig=signature [Xint]; fn_params=[p 1]; fn_stacksize=Z0; fn_entrypoint=p 1;
   fn_code=tree [1,RTL.Iop(Ointconst (int 0),[],p 2,p 2);
                 2,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 3,p 5);
                 3,RTL.Iop(Oaddimm (int 7),[p 2],p 2,p 4);
                 4,RTL.Iop(Oaddimm (int (-1)),[p 1],p 1,p 2);
                 5,RTL.Ireturn(Some(p 2))]}

let check_unroll four =
  let name = if four then "four phases" else "two phases" in
  let f=loop () in
  let tf=Experimental.transf_function four f in
  check (name^": candidate accepted") (Experimental.accepted four f);
  check (name^": actual CFG growth") (nodes tf = (if four then 4 else 2) * nodes f);
  List.iter (fun n -> check (Printf.sprintf "%s: execution at bound %d" name n)
    (execute f n = execute tf n)) [-1;0;1;2;3;4;5;7;8;15;16;17;100];
  let rho=Experimental.project_for four in
  let reject label candidate = check (name^": reject "^label)
    (not (Experimental.check_function f candidate rho)) in
  reject "changed stack" {tf with RTL.fn_stacksize=Camlcoq.Z.of_sint 8};
  reject "changed parameters" {tf with RTL.fn_params=[]};
  reject "wrong entry" {tf with RTL.fn_entrypoint=p 9999};
  reject "missing entry instruction" {tf with RTL.fn_code=PTree.remove tf.RTL.fn_entrypoint tf.RTL.fn_code};
  let changed=PTree.map1 (function
    | RTL.Iop (Oaddimm _,args,dst,next) -> RTL.Iop(Osub,args,dst,next)
    | i -> i) tf.RTL.fn_code in
  reject "changed arithmetic" {tf with RTL.fn_code=changed};
  let broken={f with RTL.fn_code=tree [1,RTL.Inop(p 999)]} in
  check (name^": malformed source candidate refused") (not (Experimental.accepted four broken));
  check (name^": refusal falls back byte-for-byte") (Experimental.transf_function four broken = broken);
  let self={f with RTL.fn_code=tree [1,RTL.Iop(Oaddimm(int 1),[p 1],p 1,p 1)]} in
  let copy=Experimental.transf_function four self in
  let rec walk n pc seen =
    if n=0 then seen else match PTree.get pc copy.RTL.fn_code with
    | Some(RTL.Iop(_,_,_,next)) -> walk (n-1) next (pc::seen)
    | _ -> failwith "missing phase instruction" in
  let visited=List.sort_uniq compare (walk 8 copy.RTL.fn_entrypoint []) in
  check (name^": self-loop visits each phase") (List.length visited = if four then 4 else 2)

let check_memory_cleanup () =
  let f : RTL.coq_function =
    {fn_sig=signature [Xptr]; fn_params=[p 1]; fn_stacksize=Z0; fn_entrypoint=p 1;
     fn_code=tree [1,RTL.Iload(Mint32,Aindexed Int64.zero,[p 1],p 2,p 2);
                   2,RTL.Iload(Mint32,Aindexed Int64.zero,[p 1],p 3,p 3);
                   3,RTL.Iop(Oadd,[p 2;p 3],p 4,p 4);4,RTL.Ireturn(Some(p 4))]} in
  let tf=function_after(require_ok(ExtraCleanup.transf_program(program f))) in
  check "cleanup actually forwards a redundant ordinary load" (count load f=2 && count load tf=1);
  let g=p 2 in
  let f={f with RTL.fn_params=[p 1;p 2;p 3]; fn_sig=signature [Xptr;Xint;Xint];
    fn_code=tree [1,RTL.Istore(Mint32,Aglobal(g,Ptrofs.zero),[],p 2,p 2);
                  2,RTL.Istore(Mint32,Aglobal(g,Ptrofs.zero),[],p 3,p 3);
                  3,RTL.Ireturn(Some(p 3))]} in
  let variable={gvar_info=();gvar_init=[Init_int32 Int.zero];gvar_readonly=false;gvar_volatile=false} in
  let prog=program f in
  let prog={prog with prog_defs=prog.prog_defs@[g,Gvar variable];prog_public=[p 1;g]} in
  let tf=function_after(require_ok(ExtraCleanup.transf_program prog)) in
  check "cleanup actually removes an overwritten global store" (count store f=2 && count store tf=1)

let () =
  check_unroll false; check_unroll true; check_memory_cleanup ();
  Printf.printf "{\"success\":true,\"checks\":[%s]}\n"
    (String.concat "," (List.map (Printf.sprintf "%S") (List.rev !passed)))
