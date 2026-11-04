(* Native differential checks of production total-operation LICM.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Op
let p=Camlcoq.P.of_int
let int n=Int.repr(Camlcoq.Z.of_sint n)
let long n=Int64.repr(Camlcoq.Z.of_sint n)
let passed=ref []
let cases=ref 0
let check name b=if not b then failwith name else passed:=name::!passed
let tree xs=List.fold_left(fun m(k,v)->PTree.set(p k)v m)PTree.empty xs
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let fixture op args : RTL.coq_function=
 {fn_sig={sig_args=[Xint;Xany64;Xany64;Xany64];sig_res=Xany64;sig_cc=cc_default};
  fn_params=List.map p [1;2;3;4];fn_stacksize=Camlcoq.Z.of_sint 32;fn_entrypoint=p 1;
  fn_code=tree[1,RTL.Iop(Ointconst(int 7),[],p 5,p 2);
   2,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 3,p 6);
   3,RTL.Iop(op,args,p 5,p 4);
   4,RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 2);
   6,RTL.Ireturn(Some(p 5))]}
let execute f selected values=
 let ge=Globalenvs.Genv.globalenv(program f) in
 let sp=Values.Vptr(p 77,Ptrofs.zero) in
 let rec run fuel pc rs count=
  if fuel=0 then failwith "LICM fixture fuel exhausted";
  match PTree.get pc f.RTL.fn_code with
  | Some(RTL.Inop s)->run(fuel-1)s rs count
  | Some(RTL.Iop(op,args,dst,s))->
   let count=if (op,args)=selected then count+1 else count in
   begin match Op.eval_operation ge sp op(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   | None->None,count
   | Some v->run(fuel-1)s(PMap.set dst v rs)count end
  | Some(RTL.Icond(c,args,yes,no))->
   begin match Op.eval_condition c(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   | None->None,count
   | Some b->run(fuel-1)(if b then yes else no)rs count end
  | Some(RTL.Ireturn(Some r))->Some(PMap.get r rs),count
  | _->failwith "unsupported LICM fixture instruction" in
 run 10000 f.RTL.fn_entrypoint(RTL.init_regs values f.RTL.fn_params)0
let edge_values=[Values.Vundef;Values.Vint(int 0);Values.Vint(int 1);Values.Vint(int(-1));
 Values.Vint(int 2147483647);Values.Vlong(long 0);Values.Vlong(long(-1));
 Values.Vfloat Floats.Float.zero;Values.Vfloat (Floats.Float.of_int (int 1));
 Values.Vfloat Floats.default_nan_64;Values.Vsingle Floats.Float32.zero;
 Values.Vsingle Floats.default_nan_32;Values.Vptr(p 9,Ptrofs.zero)]
let operations=["mul32",Omul,[p 2;p 3];"add32",Oadd,[p 2;p 3];
 "sub32",Osub,[p 2;p 3];"xor32",Oxor,[p 2;p 3];"and32",Oand,[p 2;p 3];
 "shift32",Oshl,[p 2;p 3];"mul64",Omull,[p 2;p 3];"add64",Oaddl,[p 2;p 3];
 "shift64",Oshrlu,[p 2;p 3];"float-add",Oaddf,[p 2;p 3];"float-div",Odivf,[p 2;p 3];
 "single-mul",Omulfs,[p 2;p 3];"neg32",Oneg,[p 2];"negfloat",Onegf,[p 2];
 "signed-compare",Ocmp(Ccomp Clt),[p 2;p 3];"symbol-address",Oaddrsymbol(p 1,Ptrofs.zero),[];
 "stack-address",Oaddrstack(Ptrofs.repr(Camlcoq.Z.of_sint 8)),[];
 "multiply-add",Omuladd,[p 2;p 3;p 4]]
let ()=
 List.iter(fun(name,op,args)->
  let f=fixture op args in let tf=LICM.transf_function f in
  check(name^": a nonconstant loop operation is selected")
   (match LICM.chosen f with Some b->b.LICM.invariant_op=op && b.LICM.invariant_args=args|None->false);
  check(name^": fresh entry added")
   (tf.RTL.fn_entrypoint=LICM.fresh_node f && List.length(PTree.elements tf.RTL.fn_code)=6);
  check(name^": actual entry computation")
   (PTree.get tf.RTL.fn_entrypoint tf.RTL.fn_code=
    Some(RTL.Iop(op,args,LICM.fresh_reg f,f.RTL.fn_entrypoint)));
  check(name^": original loop computation becomes a move")
   (PTree.get(p 3)tf.RTL.fn_code=Some(RTL.Iop(Omove,[LICM.fresh_reg f],p 5,p 4)));
  List.iteri(fun i x->List.iteri(fun j y->List.iter(fun n->
   incr cases;
   let values=[Values.Vint(int n);x;y;Values.Vint(int 3)] in
   let before,old_count=execute f(op,args)values in
   let after,new_count=execute tf(op,args)values in
   check(Printf.sprintf "%s values%d/%d trip%d" name i j n)(before=after);
   check(Printf.sprintf "%s counts%d/%d trip%d" name i j n)(old_count=max 0 n && new_count=1))
   [-1;0;1;2;7])edge_values)edge_values)operations;
 List.iter(fun(name,op,args)->
  let f=fixture op args in
  check(name^": unsafe candidate rejected") (LICM.chosen f=None);
  check(name^": exact fallback") (LICM.transf_function f=f);
  let a=execute f(op,args)[Values.Vint(int 0);Values.Vundef;Values.Vundef;Values.Vundef] in
  let b=execute(LICM.transf_function f)(op,args)[Values.Vint(int 0);Values.Vundef;Values.Vundef;Values.Vundef] in
  check(name^": zero-trip fault stays unexecuted")(a=b))
 ["signed-division",Odiv,[p 2;p 3];"unsigned-division",Odivu,[p 2;p 3];
  "long-division",Odivl,[p 2;p 3];"float-to-int",Ointoffloat,[p 2];
  "rounded-shift",Oshrximm(int 1),[p 2];"wrong-arity",Omul,[p 2];
  "pointer-sensitive-compare",Ocmp(Ccomplu Ceq),[p 2;p 3];
  "literal",Ointconst(int 42),[]];
 let f=fixture Omul[p 2;p 3] in
 let mutable_input={f with RTL.fn_code=PTree.set(p 99)(RTL.Iop(Ointconst(int 0),[],p 2,p 6))f.RTL.fn_code} in
 check "an operand definition even in unreachable code rejects motion"(LICM.chosen mutable_input=None);
 let acyclic={f with RTL.fn_code=tree[1,RTL.Iop(Omul,[p 2;p 3],p 5,p 6);6,RTL.Ireturn(Some(p 5))]} in
 check "acyclic operations are retained"(LICM.transf_function acyclic=acyclic);
 let oversized={f with RTL.fn_code=List.fold_left(fun m n->PTree.set(p(n+100))(RTL.Inop(p 6))m)f.RTL.fn_code(List.init 600(fun x->x))} in
 check "large functions are retained exactly"(LICM.chosen oversized=None && LICM.transf_function oversized=oversized);
 let prog=LICM.transf_program(program f) in
 check "whole-program wrapper transforms actual function"
  (match List.assoc(p 1)prog.prog_defs with Gfun(Internal tf)->tf=LICM.transf_function f|_->false);
 Printf.printf "{\"success\":true,\"execution_cases\":%d,\"checks\":[%s]}\n" !cases
 (String.concat ","(List.map(Printf.sprintf "%S")(List.rev !passed)))
