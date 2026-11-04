(* Native tests of the production extracted modular induction transformation.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Op
let p=Camlcoq.P.of_int
let int n=Int.repr(Camlcoq.Z.of_sint n)
let passed=ref []
let executions=ref 0
let check name test=if not test then failwith name else passed:=name::!passed
let tree entries=List.fold_left(fun code(pc,i)->PTree.set(p pc)i code)PTree.empty entries
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let ind=p 1 and factor=p 2 and count=p 3 and sum=p 4 and product=p 5
let loop step:RTL.coq_function={
 fn_sig={sig_args=[Xint;Xint;Xint];sig_res=Xint;sig_cc=cc_default};
 fn_params=[ind;factor;count];fn_stacksize=Z0;fn_entrypoint=p 1;
 fn_code=tree[
  1,RTL.Iop(Ointconst(int 0),[],sum,p 2);
  2,RTL.Icond(Ccompimm(Cgt,int 0),[count],p 3,p 8);
  3,RTL.Iop(Omul,[ind;factor],product,p 4);
  4,RTL.Iop(Oadd,[sum;product],sum,p 5);
  5,RTL.Iop(Oaddimm(int step),[ind],ind,p 6);
  6,RTL.Iop(Oaddimm(int(-1)),[count],count,p 2);
  8,RTL.Ireturn(Some sum)]}
let execute f values=
 let ge=Globalenvs.Genv.globalenv(program f) in
 let rec step fuel pc rs mults=
  if fuel=0 then failwith "strength-reduction fixture exhausted fuel";
  match PTree.get pc f.RTL.fn_code with
  |Some(RTL.Inop next)->step(fuel-1)next rs mults
  |Some(RTL.Iop(op,args,dst,next))->
   let mults=if op=Omul then mults+1 else mults in
   begin match Op.eval_operation ge Values.Vundef op
    (List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   |Some v->step(fuel-1)next(PMap.set dst v rs)mults
   |None->None,mults end
  |Some(RTL.Icond(cond,args,yes,no))->
   begin match Op.eval_condition cond(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   |Some take->step(fuel-1)(if take then yes else no)rs mults
   |None->None,mults end
  |Some(RTL.Ireturn(Some r))->Some(PMap.get r rs),mults
  |_ ->failwith "unsupported strength-reduction fixture instruction"
 in step 100000 f.RTL.fn_entrypoint(RTL.init_regs values f.RTL.fn_params)0
let differential f inputs=
 let tf=StrengthReduce.transf_function f in
 let a=execute f inputs and b=execute tf inputs in
 incr executions;
 if fst a<>fst b then failwith(Printf.sprintf"differential case %d"!executions);
 a,b
let assert_rejected name f=
 check(name^": candidate rejected")(StrengthReduce.chosen f=None);
 check(name^": original function retained")(StrengthReduce.transf_function f=f)
let ()=
 let f=loop 7 in
 let c=match StrengthReduce.chosen f with Some c->c|None->failwith"no induction selected" in
 check "actual induction and multiplier selected"
  (c.StrengthReduce.induction_reg=ind&&c.StrengthReduce.factor_reg=factor&&c.StrengthReduce.induction_step=int 7);
 let tf=StrengthReduce.transf_function f in
 check "transformation actually changes the function"(tf<>f);
 check "source metadata preserved"(tf.RTL.fn_sig=f.RTL.fn_sig&&tf.RTL.fn_params=f.RTL.fn_params&&tf.RTL.fn_stacksize=f.RTL.fn_stacksize);
 check "loop multiply is replaced by accumulator move"
  (PTree.get(StrengthReduce.base(p 3))tf.RTL.fn_code=
   Some(RTL.Iop(Omove,[StrengthReduce.fresh_acc f],product,StrengthReduce.base(p 4))));
 check "induction step is followed by an accumulator addition"
  (PTree.get(StrengthReduce.after1(p 5))tf.RTL.fn_code=
   Some(RTL.Iop(Oadd,[StrengthReduce.fresh_acc f;StrengthReduce.fresh_delta f],StrengthReduce.fresh_acc f,StrengthReduce.base(p 6))));
 let edges=[0;1;2;17;(-1);2147483647;(-2147483648);4294967295] in
 List.iter(fun step->let f=loop step in
  check(Printf.sprintf"step %d has a checked recurrence"step)(StrengthReduce.chosen f<>None);
  List.iter(fun start->List.iter(fun k->List.iter(fun n->
   let (_,oldmults),(_,newmults)=differential f[Values.Vint(int start);Values.Vint(int k);Values.Vint(int n)] in
   if oldmults<>max 0 n||newmults<>2 then failwith"loop multiply count did not become constant")
   [-1;0;1;2;3;7;31])edges)edges)
  [0;1;(-1);7;2147483647;(-2147483648)];
 check "wrapping and signed-edge executions preserve exact outputs"(!executions=2688);
 let values=[Values.Vundef;Values.Vptr(p 42,Ptrofs.zero);Values.Vlong(Int64.repr(Camlcoq.Z.of_sint 17));Values.Vint(int 9)] in
 List.iter(fun x->List.iter(fun k->List.iter(fun n->ignore(differential f[x;k;Values.Vint(int n)]))[0;1;4])values)values;
 check "noninteger and undefined inputs retain their source behavior"true;
 let returns_product={f with RTL.fn_params=[ind;factor;count;product];
  fn_sig={f.RTL.fn_sig with sig_args=[Xint;Xint;Xint;Xint]};
  fn_code=PTree.set(p 8)(RTL.Ireturn(Some product))f.RTL.fn_code} in
 List.iter(fun v->let a,b=differential returns_product[Values.Vundef;Values.Vundef;Values.Vint(int 0);v] in
  check "zero-trip retains original multiply destination"(fst a=Some v&&fst b=Some v))values;
 let reset={f with RTL.fn_entrypoint=p 9;
  fn_code=PTree.set(p 9)(RTL.Iop(Ointconst(int 17),[],factor,p 10))
   (PTree.set(p 10)(RTL.Iop(Ointconst(int 2147483647),[],ind,p 1))f.RTL.fn_code)} in
 check "literal initialization of factor and induction is accepted"(StrengthReduce.chosen reset<>None);
 List.iter(fun n->ignore(differential reset[Values.Vundef;Values.Vundef;Values.Vint(int n)]))[0;1;2;17];
 let factor_reset={f with RTL.fn_code=PTree.set(p 4)(RTL.Iop(Ointconst(int(-3)),[],factor,p 9))
  (PTree.set(p 9)(RTL.Iop(Oadd,[sum;product],sum,p 5))f.RTL.fn_code)} in
 check "literal factor resets are tracked rather than silently ignored"(StrengthReduce.chosen factor_reset<>None);
 List.iter(fun n->ignore(differential factor_reset[Values.Vint(int 2147483647);Values.Vint(int 17);Values.Vint(int n)]))[0;1;2;7;31];
 let ind_reset={f with RTL.fn_code=PTree.set(p 4)(RTL.Iop(Ointconst(int(-1)),[],ind,p 9))
  (PTree.set(p 9)(RTL.Iop(Oadd,[sum;product],sum,p 5))f.RTL.fn_code)} in
 check "literal induction resets are tracked"(StrengthReduce.chosen ind_reset<>None);
 List.iter(fun n->ignore(differential ind_reset[Values.Vint(int 9);Values.Vint(int 17);Values.Vint(int n)]))[0;1;7;31];
 assert_rejected "nonlinear induction update"
  {f with RTL.fn_code=PTree.set(p 5)(RTL.Iop(Oadd,[ind;factor],ind,p 6))f.RTL.fn_code};
 assert_rejected "factor modified by unsupported arithmetic"
  {f with RTL.fn_code=PTree.set(p 4)(RTL.Iop(Oaddimm(int 1),[factor],factor,p 5))f.RTL.fn_code};
 assert_rejected "incompatible induction steps even on an unreachable node"
  {f with RTL.fn_code=PTree.set(p 99)(RTL.Iop(Oaddimm(int 8),[ind],ind,p 8))f.RTL.fn_code};
 assert_rejected "load overwrites the induction"
  {f with RTL.fn_code=PTree.set(p 99)(RTL.Iload(Mint32,Aindexed Int64.zero,[factor],ind,p 8))f.RTL.fn_code};
 assert_rejected "builtin overwrites the factor"
  {f with RTL.fn_code=PTree.set(p 99)(RTL.Ibuiltin(EF_annot_val(p 1,"test",Tint),[BA ind],BR factor,p 8))f.RTL.fn_code};
 assert_rejected "multiply overwrites its own induction"
  {f with RTL.fn_code=PTree.set(p 3)(RTL.Iop(Omul,[ind;factor],ind,p 4))f.RTL.fn_code};
 assert_rejected "64-bit multiplication outside current integer32 certificate"
  {f with RTL.fn_code=PTree.set(p 3)(RTL.Iop(Omull,[ind;factor],product,p 4))f.RTL.fn_code};
 let large=List.init 600(fun n->n+100,RTL.Inop(p 8)) in
 assert_rejected "oversized function"
  {f with RTL.fn_code=List.fold_left(fun code(pc,i)->PTree.set(p pc)i code)f.RTL.fn_code large};
 let transformed=StrengthReduce.transf_program(program f) in
 check "production whole-program wrapper transforms internal function"
  (match List.assoc(p 1)transformed.prog_defs with Gfun(Internal actual)->actual=tf|_->false);
 Printf.printf"{\"success\":true,\"differential_cases\":%d,\"checks\":[%s]}\n"!executions
  (String.concat","(List.map(Printf.sprintf"%S")(List.rev!passed)))
