(* Differential checks of the production packing/extraction lowering.
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
let fixture op args dst : RTL.coq_function={
 fn_sig={sig_args=[Xany64;Xany64;Xint];sig_res=Xany64;sig_cc=cc_default};
 fn_params=[p 1;p 2;p 3];fn_stacksize=Z0;fn_entrypoint=p 1;
 fn_code=tree[1,RTL.Iop(op,args,dst,p 2);2,RTL.Ireturn(Some dst)]}
let execute f values=
 let ge=Globalenvs.Genv.globalenv(program f) in
 let rec step fuel pc rs=
  if fuel=0 then failwith "lowering fixture exhausted fuel";
  match PTree.get pc f.RTL.fn_code with
  |Some(RTL.Inop next)->step(fuel-1)next rs
  |Some(RTL.Iop(op,args,dst,next))->
   begin match Op.eval_operation ge Values.Vundef op(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   |Some v->step(fuel-1)next(PMap.set dst v rs)
   |None->None end
  |Some(RTL.Icond(c,args,yes,no))->
   begin match Op.eval_condition c(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   |Some take->step(fuel-1)(if take then yes else no)rs
   |None->None end
  |Some(RTL.Ireturn(Some r))->Some(PMap.get r rs)
  |_ ->failwith "unsupported lowering fixture instruction"
 in step 10000 f.RTL.fn_entrypoint(RTL.init_regs values f.RTL.fn_params)
let supported=function RTL.Iop((Omakelong|Ohighlong),_,_,_)->false|_->true
let nodes f=List.length(PTree.elements f.RTL.fn_code)
let suffixes f=List.fold_left(fun n(_,i)->match i with
 | RTL.Iop(Omakelong,[_;_],_,_) | RTL.Iop(Ohighlong,[_],_,_)->n+1
 | _->n)0(PTree.elements f.RTL.fn_code)
let differential f input=
 let tf=LowerLong.transf_function f in
 if nodes tf<>nodes f+suffixes f then failwith "dummy suffix nodes reintroduced";
 incr cases;
 if execute f input<>execute tf input then failwith(Printf.sprintf"lowering differential %d"!cases);
 if not(List.for_all(fun(_,i)->supported i)(PTree.elements tf.RTL.fn_code)) then failwith"unlowered operation retained"
let values=[Values.Vundef;Values.Vint(int 0);Values.Vint(int 1);Values.Vint(int(-1));
 Values.Vint(int 2147483647);Values.Vint(int(-2147483648));Values.Vint(int 2309737967);
 Values.Vlong(long 0);Values.Vlong(long(-1));Values.Vlong(Int64.ofwords(int 2309737967)(int 4275878552));
 Values.Vfloat Floats.Float.zero;Values.Vfloat Floats.default_nan_64;
 Values.Vsingle Floats.Float32.zero;Values.Vsingle Floats.default_nan_32;
 Values.Vptr(p 9,Ptrofs.zero)]
let ()=
 let f=fixture Omakelong[p 1;p 2](p 4) in
 let tf=LowerLong.transf_function f in
 check "packing is lowered into an existing unsigned extension"
  (PTree.get(LowerLong.base(p 1))tf.RTL.fn_code=
   Some(RTL.Iop(Oextend(Xuns32,LowerLong.amount_32),[p 1],LowerLong.fresh_reg f,LowerLong.after(p 1))));
 check "packing suffix adds the extended low word"
  (PTree.get(LowerLong.after(p 1))tf.RTL.fn_code=
   Some(RTL.Iop(Oaddlext(Xuns32,LowerLong.amount_zero),[LowerLong.fresh_reg f;p 2],p 4,LowerLong.base(p 2))));
 check "entry and source successor labels map consistently"
  (tf.RTL.fn_entrypoint=LowerLong.base f.RTL.fn_entrypoint);
 check "packing creates exactly one required suffix node"(nodes tf=nodes f+1);
 let ordinary=fixture Oadd[p 1;p 2](p 4) in
 let ordinary_tf=LowerLong.transf_function ordinary in
 check "ordinary functions retain their original node count"(nodes ordinary_tf=nodes ordinary);
 check "ordinary operations have no artificial suffix predecessor"
  (PTree.get(LowerLong.after(p 1))ordinary_tf.RTL.fn_code=None &&
   Schedule.predecessor_check ordinary_tf (LowerLong.base(p 1)) (LowerLong.base(p 2)));
 let sg={sig_args=[];sig_res=Xint;sig_cc=cc_default} in
 let caller={ordinary with RTL.fn_code=tree[
  1,RTL.Icall(sg,Datatypes.Coq_inr(p 99),[],p 4,p 2);
  2,RTL.Iop(Oaddimm(int 1),[p 4],p 4,p 3);
  3,RTL.Ireturn(Some(p 4))]} in
 let caller_tf=LowerLong.transf_function caller in
 check "ordinary calls do not acquire ghost predecessor edges"
  (nodes caller_tf=nodes caller &&
   Schedule.predecessor_check caller_tf (LowerLong.base(p 1)) (LowerLong.base(p 2)));
 check "source metadata retained"
  (tf.RTL.fn_sig=f.RTL.fn_sig&&tf.RTL.fn_params=f.RTL.fn_params&&tf.RTL.fn_stacksize=f.RTL.fn_stacksize);
 List.iter(fun dst->let f=fixture Omakelong[p 1;p 2](p dst) in
  List.iter(fun hi->List.iter(fun lo->differential f[hi;lo;Values.Vint(int 0)])values)values)
  [1;2;4];
 check "all value tags and packing destination aliases preserve results"true;
 List.iter(fun dst->let f=fixture Omakelong[p 1;p 1](p dst) in
  List.iter(fun v->differential f[v;Values.Vundef;Values.Vint(int 0)])values)[1;4];
 check "broadcast packing covers identical source registers and destination aliases"true;
 List.iter(fun dst->let f=fixture Ohighlong[p 1](p dst) in
  List.iter(fun v->differential f[v;Values.Vundef;Values.Vint(int 0)])values)[1;4];
 check "all value tags and extraction destination aliases preserve results"true;
 let rng=Random.State.make[|0x5041434b;0x48494748|] in
 let word ()=int((Random.State.bits rng lsl 2) lor (Random.State.bits rng land 3)) in
 for _=1 to 4096 do
  let hi=word() and lo=word() in
  List.iter(fun dst->differential(fixture Omakelong[p 1;p 2](p dst))
    [Values.Vint hi;Values.Vint lo;Values.Vint(int 0)])[1;2;4];
  List.iter(fun dst->differential(fixture Ohighlong[p 1](p dst))
    [Values.Vlong(Int64.ofwords hi lo);Values.Vundef;Values.Vint(int 0)])[1;4]
 done;
 check "random full-width words preserve packing and high extraction"true;
 List.iter(fun(op,args)->
  let f=fixture op args(p 4) in
  check "malformed source packing/extraction has no defined operation"
   (execute f[Values.Vint(int 1);Values.Vint(int 2);Values.Vint(int 3)]=None);
  check "malformed operations are eliminated despite source undefinedness"
   (List.for_all(fun(_,i)->supported i)(PTree.elements(LowerLong.transf_function f).RTL.fn_code));
  let dead={f with RTL.fn_entrypoint=p 7;
    fn_code=PTree.set(p 7)(RTL.Iop(Ointconst(int 42),[],p 4,p 2))f.RTL.fn_code} in
  differential dead[Values.Vundef;Values.Vundef;Values.Vint(int 0)])
  [Omakelong,[];Omakelong,[p 1];Omakelong,[p 1;p 2;p 3];Ohighlong,[];Ohighlong,[p 1;p 2]];
 let loop={f with RTL.fn_code=tree[
  1,RTL.Icond(Ccompimm(Cgt,int 0),[p 3],p 2,p 6);
  2,RTL.Iop(Omakelong,[p 1;p 2],p 4,p 3);
  3,RTL.Iop(Ohighlong,[p 4],p 1,p 4);
  4,RTL.Iop(Oaddimm(int(-1)),[p 3],p 3,p 1);
  6,RTL.Ireturn(Some(p 1))]} in
 List.iter(fun n->List.iter(fun hi->List.iter(fun lo->differential loop[hi;lo;Values.Vint(int n)])values)values)[0;1;2;7];
 check "cyclic packing/extraction safely reuse the fresh temporary"true;
 List.iter(fun op->List.iter(fun a->List.iter(fun b->differential(fixture op[p 1;p 2](p 4))[a;b;Values.Vint(int 0)])values)values)
  [Oadd;Oxor;Omul;Oaddl;Omull];
 check "ordinary operations retain their original semantics"true;
 let transformed=LowerLong.transf_program(program f) in
 check "production whole-program wrapper transforms the function"
  (match List.assoc(p 1)transformed.prog_defs with Gfun(Internal actual)->actual=tf|_->false);
 Printf.printf"{\"success\":true,\"differential_cases\":%d,\"checks\":[%s]}\n"!cases
  (String.concat","(List.map(Printf.sprintf"%S")(List.rev!passed)))
