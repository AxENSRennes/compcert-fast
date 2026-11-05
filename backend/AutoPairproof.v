(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Positive-step simulation of automatically paired scalar iterations.
    The target retains each memory operation and signed predicate in order.
    A cached high lane is justified by the source's preceding lookahead load. *)
Require Import Coqlib Maps AST Linking Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Experimental MemoryNeon MemoryNeonproof.
Require Import AutoPair AutoPairCounter AutoPairMemory AutoPairCodeFacts AutoPairStepFacts AutoPairPack.
Require Import PointerNeonFacts.

Lemma addl_zero_four: forall v,
  Val.addl (Val.addl v (Vlong Int64.zero)) (Vlong(Int64.repr 4)) =
  Val.addl v (Vlong(Int64.repr 4)).
Proof. intros;rewrite Val.addl_assoc;reflexivity. Qed.
Lemma addl_four_zero: forall v,
  Val.addl (Val.addl v (Vlong(Int64.repr 4))) (Vlong Int64.zero) =
  Val.addl v (Vlong(Int64.repr 4)).
Proof. intros;rewrite Val.addl_assoc;reflexivity. Qed.
Lemma source_successor_bound:
  forall p pc i next,
  (source_code p)!pc=Some i -> In next(successors_instr i) -> Ple next 9%positive.
Proof.
  intros p pc i next GET IN.
  assert(CHECK:forallb(fun kv=>forallb(fun n=>Pos.leb n 9%positive)
    (successors_instr(snd kv)))(PTree.elements(source_code p))=true)by reflexivity.
  apply forallb_forall with(x:=(pc,i))in CHECK.
  2: eapply PTree.elements_correct;exact GET.
  simpl in CHECK. apply forallb_forall with(x:=next)in CHECK;auto.
  apply Pos.leb_le;exact CHECK.
Qed.
Definition advanced_pc(pc:node):node :=
  if peq pc 2%positive then 32%positive else second_pc pc.
Definition second_header_map(pc:node):node :=
  if peq pc 1%positive then 1%positive else second_pc pc.

Inductive local_match(p:plan):node->regset->mem->node->regset->Prop :=
 | local_entry: forall rs trs m (REGS:regs_match6 rs trs),
     local_match p 10%positive rs m 10%positive trs
 | local_boundary: forall rs trs m (REGS:regs_match6 rs trs),
     local_match p 9%positive rs m 20%positive trs
 | local_scalar: forall pc rs trs m (PC:Ple pc 9%positive) (REGS:regs_match6 rs trs),
     local_match p pc rs m pc trs
 | local_first_pre: forall pc rs trs m (PC:pc=8%positive \/ pc=7%positive)
     (REGS:regs_match6 rs trs),
     local_match p pc rs m (first_pc pc) trs
 | local_first_guard: forall rs trs m (REGS:regs_match6 rs trs)
     (READ:Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong(Int64.repr 4)))=Some rs#(3%positive)),
     local_match p 6%positive rs m 71%positive trs
 | local_first_work: forall pc rs trs m (PC:pc=5%positive \/ pc=4%positive \/ pc=3%positive)
     (REGS:regs_match6 rs trs)
     (LOW:Val.loword trs#(9%positive)=Val.add rs#(4%positive)(Vint(increment p)))
     (HIGH:Val.hiword trs#(9%positive)=Val.add rs#(3%positive)(Vint(increment p)))
     (READ:Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong(Int64.repr 4)))=Some rs#(3%positive)),
     local_match p pc rs m (first_pc pc) trs
 | local_between: forall pc rs trs m (PC:pc=2%positive \/ pc=9%positive \/ pc=8%positive)
     (REGS:regs_match6 rs trs)
     (HIGH:Val.hiword trs#(9%positive)=Val.add rs#(3%positive)(Vint(increment p)))
     (READ:Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong Int64.zero))=Some rs#(3%positive)),
     local_match p pc rs m (advanced_pc pc) trs
 | local_second: forall pc rs trs m
     (PC:pc=7%positive \/ pc=6%positive \/ pc=5%positive \/ pc=4%positive \/ pc=3%positive \/ pc=2%positive)
     (REGS:regs_match6 rs trs)
     (HIGH:Val.hiword trs#(9%positive)=Val.add rs#(4%positive)(Vint(increment p))),
     local_match p pc rs m (second_pc pc) trs.

Lemma transfer_10: forall ge p sp rs m,
  transfer ge(source_template p)sp 10%positive rs m=Some(9%positive,rs,m).
Proof. reflexivity. Qed.
Lemma transfer_9: forall ge p sp rs m,
  transfer ge(source_template p)sp 9%positive rs m=
  match eval_condition(Ccompuimm Cne Int.zero)(rs#(1%positive)::nil)m with
  | Some b=>Some((if b then 8%positive else 1%positive),rs,m)|None=>None end.
Proof. reflexivity. Qed.
Lemma transfer_8: forall ge p sp rs m,
  transfer ge(source_template p)sp 8%positive rs m=
  match Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong Int64.zero)) with
  | Some v=>Some(7%positive,rs#(4%positive)<-v,m)|None=>None end.
Proof. reflexivity. Qed.
Lemma transfer_7: forall ge p sp rs m,
  transfer ge(source_template p)sp 7%positive rs m=
  match Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong(Int64.repr 4))) with
  | Some v=>Some(6%positive,rs#(3%positive)<-v,m)|None=>None end.
Proof. reflexivity. Qed.
Lemma transfer_6: forall ge p sp rs m,
  transfer ge(source_template p)sp 6%positive rs m=
  match eval_condition(Ccomp Clt)(rs#(4%positive)::rs#(3%positive)::nil)m with
  | Some b=>Some((if b then 5%positive else 3%positive),rs,m)|None=>None end.
Proof. reflexivity. Qed.
Lemma transfer_5: forall ge p sp rs m,
  transfer ge(source_template p)sp 5%positive rs m=
  Some(4%positive,rs#(6%positive)<-(Val.add rs#(4%positive)(Vint(increment p))),m).
Proof. reflexivity. Qed.
Lemma transfer_4: forall ge p sp rs m,
  transfer ge(source_template p)sp 4%positive rs m=
  match Mem.storev Mint32 m (Val.addl rs#(2%positive)(Vlong Int64.zero))rs#(6%positive) with
  | Some m'=>Some(3%positive,rs,m')|None=>None end.
Proof. reflexivity. Qed.
Lemma transfer_3: forall ge p sp rs m,
  transfer ge(source_template p)sp 3%positive rs m=
  Some(2%positive,rs#(2%positive)<-(Val.addl rs#(2%positive)(Vlong(Int64.repr 4))),m).
Proof. reflexivity. Qed.
Lemma transfer_2: forall ge p sp rs m,
  transfer ge(source_template p)sp 2%positive rs m=
  Some(9%positive,rs#(1%positive)<-(Val.add rs#(1%positive)(Vint(Int.repr(-1)))),m).
Proof. reflexivity. Qed.

Lemma source_transfer_successor:
  forall ge p sp pc rs m next rs' m' i,
  (source_code p)!pc=Some i ->
  transfer ge(source_template p)sp pc rs m=Some(next,rs',m') ->
  In next(successors_instr i).
Proof.
  intros ge p sp pc rs m next rs' m' i CODE RUN.
  assert(SUP:MemoryNeonBounds.supported i=true)by(eapply source_supported;eauto).
  unfold transfer in RUN. change((fn_code(source_template p))!pc=Some i)in CODE.
  rewrite CODE in RUN.
  destruct i as[n|op args dst n|chunk addr args dst n|chunk addr args src n|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret];
    cbn[MemoryNeonBounds.supported]in SUP;try discriminate.
  - injection RUN as A B C;subst next;simpl;auto.
  - destruct(eval_operation ge sp op rs##args m);try discriminate.
    injection RUN as A B C;subst next;simpl;auto.
  - destruct(eval_addressing ge sp addr rs##args);try discriminate.
    destruct(Mem.loadv chunk m v);try discriminate.
    injection RUN as A B C;subst next;simpl;auto.
  - destruct(eval_addressing ge sp addr rs##args);try discriminate.
    destruct(Mem.storev chunk m v rs#src);try discriminate.
    injection RUN as A B C;subst next;simpl;auto.
  - destruct(eval_condition cond rs##args m)as[b|];try discriminate.
    injection RUN as A B C;subst next;simpl;destruct b;auto.
Qed.

Lemma map_successors_identity: forall i, map_successors(fun x=>x)i=i.
Proof. destruct i;simpl;auto;f_equal;apply map_id. Qed.

Section LOCAL.
Variables ge tge: genv.
Hypothesis SYMBOLS: forall id,Genv.find_symbol tge id=Genv.find_symbol ge id.

Ltac clone_at from to rho instr :=
  match goal with
  | RUN:transfer ge(source_template ?p)?sp ?pc ?rs ?m=Some(?next,?rs',?m'),
    REGS:regs_match6 ?rs ?trs |- _ =>
    let SC:=fresh "SC" in let TC:=fresh "TC" in
    assert(SC:(source_code p)!from=Some instr)by reflexivity;
    assert(TC:(target_code p)!to=Some(map_successors rho instr))by reflexivity;
    destruct(clone_transfer ge tge SYMBOLS p sp from to rho rs trs m next rs' m' instr SC TC RUN REGS)
      as[trnext[TRANSFER[REGNEXT FRESH]]]
  end.
Ltac single_target trnext TRANSFER :=
  eexists;exists trnext;split;
  [apply plus_one;eapply MemoryNeonproof.transfer_sound;exact TRANSFER|].
Ltac rewrite_sets := repeat rewrite Regmap.gss;repeat rewrite Regmap.gso by discriminate.

Lemma local_transfer:
  forall p sp pc rs m tpc trs next rs' m',
  local_match p pc rs m tpc trs ->
  transfer ge(source_template p)sp pc rs m=Some(next,rs',m') ->
  forall stk,
  exists tnext trs',
    plus RTL.step tge(State stk(target_template p)sp tpc trs m)E0
      (State stk(target_template p)sp tnext trs' m') /\
    local_match p next rs' m' tnext trs'.
Proof.
  intros p sp pc rs m tpc trs next rs' m' LOCAL RUN stk.
  inversion LOCAL;subst;clear LOCAL.
  - clone_at 10%positive 10%positive (fun _:node=>20%positive) (Inop 9%positive).
    rewrite transfer_10 in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
    single_target trnext TRANSFER. constructor;exact REGNEXT.
  - rewrite transfer_9 in RUN.
    destruct(eval_condition(Ccompuimm Cne Int.zero)(rs#(1%positive)::nil)m)as[b|]eqn:COND;try discriminate.
    injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
    destruct(counter_condition_defined _ _ _ _ _ COND)as[n N].
    assert(TN:trs#(1%positive)=Vint n)by(rewrite REGS by(unfold Ple;simpl;lia);exact N).
    assert(DCOND:eval_condition(Ccompuimm Cge(Int.repr 2))(trs#(1%positive)::nil)m=Some(pair_guard n)).
    { rewrite TN;reflexivity. }
    destruct(pair_guard n)eqn:PAIR.
    + destruct(pair_guard_nonzero n PAIR)as[NZ _].
      rewrite N in COND. change(Some(negb(Int.eq n Int.zero))=Some b)in COND.
      rewrite Int.eq_false in COND by exact NZ. inv COND.
      exists 38%positive,trs;split.
      * apply plus_one;eapply exec_Icond;[reflexivity|exact DCOND|reflexivity].
      * constructor;auto.
    + assert(DSTEP:RTL.step tge(State stk(target_template p)sp 20%positive trs m)E0
        (State stk(target_template p)sp 9%positive trs m)).
      { eapply exec_Icond;[reflexivity|exact DCOND|reflexivity]. }
      assert(SC:(source_code p)!9%positive=Some(Icond(Ccompuimm Cne Int.zero)(1%positive::nil)8%positive 1%positive))by reflexivity.
      assert(TC:(target_code p)!9%positive=Some(map_successors(fun x=>x)(Icond(Ccompuimm Cne Int.zero)(1%positive::nil)8%positive 1%positive)))by reflexivity.
      assert(SRUN:transfer ge(source_template p)sp 9%positive rs m=Some((if b then 8%positive else 1%positive),rs,m)).
      { rewrite transfer_9,COND;reflexivity. }
      destruct(clone_transfer ge tge SYMBOLS p sp 9%positive 9%positive (fun x=>x) rs trs m
        (if b then 8%positive else 1%positive) rs m _ SC TC SRUN REGS)
        as[trnext[TRANSFER[REGNEXT FRESH]]].
      eexists;exists trnext;split.
      * eapply plus_two;[exact DSTEP|eapply MemoryNeonproof.transfer_sound;exact TRANSFER|reflexivity].
      * apply local_scalar;auto. destruct b;unfold Ple;simpl;lia.
  - rename tpc into pc.
    assert(SC:exists i,(source_code p)!pc=Some i).
    { unfold transfer in RUN. destruct(fn_code(source_template p))!pc as[i|]eqn:GET;try discriminate;eauto. }
    destruct SC as[i SC].
    assert(TC:(target_code p)!pc=Some(map_successors(fun x=>x)i)).
    { rewrite (map_successors_identity i).
      eapply target_original_lookup;eauto;unfold Ple in PC;extlia. }
    destruct(clone_transfer ge tge SYMBOLS p sp pc pc (fun x=>x) rs trs m next rs' m' i SC TC RUN REGS)
      as[trnext[TRANSFER[REGNEXT FRESH]]].
    single_target trnext TRANSFER. apply local_scalar;auto.
    eapply source_successor_bound;[exact SC|].
    eapply source_transfer_successor;eauto.
  - destruct PC as[E|E];subst pc.
    + clone_at 8%positive 38%positive first_pc
        (Iload Mint32(Aindexed Int64.zero)(2%positive::nil)4%positive 7%positive).
      rewrite transfer_8 in RUN.
      destruct(Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong Int64.zero)))as[v|]eqn:LOAD;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. constructor;auto.
    + clone_at 7%positive 37%positive first_pc
        (Iload Mint32(Aindexed(Int64.repr 4))(2%positive::nil)3%positive 6%positive).
      rewrite transfer_7 in RUN.
      destruct(Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong(Int64.repr 4))))as[v|]eqn:LOAD;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_first_guard;auto.
      rewrite_sets;exact LOAD.
  - rewrite transfer_6 in RUN.
    destruct(eval_condition(Ccomp Clt)(rs#(4%positive)::rs#(3%positive)::nil)m)as[b|]eqn:COND;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
    destruct(signed_condition_defined _ _ _ _ _ COND)as[lo[hi[LO HI]]].
    assert(TLO:trs#(4%positive)=Vint lo)by(rewrite REGS by(unfold Ple;simpl;lia);exact LO).
    assert(THI:trs#(3%positive)=Vint hi)by(rewrite REGS by(unfold Ple;simpl;lia);exact HI).
    rewrite LO,HI in COND.
    destruct(run_pack tge p sp stk trs m lo hi b TLO THI COND)as[trnext[PLUS[ORIG[LOW HIGH]]]].
    eexists;exists trnext;split;[exact PLUS|].
    assert(MAP:first_pc(if b then 5%positive else 3%positive)=(if b then 35%positive else 33%positive))by(destruct b;reflexivity).
    rewrite <-MAP. apply local_first_work;auto.
    + destruct b;auto.
    + red;intros r B;rewrite ORIG by exact B;apply REGS;exact B.
    + rewrite LO;exact LOW.
    + rewrite HI;exact HIGH.
  - destruct PC as[E|[E|E]];subst pc.
    + rewrite transfer_5 in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      set(trnext:=trs#(6%positive)<-(Val.add rs#(4%positive)(Vint(increment p)))).
      assert(TRANSFER:transfer tge(target_template p)sp 35%positive trs m=
        Some(34%positive,trnext,m)).
      { change(Some(34%positive,trs#(6%positive)<-(Val.loword trs#(9%positive)),m)=Some(34%positive,trnext,m)).
        rewrite LOW;reflexivity. }
      single_target trnext TRANSFER. apply local_first_work;auto using regs_match6_set.
      * unfold trnext;apply regs_match6_set;exact REGS.
      * unfold trnext;rewrite_sets;exact LOW.
      * unfold trnext;rewrite_sets;exact HIGH.
      * rewrite_sets;exact READ.
    + clone_at 4%positive 34%positive first_pc
        (Istore Mint32(Aindexed Int64.zero)(2%positive::nil)6%positive 3%positive).
      rewrite transfer_4 in RUN.
      destruct(Mem.storev Mint32 m (Val.addl rs#(2%positive)(Vlong Int64.zero))rs#(6%positive))as[mm|]eqn:STORE;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_first_work;auto.
      * rewrite FRESH by(unfold Plt;simpl;lia);exact LOW.
      * rewrite FRESH by(unfold Plt;simpl;lia);exact HIGH.
      * pose proof(load32_after_store32_addl _ _ _ _ STORE)as EQ.
        rewrite !addl_zero_four in EQ. rewrite EQ;exact READ.
    + clone_at 3%positive 33%positive first_pc
        (Iop(Oaddlimm(Int64.repr 4))(2%positive::nil)2%positive 2%positive).
      rewrite transfer_3 in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_between;auto.
      * rewrite FRESH by(unfold Plt;simpl;lia);rewrite_sets;exact HIGH.
      * rewrite_sets;rewrite addl_four_zero;exact READ.
  - destruct PC as[E|[E|E]];subst pc.
    + clone_at 2%positive 32%positive (fun _:node=>49%positive)
        (Iop(Oaddimm(Int.repr(-1)))(1%positive::nil)1%positive 9%positive).
      rewrite transfer_2 in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_between;auto.
      * rewrite FRESH by(unfold Plt;simpl;lia);rewrite_sets;exact HIGH.
      * rewrite_sets;exact READ.
    + clone_at 9%positive 49%positive second_header_map
        (Icond(Ccompuimm Cne Int.zero)(1%positive::nil)8%positive 1%positive).
      rewrite transfer_9 in RUN.
      destruct(eval_condition(Ccompuimm Cne Int.zero)(rs#(1%positive)::nil)m)as[b|]eqn:COND;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      destruct b.
      * single_target trnext TRANSFER. apply local_between;auto.
        -- rewrite FRESH by(unfold Plt;simpl;lia);exact HIGH.
      * single_target trnext TRANSFER. change(local_match p 1%positive rs m 1%positive trnext).
        apply local_scalar;auto. unfold Ple;simpl;lia.
    + clone_at 8%positive 48%positive second_pc
        (Iload Mint32(Aindexed Int64.zero)(2%positive::nil)4%positive 7%positive).
      rewrite transfer_8,READ in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_second;try tauto;auto.
      * rewrite FRESH by(unfold Plt;simpl;lia);rewrite_sets;exact HIGH.
  - destruct PC as[E|[E|[E|[E|[E|E]]]]];subst pc.
    + clone_at 7%positive 47%positive second_pc
        (Iload Mint32(Aindexed(Int64.repr 4))(2%positive::nil)3%positive 6%positive).
      rewrite transfer_7 in RUN.
      destruct(Mem.loadv Mint32 m (Val.addl rs#(2%positive)(Vlong(Int64.repr 4))))as[v|]eqn:LOAD;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_second;try tauto;auto.
      * rewrite FRESH by(unfold Plt;simpl;lia);rewrite_sets;exact HIGH.
    + clone_at 6%positive 46%positive second_pc
        (Icond(Ccomp Clt)(4%positive::3%positive::nil)5%positive 3%positive).
      rewrite transfer_6 in RUN.
      destruct(eval_condition(Ccomp Clt)(rs#(4%positive)::rs#(3%positive)::nil)m)as[b|]eqn:COND;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_second;try tauto;auto.
      * destruct b;tauto.
      * rewrite FRESH by(unfold Plt;simpl;lia);exact HIGH.
    + rewrite transfer_5 in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      set(trnext:=trs#(6%positive)<-(Val.add rs#(4%positive)(Vint(increment p)))).
      assert(TRANSFER:transfer tge(target_template p)sp 45%positive trs m=
        Some(44%positive,trnext,m)).
      { change(Some(44%positive,trs#(6%positive)<-(Val.hiword trs#(9%positive)),m)=Some(44%positive,trnext,m)).
        rewrite HIGH;reflexivity. }
      single_target trnext TRANSFER. apply local_second;auto using regs_match6_set.
      * unfold trnext;apply regs_match6_set;exact REGS.
      * unfold trnext;rewrite_sets;exact HIGH.
    + clone_at 4%positive 44%positive second_pc
        (Istore Mint32(Aindexed Int64.zero)(2%positive::nil)6%positive 3%positive).
      rewrite transfer_4 in RUN.
      destruct(Mem.storev Mint32 m (Val.addl rs#(2%positive)(Vlong Int64.zero))rs#(6%positive))as[mm|]eqn:STORE;try discriminate;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_second;try tauto;auto.
      * rewrite FRESH by(unfold Plt;simpl;lia);exact HIGH.
    + clone_at 3%positive 43%positive second_pc
        (Iop(Oaddlimm(Int64.repr 4))(2%positive::nil)2%positive 2%positive).
      rewrite transfer_3 in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. apply local_second;try tauto;auto.
      * rewrite FRESH by(unfold Plt;simpl;lia);rewrite_sets;exact HIGH.
    + clone_at 2%positive 42%positive (fun _:node=>20%positive)
        (Iop(Oaddimm(Int.repr(-1)))(1%positive::nil)1%positive 9%positive).
      rewrite transfer_2 in RUN;injection RUN as NEXT0 RS0 MEM0; subst next rs' m'.
      single_target trnext TRANSFER. constructor;exact REGNEXT.
Qed.
End LOCAL.
