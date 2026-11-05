(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Copied scalar instructions preserve original registers and cached lanes. *)
Require Import Coqlib Maps AST Integers Values Memory Events Globalenvs.
Require Import Op Registers RTL Experimental MemoryNeon AutoPair AutoPairCodeFacts.

Definition regs_match6 (rs trs:regset): Prop :=
  forall r, Ple r 6%positive -> trs#r=rs#r.

Lemma regs_match6_refl: forall rs, regs_match6 rs rs.
Proof. red;auto. Qed.

Lemma regs_match6_list:
  forall rs trs args,
  regs_match6 rs trs -> (forall r, In r args -> Ple r 6%positive) ->
  trs##args=rs##args.
Proof. intros;apply list_map_exten;intros;symmetry;auto. Qed.

Lemma regs_match6_set:
  forall rs trs r v,
  regs_match6 rs trs -> regs_match6 (rs#r<-v) (trs#r<-v).
Proof.
  red;intros. rewrite !Regmap.gsspec. destruct(peq r0 r);auto.
Qed.

Lemma regs_match6_fresh:
  forall rs trs r v,
  regs_match6 rs trs -> Plt 6%positive r -> regs_match6 rs (trs#r<-v).
Proof. red;intros. rewrite Regmap.gso by extlia. auto. Qed.

Lemma source_uses_bound:
  forall p pc i r,
  (source_code p)!pc=Some i -> In r(instr_uses i) -> Ple r 6%positive.
Proof.
  intros. rewrite <-(source_max_reg p). eapply max_reg_function_use;eauto.
Qed.

Lemma source_defs_bound:
  forall p pc i r,
  (source_code p)!pc=Some i -> instr_defs i=Some r -> Ple r 6%positive.
Proof.
  intros. rewrite <-(source_max_reg p). eapply max_reg_function_def;eauto.
Qed.

Lemma clone_transfer:
  forall ge tge,
  (forall id,Genv.find_symbol tge id=Genv.find_symbol ge id) ->
  forall p sp pc tpc rho rs trs m next rs' m' i,
  (source_code p)!pc=Some i ->
  (target_code p)!tpc=Some(map_successors rho i) ->
  MemoryNeon.transfer ge (source_template p) sp pc rs m=Some(next,rs',m') ->
  regs_match6 rs trs ->
  exists trs',
    MemoryNeon.transfer tge (target_template p) sp tpc trs m=Some(rho next,trs',m') /\
    regs_match6 rs' trs' /\
    (forall r,Plt 6%positive r -> trs'#r=trs#r).
Proof.
  intros ge tge SYMBOLS p sp pc tpc rho rs trs m next rs' m' i CODE TARGET RUN REGS.
  assert(SUPPORT:MemoryNeonBounds.supported i=true)by(eapply source_supported;eauto).
  assert(USES:forall r,In r(instr_uses i)->Ple r 6%positive)by(eauto using source_uses_bound).
  assert(DEFS:forall r,instr_defs i=Some r->Ple r 6%positive)by(eauto using source_defs_bound).
  unfold MemoryNeon.transfer in *.
  change ((fn_code(source_template p))!pc=Some i) in CODE.
  change ((fn_code(target_template p))!tpc=Some(map_successors rho i)) in TARGET.
  rewrite CODE in RUN. rewrite TARGET.
  destruct i as[n|op args dst n|chunk addr args dst n|chunk addr args src n|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret];
    cbn [MemoryNeonBounds.supported map_successors] in SUPPORT,RUN |- *;try discriminate.
  - injection RUN as NEXT RS MEM; subst next rs' m'. exists trs;repeat split;auto.
  - destruct(eval_operation ge sp op rs##args m)as[v|]eqn:EV;try discriminate.
    injection RUN as NEXT RS MEM; subst next rs' m'.
    assert(ARGS:trs##args=rs##args)by(eapply regs_match6_list;eauto).
    rewrite ARGS.
    assert(OP:eval_operation tge sp op rs##args m=Some v).
    { rewrite <-EV. apply eval_operation_preserved;exact SYMBOLS. }
    rewrite OP. exists(trs#dst<-v);split;[reflexivity|].
    split;auto using regs_match6_set.
    intros r GT. rewrite Regmap.gso by (specialize(DEFS dst eq_refl);extlia). reflexivity.
  - destruct(eval_addressing ge sp addr rs##args)as[a|]eqn:ADDRESS;try discriminate.
    destruct(Mem.loadv chunk m a)as[v|]eqn:LOAD;try discriminate. injection RUN as NEXT RS MEM; subst next rs' m'.
    assert(ARGS:trs##args=rs##args)by(eapply regs_match6_list;eauto).
    rewrite ARGS.
    assert(AD:eval_addressing tge sp addr rs##args=Some a).
    { rewrite <-ADDRESS. apply eval_addressing_preserved;exact SYMBOLS. }
    rewrite AD,LOAD. exists(trs#dst<-v);split;[reflexivity|].
    split;auto using regs_match6_set.
    intros r GT. rewrite Regmap.gso by (specialize(DEFS dst eq_refl);extlia). reflexivity.
  - destruct(eval_addressing ge sp addr rs##args)as[a|]eqn:ADDRESS;try discriminate.
    destruct(Mem.storev chunk m a rs#src)as[m2|]eqn:STORE;try discriminate. injection RUN as NEXT RS MEM; subst next rs' m'.
    assert(ARGS:trs##args=rs##args).
    { eapply regs_match6_list;eauto. intros;eapply USES;simpl;auto. }
    rewrite ARGS.
    assert(AD:eval_addressing tge sp addr rs##args=Some a).
    { rewrite <-ADDRESS. apply eval_addressing_preserved;exact SYMBOLS. }
    rewrite AD. rewrite REGS by(apply USES;simpl;auto). rewrite STORE.
    exists trs;repeat split;auto.
  - destruct(eval_condition cond rs##args m)as[b|]eqn:COND;try discriminate. injection RUN as NEXT RS MEM; subst next rs' m'.
    assert(ARGS:trs##args=rs##args)by(eapply regs_match6_list;eauto).
    rewrite ARGS,COND. exists trs;split;[destruct b;reflexivity|]. split;auto.
Qed.
