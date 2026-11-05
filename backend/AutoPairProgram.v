(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Whole-program composition of the positive-step scalar/pair simulation. *)
Require Import Coqlib Maps AST Linking Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Experimental MemoryNeon MemoryNeonproof.
Require Import AutoPair AutoPairCodeFacts AutoPairStepFacts AutoPairproof.

Lemma source_return_pc:
  forall p pc,
  (source_code p)!pc=Some(Ireturn None) -> pc=1%positive.
Proof.
  intros p pc CODE.
  assert(CHECK:forallb(fun item=>match snd item with
      | Ireturn _=>if peq(fst item)1%positive then true else false
      | _=>true end)(PTree.elements(source_code p))=true)by reflexivity.
  rewrite forallb_forall in CHECK.
  specialize(CHECK(pc,Ireturn None)(PTree.elements_correct _ _ CODE));simpl in CHECK.
  destruct(peq pc 1%positive);congruence.
Qed.

Lemma local_return:
  forall p pc rs m tpc trs,
  local_match p pc rs m tpc trs ->
  (source_code p)!pc=Some(Ireturn None) ->
  tpc=1%positive /\ regs_match6 rs trs.
Proof.
  intros p pc rs m tpc trs LOCAL RETURN.
  apply source_return_pc in RETURN;subst pc.
  inversion LOCAL;subst;try congruence;intuition congruence.
Qed.

Definition match_prog(p tp:program) :=
  match_program(fun ctx f tf=>tf=AutoPair.transf_fundef f)eq p tp.
Global Instance TransfAutoPairLink: TransfLink match_prog := TransfTotalLink AutoPair.transf_function.
Lemma transf_program_match:
  forall p, match_prog p(AutoPair.transf_program p).
Proof. intros;apply match_transform_program. Qed.

Section PRESERVATION.
Variables prog tprog:program.
Hypothesis TRANSL:match_prog prog tprog.
Let ge:=Genv.globalenv prog.
Let tge:=Genv.globalenv tprog.

Lemma functions_translated:forall v fd,
  Genv.find_funct ge v=Some fd ->Genv.find_funct tge v=Some(AutoPair.transf_fundef fd).
Proof. exact(Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated:forall v fd,
  Genv.find_funct_ptr ge v=Some fd ->Genv.find_funct_ptr tge v=Some(AutoPair.transf_fundef fd).
Proof. exact(Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved:forall id,Genv.find_symbol tge id=Genv.find_symbol ge id.
Proof. exact(Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved:Senv.equiv ge tge.
Proof. exact(Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved:forall fd,funsig(AutoPair.transf_fundef fd)=funsig fd.
Proof. destruct fd;simpl;auto;apply(proj1(AutoPairCodeFacts.metadata_preserved f)). Qed.
Lemma find_function_translated:forall ros rs fd,
  find_function ge ros rs=Some fd ->find_function tge ros rs=Some(AutoPair.transf_fundef fd).
Proof.
  intros;unfold find_function in *;destruct ros.
  eapply functions_translated;eauto.
  rewrite symbols_preserved;destruct(Genv.find_symbol ge i);try discriminate.
  eapply function_ptr_translated;eauto.
Qed.

Inductive match_frames:RTL.stackframe->RTL.stackframe->Prop :=
 | match_frame:forall res f sp pc rs (SELECT:AutoPair.selected f=None),
   match_frames(Stackframe res f sp pc rs)(Stackframe res f sp pc rs).
Inductive match_states:RTL.state->RTL.state->Prop :=
 | match_normal:forall stk stk' f sp pc rs m
     (STACKS:list_forall2 match_frames stk stk')(SELECT:AutoPair.selected f=None),
   match_states(State stk f sp pc rs m)(State stk' f sp pc rs m)
 | match_selected:forall stk stk' f sp pc rs m tpc trs p
     (STACKS:list_forall2 match_frames stk stk')(SELECT:AutoPair.selected f=Some p)
     (LOCAL:local_match p pc rs m tpc trs),
   match_states(State stk f sp pc rs m)
     (State stk'(AutoPair.transf_function f)sp tpc trs m)
 | match_call:forall stk stk' fd args m(STACKS:list_forall2 match_frames stk stk'),
   match_states(Callstate stk fd args m)(Callstate stk'(AutoPair.transf_fundef fd)args m)
 | match_return:forall stk stk' v m(STACKS:list_forall2 match_frames stk stk'),
   match_states(Returnstate stk v m)(Returnstate stk' v m).

Lemma selected_step:
  forall stk f sp pc rs m trace after,
  RTL.step ge(State stk f sp pc rs m)trace after ->
  forall stk' tpc trs p,
  list_forall2 match_frames stk stk' ->AutoPair.selected f=Some p ->
  local_match p pc rs m tpc trs ->
  exists target,
    plus RTL.step tge(State stk'(AutoPair.transf_function f)sp tpc trs m)trace target /\
    match_states after target.
Proof.
  intros stk f sp pc rs m trace after STEP stk' tpc trs p STACKS SELECT LOCAL.
  assert(FEQ:f=source_template p)by(eapply AutoPairCodeFacts.selected_sound;eauto).
  assert(TFEQ:AutoPair.transf_function f=target_template p).
  { unfold AutoPair.transf_function;rewrite SELECT;reflexivity. }
  assert(CODE:exists i,(fn_code f)!pc=Some i)by(inv STEP;eauto).
  destruct CODE as[i CODE].
  assert(SUPPORT:MemoryNeonBounds.supported i=true).
  { apply (AutoPairCodeFacts.source_supported p pc i). rewrite FEQ in CODE; exact CODE. }
  destruct(MemoryNeonproof.supported_step _ _ _ _ _ _ _ _ _ _ CODE SUPPORT STEP)as
    [[next[rs'[m'[TRACE[AFTER[TRANSFER SUCC]]]]]]|[block[final[SP[TRACE[AFTER[RETURN FREE]]]]]]].
  - subst trace after. rewrite FEQ in TRANSFER.
    destruct(AutoPairproof.local_transfer ge tge symbols_preserved p sp pc rs m tpc trs next rs' m'
      LOCAL TRANSFER stk')as[tnext[trs'[PLUS MATCH]]].
    exists(State stk'(AutoPair.transf_function f)sp tnext trs' m');split.
    + rewrite TFEQ;exact PLUS.
    + econstructor;eauto.
  - subst sp trace after i.
    assert(RETPC:tpc=1%positive).
    { assert(RCODE:(source_code p)!pc=Some(Ireturn None)).
      { rewrite FEQ in CODE;exact CODE. }
      exact(proj1(local_return p pc rs m tpc trs LOCAL RCODE)). }
    exists(Returnstate stk' Vundef final);split.
    + apply plus_one;eapply exec_Ireturn with(or:=None).
      * rewrite TFEQ,RETPC;reflexivity.
      * rewrite(proj1(proj2(proj2(AutoPairCodeFacts.metadata_preserved f))));exact FREE.
    + constructor;auto.
Qed.

Lemma normal_step:
  forall stk f sp pc rs m trace after,
  RTL.step ge(State stk f sp pc rs m)trace after ->
  forall stk',list_forall2 match_frames stk stk' ->AutoPair.selected f=None ->
  exists target,plus RTL.step tge(State stk' f sp pc rs m)trace target /\ match_states after target.
Proof.
  intros stk f sp pc rs m trace after STEP stk' STACKS SELECT.
  inversion STEP;subst.
  - econstructor;split. apply plus_one;eapply exec_Inop;eauto. constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Iop;eauto.
    match goal with EV:eval_operation ge _ _ _ _=Some _|-_=>rewrite <-EV end.
    apply eval_operation_preserved;exact symbols_preserved.
    constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Iload;eauto.
    match goal with EV:eval_addressing ge _ _ _=Some _|-_=>rewrite <-EV end.
    apply eval_addressing_preserved;exact symbols_preserved.
    constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Istore;eauto.
    match goal with EV:eval_addressing ge _ _ _=Some _|-_=>rewrite <-EV end.
    apply eval_addressing_preserved;exact symbols_preserved.
    constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Icall with(fd:=AutoPair.transf_fundef fd);eauto.
    eapply find_function_translated;eauto. rewrite sig_preserved;auto.
    constructor;constructor;auto. constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Itailcall with(fd:=AutoPair.transf_fundef fd);eauto.
    eapply find_function_translated;eauto. rewrite sig_preserved;auto.
    constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Ibuiltin;eauto.
    eapply eval_builtin_args_preserved with(ge1:=ge);eauto;exact symbols_preserved.
    eapply external_call_symbols_preserved;eauto;apply senv_preserved.
    constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Icond;eauto. constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Ijumptable;eauto. constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Ireturn;eauto. constructor;auto.
Qed.

Lemma step_simulation:
  forall source trace after,RTL.step ge source trace after ->
  forall target,match_states source target ->
  exists target_after,plus RTL.step tge target trace target_after /\match_states after target_after.
Proof.
  intros source trace after STEP target MATCH;inv MATCH.
  - eapply normal_step;eauto.
  - eapply selected_step;eauto.
  - inversion STEP;subst.
    + destruct(AutoPairCodeFacts.metadata_preserved f)as[SIG[PARAM[STACK ENTRY]]].
      exists(State stk'(AutoPair.transf_function f)(Vptr stk0 Ptrofs.zero)
        (fn_entrypoint(AutoPair.transf_function f))(init_regs args(fn_params f))m');split.
      * apply plus_one. rewrite <-PARAM.
        eapply exec_function_internal;rewrite ?SIG,?STACK;eauto.
      * destruct(AutoPair.selected f)as[p|]eqn:SELECT.
        -- eapply match_selected with(p:=p);eauto.
           rewrite ENTRY. rewrite(AutoPairCodeFacts.selected_sound _ _ SELECT);simpl.
           constructor;apply regs_match6_refl.
        -- unfold AutoPair.transf_function;rewrite SELECT;constructor;auto.
    + econstructor;split. apply plus_one;eapply exec_function_external;eauto.
      eapply external_call_symbols_preserved;eauto;apply senv_preserved.
      constructor;auto.
  - inversion STEP;subst. inv STACKS. inv H1.
    econstructor;split. apply plus_one;eapply exec_return;eauto. constructor;auto.
Qed.

Lemma transf_initial_states:
  forall source,RTL.initial_state prog source ->
  exists target,RTL.initial_state tprog target /\match_states source target.
Proof.
  intros;inv H. exists(Callstate nil(AutoPair.transf_fundef f)nil m0);split.
  - econstructor.
    + eapply(Genv.init_mem_transf TRANSL);eauto.
    + rewrite symbols_preserved.
      exact(eq_trans(f_equal(Genv.find_symbol ge)(match_program_main TRANSL))H1).
    + eapply function_ptr_translated;eauto.
    + rewrite <-H3;apply sig_preserved.
  - constructor;constructor.
Qed.
Lemma transf_final_states:
  forall source target result,
  match_states source target ->RTL.final_state source result ->RTL.final_state target result.
Proof. intros;inv H0;inv H;inv STACKS;constructor. Qed.

Theorem transf_program_correct:
  forward_simulation(RTL.semantics prog)(RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved. exact transf_initial_states. exact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.
