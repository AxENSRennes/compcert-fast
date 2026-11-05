(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Maps AST Linking Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Builtins0 Builtins1 Builtins MemoryLaneFacts MemoryNeon.

Lemma code_equal: forall a b:code,
  PTree.beq (fun i j=>if Experimental.instruction_eq i j then true else false) a b=true ->a=b.
Proof.
  intros a b E. apply PTree.extensionality;intro x.
  rewrite PTree.beq_correct in E;specialize(E x).
  destruct a!x as[i|],b!x as[j|];auto;try contradiction.
  destruct(Experimental.instruction_eq i j);congruence.
Qed.

Lemma selected_sound:
  forall f p, selected f=Some p -> f=source_template p.
Proof.
  intros f p. unfold selected.
  destruct(fn_code f)!22%positive as[i|]eqn:A;try discriminate.
  destruct i;try discriminate. destruct o;try discriminate.
  destruct(fn_code f)!13%positive as[i|]eqn:B;try discriminate.
  destruct i;try discriminate. destruct o;try discriminate.
  destruct(fn_code f)!5%positive as[i|]eqn:C;try discriminate.
  destruct i;try discriminate. destruct o;try discriminate.
  destruct(signature_eq(fn_sig f)void_sig);try discriminate.
  destruct(list_eq_dec peq(fn_params f)nil);try discriminate.
  destruct(zeq(fn_stacksize f)0);try discriminate.
  destruct(peq(fn_entrypoint f)22%positive);try discriminate.
  destruct(PTree.beq _ (fn_code f) _)eqn:CODE;try discriminate.
  intro EQ;inv EQ.
  apply code_equal in CODE.
  destruct f;simpl in *;subst;reflexivity.
Qed.
Lemma metadata_preserved: forall f,
  fn_sig(transf_function f)=fn_sig f /\ fn_params(transf_function f)=fn_params f /\
  fn_stacksize(transf_function f)=fn_stacksize f.
Proof.
  intros f. unfold transf_function. destruct(selected f)eqn:SEL;auto.
  apply selected_sound in SEL;subst;repeat split;reflexivity.
Qed.
Lemma packed_builtin_correct: forall ge a b m,
  external_call packed_builtin ge (a::b::nil)m E0(packed_eval a b)m.
Proof.
  intros. change(known_builtin_sem(BI_platform BI_neon_add_u32x2)ge
    (a::b::nil)m E0(packed_eval a b)m).
  constructor. destruct a,b;reflexivity.
Qed.
Lemma transfer_sound:
  forall ge f sp pc rs m next rs' m',
  transfer ge f sp pc rs m=Some(next,rs',m') ->
  forall stk, RTL.step ge(State stk f sp pc rs m)E0(State stk f sp next rs' m').
Proof.
  intros ge f sp pc rs m next rs' m' H stk. unfold transfer in H.
  destruct(fn_code f)!pc as[i|]eqn:CODE;try discriminate.
  destruct i as[n|op args dst n|chunk addr args dst n|chunk addr args src n|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret];try discriminate.
  - inv H;eapply exec_Inop;eauto.
  - destruct(eval_operation ge sp op rs##args m)eqn:E;try discriminate.
    inv H;eapply exec_Iop;eauto.
  - destruct(eval_addressing ge sp addr rs##args)eqn:A;try discriminate.
    destruct(Mem.loadv chunk m v)eqn:L;try discriminate.
    inv H;eapply exec_Iload;eauto.
  - destruct(eval_addressing ge sp addr rs##args)eqn:A;try discriminate.
    destruct(Mem.storev chunk m v rs#src)eqn:S;try discriminate.
    inv H;eapply exec_Istore;eauto.
  - destruct args as[|a tail];cbn in H;try discriminate.
    destruct a;cbn in H;try discriminate.
    destruct tail as[|b tail];cbn in H;try discriminate.
    destruct b;cbn in H;try discriminate.
    destruct tail;cbn in H;try discriminate.
    destruct res;cbn in H;try discriminate.
    destruct(external_function_eq ef packed_builtin)as[EQ|NE];try discriminate.
    subst ef. inv H. eapply exec_Ibuiltin with(res:=BR x1)(vres:=packed_eval rs#x rs#x0)(vargs:=rs#x::rs#x0::nil).
    exact CODE.
    unfold eval_builtin_args;constructor;[constructor|constructor;[constructor|constructor]].
    apply packed_builtin_correct.
  - destruct(eval_condition cond rs##args m)eqn:E;try discriminate.
    inv H;eapply exec_Icond;eauto.
Qed.

Lemma execute_transfer:
  forall ge f sp pc rs m next rs' m' fuel,
  transfer ge f sp pc rs m=Some(next,rs',m') ->
  execute ge f sp (S fuel) pc rs m=execute ge f sp fuel next rs' m'.
Proof.
  intros. cbn [execute].
  assert(NR: forall r,(fn_code f)!pc<>Some(Ireturn r)).
  { intros r EQ. unfold transfer in H;rewrite EQ in H;discriminate. }
  destruct(fn_code f)!pc as[i|]eqn:CODE.
  - destruct i;try rewrite H;try reflexivity. exfalso;eapply NR;eauto.
  - unfold transfer in H;rewrite CODE in H;discriminate.
Qed.
Lemma transfer_preserved:
  forall ge tge,
  (forall id,Genv.find_symbol tge id=Genv.find_symbol ge id) ->
  forall f sp pc rs m, transfer tge f sp pc rs m=transfer ge f sp pc rs m.
Proof.
  intros ge tge SYMBOLS f sp pc rs m. unfold transfer.
  destruct(fn_code f)!pc as[i|];auto. destruct i;auto.
  - erewrite eval_operation_preserved;eauto.
  - erewrite eval_addressing_preserved;eauto.
  - erewrite eval_addressing_preserved;eauto.
Qed.
Lemma execute_preserved:
  forall ge tge,
  (forall id,Genv.find_symbol tge id=Genv.find_symbol ge id) ->
  forall f sp fuel pc rs m, execute tge f sp fuel pc rs m=execute ge f sp fuel pc rs m.
Proof.
  intros ge tge SYMBOLS f sp fuel. induction fuel;intros;auto.
  cbn [execute]. rewrite(transfer_preserved _ _ SYMBOLS).
  destruct(fn_code f)!pc as[i|];try reflexivity.
  destruct i;try destruct o;try reflexivity;
    destruct(transfer ge f sp pc rs m)as[[[next trs]tm]|];auto.
  all: destruct(transfer ge f sp pc rs m)as[[[next trs]tm]|];auto.
Qed.
Lemma execute_sound:
  forall ge f sp fuel pc rs m final,
  execute ge f sp fuel pc rs m=Some final ->
  forall stk,exists last trs,
    star RTL.step ge(State stk f sp pc rs m)E0(State stk f sp last trs final) /\
    (fn_code f)!last=Some(Ireturn None).
Proof.
  intros ge f sp fuel. induction fuel as[|fuel IH];intros pc rs m final RUN stk;try discriminate.
  cbn [execute] in RUN.
  destruct(fn_code f)!pc as[i|]eqn:CODE;try discriminate.
  destruct i;try match goal with o:option reg|-_=>destruct o end;
    try solve[inv RUN;exists pc,rs;split;[apply star_refl|exact CODE]];
    destruct(transfer ge f sp pc rs m)as[[[next trs]tm]|]eqn:T;try discriminate;
    destruct(IH _ _ _ _ RUN stk)as[last[rr[STAR RET]]];
    exists last,rr;split;auto;eapply star_left;eauto using transfer_sound.
  unfold transfer in RUN;rewrite CODE in RUN;discriminate.
Qed.

Require Import MemoryNeonBounds.
Lemma supported_step:
  forall ge stk f sp pc rs m trace after i,
  (fn_code f)!pc=Some i -> supported i=true ->
  RTL.step ge(State stk f sp pc rs m)trace after ->
  (exists next trs tm, trace=E0 /\ after=State stk f sp next trs tm /\
     transfer ge f sp pc rs m=Some(next,trs,tm) /\ In next(successors_instr i)) \/
  (exists block final, sp=Vptr block Ptrofs.zero /\ trace=E0 /\
     after=Returnstate stk Vundef final /\ i=Ireturn None /\
     Mem.free m block 0(fn_stacksize f)=Some final).
Proof.
  intros ge stk f sp pc rs m trace after i CODE SUPPORT STEP.
  inversion STEP;subst;
    match goal with C:(fn_code f)!pc=Some _|-_=>rewrite CODE in C;inv C end;
    simpl in SUPPORT;try discriminate.
  - left;eexists;eexists;eexists;repeat split;eauto.
    unfold transfer;rewrite CODE;reflexivity. simpl;auto.
  - left;eexists;eexists;eexists;repeat split;eauto.
    unfold transfer;rewrite CODE.
    match goal with E:eval_operation _ _ _ _ _=Some _|-_=>rewrite E end;reflexivity. simpl;auto.
  - left;eexists;eexists;eexists;repeat split;eauto.
    unfold transfer;rewrite CODE.
    match goal with E:eval_addressing _ _ _ _=Some _|-_=>rewrite E end.
    match goal with E:Mem.loadv _ _ _=Some _|-_=>rewrite E end;reflexivity. simpl;auto.
  - left;eexists;eexists;eexists;repeat split;eauto.
    unfold transfer;rewrite CODE.
    match goal with E:eval_addressing _ _ _ _=Some _|-_=>rewrite E end.
    match goal with E:Mem.storev _ _ _ _=Some _|-_=>rewrite E end;reflexivity. simpl;auto.
  - left;eexists;eexists;eexists;repeat split;eauto.
    unfold transfer;rewrite CODE.
    match goal with E:eval_condition _ _ _=Some _|-_=>rewrite E end;reflexivity. simpl;destruct b;auto.
  - destruct or;try discriminate. right;eexists;eexists;repeat split;eauto.
Qed.

Lemma execute_return: forall ge f sp fuel pc rs m,
  (fn_code f)!pc=Some(Ireturn None) ->
  execute ge f sp(S fuel)pc rs m=Some m.
Proof. intros;cbn[execute];rewrite H;reflexivity. Qed.
Definition match_prog (p tp: program) :=
  match_program(fun ctx f tf=>tf=transf_fundef f)eq p tp.
Global Instance TransfMemoryNeonLink: TransfLink match_prog := TransfTotalLink transf_function.
Lemma transf_program_match: forall p,match_prog p(transf_program p).
Proof. intros;apply match_transform_program. Qed.

Section PRESERVATION.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Hypothesis REPLAY: forall ge p sp rs m final,
  execute ge(source_template p)sp 32 22%positive rs m=Some final ->
  execute ge(target_template p)sp 32 7%positive rs m=Some final.
Let ge:=Genv.globalenv prog.
Let tge:=Genv.globalenv tprog.
Lemma functions_translated: forall v fd,
  Genv.find_funct ge v=Some fd ->Genv.find_funct tge v=Some(transf_fundef fd).
Proof. exact(Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated: forall v fd,
  Genv.find_funct_ptr ge v=Some fd ->Genv.find_funct_ptr tge v=Some(transf_fundef fd).
Proof. exact(Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved: forall id,Genv.find_symbol tge id=Genv.find_symbol ge id.
Proof. exact(Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact(Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall fd,funsig(transf_fundef fd)=funsig fd.
Proof. destruct fd;simpl;auto. apply(proj1(metadata_preserved f)). Qed.
Lemma find_function_translated: forall ros rs fd,
  find_function ge ros rs=Some fd ->find_function tge ros rs=Some(transf_fundef fd).
Proof.
  intros;unfold find_function in *;destruct ros.
  eapply functions_translated;eauto.
  rewrite symbols_preserved;destruct(Genv.find_symbol ge i);try discriminate.
  eapply function_ptr_translated;eauto.
Qed.
Inductive match_frames: RTL.stackframe->RTL.stackframe->Prop :=
 | match_frame: forall res f sp pc rs (SELECT:selected f=None),
     match_frames(Stackframe res f sp pc rs)(Stackframe res f sp pc rs).
Inductive match_states: RTL.state->RTL.state->Prop :=
 | match_normal: forall stk stk' f sp pc rs m
     (STACKS:list_forall2 match_frames stk stk') (SELECT:selected f=None),
     match_states(State stk f sp pc rs m)(State stk' f sp pc rs m)
 | match_held: forall stk stk' f sp pc rs m initial_regs initial_mem fuel p
     (STACKS:list_forall2 match_frames stk stk') (SELECT:selected f=Some p)
     (BOUND:(Pos.to_nat pc<=fuel)%nat)
     (PREFIX:forall final,execute ge f sp fuel pc rs m=Some final ->
        execute ge f sp 32(fn_entrypoint f)initial_regs initial_mem=Some final),
     match_states(State stk f sp pc rs m)
       (State stk'(transf_function f)sp(fn_entrypoint(transf_function f))initial_regs initial_mem)
 | match_call: forall stk stk' fd args m (STACKS:list_forall2 match_frames stk stk'),
     match_states(Callstate stk fd args m)(Callstate stk'(transf_fundef fd)args m)
 | match_return: forall stk stk' v m (STACKS:list_forall2 match_frames stk stk'),
     match_states(Returnstate stk v m)(Returnstate stk' v m).
Definition measure(st:RTL.state):nat :=
  match st with State _ f _ pc _ _=>match selected f with Some _=>Pos.to_nat pc|None=>O end|_=>O end.

Lemma held_step:
  forall stk stk' f sp pc rs m initial_regs initial_mem fuel p trace after,
  list_forall2 match_frames stk stk' ->selected f=Some p ->(Pos.to_nat pc<=fuel)%nat ->
  (forall final,execute ge f sp fuel pc rs m=Some final ->
    execute ge f sp 32(fn_entrypoint f)initial_regs initial_mem=Some final) ->
  RTL.step ge(State stk f sp pc rs m)trace after ->
  (exists target,plus RTL.step tge
    (State stk'(transf_function f)sp(fn_entrypoint(transf_function f))initial_regs initial_mem)
    trace target /\match_states after target) \/
  (measure after<measure(State stk f sp pc rs m) /\trace=E0 /\
    match_states after(State stk'(transf_function f)sp(fn_entrypoint(transf_function f))initial_regs initial_mem))%nat.
Proof.
  intros stk stk' f sp pc rs m ir im fuel p trace after STACKS SELECT BOUND PREFIX STEP.
  destruct fuel as[|fuel].
  { generalize(Pos2Nat.is_pos pc);lia. }
  assert(CODE:exists i,(fn_code f)!pc=Some i)by(inv STEP;eauto).
  destruct CODE as[i CODE].
  assert(SUPPORT:supported i=true).
  { rewrite(selected_sound _ _ SELECT)in CODE;eapply source_supported;eauto. }
  destruct(supported_step _ _ _ _ _ _ _ _ _ _ CODE SUPPORT STEP)as
    [[next[trs[tm[TRACE[AFTER[TRANSFER SUCC]]]]]]|[block[final[SP[TRACE[AFTER[RETURN FREE]]]]]]].
  - subst trace after. right;split.
    + unfold measure;rewrite SELECT. eapply source_rank;eauto.
      rewrite(selected_sound _ _ SELECT)in CODE;exact CODE.
    + split;auto. eapply match_held with(fuel:=fuel)(p:=p);eauto.
      * assert(RANK:(Pos.to_nat next<Pos.to_nat pc)%nat).
        { eapply source_rank;eauto. rewrite(selected_sound _ _ SELECT)in CODE;exact CODE. }
        lia.
      * intros mf RUN. apply PREFIX. rewrite(execute_transfer _ _ _ _ _ _ _ _ _ _ TRANSFER);exact RUN.
  - subst sp trace after i. left.
    assert(RUN:execute ge f(Vptr block Ptrofs.zero)32(fn_entrypoint f)ir im=Some m).
    { apply PREFIX;eapply execute_return;eauto. }
    assert(TARGET:execute tge(transf_function f)(Vptr block Ptrofs.zero)32
       (fn_entrypoint(transf_function f))ir im=Some m).
    { unfold transf_function;rewrite SELECT.
      rewrite(execute_preserved ge tge symbols_preserved).
      apply REPLAY. rewrite(selected_sound _ _ SELECT)in RUN;exact RUN. }
    destruct(execute_sound _ _ _ _ _ _ _ _ TARGET stk')as[last[trs[STAR RET]]].
    exists(Returnstate stk' Vundef final);split.
    + eapply star_plus_trans;[exact STAR| |reflexivity]. apply plus_one.
      eapply exec_Ireturn with(or:=None);eauto.
      rewrite(proj2(proj2(metadata_preserved f)));exact FREE.
    + constructor;auto.
Qed.

Lemma normal_step:
  forall stk f sp pc rs m trace after,
  RTL.step ge(State stk f sp pc rs m)trace after ->
  forall stk',list_forall2 match_frames stk stk' -> selected f=None ->
  exists target,plus RTL.step tge(State stk' f sp pc rs m)trace target /\match_states after target.
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
  - econstructor;split. apply plus_one;eapply exec_Icall with(fd:=transf_fundef fd);eauto.
    eapply find_function_translated;eauto. rewrite sig_preserved;auto.
    constructor;constructor;auto. constructor;auto.
  - econstructor;split. apply plus_one;eapply exec_Itailcall with(fd:=transf_fundef fd);eauto.
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
  (exists target_after,plus RTL.step tge target trace target_after /\match_states after target_after) \/
  (measure after<measure source /\trace=E0 /\match_states after target)%nat.
Proof.
  intros source trace after STEP target MATCH;inv MATCH.
  - left;eapply normal_step;eauto.
  - eapply held_step;eauto.
  - inversion STEP;subst.
    + left. destruct(metadata_preserved f)as[SIG[PARAM STACK]].
      exists(State stk'(transf_function f)(Vptr stk0 Ptrofs.zero)
        (fn_entrypoint(transf_function f))(init_regs args(fn_params f))m');split.
      * apply plus_one.
        rewrite <-PARAM. eapply exec_function_internal;rewrite ?SIG,?STACK;eauto.
      * destruct(selected f)as[p|]eqn:SELECT.
        -- eapply match_held with(fuel:=32%nat)(p:=p);eauto.
           rewrite(selected_sound _ _ SELECT);simpl;lia.
        -- unfold transf_function;rewrite SELECT;constructor;auto.
    + left;econstructor;split. apply plus_one;eapply exec_function_external;eauto.
      eapply external_call_symbols_preserved;eauto;apply senv_preserved.
      constructor;auto.
  - inversion STEP;subst. inv STACKS. inv H1.
    left;econstructor;split. apply plus_one;eapply exec_return;eauto.
    constructor;auto.
Qed.
Lemma transf_initial_states:
  forall source,RTL.initial_state prog source ->exists target,RTL.initial_state tprog target /\match_states source target.
Proof.
  intros;inv H. exists(Callstate nil(transf_fundef f)nil m0);split.
  - econstructor.
    + eapply(Genv.init_mem_transf TRANSL);eauto.
    + rewrite symbols_preserved.
      exact(eq_trans(f_equal(Genv.find_symbol ge)(match_program_main TRANSL))H1).
    + eapply function_ptr_translated;eauto.
    + rewrite <-H3;apply sig_preserved.
  - constructor;constructor.
Qed.
Lemma transf_final_states:
  forall source target result,match_states source target ->RTL.final_state source result ->RTL.final_state target result.
Proof. intros;inv H0;inv H;inv STACKS;constructor. Qed.
Theorem transf_program_correct_given:
  forward_simulation(RTL.semantics prog)(RTL.semantics tprog).
Proof.
  eapply forward_simulation_star with(measure:=measure).
  apply senv_preserved. exact transf_initial_states. exact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.

Require Import MemoryNeonReplay.
Theorem transf_program_correct:
  forall prog tprog,match_prog prog tprog ->
  forward_simulation(RTL.semantics prog)(RTL.semantics tprog).
Proof.
  intros prog tprog MATCH.
  exact(transf_program_correct_given prog tprog MATCH execute_source_target).
Qed.
