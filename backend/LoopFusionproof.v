(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Semantic preservation of checked finite pure schedules. *)
Require Import Coqlib Maps AST Linking Integers Lia.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL LICM LICMproof LoopFusion.

Lemma no_context_correct:
  forall F V F' V' (ge: Genv.t F V) (ge': Genv.t F' V') sp sp' op args m,
  no_context op = true -> eval_operation ge sp op args m = eval_operation ge' sp' op args m.
Proof. intros; destruct op; simpl in *; try discriminate; reflexivity. Qed.

Lemma raw_expr_denote:
  forall F V (ge: Genv.t F V) sp rs op args e,
  raw_expr op args = Some e ->
  denote ge sp rs e = Val.maketotal (eval_operation ge sp op (map (denote ge sp rs) args) Mem.empty).
Proof.
  intros F V ge sp rs op args e H.
  destruct args as [|a [|b [|c [|d rest]]]]; simpl in H; try discriminate; inv H; reflexivity.
Qed.
Lemma constant_args_denote:
  forall F V (ge: Genv.t F V) sp rs args vs,
  constant_args args = Some vs -> map (denote ge sp rs) args = vs.
Proof.
  intros F V ge sp rs args. induction args as [|a rest IH]; simpl; intros; try congruence.
  destruct a; try discriminate. destruct (constant_args rest) eqn:E; try discriminate.
  inv H. simpl. f_equal. eapply IH; eauto.
Qed.
Lemma make_expr_denote:
  forall F V (ge: Genv.t F V) sp rs op args e,
  make_expr op args = Some e ->
  denote ge sp rs e = Val.maketotal (eval_operation ge sp op (map (denote ge sp rs) args) Mem.empty).
Proof.
  intros F V ge sp rs op args e H. unfold make_expr in H.
  destruct (no_context op) eqn:NC.
  - destruct (constant_args args) as [vs|] eqn:CA.
    + destruct (eval_operation empty_ge Vundef op vs Mem.empty) as [v|] eqn:EV.
      * destruct v; try solve [destruct (raw_expr op args) eqn:R; try discriminate; destruct (small e0); inv H; eapply raw_expr_denote; eauto].
        destruct (small (Intval i)); inv H. simpl.
        rewrite (constant_args_denote _ _ ge sp rs _ _ CA).
        rewrite (no_context_correct _ _ _ _ ge empty_ge sp Vundef op vs Mem.empty NC), EV. reflexivity.
      * destruct (raw_expr op args) eqn:R; try discriminate; destruct (small e0); inv H; eapply raw_expr_denote; eauto.
    + destruct (raw_expr op args) eqn:R; try discriminate; destruct (small e0); inv H; eapply raw_expr_denote; eauto.
  - destruct (raw_expr op args) eqn:R; try discriminate; destruct (small e0); inv H; eapply raw_expr_denote; eauto.
Qed.
Definition regs_match {F V: Type} (ge: Genv.t F V) (sp: val) (initial: regset) (ss: symregs) (rs: regset): Prop :=
  forall r, rs#r = denote ge sp initial (symget ss r).
Lemma regs_match_empty:
  forall F V (ge: Genv.t F V) sp initial, regs_match ge sp initial (PTree.empty expr) initial.
Proof. intros; red; intros; reflexivity. Qed.
Lemma regs_match_args:
  forall F V (ge: Genv.t F V) sp initial ss rs args,
  regs_match ge sp initial ss rs -> rs##args = map (denote ge sp initial) (symargs ss args).
Proof. intros; unfold symargs. rewrite map_map. apply list_map_exten; auto. Qed.
Lemma regs_match_set:
  forall F V (ge: Genv.t F V) sp initial ss rs dst e v,
  regs_match ge sp initial ss rs -> denote ge sp initial e = v ->
  regs_match ge sp initial (PTree.set dst e ss) (rs#dst <- v).
Proof.
  unfold regs_match,symget; intros. rewrite Regmap.gsspec,PTree.gsspec.
  destruct (peq r dst); subst; auto.
Qed.
Lemma safe_operation_properties:
  forall op args, safe_operation op args = true ->
  op_depends_on_memory op = false /\ LICM.total_arity op (length args) = true.
Proof.
  unfold safe_operation; intros op args H. repeat rewrite andb_true_iff in H.
  destruct H as [[A B] C]. apply negb_true_iff in A; auto.
Qed.
Lemma known_condition_sound:
  forall F V (ge: Genv.t F V) sp initial cond args m b,
  known_condition cond args = Some b ->
  eval_condition cond (map (denote ge sp initial) args) m = Some b.
Proof.
  intros F V ge sp initial cond args m b H. unfold known_condition in H.
  destruct (negb (op_depends_on_memory (Ocmp cond))) eqn:MEM; try discriminate.
  apply negb_true_iff in MEM. destruct (constant_args args) as [vs|] eqn:CA; try discriminate.
  rewrite (constant_args_denote _ _ ge sp initial _ _ CA).
  rewrite (cond_depends_on_memory_correct cond vs m Mem.empty MEM). exact H.
Qed.

Lemma run_sound:
  forall (ge: genv) f fuel pc ss e initial rs stk block m m',
  run f fuel pc ss = Some e ->
  regs_match ge (Vptr block Ptrofs.zero) initial ss rs ->
  Mem.free m block 0 (fn_stacksize f) = Some m' ->
  plus RTL.step ge (State stk f (Vptr block Ptrofs.zero) pc rs m) E0
       (Returnstate stk (denote ge (Vptr block Ptrofs.zero) initial e) m').
Proof.
  intros ge f fuel. induction fuel as [|fuel IH]; intros pc ss e initial rs stk block m m' RUN REGS FREE; simpl in RUN; try discriminate.
  destruct (fn_code f)!pc as [i|] eqn:GET; try discriminate.
  destruct i; try discriminate.
  - eapply plus_left with (t1 := E0) (t2 := E0); eauto using exec_Inop.
    apply plus_star. eapply IH; eauto.
  - destruct (safe_operation o l) eqn:SAFE; try discriminate.
    destruct (make_expr o (symargs ss l)) as [se|] eqn:MAKE; try discriminate.
    destruct (safe_operation_properties _ _ SAFE) as [MEM TOTAL].
    destruct (LICMproof.total_operation _ _ ge (Vptr block Ptrofs.zero) o (rs##l) m) as [v EV].
    rewrite list_length_map; exact TOTAL.
    assert (VALUE: denote ge (Vptr block Ptrofs.zero) initial se = v).
    { rewrite (make_expr_denote _ _ ge _ initial _ _ _ MAKE).
      rewrite <- (regs_match_args _ _ ge _ initial ss rs l REGS).
      rewrite <- (@op_depends_on_memory_correct _ _ ge _ o (rs##l) m Mem.empty MEM), EV. reflexivity. }
    eapply plus_left with (t1 := E0) (t2 := E0).
    eapply exec_Iop; eauto.
    apply plus_star. eapply IH; eauto. eapply regs_match_set; eauto. reflexivity.
  - destruct (known_condition c (symargs ss l)) eqn:COND; try discriminate.
    eapply plus_left with (t1 := E0) (t2 := E0).
    eapply exec_Icond; eauto.
    rewrite (regs_match_args _ _ ge _ initial ss rs l REGS).
    eapply known_condition_sound; eauto.
    apply plus_star. eapply IH; eauto. reflexivity.
  - inv RUN.
    replace (denote ge (Vptr block Ptrofs.zero) initial
              (match o with Some r => symget ss r | None => Undef end))
      with (regmap_optget o Vundef rs).
    apply plus_one. eapply exec_Ireturn; eauto.
    destruct o; simpl; auto.
Qed.

Lemma validate_function_properties:
  forall f tf, validate_function f tf = true ->
  fn_sig tf = fn_sig f /\ fn_params tf = fn_params f /\ fn_stacksize tf = fn_stacksize f /\
  exists e, run_function f = Some e /\ run_function tf = Some e.
Proof.
  unfold validate_function; intros f tf H.
  destruct (signature_eq _ _); try discriminate.
  destruct (list_eq_dec peq _ _); try discriminate.
  destruct (zeq _ _); try discriminate.
  destruct (run_function f) as [ee1|] eqn:A; try discriminate.
  destruct (run_function tf) as [ee2|] eqn:B; try discriminate.
  destruct (expr_eq _ _); try discriminate. subst ee2.
  repeat split; auto. exists ee1; auto.
Qed.
Lemma transf_function_sig:
  forall proposal f, fn_sig (transf_function_with proposal f) = fn_sig f.
Proof.
  unfold transf_function_with; intros. destruct (validate_function f (proposal f)) eqn:E; auto.
  apply validate_function_properties in E; tauto.
Qed.
Lemma transf_function_params:
  forall proposal f, fn_params (transf_function_with proposal f) = fn_params f.
Proof.
  unfold transf_function_with; intros. destruct (validate_function f (proposal f)) eqn:E; auto.
  apply validate_function_properties in E; tauto.
Qed.
Lemma transf_function_stacksize:
  forall proposal f, fn_stacksize (transf_function_with proposal f) = fn_stacksize f.
Proof.
  unfold transf_function_with; intros. destruct (validate_function f (proposal f)) eqn:E; auto.
  apply validate_function_properties in E; tauto.
Qed.

Lemma run_source_step:
  forall ge f fuel pc ss e initial rs stk block m m' t S2,
  run f fuel pc ss = Some e ->
  regs_match ge (Vptr block Ptrofs.zero) initial ss rs ->
  Mem.free m block 0 (fn_stacksize f) = Some m' ->
  RTL.step ge (State stk f (Vptr block Ptrofs.zero) pc rs m) t S2 ->
  (exists fuel' pc' ss' rs',
    (fuel' < fuel)%nat /\ t = E0 /\
    S2 = State stk f (Vptr block Ptrofs.zero) pc' rs' m /\
    run f fuel' pc' ss' = Some e /\ regs_match ge (Vptr block Ptrofs.zero) initial ss' rs') \/
  (t = E0 /\ S2 = Returnstate stk (denote ge (Vptr block Ptrofs.zero) initial e) m').
Proof.
  intros ge f fuel pc ss e initial rs stk block m m' t S2 RUN REGS FREE STEP.
  destruct fuel as [|fuel]; simpl in RUN; try discriminate.
  inv STEP; match goal with GET: (fn_code f)!pc = Some _ |- _ => rewrite GET in RUN end; simpl in RUN; try discriminate.
  - left. exists fuel,pc',ss,rs. repeat split; auto; lia.
  - destruct (safe_operation op args) eqn:SAFE; try discriminate.
    destruct (make_expr op (symargs ss args)) as [se|] eqn:MAKE; try discriminate.
    destruct (safe_operation_properties _ _ SAFE) as [MEM TOTAL].
    assert (VALUE: denote ge (Vptr block Ptrofs.zero) initial se = v).
    { rewrite (make_expr_denote _ _ ge _ initial _ _ _ MAKE).
      rewrite <- (regs_match_args _ _ ge _ initial ss rs args REGS).
      rewrite <- (@op_depends_on_memory_correct _ _ ge _ op (rs##args) m Mem.empty MEM).
      match goal with EV: eval_operation _ _ _ _ m = Some v |- _ => rewrite EV end. reflexivity. }
    left. exists fuel,pc',(PTree.set res se ss),(rs#res <- v).
    repeat split; auto; try lia. eapply regs_match_set; eauto.
  - destruct (known_condition cond (symargs ss args)) eqn:COND; try discriminate.
    assert (EVAL: eval_condition cond (rs##args) m = Some b0).
    { rewrite (regs_match_args _ _ ge _ initial ss rs args REGS). eapply known_condition_sound; eauto. }
    assert (b=b0) by congruence. subst b0. left. exists fuel,(if b then ifso else ifnot),ss,rs.
    repeat split; auto; lia.
  - inv RUN. right. split; auto.
    assert (m'0=m') by congruence. subst m'0. f_equal.
    destruct or; simpl; auto.
Qed.

Lemma run_zero: forall f pc ss, run f 0 pc ss = None.
Proof. reflexivity. Qed.
Local Opaque run.

Definition match_prog_with (proposal: function -> function) (p tp: program) :=
  match_program (fun ctx f tf => tf = transf_fundef_with proposal f) eq p tp.
Lemma transf_program_with_match:
  forall proposal p, match_prog_with proposal p (transf_program_with proposal p).
Proof. intros. eapply match_transform_program; eauto. Qed.

Section PRESERVATION.
Variable proposal: function -> function.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog_with proposal prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Lemma functions_translated:
  forall v f, Genv.find_funct ge v = Some f -> Genv.find_funct tge v = Some (transf_fundef_with proposal f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated:
  forall v f, Genv.find_funct_ptr ge v = Some f -> Genv.find_funct_ptr tge v = Some (transf_fundef_with proposal f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved: forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig (transf_fundef_with proposal f) = funsig f.
Proof. destruct f; simpl; auto. apply transf_function_sig. Qed.
Lemma find_function_translated:
  forall ros rs fd, find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef_with proposal fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.
Lemma denote_preserved:
  forall sp initial e, denote tge sp initial e = denote ge sp initial e.
Proof.
  intros sp initial e; induction e; simpl; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3;
  rewrite (eval_operation_preserved _ _ symbols_preserved); reflexivity.
Qed.
Lemma unchanged:
  forall f, validate_function f (proposal f) = false -> transf_function_with proposal f = f.
Proof. unfold transf_function_with; intros; rewrite H; reflexivity. Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
| match_frames_intro: forall res f sp pc rs
    (PLAIN: validate_function f (proposal f) = false),
    match_frames (Stackframe res f sp pc rs) (Stackframe res f sp pc rs).
Inductive match_states: nat -> RTL.state -> RTL.state -> Prop :=
| match_regular_states: forall stk f sp pc rs m stk'
    (STACKS: list_forall2 match_frames stk stk')
    (PLAIN: validate_function f (proposal f) = false),
    match_states 0 (State stk f sp pc rs m) (State stk' f sp pc rs m)
| match_cached_states: forall stk f block pc rs m stk' fuel ss e initial m'
    (STACKS: list_forall2 match_frames stk stk')
    (RUN: run f fuel pc ss = Some e)
    (REGS: regs_match ge (Vptr block Ptrofs.zero) initial ss rs)
    (FREE: Mem.free m block 0 (fn_stacksize f) = Some m'),
    match_states fuel (State stk f (Vptr block Ptrofs.zero) pc rs m)
      (Returnstate stk' (denote ge (Vptr block Ptrofs.zero) initial e) m')
| match_callstates: forall stk fd args m stk'
    (STACKS: list_forall2 match_frames stk stk'),
    match_states 0 (Callstate stk fd args m) (Callstate stk' (transf_fundef_with proposal fd) args m)
| match_returnstates: forall stk v m stk'
    (STACKS: list_forall2 match_frames stk stk'),
    match_states 0 (Returnstate stk v m) (Returnstate stk' v m).

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall i S1', match_states i S1 S1' ->
  exists i' S2', (plus RTL.step tge S1' t S2' \/ (star RTL.step tge S1' t S2' /\ (i' < i)%nat)) /\
                match_states i' S2 S2'.
Proof.
  intros S1 t S2 STEP i S1' MS. inv MS.
  - inv STEP.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Inop; eauto. constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Iop; eauto.
      match goal with EV: eval_operation ge _ _ _ _ = Some _ |- _ => rewrite <- EV end.
      apply eval_operation_preserved. exact symbols_preserved.
      constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Iload; eauto.
      match goal with EV: eval_addressing ge _ _ _ = Some _ |- _ => rewrite <- EV end.
      apply eval_addressing_preserved. exact symbols_preserved.
      constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Istore; eauto.
      match goal with EV: eval_addressing ge _ _ _ = Some _ |- _ => rewrite <- EV end.
      apply eval_addressing_preserved. exact symbols_preserved.
      constructor; auto.
    + exists 0%nat. exists (Callstate (Stackframe res f sp pc' rs :: stk') (transf_fundef_with proposal fd) (rs##args) m).
      split. left; apply plus_one; eapply exec_Icall; eauto.
      eapply find_function_translated; eauto. apply sig_preserved.
      constructor. constructor; auto. constructor; auto.
    + exists 0%nat. match goal with FREE: Mem.free m _ _ _ = Some ?mf |- _ =>
        exists (Callstate stk' (transf_fundef_with proposal fd) (rs##args) mf) end.
      split. left; apply plus_one; eapply exec_Itailcall; eauto.
      eapply find_function_translated; eauto. apply sig_preserved.
      constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Ibuiltin; eauto.
      eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Icond; eauto. constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Ijumptable; eauto. constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_Ireturn; eauto. constructor; auto.
  - destruct (run_source_step ge f i pc ss e initial rs stk block m m' t S2 RUN REGS FREE STEP)
      as [(fuel' & pc' & ss' & rs' & LT & TRACE & NEXT & REM & REL) | (TRACE & NEXT)].
    + subst t S2. exists fuel'. econstructor; split.
      right; split; [apply star_refl|exact LT]. econstructor; eauto.
    + subst t S2. assert (0 < i)%nat by (destruct i; [rewrite run_zero in RUN; discriminate|lia]).
      exists 0%nat. econstructor; split. right; split; [apply star_refl|assumption]. constructor; auto.
  - inv STEP.
    + simpl. destruct (validate_function f (proposal f)) eqn:VALID.
      * destruct (validate_function_properties _ _ VALID) as [SIG [PARAMS [SIZE [e [SOURCE TARGET]]]]].
        destruct (Mem.range_perm_free m' stk0 0 (fn_stacksize f)) as [mfree FREE].
        red; intros; eapply Mem.perm_alloc_2; eauto.
        set (initial := init_regs args (fn_params f)).
        assert (BODY: plus RTL.step tge
          (State stk' (proposal f) (Vptr stk0 Ptrofs.zero) (fn_entrypoint (proposal f)) initial m') E0
          (Returnstate stk' (denote ge (Vptr stk0 Ptrofs.zero) initial e) mfree)).
        { rewrite <- (denote_preserved (Vptr stk0 Ptrofs.zero) initial e).
          eapply run_sound; eauto. apply regs_match_empty. rewrite SIZE; auto. }
        exists 128%nat. exists (Returnstate stk' (denote ge (Vptr stk0 Ptrofs.zero) initial e) mfree). split.
        left. eapply plus_left with (t1 := E0) (t2 := E0).
        unfold transf_fundef_with, AST.transf_fundef, transf_function_with; rewrite VALID.
        eapply exec_function_internal; eauto. rewrite SIG; eauto. rewrite SIZE; eauto.
        apply plus_star. rewrite PARAMS. exact BODY. reflexivity.
        exact (@match_cached_states stk f stk0 (fn_entrypoint f)
          (init_regs args (fn_params f)) m' stk' 128 (PTree.empty expr) e initial mfree
          STACKS SOURCE (regs_match_empty _ _ ge _ initial) FREE).
      * exists 0%nat. econstructor; split. left; apply plus_one.
        unfold transf_fundef_with, AST.transf_fundef, transf_function_with; rewrite VALID.
        eapply exec_function_internal; eauto. constructor; auto.
    + exists 0%nat. econstructor; split. left; apply plus_one. eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved. constructor; auto.
  - inv STEP. inv STACKS. inv H1.
    exists 0%nat. econstructor; split. left; apply plus_one; eapply exec_return; eauto. constructor; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists i S2, RTL.initial_state tprog S2 /\ match_states i S1 S2.
Proof.
  intros. inv H. exists 0%nat. econstructor; split. econstructor.
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
  eapply function_ptr_translated; eauto.
  rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.
Lemma transf_final_states:
  forall i S1 S2 r, match_states i S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. intros; inv H0; inv H; inv STACKS; constructor. Qed.
Theorem transf_program_with_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  apply Forward_simulation with lt match_states; constructor.
  - apply lt_wf.
  - exact transf_initial_states.
  - exact transf_final_states.
  - exact step_simulation.
  - apply senv_preserved.
Qed.
End PRESERVATION.

Definition match_prog := match_prog_with candidate.
Global Instance TransfLoopFusionLink: TransfLink match_prog := TransfTotalLink transf_function.
Lemma transf_program_match: forall p, match_prog p (transf_program p).
Proof. apply transf_program_with_match. Qed.
Theorem transf_program_correct:
  forall p tp, match_prog p tp -> forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof. intros; eapply transf_program_with_correct; eauto. Qed.
