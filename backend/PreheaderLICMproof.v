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

(** Preservation of invariant motion after a retained entry preheader. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Experimental Experimentalproof LICM PreheaderLICM.
Require LICMproof.

Lemma choose_in_sound:
  forall items f pre fuel b,
  (forall pc i, In (pc,i) items -> (fn_code f)!pc = Some i) ->
  choose_in f pre fuel items = Some b ->
  region_prefix b = pre /\ eligible f pre (region_op b) (region_args b) = true /\
  exists pc dst next, (fn_code f)!pc = Some (Iop (region_op b) (region_args b) dst next).
Proof.
  induction items as [|[pc i] rest IH]; simpl; intros f pre fuel b GET CHOICE; try discriminate.
  destruct i; try solve [eapply IH; eauto with coqlib].
  destruct fuel; try discriminate.
  destruct (outsideb pre pc && eligible f pre o l && HoistConst.cyclic f pc (Iop o l r n)) eqn:E.
  - inv CHOICE. repeat rewrite andb_true_iff in E. split; auto. split; try tauto.
    exists pc,r,n; auto.
  - eapply IH; eauto with coqlib.
Qed.
Record region_valid (f: function) (b: region) : Prop := {
  valid_source: exists pc dst next, (fn_code f)!pc = Some (Iop (region_op b) (region_args b) dst next);
  valid_memory: op_depends_on_memory (region_op b) = false;
  valid_speculation: LICM.total_arity (region_op b) (length (region_args b)) = true \/
    exists dst next, (fn_code f)!(prefix_exit (region_prefix b)) =
      Some (Iop (region_op b) (region_args b) dst next);
  valid_anchor: outsideb (region_prefix b) (prefix_exit (region_prefix b)) = true;
  valid_closed: prefix_closed f (region_prefix b) = true;
  valid_args: forallb (stable_after f (region_prefix b)) (region_args b) = true
}.
Lemma linear_choice_sound:
  forall f pre fuel items b,
  (forall pc i, In (pc,i) items -> (fn_code f)!pc = Some i) ->
  outsideb pre (prefix_exit pre) && prefix_closed f pre = true ->
  choose_in f pre fuel items = Some b -> region_valid f b.
Proof.
  intros f pre fuel items b GET CHECK CHOICE.
  destruct (choose_in_sound items f pre fuel b GET CHOICE) as [PRE [ELIG SOURCE]].
  unfold eligible in ELIG; repeat rewrite andb_true_iff in ELIG.
  destruct ELIG as [[[MEM TOTAL] ARGS] _]. apply negb_true_iff in MEM.
  apply andb_true_iff in CHECK. rewrite <- PRE in *. constructor; tauto.
Qed.
Lemma suffix_choice_sound:
  forall items f fuel b,
  (forall pc i, In (pc,i) items -> (fn_code f)!pc = Some i) ->
  choose_suffix f fuel items = Some b -> region_valid f b.
Proof.
  induction items as [|[pc i] rest IH]; simpl; intros f fuel b GET CHOICE; try discriminate.
  destruct i; try solve [eapply IH; eauto with coqlib].
  destruct fuel; try discriminate.
  destruct (HoistConst.cyclic f pc (Iop o l r n)); try solve [eapply IH; eauto with coqlib].
  remember (suffix_prefix f pc) as pre.
  destruct (outsideb pre pc && prefix_closed f pre && lazy_eligible f pre o l) eqn:CHECK.
  - inv CHOICE. repeat rewrite andb_true_iff in CHECK.
    destruct CHECK as [[OUT CLOSED] ELIG]. unfold lazy_eligible in ELIG.
    repeat rewrite andb_true_iff in ELIG. destruct ELIG as [[[MEM ARITY] ARGS] WORTH].
    apply negb_true_iff in MEM. constructor; simpl.
    + exists pc,r,n; auto.
    + exact MEM.
    + right. exists r,n. simpl. apply GET; simpl; auto.
    + exact OUT.
    + exact CLOSED.
    + exact ARGS.
  - eapply IH; eauto with coqlib.
Qed.
Lemma chosen_sound: forall f b, chosen f = Some b -> region_valid f b.
Proof.
  unfold chosen. intros f b CHOICE.
  destruct (Nat.leb (length (PTree.elements (fn_code f))) 512); try discriminate.
  assert (GET: forall pc i, In (pc,i) (PTree.elements (fn_code f)) -> (fn_code f)!pc = Some i)
    by (intros; eapply PTree.elements_complete; eauto).
  remember (find_prefix 16 f (fn_entrypoint f) nil) as pre.
  destruct (outsideb pre (prefix_exit pre) && prefix_closed f pre) eqn:CHECK.
  - destruct (choose_in f pre 32 (PTree.elements (fn_code f))) eqn:C.
    + inv CHOICE. eapply linear_choice_sound; eauto.
    + eapply suffix_choice_sound; eauto.
  - eapply suffix_choice_sound; eauto.
Qed.
Lemma closed_successor:
  forall f pre pc i next,
  prefix_closed f pre = true -> (fn_code f)!pc = Some i ->
  outsideb pre pc = true -> In next (successors_instr i) -> outsideb pre next = true.
Proof.
  unfold prefix_closed; intros f pre pc i next CLOSED GET OUT IN.
  rewrite forallb_forall in CLOSED.
  specialize (CLOSED (pc,i) (PTree.elements_correct _ _ GET)). simpl in CLOSED.
  rewrite OUT in CLOSED. rewrite forallb_forall in CLOSED. auto.
Qed.
Lemma stable_after_def:
  forall f pre r pc i dst,
  stable_after f pre r = true -> (fn_code f)!pc = Some i ->
  outsideb pre pc = true -> instr_defs i = Some dst -> dst <> r.
Proof.
  unfold stable_after; intros f pre r pc i dst STABLE GET OUT DEF.
  rewrite forallb_forall in STABLE.
  specialize (STABLE (pc,i) (PTree.elements_correct _ _ GET)). simpl in STABLE.
  rewrite OUT, DEF in STABLE. destruct (peq dst r); congruence.
Qed.
Lemma invariant_arg_bound:
  forall f b r, chosen f = Some b -> In r (region_args b) -> Plt r (LICM.fresh_reg f).
Proof.
  intros. destruct (valid_source _ _ (chosen_sound _ _ H)) as (pc & dst & next & GET).
  eapply LICMproof.fresh_reg_use; eauto.
Qed.
Definition outside (f: function) (warm: bool) (pc: node) : Prop :=
  match chosen f, warm with Some b, true => outsideb (region_prefix b) pc = true | _, _ => True end.
Definition ready (f: function) (warm: bool) (pc: node) : Prop :=
  match chosen f with Some b => warm = true \/ pc <> prefix_exit (region_prefix b) | None => True end.
Definition result_safe (f: function) (warm: bool) (dst: reg) : Prop :=
  match chosen f, warm with Some b, true => ~ In dst (region_args b) | _, _ => True end.
Lemma outside_successor:
  forall f warm pc i next, outside f warm pc -> (fn_code f)!pc = Some i ->
  In next (successors_instr i) -> outside f warm next.
Proof.
  unfold outside; intros. destruct (chosen f) as [b|] eqn:C; auto. destruct warm; auto.
  eapply closed_successor; eauto. apply (valid_closed _ _ (chosen_sound _ _ C)).
Qed.
Lemma safe_def:
  forall f warm pc i dst, outside f warm pc -> (fn_code f)!pc = Some i ->
  instr_defs i = Some dst -> result_safe f warm dst.
Proof.
  unfold outside,result_safe; intros f warm pc i dst OUT GET DEF.
  destruct (chosen f) as [b|] eqn:C; auto. destruct warm; auto. intros IN.
  pose proof (valid_args _ _ (chosen_sound _ _ C)) as ARGS.
  rewrite forallb_forall in ARGS. specialize (ARGS dst IN).
  eapply (stable_after_def _ _ _ _ _ _ ARGS GET OUT DEF); auto.
Qed.
Definition regs_match {F V: Type} (ge: Genv.t F V) (f: function) (warm: bool) (sp: val) (rs trs: regset) : Prop :=
  (forall r, Plt r (LICM.fresh_reg f) -> trs#r = rs#r) /\
  match chosen f,warm with
  | Some b,true => eval_operation ge sp (region_op b) rs##(region_args b) Mem.empty = Some trs#(LICM.fresh_reg f)
  | _,_ => True end.
Lemma regs_match_list:
  forall (F V: Type) (ge: Genv.t F V) f warm sp rs trs rl,
  regs_match ge f warm sp rs trs ->
  (forall r, In r rl -> Plt r (LICM.fresh_reg f)) -> trs##rl = rs##rl.
Proof. intros F V ge f warm sp rs trs rl [A B] C. apply list_map_exten. intros; symmetry; apply A; auto. Qed.
Arguments regs_match_list {F V} ge f warm sp rs trs rl _ _.
Lemma regs_match_set:
  forall (F V: Type) (ge: Genv.t F V) f warm sp rs trs r v,
  regs_match ge f warm sp rs trs -> r <> LICM.fresh_reg f -> result_safe f warm r ->
  regs_match ge f warm sp (rs#r <- v) (trs#r <- v).
Proof.
  intros F V ge f warm sp rs trs r v [A B] NE SAFE. split.
  - intros x LT. rewrite !Regmap.gsspec. destruct (peq x r); auto.
  - unfold result_safe in SAFE. destruct (chosen f) as [b|] eqn:C; auto. destruct warm; auto.
    rewrite LICMproof.get_list_set_other by exact SAFE. rewrite Regmap.gso; auto.
Qed.
Lemma regs_match_setres:
  forall (F V: Type) (ge: Genv.t F V) f warm sp rs trs res v,
  regs_match ge f warm sp rs trs ->
  (match res with BR r => r <> LICM.fresh_reg f /\ result_safe f warm r | _ => True end) ->
  regs_match ge f warm sp (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto. destruct H0. apply regs_match_set; auto. Qed.
Lemma regs_match_cold: forall (F V: Type) (ge: Genv.t F V) f sp rs, regs_match ge f false sp rs rs.
Proof. intros; split; auto. destruct (chosen f); auto. Qed.
Lemma outside_cold: forall f pc, outside f false pc.
Proof. intros; unfold outside; destruct (chosen f); auto. Qed.
Lemma transf_function_sig: forall f, fn_sig (transf_function f) = fn_sig f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_params: forall f, fn_params (transf_function f) = fn_params f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_stacksize: forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_entry: forall f, fn_entrypoint (transf_function f) = label f false (fn_entrypoint f).
Proof. intros; unfold transf_function,label; destruct (chosen f); reflexivity. Qed.
Lemma cache_code:
  forall f b, chosen f = Some b ->
  (fn_code (transf_function f))!(label f false (prefix_exit (region_prefix b))) =
    Some (Iop (region_op b) (region_args b) (LICM.fresh_reg f) (label f true (prefix_exit (region_prefix b)))).
Proof. intros; unfold transf_function,label; rewrite H; simpl. apply PTree.gss. Qed.
Inductive instr_spec (f: function) (warm: bool): instruction -> instruction -> Prop :=
  | instr_default: forall i, instr_spec f warm i (Experimental.map_successors (label f warm) i)
  | instr_hoisted: forall b dst next, chosen f = Some b -> warm = true ->
      instr_spec f warm (Iop (region_op b) (region_args b) dst next)
        (Iop Omove (LICM.fresh_reg f :: nil) dst (label f warm next)).
Lemma transf_function_at:
  forall f warm pc i, (fn_code f)!pc = Some i -> ready f warm pc ->
  exists ti, (fn_code (transf_function f))!(label f warm pc) = Some ti /\ instr_spec f warm i ti.
Proof.
  intros f warm pc i GET READY. unfold transf_function,label.
  destruct (chosen f) as [b|] eqn:C.
  - assert (LABEL: forall mode pc, label f mode pc = tag mode pc) by (intros; unfold label; rewrite C; auto).
    exists (copy_instr f b warm i). split.
    + unfold hoisted,copy_code; simpl.
      rewrite PTree.gso.
      unfold tag. destruct warm; rewrite PTree.gNode, PTree.gmap1, GET; reflexivity.
      unfold ready in READY. rewrite C in READY. unfold tag. destruct warm; try discriminate.
      intros EQ. injection EQ as EQ. destruct READY as [BAD|NE]; try discriminate. apply NE. exact EQ.
    + unfold copy_instr. replace (tag warm) with (label f warm) by (unfold label; rewrite C; reflexivity). destruct warm.
      * destruct i; try constructor. unfold cached,LICM.transf_instr_cached; simpl.
        destruct (Op.eq_operation o (region_op b)); try constructor.
        destruct (list_eq_dec peq l (region_args b)); try constructor.
        subst. apply instr_hoisted; auto.
      * constructor.
  - exists i; split; auto.
    replace i with (Experimental.map_successors (label f warm) i) at 2.
    constructor. unfold label; rewrite C. apply Experimentalproof.map_successors_id.
Qed.
Definition match_prog (p tp: program) := match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Lemma transf_program_match: forall p, match_prog p (transf_program p).
Proof. intros; eapply match_transform_program; eauto. Qed.

Section PRESERVATION.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Lemma functions_translated:
  forall v f, Genv.find_funct ge v = Some f -> Genv.find_funct tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated:
  forall v f, Genv.find_funct_ptr ge v = Some f -> Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig (transf_fundef f) = funsig f.
Proof. destruct f; simpl; auto. apply transf_function_sig. Qed.

Lemma builtin_arg_regs:
  forall f warm rs trs sp m arg v,
  regs_match ge f warm sp rs trs ->
  eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  (forall r, In r (params_of_builtin_arg arg) -> Plt r (LICM.fresh_reg f)) ->
  eval_builtin_arg ge (fun r => trs#r) sp m arg v.
Proof.
  intros f warm rs trs sp m arg v REGS EV. induction EV; simpl; intros;
  try (constructor; eauto using in_or_app).
  rewrite <- (proj1 REGS x) by eauto with coqlib. constructor.
Qed.
Lemma builtin_args_regs:
  forall f warm rs trs sp m args vl,
  regs_match ge f warm sp rs trs ->
  eval_builtin_args ge (fun r => rs#r) sp m args vl ->
  (forall r, In r (params_of_builtin_args args) -> Plt r (LICM.fresh_reg f)) ->
  eval_builtin_args ge (fun r => trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f warm rs trs sp m args vl REGS EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs, in_or_app.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs trs warm
      (REGS: regs_match ge f warm sp rs trs) (OUT: outside f warm pc)
      (RES: res <> LICM.fresh_reg f) (SAFE: result_safe f warm res),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp (label f warm pc) trs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs trs m stk' warm
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match ge f warm sp rs trs)
      (OUT: outside f warm pc),
      match_states (State stk f sp pc rs m)
        (State stk' (transf_function f) sp (label f warm pc) trs m)
  | match_callstates: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | match_returnstates: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m) (Returnstate stk' v m).
Inductive ready_states: RTL.state -> RTL.state -> Prop :=
  | ready_regular: forall stk f sp pc rs trs m stk' warm
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match ge f warm sp rs trs)
      (OUT: outside f warm pc) (READY: ready f warm pc),
      ready_states (State stk f sp pc rs m)
        (State stk' (transf_function f) sp (label f warm pc) trs m)
  | ready_call: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      ready_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | ready_return: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      ready_states (Returnstate stk v m) (Returnstate stk' v m).
Lemma operation_step_defined:
  forall stk f sp pc rs m t S2 op args dst next,
  (fn_code f)!pc = Some (Iop op args dst next) ->
  RTL.step ge (State stk f sp pc rs m) t S2 ->
  exists v, eval_operation ge sp op rs##args m = Some v.
Proof.
  intros stk f sp pc rs m t S2 op args dst next GET STEP.
  inv STEP; try congruence.
  rewrite GET in H7. inv H7. eauto.
Qed.
Lemma prepare_states:
  forall S1 t S2, RTL.step ge S1 t S2 -> forall S1', match_states S1 S1' ->
  exists S1'', star RTL.step tge S1' E0 S1'' /\ ready_states S1 S1''.
Proof.
  intros S1 t S2 STEP S1' MATCH. inv MATCH.
  - destruct (chosen f) as [b|] eqn:C.
    + destruct warm.
      * econstructor; split. apply star_refl. eapply ready_regular with (warm := true); eauto.
        unfold ready; rewrite C; auto.
      * destruct (peq pc (prefix_exit (region_prefix b))) as [PC|PC].
        -- subst pc. pose proof (chosen_sound _ _ C) as VALID.
           assert (EX: exists v, eval_operation ge sp (region_op b) rs##(region_args b) Mem.empty = Some v).
           { destruct (valid_speculation _ _ VALID) as [TOTAL|AT].
             - apply LICMproof.total_operation. rewrite list_length_map. exact TOTAL.
             - destruct AT as (dst & next & CODE).
               destruct (operation_step_defined _ _ _ _ _ _ _ _ _ _ _ _ CODE STEP) as [v EVAL].
               exists v. rewrite <- (@op_depends_on_memory_correct _ _ _ _ _ _ m Mem.empty (valid_memory _ _ VALID)). exact EVAL. }
           destruct EX as [v EVAL].
           exists (State stk' (transf_function f) sp (label f true (prefix_exit (region_prefix b)))
                    (trs#(LICM.fresh_reg f) <- v) m). split.
           apply star_one. eapply exec_Iop. apply cache_code; eauto.
           rewrite (regs_match_list ge f false sp rs trs (region_args b) REGS)
             by (intros; eapply invariant_arg_bound; eauto).
           rewrite eval_operation_preserved with (ge1 := ge) by exact symbols_preserved.
           rewrite (@op_depends_on_memory_correct _ _ _ _ _ _ m Mem.empty (valid_memory _ _ VALID)). exact EVAL.
           eapply ready_regular with (warm := true); auto.
           split. intros r LT. rewrite Regmap.gso by extlia. apply (proj1 REGS); auto.
           rewrite Regmap.gss. unfold regs_match in REGS. simpl. rewrite C. exact EVAL.
           unfold outside; rewrite C. apply (valid_anchor _ _ VALID).
           unfold ready; rewrite C; auto.
        -- econstructor; split. apply star_refl. eapply ready_regular with (warm := false); eauto.
           unfold ready; rewrite C; auto.
    + econstructor; split. apply star_refl. eapply ready_regular with (warm := warm); eauto.
      unfold ready; rewrite C; auto.
  - econstructor; split. apply star_refl. constructor; auto.
  - econstructor; split. apply star_refl. constructor; auto.
Qed.
Ltac AT :=
  match goal with
  | [ A: (fn_code ?f)!?pc = Some ?i, OUT: outside ?f ?warm ?pc, READY: ready ?f ?warm ?pc |- _ ] =>
    destruct (transf_function_at f warm pc i A READY) as [ti [CODE SPEC]];
    assert (USES: forall r, In r (instr_uses i) -> Plt r (LICM.fresh_reg f))
      by (intros; eapply LICMproof.fresh_reg_use; eauto);
    assert (DEFS: forall r, instr_defs i = Some r -> r <> LICM.fresh_reg f)
      by (intros; eapply LICMproof.fresh_reg_def; eauto);
    assert (SAFE: forall r, instr_defs i = Some r -> result_safe f warm r)
      by (intros; eapply safe_def; eauto);
    assert (NEXT: forall next, In next (successors_instr i) -> outside f warm next)
      by (intros; eapply outside_successor; eauto)
  end.
Lemma step_simulation_ready:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', ready_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try AT.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Inop; eauto.
    constructor; auto. apply NEXT; simpl; auto.
  - inv SPEC.
    + simpl Experimental.map_successors in CODE.
      econstructor; split. eapply exec_Iop; eauto.
      rewrite (regs_match_list ge f warm _ rs trs args REGS) by (intros; apply USES; auto).
      rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
      constructor; auto. apply regs_match_set; eauto. apply NEXT; simpl; auto.
    + match goal with C: chosen f = Some ?b |- _ =>
        pose proof (chosen_sound f b C) as VALID;
        pose proof (proj2 REGS) as TEMP; rewrite C in TEMP end.
      rewrite (@op_depends_on_memory_correct _ _ _ _ _ _ m Mem.empty (valid_memory _ _ VALID)) in H0.
      rewrite H0 in TEMP. inv TEMP.
      econstructor; split. eapply exec_Iop; eauto. simpl; reflexivity.
      constructor; auto. apply regs_match_set; eauto. apply NEXT; simpl; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Iload; eauto.
    rewrite (regs_match_list ge f warm _ rs trs args REGS) by (intros; apply USES; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    constructor; auto. apply regs_match_set; eauto. apply NEXT; simpl; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Istore; eauto.
    rewrite (regs_match_list ge f warm _ rs trs args REGS) by (intros; apply USES; simpl; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    rewrite (proj1 REGS) by (apply USES; simpl; auto). eauto.
    constructor; auto. apply NEXT; simpl; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite (proj1 REGS) by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. eapply exec_Icall; eauto. apply sig_preserved.
    rewrite (regs_match_list ge f warm _ rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor. constructor; auto. constructor; auto. apply NEXT; simpl; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite (proj1 REGS) by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. eapply exec_Itailcall; eauto. apply sig_preserved.
    rewrite transf_function_stacksize; eauto.
    rewrite (regs_match_list ge f warm _ rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply builtin_args_regs; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto. apply regs_match_setres; auto. destruct res; simpl; auto.
    apply NEXT; simpl; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Icond; eauto.
    rewrite (regs_match_list ge f warm _ rs trs args REGS) by (intros; apply USES; simpl; auto). eauto.
    replace (if b then label f warm ifso else label f warm ifnot)
      with (label f warm (if b then ifso else ifnot)) by (destruct b; reflexivity).
    constructor; auto. apply NEXT; simpl; destruct b; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Ijumptable; eauto.
    rewrite (proj1 REGS) by (apply USES; simpl; auto). eauto.
    rewrite list_nth_z_map, H1; simpl; eauto.
    constructor; auto. apply NEXT; simpl. eapply list_nth_z_in; eauto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Ireturn; eauto.
    rewrite transf_function_stacksize; eauto.
    destruct or; simpl. rewrite (proj1 REGS) by (apply USES; simpl; auto). constructor; auto.
    constructor; auto.
  - simpl. econstructor; split. eapply exec_function_internal;
      rewrite ?transf_function_sig, ?transf_function_stacksize; eauto.
    rewrite transf_function_entry,transf_function_params.
    eapply match_regular_states with (warm := false); auto.
    apply regs_match_cold. apply outside_cold.
  - econstructor; split. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved. constructor; auto.
  - inv STACKS. inv H1. econstructor; split. eapply exec_return; eauto.
    constructor; auto. apply regs_match_set; auto.
Qed.
Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', plus RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros S1 t S2 STEP S1' MATCH.
  destruct (prepare_states S1 t S2 STEP S1' MATCH) as (MID & PREP & READY).
  destruct (step_simulation_ready S1 t S2 STEP MID READY) as (FINAL & EXEC & MATCH').
  exists FINAL; split; auto. eapply star_plus_trans with (t1 := E0) (t2 := t).
  exact PREP. apply plus_one; exact EXEC. reflexivity.
Qed.
Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split. econstructor.
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
  eapply function_ptr_translated; eauto. rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.
Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. intros. inv H0. inv H. inv STACKS. constructor. Qed.
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved. eexact transf_initial_states. eexact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.
