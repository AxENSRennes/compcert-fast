(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of automatic correlated-input two-lane SLP. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Builtins0 Builtins1 Builtins Scheduleproof Vectorize.

Record valid_pair (f: function) (plan: vector_pair): Prop := {
  valid_first: (fn_code f)!(first_pc plan) =
    Some (Iop (Oaddimm plan.(first_imm)) (plan.(source_reg) :: nil)
              plan.(first_dst) plan.(second_pc));
  valid_second: (fn_code f)!(second_pc plan) =
    Some (Iop (Oaddimm plan.(second_imm)) (plan.(source_reg) :: nil)
              plan.(second_dst) plan.(after_pc));
  different_pcs: plan.(first_pc) <> plan.(second_pc);
  safe_entry: f.(fn_entrypoint) <> plan.(second_pc);
  source_not_first_dst: plan.(first_dst) <> plan.(source_reg);
  different_dsts: plan.(first_dst) <> plan.(second_dst);
  unique_predecessor: forall pc instr,
    f.(fn_code)!pc = Some instr -> In plan.(second_pc) (successors_instr instr) ->
    pc = plan.(first_pc)
}.

Lemma validate_candidate_sound:
  forall f a b plan, validate_candidate f a b = Some plan -> valid_pair f plan.
Proof.
  unfold validate_candidate; intros f a b plan.
  destruct f.(fn_code)!a as [ia|] eqn:FIRST; try discriminate.
  destruct ia; try discriminate. destruct o; try discriminate.
  destruct l as [|ra tail]; try discriminate. destruct tail; try discriminate.
  destruct f.(fn_code)!b as [ib|] eqn:SECOND; try discriminate.
  destruct ib; try discriminate. destruct o; try discriminate.
  destruct l as [|rb tail]; try discriminate. destruct tail; try discriminate.
  destruct (peq n b); try discriminate. subst n.
  destruct (peq ra rb); try discriminate. subst rb.
  destruct (peq a b); try discriminate.
  destruct (peq (fn_entrypoint f) b); try discriminate.
  destruct (peq r ra); try discriminate.
  destruct (peq r r0); try discriminate.
  destruct (Schedule.predecessor_check f a b) eqn:PRED; try discriminate.
  intro EQ; inv EQ. constructor; simpl; auto.
  eapply Scheduleproof.predecessor_check_sound; eauto.
Qed.

Lemma find_candidate_sound:
  forall f items plan, find_candidate f items = Some plan -> valid_pair f plan.
Proof.
  induction items as [|[pc i] rest IH]; simpl; intros; try discriminate.
  destruct i; eauto. destruct o; eauto.
  destruct l as [|argx tail]; eauto. destruct tail; eauto.
  destruct (validate_candidate f pc n) eqn:VAL; eauto.
  inv H. eapply validate_candidate_sound; eauto.
Qed.
Lemma selected_pair_sound:
  forall f plan, selected_pair f = Some plan -> valid_pair f plan.
Proof.
  unfold selected_pair; intros. destruct (Nat.leb _ _); try discriminate.
  eapply find_candidate_sound; eauto.
Qed.

Definition regs_match (f: function) (rs trs: regset): Prop :=
  forall r, Ple r (max_reg_function f) -> trs#r = rs#r.
Lemma regs_match_refl: forall f rs, regs_match f rs rs.
Proof. red; auto. Qed.
Lemma regs_match_list:
  forall f rs trs args, regs_match f rs trs ->
  (forall r, In r args -> Ple r (max_reg_function f)) -> trs##args = rs##args.
Proof. intros; apply list_map_exten; intros; symmetry; auto. Qed.
Lemma regs_match_set:
  forall f rs trs r v, regs_match f rs trs ->
  regs_match f (rs#r <- v) (trs#r <- v).
Proof.
  red; intros. rewrite !Regmap.gsspec. destruct (peq r0 r); auto.
Qed.
Lemma regs_match_setres:
  forall f rs trs res v, regs_match f rs trs ->
  regs_match f (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto using regs_match_set. Qed.
Lemma regs_match_fresh:
  forall f rs trs r v, regs_match f rs trs -> Plt (max_reg_function f) r ->
  regs_match f rs (trs#r <- v).
Proof. red; intros. rewrite Regmap.gso by extlia. auto. Qed.

Lemma fresh_regs:
  forall f,
  Plt (max_reg_function f) (input_reg f) /\
  Plt (max_reg_function f) (constant_reg f) /\
  Plt (max_reg_function f) (result_reg f) /\
  input_reg f <> constant_reg f /\ input_reg f <> result_reg f /\
  constant_reg f <> result_reg f.
Proof. unfold result_reg, constant_reg, input_reg; intros; repeat split; extlia. Qed.
Lemma fresh_nodes:
  forall f,
  Plt (max_pc_function f) (constant_pc f) /\
  Plt (max_pc_function f) (builtin_pc f) /\
  Plt (max_pc_function f) (extract_pc f) /\
  constant_pc f <> builtin_pc f /\ constant_pc f <> extract_pc f /\
  builtin_pc f <> extract_pc f.
Proof. unfold extract_pc, builtin_pc, constant_pc; intros; repeat split; extlia. Qed.

Definition packed_result (v: val) (n1 n2: int): val :=
  match v with
  | Vint n => Vlong (packed_u32x2 Int.add (Int64.ofwords n n) (Int64.ofwords n2 n1))
  | _ => Vundef
  end.
Lemma packed_result_low:
  forall v n1 n2, Val.loword (packed_result v n1 n2) = Val.add v (Vint n1).
Proof.
  intros. destruct v; simpl; try reflexivity.
  unfold packed_u32x2. rewrite !Int64.lo_ofwords. reflexivity.
Qed.
Lemma packed_result_high:
  forall v n1 n2, Val.hiword (packed_result v n1 n2) = Val.add v (Vint n2).
Proof.
  intros. destruct v; simpl; try reflexivity.
  unfold packed_u32x2. rewrite !Int64.hi_ofwords. reflexivity.
Qed.
Lemma packed_builtin_correct:
  forall ge v n1 n2 m,
  external_call packed_builtin ge
    (Val.longofwords v v :: Vlong (Int64.ofwords n2 n1) :: nil)
    m E0 (packed_result v n1 n2) m.
Proof.
  intros. change (known_builtin_sem (BI_platform BI_neon_add_u32x2) ge
    (Val.longofwords v v :: Vlong (Int64.ofwords n2 n1) :: nil) m E0 (packed_result v n1 n2) m).
  constructor. destruct v; reflexivity.
Qed.

Lemma metadata_preserved:
  forall f,
  fn_sig (transf_function f) = fn_sig f /\
  fn_stacksize (transf_function f) = fn_stacksize f /\
  fn_params (transf_function f) = fn_params f /\
  fn_entrypoint (transf_function f) = fn_entrypoint f.
Proof. intros; unfold transf_function; destruct (selected_pair f); simpl; tauto. Qed.
Definition safe_pc (f: function) (pc: node): Prop :=
  match selected_pair f with Some plan => pc <> plan.(second_pc) | None => True end.
Lemma entry_safe: forall f, safe_pc f f.(fn_entrypoint).
Proof.
  unfold safe_pc; intros. destruct (selected_pair f) as [plan|] eqn:SELECT; auto.
  eapply safe_entry. eapply selected_pair_sound; eauto.
Qed.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof. intros; eapply match_transform_program; eauto. Qed.

Lemma selected_bounds:
  forall f plan, selected_pair f = Some plan ->
  Ple plan.(first_pc) (max_pc_function f) /\
  Ple plan.(second_pc) (max_pc_function f) /\
  Ple plan.(source_reg) (max_reg_function f) /\
  Ple plan.(first_dst) (max_reg_function f) /\
  Ple plan.(second_dst) (max_reg_function f).
Proof.
  intros f plan SELECT. pose proof (selected_pair_sound _ _ SELECT) as V.
  pose proof (valid_first _ _ V) as A. pose proof (valid_second _ _ V) as B.
  repeat split.
  - eapply max_pc_function_sound; eauto.
  - eapply max_pc_function_sound; eauto.
  - eapply max_reg_function_use; [exact A|simpl; auto].
  - eapply max_reg_function_def; [exact A|reflexivity].
  - eapply max_reg_function_def; [exact B|reflexivity].
Qed.

Lemma transformed_first:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(first_pc plan) =
    Some (Iop Omakelong (plan.(source_reg) :: plan.(source_reg) :: nil)
               (input_reg f) (constant_pc f)).
Proof. unfold transf_function; intros. rewrite H. simpl. apply PTree.gss. Qed.
Lemma transformed_constant:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(constant_pc f) =
    Some (Iop (Olongconst (packed_constant plan)) nil (constant_reg f) (builtin_pc f)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  unfold transf_function; rewrite SELECT; simpl. rewrite PTree.gso by extlia. apply PTree.gss.
Qed.
Lemma transformed_builtin:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(builtin_pc f) =
    Some (Ibuiltin packed_builtin (BA (input_reg f) :: BA (constant_reg f) :: nil)
               (BR (result_reg f)) (extract_pc f)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  unfold transf_function; rewrite SELECT; simpl. rewrite !PTree.gso by extlia. apply PTree.gss.
Qed.
Lemma transformed_extract:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(extract_pc f) =
    Some (Iop Olowlong (result_reg f :: nil) plan.(first_dst) plan.(second_pc)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  unfold transf_function; rewrite SELECT; simpl. rewrite !PTree.gso by extlia. apply PTree.gss.
Qed.
Lemma transformed_second:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(second_pc plan) =
    Some (Iop Ohighlong (result_reg f :: nil) plan.(second_dst) plan.(after_pc)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  pose proof (different_pcs _ _ (selected_pair_sound _ _ SELECT)).
  unfold transf_function; rewrite SELECT; simpl. rewrite !PTree.gso by extlia. apply PTree.gss.
Qed.

Lemma normal_classification:
  forall f pc, safe_pc f pc ->
  (exists plan, selected_pair f = Some plan /\ pc = plan.(first_pc)) \/
  ((forall instr, f.(fn_code)!pc = Some instr ->
     (fn_code (transf_function f))!pc = Some instr) /\
   forall instr next, f.(fn_code)!pc = Some instr ->
     In next (successors_instr instr) -> safe_pc f next).
Proof.
  intros f pc SAFE. unfold safe_pc in SAFE.
  destruct (selected_pair f) as [plan|] eqn:SELECT.
  - destruct (peq pc plan.(first_pc)).
    + left; eauto.
    + right; split.
      * intros instr GET. pose proof (max_pc_function_sound _ _ _ GET).
        pose proof (fresh_nodes f).
        unfold transf_function; rewrite SELECT; simpl.
        rewrite !PTree.gso by (try extlia; congruence). exact GET.
      * unfold safe_pc; rewrite SELECT. intros instr next GET IN EQ; subst next.
        apply n. eapply unique_predecessor; eauto using selected_pair_sound.
  - right; split.
    + intros. unfold transf_function; rewrite SELECT; auto.
    + unfold safe_pc; rewrite SELECT; auto.
Qed.
Lemma after_safe:
  forall f plan, selected_pair f = Some plan -> safe_pc f plan.(after_pc).
Proof.
  intros f plan SELECT. pose proof (selected_pair_sound _ _ SELECT) as V.
  unfold safe_pc; rewrite SELECT; intro EQ.
  assert (plan.(second_pc) = plan.(first_pc)).
  { eapply unique_predecessor; eauto. apply valid_second; auto. simpl; auto. }
  elim (different_pcs _ _ V). congruence.
Qed.

Section PRESERVATION.
Variables prog tprog: RTL.program.
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
Proof. destruct f; simpl; auto. apply metadata_preserved. Qed.

Lemma builtin_arg_regs:
  forall f rs trs sp m arg v,
  regs_match f rs trs -> eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  (forall r, In r (params_of_builtin_arg arg) -> Ple r (max_reg_function f)) ->
  eval_builtin_arg ge (fun r => trs#r) sp m arg v.
Proof.
  intros f rs trs sp m arg v REGS EV. induction EV; simpl; intros;
  try (constructor; eauto using in_or_app).
  rewrite <- (REGS x) by eauto with coqlib. constructor.
Qed.
Lemma builtin_args_regs:
  forall f rs trs sp m args vl,
  regs_match f rs trs -> eval_builtin_args ge (fun r => rs#r) sp m args vl ->
  (forall r, In r (params_of_builtin_args args) -> Ple r (max_reg_function f)) ->
  eval_builtin_args ge (fun r => trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl REGS EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs, in_or_app.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frame: forall res f sp pc rs trs
      (REGS: regs_match f rs trs) (SAFE: safe_pc f pc),
      match_frames (Stackframe res f sp pc rs) (Stackframe res (transf_function f) sp pc trs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_normal: forall stk f sp pc rs trs m stk'
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match f rs trs)
      (SAFE: safe_pc f pc),
      match_states (State stk f sp pc rs m) (State stk' (transf_function f) sp pc trs m)
  | match_intermediate: forall stk f sp rs trs m stk' plan
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match f rs trs)
      (SELECT: selected_pair f = Some plan),
      match_states
        (State stk f sp plan.(second_pc)
           (rs#(first_dst plan) <- (Val.add (rs#(source_reg plan)) (Vint plan.(first_imm)))) m)
        (State stk' (transf_function f) sp plan.(first_pc) trs m)
  | match_call: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | match_return: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m) (Returnstate stk' v m).

Definition measure (st: RTL.state): nat :=
  match st with
  | State _ f _ pc _ _ =>
      match selected_pair f with Some plan => if peq pc plan.(second_pc) then O else S O | None => S O end
  | _ => S O
  end.

Ltac ORIGINAL_BOUNDS :=
  match goal with
  | GET: (fn_code ?f)!?pc = Some ?i |- _ =>
      assert (USES: forall r, In r (instr_uses i) -> Ple r (max_reg_function f))
        by (intros; eapply max_reg_function_use; eauto)
  end.

Lemma normal_step:
  forall stk f sp pc rs m trace after,
  RTL.step ge (State stk f sp pc rs m) trace after ->
  forall stk' trs, list_forall2 match_frames stk stk' -> regs_match f rs trs -> safe_pc f pc ->
  (exists target, plus RTL.step tge (State stk' (transf_function f) sp pc trs m) trace target /\
     match_states after target) \/
  (measure after < measure (State stk f sp pc rs m) /\ trace = E0 /\
     match_states after (State stk' (transf_function f) sp pc trs m))%nat.
Proof.
  intros stk f sp pc rs m trace after STEP stk' trs STACKS REGS SAFE.
  destruct (normal_classification f pc SAFE) as [[plan [SELECT PC]] | [CODE NEXT]].
  - subst pc. pose proof (selected_pair_sound _ _ SELECT) as VALID.
    pose proof (valid_first _ _ VALID) as FIRST.
    inversion STEP; subst; try congruence.
    match goal with GET: (fn_code f)!(first_pc plan) = Some _ |- _ => rewrite FIRST in GET; inv GET end.
    match goal with E: eval_operation _ _ _ _ _ = Some _ |- _ => simpl in E; inv E end.
    right; split.
    + unfold measure; rewrite SELECT; simpl.
      destruct (peq plan.(second_pc) plan.(second_pc)); try congruence.
      destruct (peq plan.(first_pc) plan.(second_pc)); simpl; try lia.
      elim (different_pcs _ _ VALID); auto.
    + split; auto. econstructor; eauto.
  - inversion STEP; subst; ORIGINAL_BOUNDS.
    + left; econstructor; split. apply plus_one; eapply exec_Inop; eauto.
      constructor; auto. eapply NEXT; eauto; simpl; auto.
    + left; econstructor; split. apply plus_one; eapply exec_Iop; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
      match goal with E: eval_operation ge _ _ _ _ = Some _ |- _ => rewrite <- E end.
      apply eval_operation_preserved; exact symbols_preserved.
      constructor; auto using regs_match_set. eapply NEXT; eauto; simpl; auto.
    + left; econstructor; split. apply plus_one; eapply exec_Iload; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
      match goal with E: eval_addressing ge _ _ _ = Some _ |- _ => rewrite <- E end.
      apply eval_addressing_preserved; exact symbols_preserved.
      constructor; auto using regs_match_set. eapply NEXT; eauto; simpl; auto.
    + left; econstructor; split. apply plus_one; eapply exec_Istore; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto).
      match goal with E: eval_addressing ge _ _ _ = Some _ |- _ => rewrite <- E end.
      apply eval_addressing_preserved; exact symbols_preserved.
      rewrite REGS by (apply USES; simpl; auto). eauto.
      constructor; auto. eapply NEXT; eauto; simpl; auto.
    + assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
      { unfold find_function in *. destruct ros as [r|id].
        rewrite REGS by (apply USES; simpl; auto). apply functions_translated; auto.
        rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
        apply function_ptr_translated; auto. }
      left; econstructor; split. apply plus_one; eapply exec_Icall; eauto.
      apply sig_preserved.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
      constructor. constructor; auto. constructor; auto.
      eapply NEXT; eauto; simpl; auto.
    + assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
      { unfold find_function in *. destruct ros as [r|id].
        rewrite REGS by (apply USES; simpl; auto). apply functions_translated; auto.
        rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
        apply function_ptr_translated; auto. }
      left; econstructor; split. apply plus_one; eapply exec_Itailcall; eauto.
      apply sig_preserved.
      rewrite (proj1 (proj2 (metadata_preserved f))); eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
      constructor; auto.
    + left; econstructor; split. apply plus_one; eapply exec_Ibuiltin; eauto.
      eapply eval_builtin_args_preserved with (ge1:=ge); eauto. exact symbols_preserved.
      eapply builtin_args_regs; eauto.
      eapply external_call_symbols_preserved; eauto; apply senv_preserved.
      constructor; auto using regs_match_setres. eapply NEXT; eauto; simpl; auto.
    + left; econstructor; split. apply plus_one; eapply exec_Icond; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto); eauto.
      constructor; auto. eapply NEXT; eauto; simpl; destruct b; auto.
    + left; econstructor; split. apply plus_one; eapply exec_Ijumptable; eauto.
      rewrite REGS by (apply USES; simpl; auto); eauto.
      constructor; auto. eapply NEXT; eauto; simpl; eapply list_nth_z_in; eauto.
    + left; econstructor; split. apply plus_one; eapply exec_Ireturn; eauto.
      rewrite (proj1 (proj2 (metadata_preserved f))); eauto.
      destruct or; simpl. rewrite REGS by (apply USES; simpl; auto); constructor; auto.
      constructor; auto.
Qed.

Lemma run_vector_pair:
  forall f plan stk sp rs trs m,
  selected_pair f = Some plan -> regs_match f rs trs ->
  exists final_regs,
    plus RTL.step tge (State stk (transf_function f) sp plan.(first_pc) trs m) E0
      (State stk (transf_function f) sp plan.(after_pc) final_regs m) /\
    regs_match f
      ((rs#(first_dst plan) <- (Val.add (rs#(source_reg plan)) (Vint plan.(first_imm))))
          #(second_dst plan) <- (Val.add (rs#(source_reg plan)) (Vint plan.(second_imm))))
      final_regs.
Proof.
  intros f plan stk sp rs trs m SELECT REGS.
  pose proof (selected_bounds _ _ SELECT) as BOUNDS.
  pose proof (fresh_regs f) as FRESH.
  assert (SOURCE: trs#(source_reg plan) = rs#(source_reg plan)) by (apply REGS; tauto).
  set (v := rs#(source_reg plan)).
  set (t0 := trs#(input_reg f) <- (Val.longofwords v v)).
  set (t1 := t0#(constant_reg f) <- (Vlong (packed_constant plan))).
  set (t2 := t1#(result_reg f) <- (packed_result v plan.(first_imm) plan.(second_imm))).
  set (t3 := t2#(first_dst plan) <- (Val.add v (Vint plan.(first_imm)))).
  set (t4 := t3#(second_dst plan) <- (Val.add v (Vint plan.(second_imm)))).
  exists t4; split.
  - eapply plus_left with
        (s2 := State stk (transf_function f) sp (constant_pc f) t0 m) (t1 := E0) (t2 := E0).
    + eapply exec_Iop. eapply transformed_first; eauto.
      simpl. rewrite SOURCE. reflexivity.
    + eapply star_four with
        (s2 := State stk (transf_function f) sp (builtin_pc f) t1 m)
        (s3 := State stk (transf_function f) sp (extract_pc f) t2 m)
        (s4 := State stk (transf_function f) sp plan.(second_pc) t3 m)
        (t1 := E0) (t2 := E0) (t3 := E0) (t4 := E0).
      * eapply exec_Iop. eapply transformed_constant; eauto. reflexivity.
      * eapply exec_Ibuiltin with
          (res := BR (result_reg f))
          (vres := packed_result v plan.(first_imm) plan.(second_imm))
          (vargs := Val.longofwords v v :: Vlong (packed_constant plan) :: nil).
        eapply transformed_builtin; eauto.
        assert (A1: t1#(input_reg f) = Val.longofwords v v).
        { unfold t1, t0. rewrite Regmap.gso by extlia. apply Regmap.gss. }
        assert (A2: t1#(constant_reg f) = Vlong (packed_constant plan)).
        { unfold t1; apply Regmap.gss. }
        unfold eval_builtin_args. constructor. rewrite <- A1; constructor.
        constructor. rewrite <- A2; constructor. constructor.
        exact (packed_builtin_correct tge v plan.(first_imm) plan.(second_imm) m).
      * eapply exec_Iop. eapply transformed_extract; eauto.
        simpl. unfold t2. rewrite Regmap.gss. rewrite packed_result_low. reflexivity.
      * eapply exec_Iop. eapply transformed_second; eauto.
        simpl. unfold t3, t2. rewrite Regmap.gso by extlia. rewrite Regmap.gss.
        rewrite packed_result_high. reflexivity.
      * reflexivity.
    + reflexivity.
  - unfold t4, t3. apply regs_match_set. apply regs_match_set.
    unfold t2, t1, t0. repeat apply regs_match_fresh; tauto.
Qed.

Lemma intermediate_step:
  forall stk f sp rs trs m plan trace after,
  selected_pair f = Some plan -> regs_match f rs trs ->
  RTL.step ge
    (State stk f sp plan.(second_pc)
      (rs#(first_dst plan) <- (Val.add (rs#(source_reg plan)) (Vint plan.(first_imm)))) m)
    trace after ->
  forall stk', list_forall2 match_frames stk stk' ->
  exists target, plus RTL.step tge (State stk' (transf_function f) sp plan.(first_pc) trs m)
                   trace target /\ match_states after target.
Proof.
  intros stk f sp rs trs m plan trace after SELECT REGS STEP stk' STACKS.
  pose proof (selected_pair_sound _ _ SELECT) as VALID.
  pose proof (valid_second _ _ VALID) as SECOND.
  inversion STEP; subst; try congruence.
  match goal with GET: (fn_code f)!(second_pc plan) = Some _ |- _ => rewrite SECOND in GET; inv GET end.
  pose proof (source_not_first_dst _ _ VALID) as NE.
  match goal with E: eval_operation _ _ _ _ _ = Some _ |- _ =>
    simpl in E; rewrite Regmap.gso in E by congruence; inv E end.
  destruct (run_vector_pair f plan stk' sp rs trs m SELECT REGS) as [final_regs [RUN MATCH]].
  econstructor; split. exact RUN. constructor; auto. eapply after_safe; eauto.
Qed.

Lemma step_simulation:
  forall source trace after, RTL.step ge source trace after ->
  forall target, match_states source target ->
  (exists target_after, plus RTL.step tge target trace target_after /\ match_states after target_after) \/
  (measure after < measure source /\ trace = E0 /\ match_states after target)%nat.
Proof.
  intros source trace after STEP target MATCH. inv MATCH.
  - eapply normal_step; eauto.
  - left. eapply intermediate_step; eauto.
  - inversion STEP; subst.
    + left. destruct (metadata_preserved f) as [SIG [STACK [PARAM ENTRY]]].
      exists (State stk' (transf_function f) (Vptr stk0 Ptrofs.zero)
                    (fn_entrypoint f) (init_regs args (fn_params f)) m'); split.
      * apply plus_one.
        assert (RUN: RTL.step tge (Callstate stk' (Internal (transf_function f)) args m)
          E0 (State stk' (transf_function f) (Vptr stk0 Ptrofs.zero)
            (fn_entrypoint (transf_function f)) (init_regs args (fn_params (transf_function f))) m')).
        { eapply exec_function_internal; rewrite ?SIG, ?STACK; eauto. }
        rewrite ENTRY, PARAM in RUN. exact RUN.
      * constructor; auto using regs_match_refl, entry_safe.
    + left; econstructor; split. apply plus_one; eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto; apply senv_preserved.
      constructor; auto.
  - inversion STEP; subst. inv STACKS. inv H1.
    left; econstructor; split. apply plus_one; eapply exec_return; eauto.
    constructor; auto using regs_match_set.
Qed.
Lemma transf_initial_states:
  forall source, RTL.initial_state prog source ->
  exists target, RTL.initial_state tprog target /\ match_states source target.
Proof.
  intros; inv H. econstructor; split. econstructor.
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite symbols_preserved; rewrite (match_program_main TRANSL); eauto.
  eapply function_ptr_translated; eauto. rewrite <- H3; apply sig_preserved.
  constructor; constructor.
Qed.
Lemma transf_final_states:
  forall source target result, match_states source target -> RTL.final_state source result ->
  RTL.final_state target result.
Proof. intros; inv H0; inv H; inv STACKS; constructor. Qed.
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved. exact transf_initial_states. exact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.
