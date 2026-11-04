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

(** Correctness of modular induction strength reduction. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Experimental Experimentalproof StrengthReduce.

Lemma choose_factor_valid:
  forall items f ind step c, choose_factor f ind step items = Some c -> valid f c = true.
Proof.
  induction items as [|[pc i] rest IH]; simpl; intros; try discriminate.
  destruct i; try solve [eapply IH; eauto].
  destruct o; try solve [eapply IH; eauto].
  destruct l as [|a [|b [|extra tail]]]; try solve [eapply IH; eauto].
  destruct (peq a ind); try solve [eapply IH; eauto].
  destruct (valid f (mkrecurrence ind b step)) eqn:V.
  inv H; auto. eapply IH; eauto.
Qed.
Lemma choose_update_valid:
  forall items fuel f c, choose_update f fuel items = Some c -> valid f c = true.
Proof.
  induction items as [|[pc i] rest IH]; destruct fuel; simpl; intros; try discriminate.
  destruct i; try solve [eapply IH; eauto].
  destruct o; try solve [eapply IH; eauto].
  destruct l as [|a [|extra tail]]; try solve [eapply IH; eauto].
  destruct (peq a r); try solve [eapply IH; eauto].
  destruct (HoistConst.cyclic _ _ _); try solve [eapply IH; eauto].
  destruct (choose_factor f a n0 (PTree.elements (fn_code f))) eqn:C.
  inv H. eapply choose_factor_valid; eauto. eapply IH; eauto.
Qed.
Lemma chosen_valid: forall f c, chosen f = Some c -> valid f c = true.
Proof.
  unfold chosen; intros. destruct (Nat.leb _ _); try discriminate.
  eapply choose_update_valid; eauto.
Qed.
Lemma valid_properties:
  forall f c, valid f c = true ->
  induction_reg c <> factor_reg c /\
  Plt (induction_reg c) (fresh_acc f) /\ Plt (factor_reg c) (fresh_acc f) /\
  forall pc i, (fn_code f)!pc = Some i -> allowed_definition c i = true.
Proof.
  unfold valid; intros f c. destruct (peq _ _); try discriminate.
  destruct (plt _ _); try discriminate. destruct (plt _ _); try discriminate.
  intros V. repeat split; auto. intros pc i GET.
  apply forallb_forall with (x:=(pc,i)) in V; simpl in V; auto.
  apply PTree.elements_correct; auto.
Qed.
Lemma allowed_cases:
  forall c i, allowed_definition c i = true ->
  (forall dst, instr_defs i = Some dst -> dst <> induction_reg c /\ dst <> factor_reg c) \/
  (exists n s, i = Iop (Ointconst n) nil (induction_reg c) s) \/
  (exists s, i = Iop (Oaddimm (induction_step c)) (induction_reg c :: nil) (induction_reg c) s) \/
  (exists n s, i = Iop (Ointconst n) nil (factor_reg c) s).
Proof.
  intros c i A. unfold allowed_definition in A.
  destruct (instr_defs i) as [dst|] eqn:D.
  2: left; intros; congruence.
  destruct (peq dst (induction_reg c)) as [E|NE].
  - subst dst. destruct i; simpl in D; try discriminate; try discriminate A.
    inv D. destruct o; try discriminate A.
    + destruct l; try discriminate A. right; left; eauto.
    + destruct l as [|r [|x tail]]; try discriminate A.
      destruct (peq r (induction_reg c)); try discriminate A. subst r.
      apply Int.same_if_eq in A. subst n0. right; right; left; eauto.
  - destruct (peq dst (factor_reg c)) as [E|NK].
    + subst dst. destruct i; simpl in D; try discriminate; try discriminate A.
      inv D. destruct o; try discriminate A. destruct l; try discriminate A.
      right; right; right; eauto.
    + left; intros r R; inv R; auto.
Qed.
Lemma neutral_classify:
  forall c i,
  (forall dst, instr_defs i = Some dst -> dst <> induction_reg c /\ dst <> factor_reg c) ->
  classify c i = Default \/
  exists dst s, i = Iop Omul (induction_reg c :: factor_reg c :: nil) dst s /\ classify c i = Multiply.
Proof.
  intros c i SAFE. destruct i; try (left; reflexivity).
  destruct (SAFE r eq_refl) as [NI NK]. unfold classify.
  destruct (peq r (induction_reg c)); try contradiction.
  destruct (peq r (factor_reg c)); try contradiction.
  destruct o; try (left; reflexivity).
  destruct l as [|a [|b [|extra tail]]]; try (left; reflexivity).
  destruct (peq a (induction_reg c)); try (left; reflexivity).
  destruct (peq b (factor_reg c)); try (left; reflexivity).
  subst a b. right. eauto.
Qed.
Lemma classify_advance:
  forall c s, classify c (Iop (Oaddimm (induction_step c)) (induction_reg c :: nil) (induction_reg c) s) = Advance.
Proof. intros; simpl. destruct (peq _ _); congruence. Qed.
Lemma classify_reset_ind:
  forall c n s, classify c (Iop (Ointconst n) nil (induction_reg c) s) = ResetInd.
Proof. intros; simpl. destruct (peq _ _); congruence. Qed.
Lemma classify_reset_factor:
  forall c n s, induction_reg c <> factor_reg c ->
  classify c (Iop (Ointconst n) nil (factor_reg c) s) = ResetFactor.
Proof. intros; simpl. destruct (peq _ _); try congruence. destruct (peq _ _); congruence. Qed.

Lemma fresh_acc_use:
  forall f pc i r, (fn_code f)!pc = Some i -> In r (instr_uses i) -> Plt r (fresh_acc f).
Proof. unfold fresh_acc; intros; generalize (max_reg_function_use _ _ _ _ H H0); extlia. Qed.
Lemma fresh_acc_def:
  forall f pc i r, (fn_code f)!pc = Some i -> instr_defs i = Some r -> r <> fresh_acc f.
Proof. unfold fresh_acc; intros; generalize (max_reg_function_def _ _ _ _ H H0); extlia. Qed.
Lemma fresh_delta_def:
  forall f pc i r, (fn_code f)!pc = Some i -> instr_defs i = Some r -> r <> fresh_delta f.
Proof. unfold fresh_delta,fresh_acc; intros; generalize (max_reg_function_def _ _ _ _ H H0); extlia. Qed.
Lemma transf_function_sig: forall f, fn_sig (transf_function f) = fn_sig f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_params: forall f, fn_params (transf_function f) = fn_params f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_stacksize: forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma code_base:
  forall f c pc i, chosen f = Some c -> (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!(base pc) = Some (first_instr f c pc i).
Proof. intros. unfold transf_function; rewrite H. simpl. unfold base. rewrite !PTree.gNode,PTree.gmap,H0; reflexivity. Qed.
Lemma code_next:
  forall f c pc i, chosen f = Some c -> (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!(after1 pc) = Some (next_instr f c pc i).
Proof. intros. unfold transf_function; rewrite H. simpl. unfold after1. rewrite !PTree.gNode,PTree.gmap,H0; reflexivity. Qed.
Lemma code_last:
  forall f c pc i, chosen f = Some c -> (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!(after2 pc) = Some (last_instr f c pc i).
Proof. intros. unfold transf_function; rewrite H. simpl. unfold after2. rewrite !PTree.gNode,PTree.gmap,H0; reflexivity. Qed.

Definition definition_safe (f: function) (dst: reg): Prop :=
  match chosen f with Some c => dst <> induction_reg c /\ dst <> factor_reg c | None => True end.
Inductive instr_spec (f: function) (pc: node): instruction -> instruction -> Prop :=
 | spec_default: forall i,
     (forall dst, instr_defs i = Some dst -> definition_safe f dst) ->
     instr_spec f pc i (Experimental.map_successors (label f) i)
 | spec_multiply: forall c dst s,
     chosen f = Some c -> dst <> induction_reg c -> dst <> factor_reg c ->
     instr_spec f pc (Iop Omul (induction_reg c :: factor_reg c :: nil) dst s)
       (Iop Omove (fresh_acc f :: nil) dst (base s))
 | spec_advance: forall c s,
     chosen f = Some c ->
     instr_spec f pc (Iop (Oaddimm (induction_step c)) (induction_reg c :: nil) (induction_reg c) s)
       (Iop (Oaddimm (induction_step c)) (induction_reg c :: nil) (induction_reg c) (after1 pc))
 | spec_reset_ind: forall c n s,
     chosen f = Some c ->
     instr_spec f pc (Iop (Ointconst n) nil (induction_reg c) s)
       (Iop (Ointconst n) nil (induction_reg c) (after1 pc))
 | spec_reset_factor: forall c n s,
     chosen f = Some c ->
     instr_spec f pc (Iop (Ointconst n) nil (factor_reg c) s)
       (Iop (Ointconst n) nil (factor_reg c) (after1 pc)).
Lemma transf_function_at:
  forall f pc i, (fn_code f)!pc = Some i ->
  exists ti, (fn_code (transf_function f))!(label f pc) = Some ti /\ instr_spec f pc i ti.
Proof.
  intros f pc i GET. unfold label. destruct (chosen f) as [c|] eqn:C.
  - exists (first_instr f c pc i). split; eauto using code_base.
    destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
    destruct (allowed_cases c i (ALL _ _ GET)) as [SAFE|[(n&s&E)|[(s&E)|(n&s&E)]]].
    + destruct (neutral_classify c i SAFE) as [D|(dst&s&E&D)].
      * unfold first_instr; rewrite D. replace base with (label f).
        constructor. unfold definition_safe; rewrite C; auto. unfold label; rewrite C; auto.
      * subst i. unfold first_instr; rewrite D. apply spec_multiply; auto; apply SAFE; reflexivity.
    + subst i. unfold first_instr; rewrite classify_reset_ind. constructor; auto.
    + subst i. unfold first_instr; rewrite classify_advance. constructor; auto.
    + subst i. unfold first_instr; rewrite classify_reset_factor by auto. constructor; auto.
  - exists i. split. unfold transf_function; rewrite C; auto.
    replace i with (Experimental.map_successors (label f) i) at 2.
    constructor. unfold definition_safe; rewrite C; auto.
    unfold label; rewrite C; apply Experimentalproof.map_successors_id.
Qed.

Definition regs_match (f: function) (rs trs: regset): Prop :=
  (forall r, Plt r (fresh_acc f) -> trs#r = rs#r) /\
  (forall c, chosen f = Some c ->
    trs#(fresh_acc f) = Val.mul rs#(induction_reg c) rs#(factor_reg c) /\
    trs#(fresh_delta f) = Val.mul (Vint (induction_step c)) rs#(factor_reg c)).
Lemma regs_match_list:
  forall f rs trs rl, regs_match f rs trs ->
  (forall r, In r rl -> Plt r (fresh_acc f)) -> trs##rl = rs##rl.
Proof. intros f rs trs rl [A B] C. apply list_map_exten. intros; symmetry; apply A; auto. Qed.
Lemma fresh_distinct: forall f, fresh_acc f <> fresh_delta f.
Proof. unfold fresh_delta; intros; extlia. Qed.
Lemma regs_agree_set:
  forall f (rs trs: regset) r v,
  (forall x, Plt x (fresh_acc f) -> trs#x = rs#x) ->
  (forall x, Plt x (fresh_acc f) -> (trs#r <- v)#x = (rs#r <- v)#x).
Proof. intros. rewrite !Regmap.gsspec; destruct (peq x r); auto. Qed.
Lemma regs_match_set_other:
  forall f rs trs r v, regs_match f rs trs -> definition_safe f r ->
  r <> fresh_acc f -> r <> fresh_delta f -> regs_match f (rs#r <- v) (trs#r <- v).
Proof.
  intros f rs trs r v [A B] SAFE NA ND. split; eauto using regs_agree_set.
  intros c C. specialize (B c C). unfold definition_safe in SAFE; rewrite C in SAFE.
  destruct SAFE as [NI NK]. rewrite !Regmap.gso by congruence. exact B.
Qed.
Lemma regs_match_setres:
  forall f rs trs res v, regs_match f rs trs ->
  (match res with BR r => definition_safe f r /\ r <> fresh_acc f /\ r <> fresh_delta f | _ => True end) ->
  regs_match f (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto. apply regs_match_set_other; tauto. Qed.
Lemma regs_match_reset_ind:
  forall f c rs trs n, chosen f = Some c -> regs_match f rs trs ->
  regs_match f (rs#(induction_reg c) <- (Vint n))
    ((trs#(induction_reg c) <- (Vint n))#(fresh_acc f) <- (Val.mul (Vint n) rs#(factor_reg c))).
Proof.
  intros f c rs trs n C [A B].
  destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
  split.
  - intros r LT. rewrite Regmap.gso by extlia. eapply regs_agree_set; eauto.
  - intros c' C'; assert (c'=c) by congruence; subst c'.
    destruct (B c C) as [ACC DELTA]. split.
    + rewrite Regmap.gss, Regmap.gss, Regmap.gso by congruence. reflexivity.
    + rewrite !Regmap.gso by (unfold fresh_delta; extlia || congruence).
      exact DELTA.
Qed.
Lemma regs_match_advance:
  forall f c rs trs, chosen f = Some c -> regs_match f rs trs ->
  let v := Val.add rs#(induction_reg c) (Vint (induction_step c)) in
  regs_match f (rs#(induction_reg c) <- v)
    ((trs#(induction_reg c) <- v)#(fresh_acc f) <- (Val.mul v rs#(factor_reg c))).
Proof.
  intros f c rs trs C [A B] v.
  destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
  split.
  - intros r LT. rewrite Regmap.gso by extlia. eapply regs_agree_set; eauto.
  - intros c' C'; assert (c'=c) by congruence; subst c'.
    destruct (B c C) as [ACC DELTA]. split.
    + rewrite Regmap.gss, Regmap.gss, Regmap.gso by congruence. reflexivity.
    + rewrite !Regmap.gso by (unfold fresh_delta; extlia || congruence). exact DELTA.
Qed.
Lemma regs_match_reset_factor:
  forall f c rs trs n, chosen f = Some c -> regs_match f rs trs ->
  regs_match f (rs#(factor_reg c) <- (Vint n))
    (((trs#(factor_reg c) <- (Vint n))#(fresh_delta f) <- (Vint (Int.mul (induction_step c) n)))
       #(fresh_acc f) <- (Val.mul rs#(induction_reg c) (Vint n))).
Proof.
  intros f c rs trs n C [A B].
  destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
  split.
  - intros r LT. rewrite !Regmap.gso by (unfold fresh_delta; extlia). eapply regs_agree_set; eauto.
  - intros c' C'; assert (c'=c) by congruence; subst c'. split.
    + rewrite Regmap.gss, Regmap.gss, Regmap.gso by congruence. reflexivity.
    + rewrite Regmap.gso by (pose proof (fresh_distinct f); congruence). rewrite !Regmap.gss. reflexivity.
Qed.
Lemma regs_match_initialize:
  forall f c rs, chosen f = Some c ->
  regs_match f rs
    ((rs#(fresh_delta f) <- (Val.mul (Vint (induction_step c)) rs#(factor_reg c)))
      #(fresh_acc f) <- (Val.mul rs#(induction_reg c) rs#(factor_reg c))).
Proof.
  intros f c rs C. split.
  - intros r LT. rewrite !Regmap.gso by (unfold fresh_delta; extlia). reflexivity.
  - intros c' C'; assert (c'=c) by congruence; subst c'. split. apply Regmap.gss.
    rewrite Regmap.gso by (pose proof (fresh_distinct f); congruence). apply Regmap.gss.
Qed.

Definition match_prog (p tp: program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Lemma transf_program_match: forall p, match_prog p (transf_program p).
Proof. intros. eapply match_transform_program; eauto. Qed.
Global Instance TransfStrengthReduceLink: TransfLink match_prog := TransfTotalLink transf_function.
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
Lemma symbols_preserved: forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig (transf_fundef f) = funsig f.
Proof. destruct f; simpl; auto. apply transf_function_sig. Qed.
Lemma builtin_arg_regs:
  forall f rs trs sp m arg v, regs_match f rs trs ->
  eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  (forall r, In r (params_of_builtin_arg arg) -> Plt r (fresh_acc f)) ->
  eval_builtin_arg ge (fun r => trs#r) sp m arg v.
Proof.
  intros f rs trs sp m arg v REGS EV. induction EV; simpl; intros;
  try (constructor; eauto using in_or_app).
  rewrite <- (proj1 REGS x) by eauto with coqlib. constructor.
Qed.
Lemma builtin_args_regs:
  forall f rs trs sp m args vl, regs_match f rs trs ->
  eval_builtin_args ge (fun r => rs#r) sp m args vl ->
  (forall r, In r (params_of_builtin_args args) -> Plt r (fresh_acc f)) ->
  eval_builtin_args ge (fun r => trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl REGS EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs, in_or_app.
Qed.
Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs trs
      (REGS: regs_match f rs trs) (RES: definition_safe f res)
      (ACC: res <> fresh_acc f) (DELTA: res <> fresh_delta f),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp (label f pc) trs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs trs m stk'
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match f rs trs),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (label f pc) trs m)
  | match_callstates: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | match_returnstates: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m) (Returnstate stk' v m).
Ltac AT :=
  match goal with
  | [ A: (fn_code ?f)!?pc = Some ?i |- _ ] =>
    destruct (transf_function_at f pc i A) as [ti [CODE SPEC]];
    assert (USES: forall r, In r (instr_uses i) -> Plt r (fresh_acc f))
      by (intros; eapply fresh_acc_use; eauto);
    assert (DEFS: forall r, instr_defs i = Some r -> r <> fresh_acc f /\ r <> fresh_delta f)
      by (intros; split; eauto using fresh_acc_def,fresh_delta_def);
    assert (DEFA: forall r, instr_defs i = Some r -> r <> fresh_acc f)
      by (intros; eapply fresh_acc_def; eauto);
    assert (DEFD: forall r, instr_defs i = Some r -> r <> fresh_delta f)
      by (intros; eapply fresh_delta_def; eauto)
  end.
Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', plus RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try AT.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Inop; eauto. constructor; auto.
  - inversion SPEC as [i' SAFE |cand dst succ C NI NK |cand succ C |cand n succ C|cand n succ C]; subst.
    + simpl Experimental.map_successors in CODE.
      econstructor; split. apply plus_one. eapply exec_Iop; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
      rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
      constructor; auto. apply regs_match_set_other; eauto; try tauto.
    + simpl in H0. inv H0.
      econstructor; split. apply plus_one. eapply exec_Iop; eauto.
      simpl. rewrite (proj1 (proj2 REGS cand C)); reflexivity.
      replace (base pc') with (label f pc') by (unfold label; rewrite C; auto).
      constructor; auto. apply regs_match_set_other; eauto; try tauto.
      unfold definition_safe; rewrite C; auto.
    + simpl in H0. inv H0.
      destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
      destruct (proj2 REGS cand C) as [ACC DELTA].
      exists (State stk' (transf_function f) sp (base pc')
        ((trs#(induction_reg cand) <- (Val.add rs#(induction_reg cand) (Vint (induction_step cand))))
         #(fresh_acc f) <- (Val.mul (Val.add rs#(induction_reg cand) (Vint (induction_step cand))) rs#(factor_reg cand))) m).
      split.
      * eapply plus_two.
        eapply exec_Iop; eauto. simpl. rewrite (proj1 REGS _ IND). reflexivity.
        eapply exec_Iop.
        eapply eq_trans. eapply code_next; eauto. unfold next_instr; rewrite classify_advance; reflexivity.
        simpl. rewrite !Regmap.gso by (unfold fresh_delta; extlia). rewrite ACC,DELTA,<- Val.mul_add_distr_l. reflexivity.
        traceEq.
      * replace (base pc') with (label f pc') by (unfold label; rewrite C; auto).
        constructor; auto. apply regs_match_advance; auto.
    + simpl in H0. inv H0.
      destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
      exists (State stk' (transf_function f) sp (base pc')
        ((trs#(induction_reg cand) <- (Vint n))#(fresh_acc f) <- (Val.mul (Vint n) rs#(factor_reg cand))) m).
      split.
      * eapply plus_two.
        eapply exec_Iop; eauto. reflexivity.
        eapply exec_Iop.
        eapply eq_trans. eapply code_next; eauto. unfold next_instr; rewrite classify_reset_ind; reflexivity.
        simpl. rewrite Regmap.gss,Regmap.gso by congruence. rewrite (proj1 REGS _ FAC). reflexivity.
        traceEq.
      * replace (base pc') with (label f pc') by (unfold label; rewrite C; auto).
        constructor; auto. apply regs_match_reset_ind; auto.
    + simpl in H0. inv H0.
      destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
      exists (State stk' (transf_function f) sp (base pc')
        (((trs#(factor_reg cand) <- (Vint n))#(fresh_delta f) <- (Vint (Int.mul (induction_step cand) n)))
         #(fresh_acc f) <- (Val.mul rs#(induction_reg cand) (Vint n))) m).
      split.
      * eapply plus_three.
        eapply exec_Iop; eauto. reflexivity.
        eapply exec_Iop.
        eapply eq_trans. eapply code_next; eauto. unfold next_instr; rewrite classify_reset_factor by auto; reflexivity.
        reflexivity.
        eapply exec_Iop.
        eapply eq_trans. eapply code_last; eauto. unfold last_instr; rewrite classify_reset_factor by auto; reflexivity.
        simpl. rewrite !Regmap.gso by (unfold fresh_delta; extlia || congruence).
        rewrite Regmap.gss. rewrite (proj1 REGS _ IND). reflexivity.
        traceEq.
      * replace (base pc') with (label f pc') by (unfold label; rewrite C; auto).
        constructor; auto. apply regs_match_reset_factor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Iload; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    constructor; auto. apply regs_match_set_other; eauto; try tauto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Istore; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    rewrite (proj1 REGS) by (apply USES; simpl; auto). eauto.
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite (proj1 REGS) by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. apply plus_one. eapply exec_Icall; eauto. apply sig_preserved.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor. constructor; auto. constructor; eauto; try tauto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite (proj1 REGS) by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. apply plus_one. eapply exec_Itailcall; eauto.
    apply sig_preserved. rewrite transf_function_stacksize; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply builtin_args_regs; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto. apply regs_match_setres; auto. destruct res; simpl; auto; eauto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Icond; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto). eauto.
    replace (if b then label f ifso else label f ifnot) with (label f (if b then ifso else ifnot)) by (destruct b; auto).
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Ijumptable; eauto.
    rewrite (proj1 REGS) by (apply USES; simpl; auto). eauto.
    rewrite list_nth_z_map,H1; simpl; eauto.
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Ireturn; eauto. rewrite transf_function_stacksize; eauto.
    destruct or; simpl. rewrite (proj1 REGS) by (apply USES; simpl; auto). constructor; auto. constructor; auto.
  - destruct (chosen f) as [cand|] eqn:C.
    + destruct (valid_properties _ _ (chosen_valid _ _ C)) as [NE [IND [FAC ALL]]].
      set (rs := init_regs args (fn_params f)).
      exists (State stk' (transf_function f) (Vptr stk Ptrofs.zero) (base (fn_entrypoint f))
        ((rs#(fresh_delta f) <- (Val.mul (Vint (induction_step cand)) rs#(factor_reg cand)))
           #(fresh_acc f) <- (Val.mul rs#(induction_reg cand) rs#(factor_reg cand))) m'). split.
      * eapply plus_left.
        eapply exec_function_internal; rewrite ?transf_function_sig, ?transf_function_stacksize; eauto.
        unfold transf_function; rewrite C. simpl.
        apply plus_star. eapply plus_three.
        eapply exec_Iop. unfold reduced; simpl; rewrite !PTree.gNode; reflexivity. reflexivity.
        eapply exec_Iop. unfold reduced; simpl; rewrite !PTree.gNode; reflexivity. simpl. rewrite Regmap.gss,Regmap.gso by (unfold fresh_delta; extlia).
        reflexivity.
        rewrite Regmap.set2.
        eapply exec_Iop. unfold reduced; simpl; rewrite !PTree.gNode; reflexivity. simpl.
        rewrite !Regmap.gso by (unfold fresh_delta; extlia).
        reflexivity.
        traceEq. traceEq.
      * replace (base (fn_entrypoint f)) with (label f (fn_entrypoint f)) by (unfold label; rewrite C; auto).
        constructor; auto. apply regs_match_initialize; auto.
    + econstructor; split. apply plus_one. eapply exec_function_internal;
        rewrite ?transf_function_sig, ?transf_function_stacksize; eauto.
      assert (ENTRY: fn_entrypoint (transf_function f) = label f (fn_entrypoint f)).
      { unfold transf_function,label; rewrite C; auto. }
      rewrite ENTRY,transf_function_params. constructor; auto. split; auto. intros; congruence.
  - econstructor; split. apply plus_one. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved. constructor; auto.
  - inv STACKS. inv H1. econstructor; split. apply plus_one. eapply exec_return; eauto.
    constructor; auto. apply regs_match_set_other; auto.
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
