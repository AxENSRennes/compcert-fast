(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Delay a selected Clight loop until one or two complete source turns
    have justified a scalar or packed target turn. All delayed steps are
    silent and the finite cursor measure decreases during the delay. *)
Require Import Coqlib AST Integers Values Memory Events Maps Smallstep Globalenvs.
Require Import Ctypes Cop Clight ClightBigstep.
Require Import ArrayPair ArrayPairMatch ArrayPairLocalFacts ArrayPairLocalSource.
Require Import ArrayPairTarget ArrayPairTurn.

Definition temp_agree (p: plan) (le tle: temp_env) : Prop :=
  exists v, tle = PTree.set (scratch p) v le.

Lemma temp_agree_set:
  forall p le tle id v,
  temp_agree p le tle -> scratch p <> id ->
  temp_agree p (PTree.set id v le) (PTree.set id v tle).
Proof.
  intros p le tle id v [old ->] DIFFERENT.
  exists old. apply PTree.extensionality; intro key.
  rewrite !PTree.gsspec. destruct (peq key id), (peq key (scratch p));
    try congruence; reflexivity.
Qed.

Definition init_index (i: ident) : statement := Sset i (sint 0).

Inductive init_cursor (p: plan) (i: ident) (k tk: cont) (le: temp_env)
    : statement -> cont -> statement -> cont -> Prop :=
  | init_outer:
      init_cursor p i k tk le
        (Ssequence (with_skip (init_index i)) (source_loop p)) k
        (Ssequence (with_skip (init_index i)) (target_loop p)) tk
  | init_wrapper:
      init_cursor p i k tk le
        (with_skip (init_index i)) (Kseq (source_loop p) k)
        (with_skip (init_index i)) (Kseq (target_loop p) tk)
  | init_before_set:
      init_cursor p i k tk le
        Sskip (Kseq (init_index i) (Kseq (source_loop p) k))
        Sskip (Kseq (init_index i) (Kseq (target_loop p) tk))
  | init_set:
      init_cursor p i k tk le
        (init_index i) (Kseq (source_loop p) k)
        (init_index i) (Kseq (target_loop p) tk)
  | init_after_set:
      wide_ready p le ->
      init_cursor p i k tk le
        Sskip (Kseq (source_loop p) k)
        Sskip (Kseq (target_loop p) tk).

Inductive loop_history (ge: genv) (p: plan) (e: env)
    (le0: temp_env) (m0: mem) : bool -> temp_env -> mem -> Prop :=
  | history_new: loop_history ge p e le0 m0 true le0 m0
  | history_one: forall le m,
      source_turn ge p e le0 m0 le m ->
      ~ test_value ge e le m (loop_test p) false ->
      loop_history ge p e le0 m0 false le m.

Definition first_cost (p: plan) := cursor_cost (source_first p :: nil).
Definition second_cost (p: plan) := cursor_cost (source_second p :: nil).
Definition loop_cost (p: plan) := S (first_cost p + S (second_cost p)).
Definition history_cost (p: plan) (fresh: bool) :=
  if fresh then S (loop_cost p) else O.

Definition cursor_prefix (ge: genv) (e: env) (le0: temp_env) (m0: mem)
    (initial: statement) (le: temp_env) (m: mem) (work: list statement) : Prop :=
  forall le' m' out, finish_cursor ge e le m work le' m' out ->
    Clight2.exec_stmt ge e le0 m0 initial E0 le' m' out.

Inductive local_match (ge tge: genv) (p: plan) (sf tf: function) (k tk: cont)
    : nat -> state -> state -> Prop :=
  | local_init_cursor: forall i e le tle m s sk ts tsk,
      layout p = Indexed i ->
      init_cursor p i k tk le s sk ts tsk ->
      base_ready p le ->
      temp_agree p le tle ->
      local_match ge tge p sf tf k tk O
        (State sf s sk e le m)
        (State tf ts tsk e tle m)
  | local_loop: forall e le0 tle m0 fresh le m,
      temp_agree p le0 tle ->
      wide_ready p le0 ->
      loop_history ge p e le0 m0 fresh le m ->
      local_match ge tge p sf tf k tk (loop_cost p + history_cost p fresh)%nat
        (State sf (source_loop p) k e le m)
        (State tf (target_loop p) tk e tle m0)
  | local_first: forall e le0 tle m0 fresh le1 m1 s rest le m,
      temp_agree p le0 tle ->
      wide_ready p le0 ->
      loop_history ge p e le0 m0 fresh le1 m1 ->
      forallb plain_statement (s :: rest) = true ->
      cursor_prefix ge e le1 m1 (source_first p) le m (s :: rest) ->
      local_match ge tge p sf tf k tk
        (cursor_cost (s :: rest) + S (second_cost p) + history_cost p fresh)%nat
        (State sf s
          (pending_cont rest (Kloop1 (source_first p) (source_second p) k)) e le m)
        (State tf (target_loop p) tk e tle m0)
  | local_second: forall e le0 tle m0 fresh le1 m1 le2 m2 s rest le m,
      temp_agree p le0 tle ->
      wide_ready p le0 ->
      loop_history ge p e le0 m0 fresh le1 m1 ->
      Clight2.exec_stmt ge e le1 m1 (source_first p) E0 le2 m2 Out_normal ->
      forallb plain_statement (s :: rest) = true ->
      cursor_prefix ge e le2 m2 (source_second p) le m (s :: rest) ->
      local_match ge tge p sf tf k tk
        (cursor_cost (s :: rest) + history_cost p fresh)%nat
        (State sf s
          (pending_cont rest (Kloop2 (source_first p) (source_second p) k)) e le m)
        (State tf (target_loop p) tk e tle m0)
  | local_exit: forall e le tle m,
      temp_agree p le tle ->
      local_match ge tge p sf tf k tk O
        (State sf Sskip k e le m)
        (State tf Sskip tk e tle m).

Lemma local_init:
  forall ge tge p sf tf k e le v m,
  base_ready p le ->
  exists rank, local_match ge tge p sf tf k k rank
    (State sf (source_body p) k e le m)
    (State tf (target_body p) k e (PTree.set (scratch p) v le) m).
Proof.
  intros ge tge p sf tf k e le v m BASE.
  unfold source_body, target_body, with_init.
  destruct (layout p) eqn:LAYOUT.
  - eexists; eapply local_loop; [exists v; reflexivity| |constructor].
    apply wide_ready_narrow. unfold wide; now rewrite LAYOUT.
  - eexists; eapply local_loop; [exists v; reflexivity| |constructor].
    apply wide_ready_narrow. unfold wide; now rewrite LAYOUT.
  - eexists; eapply local_init_cursor;
      [exact LAYOUT|constructor|exact BASE|exists v; reflexivity].
Qed.

Definition cursor_end_dec (s: statement) (rest: list statement)
  : {cursor_end s rest} + {~ cursor_end s rest}.
Proof.
  destruct rest.
  - destruct s; try solve [left; unfold cursor_end; auto];
      right; intros [_ [A|A]]; discriminate.
  - right; intros [A _]; discriminate.
Defined.

Ltac invert_local_step STEP :=
  inversion STEP; subst; cbn [is_call_cont] in *;
    try contradiction; try solve [intuition discriminate].

Lemma local_init_step:
  forall ge tge p sf tf i k tk e le tle m s sk ts tsk t after,
  layout p = Indexed i ->
  init_cursor p i k tk le s sk ts tsk ->
  well_formed p ->
  base_ready p le ->
  temp_agree p le tle ->
  step2 ge (State sf s sk e le m) t after ->
  exists rank target,
    plus step2 tge (State tf ts tsk e tle m) t target /\
    local_match ge tge p sf tf k tk rank after target.
Proof.
  intros ge tge p sf tf i k tk e le tle m s sk ts tsk t after
    LAYOUT CURSOR WF BASE AGREE STEP.
  destruct CURSOR.
  - invert_local_step STEP.
    eexists; eexists; split; [apply plus_one; apply step_seq|].
    eapply local_init_cursor; [exact LAYOUT|constructor|exact BASE|exact AGREE].
  - unfold with_skip in STEP. invert_local_step STEP.
    eexists; eexists; split; [apply plus_one; apply step_seq|].
    eapply local_init_cursor; [exact LAYOUT|constructor|exact BASE|exact AGREE].
  - invert_local_step STEP.
    eexists; eexists; split; [apply plus_one; apply step_skip_seq|].
    eapply local_init_cursor; [exact LAYOUT|constructor|exact BASE|exact AGREE].
  - unfold init_index in STEP. invert_local_step STEP.
    match goal with
    | EV: eval_expr _ _ _ _ (sint 0) _ |- _ =>
        unfold sint in EV; inversion EV; subst; try reject_non_lvalue
    end.
    assert (BASE': base_ready p (PTree.set i (Vint Int.zero) le)).
    { assert (FRESH: i <> pointer p).
      { destruct WF as [_ FRESH]. rewrite LAYOUT in FRESH. exact (proj1 FRESH). }
      now apply (proj2 (base_ready_set_other p le i (Vint Int.zero) FRESH)). }
    eexists; eexists; split.
    + apply plus_one. apply step_set. constructor.
    + eapply local_init_cursor; [exact LAYOUT| |exact BASE'|].
      * constructor. apply wide_ready_init; assumption.
      * apply temp_agree_set; auto using scratch_index.
  - invert_local_step STEP.
    eexists; eexists; split; [apply plus_one; apply step_skip_seq|].
    eapply local_loop; [exact AGREE|assumption|constructor].
Qed.

Lemma prefix_start:
  forall ge e le m s, cursor_prefix ge e le m s le m (s :: nil).
Proof. intros; red; eauto using finish_single. Qed.

Lemma local_step:
  forall ge (tprog: Clight.program) p sf tf k rank s t after target,
  (forall e, blocks_of_env (globalenv tprog) e = blocks_of_env ge e) ->
  (forall id, Genv.find_symbol (globalenv tprog) id = Genv.find_symbol ge id) ->
  well_formed p ->
  is_call_cont k ->
  local_match ge (globalenv tprog) p sf tf k k rank s target ->
  step2 ge s t after ->
  exists rank' target',
    (plus step2 (globalenv tprog) target t target' \/
      (t = E0 /\ target' = target /\ (rank' < rank)%nat)) /\
    (local_match ge (globalenv tprog) p sf tf k k rank' after target' \/
      exists v m, after = Returnstate v k m /\ target' = Returnstate v k m).
Proof.
  intros ge tprog p sf tf k rank s t after target BLOCKS SYMBOLS WF CALL MATCH STEP.
  destruct MATCH as
    [i e le tle m cur sk tcur tsk LAYOUT INIT BASE AGREE
    |e le0 tle m0 fresh le m AGREE READY HISTORY
    |e le0 tle m0 fresh le1 m1 cur rest le m AGREE READY HISTORY PLAIN PREFIX
    |e le0 tle m0 fresh le1 m1 le2 m2 cur rest le m AGREE READY HISTORY FIRST PLAIN PREFIX
    |e le tle m AGREE].
  - destruct (local_init_step ge (globalenv tprog) p sf tf i k k e le tle m
      cur sk tcur tsk t after LAYOUT INIT WF BASE AGREE STEP)
      as [r [st [RUN NEXT]]].
    exists r, st; split; auto.
  - rewrite source_loop_parts in STEP.
    invert_local_step STEP.
    eexists; eexists; split.
    2: {
      left. eapply local_first with (rest := nil); [exact AGREE|exact READY|exact HISTORY| |].
      - cbn [forallb]. rewrite (proj1 (source_plain p)). reflexivity.
      - apply prefix_start.
    }
    right; repeat split; try reflexivity. unfold loop_cost, first_cost; lia.
  - destruct (cursor_end_dec cur rest) as [END|OPEN].
    + destruct END as [-> [-> | ->]]; cbn [pending_cont] in STEP.
      * assert (FIRST : Clight2.exec_stmt ge e le1 m1 (source_first p) E0 le m Out_normal).
        { apply PREFIX. apply finish_skip. repeat split; reflexivity. }
        invert_local_step STEP.
        eexists; eexists; split.
        2: {
          left. eapply local_second with (rest := nil);
            [exact AGREE|exact READY|exact HISTORY|exact FIRST| |].
          - cbn [forallb]. rewrite (proj2 (source_plain p)). reflexivity.
          - apply prefix_start.
        }
        right; repeat split; try reflexivity. unfold second_cost; cbn [cursor_cost statement_cost]; lia.
      * assert (BREAK : Clight2.exec_stmt ge e le1 m1 (source_first p) E0 le m Out_break).
        { apply PREFIX, finish_break. }
        destruct (source_finish_exit _ _ _ _ _ _ _ BREAK) as [-> [-> EXIT]].
        invert_local_step STEP.
        destruct HISTORY as [|l z TURN NOEXIT]; [|contradiction].
        eexists; eexists; split.
        -- left. eapply target_turn_zero; eauto.
        -- left. apply local_exit; exact AGREE.
    + destruct (cursor_step ge _ _ _ _ _ _ _ _ _ PLAIN OPEN STEP)
        as [cur' [rest' [le' [m' [TRACE [AFTER [GOOD [LT BACK]]]]]]]].
      subst t after. eexists; eexists; split.
      2: {
        left. eapply local_first; [exact AGREE|exact READY|exact HISTORY|exact GOOD|].
        intros l z out FINISH. apply PREFIX, BACK, FINISH.
      }
      right; repeat split; try reflexivity; lia.
  - destruct (cursor_end_dec cur rest) as [END|OPEN].
    + destruct END as [-> [-> | ->]]; cbn [pending_cont] in STEP.
      * assert (SECOND : Clight2.exec_stmt ge e le2 m2 (source_second p) E0 le m Out_normal).
        { apply PREFIX. apply finish_skip. repeat split; reflexivity. }
        assert (TURN : source_turn ge p e le1 m1 le m).
        { eapply source_finish_turn; eassumption. }
        invert_local_step STEP. rewrite <- (source_loop_parts p).
        destruct HISTORY as [|l z PRIOR NOEXIT].
        -- destruct (source_turn_choice _ _ _ _ _ _ _ WF TURN) as [TAIL|NEXT].
           ++ destruct (target_turn_tail ge tprog SYMBOLS p tf k e le0 tle m0 le m
                WF AGREE TURN TAIL) as [tle' [RUN [AGR READY']]].
              eexists; eexists; split; [left; exact RUN|].
              left. eapply local_loop; [exact AGR|exact READY'|constructor].
           ++ eexists; eexists; split.
              2: { left. eapply local_loop; [exact AGREE|exact READY|eapply history_one; eauto]. }
              right; repeat split; try reflexivity.
              cbn [history_cost cursor_cost statement_cost]. lia.
        -- destruct (target_turn_pair ge tprog SYMBOLS p tf k e le0 tle m0 l z le m
             WF READY AGREE PRIOR TURN) as [tle' [RUN [AGR READY']]].
           eexists; eexists; split; [left; exact RUN|].
           left. eapply local_loop; [exact AGR|exact READY'|constructor].
      * exfalso. eapply source_second_cannot_break.
        apply PREFIX, finish_break.
    + destruct (cursor_step ge _ _ _ _ _ _ _ _ _ PLAIN OPEN STEP)
        as [cur' [rest' [le' [m' [TRACE [AFTER [GOOD [LT BACK]]]]]]]].
      subst t after. eexists; eexists; split.
      2: {
        left. eapply local_second; [exact AGREE|exact READY|exact HISTORY|exact FIRST|exact GOOD|].
        intros l z out FINISH. apply PREFIX, BACK, FINISH.
      }
      right; repeat split; try reflexivity; lia.
  - invert_local_step STEP.
    exists O; eexists; split.
    + left. apply plus_one. eapply step_skip_call; [exact CALL|].
      rewrite BLOCKS. eassumption.
    + right. eauto.
Qed.
