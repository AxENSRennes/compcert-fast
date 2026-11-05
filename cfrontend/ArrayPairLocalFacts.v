(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** A cursor over a finite Clight fragment carries pending sequence
    statements and a decreasing cost. At its end it yields a big-step
    derivation for the original fragment. *)
Require Import Coqlib AST Values Memory Events Maps Smallstep.
Require Import Ctypes Cop Clight ClightBigstep.

Fixpoint plain_statement (s: statement) : bool :=
  match s with
  | Sskip | Sbreak | Sset _ _ | Sassign _ _ => true
  | Ssequence a b | Sifthenelse _ a b =>
      plain_statement a && plain_statement b
  | _ => false
  end.

Fixpoint statement_cost (s: statement) : nat :=
  match s with
  | Ssequence a b => 2 + statement_cost a + statement_cost b
  | Sifthenelse _ a b => S (Nat.max (statement_cost a) (statement_cost b))
  | Sassign _ _ | Sset _ _ => 1
  | _ => 0
  end.

Fixpoint cursor_cost (work: list statement) : nat :=
  match work with
  | nil => O
  | s :: rest => S (statement_cost s + cursor_cost rest)
  end.

Fixpoint pending_cont (rest: list statement) (k: cont) : cont :=
  match rest with
  | nil => k
  | s :: tail => Kseq s (pending_cont tail k)
  end.

Definition cursor_end (s: statement) (rest: list statement) : Prop :=
  rest = nil /\ (s = Sskip \/ s = Sbreak).

Section FRAGMENT.
Variable ge : genv.

Fixpoint finish_cursor (e: env) (le: temp_env) (m: mem)
    (work: list statement) (le': temp_env) (m': mem) (out: outcome) : Prop :=
  match work with
  | nil => le' = le /\ m' = m /\ out = Out_normal
  | s :: rest =>
      (exists le1 m1,
        Clight2.exec_stmt ge e le m s E0 le1 m1 Out_normal /\
        finish_cursor e le1 m1 rest le' m' out) \/
      (out = Out_break /\ Clight2.exec_stmt ge e le m s E0 le' m' Out_break)
  end.

Lemma finish_single:
  forall e le m s le' m' out,
  finish_cursor e le m (s :: nil) le' m' out ->
  Clight2.exec_stmt ge e le m s E0 le' m' out.
Proof.
  cbn [finish_cursor].
  intros e le m s le' m' out [[l [m1 [RUN [A [B C]]]]]|[A RUN]];
    subst; assumption.
Qed.

Lemma finish_skip:
  forall e le m rest le' m' out,
  finish_cursor e le m rest le' m' out ->
  finish_cursor e le m (Sskip :: rest) le' m' out.
Proof. intros; left; exists le, m; split; [constructor|assumption]. Qed.

Lemma finish_break:
  forall e le m rest,
  finish_cursor e le m (Sbreak :: rest) le m Out_break.
Proof. intros; right; split; [reflexivity|constructor]. Qed.

Lemma finish_break_inv:
  forall e le m rest le' m' out,
  finish_cursor e le m (Sbreak :: rest) le' m' out ->
  le' = le /\ m' = m /\ out = Out_break.
Proof.
  cbn [finish_cursor].
  intros e le m rest le' m' out [[l [m1 [RUN REST]]]|[OUT RUN]];
    inversion RUN; subst; auto.
Qed.

Lemma finish_sequence:
  forall e le m a b rest le' m' out,
  finish_cursor e le m (a :: b :: rest) le' m' out ->
  finish_cursor e le m (Ssequence a b :: rest) le' m' out.
Proof.
  cbn [finish_cursor].
  intros e le m a b rest le' m' out [[la [ma [A RUN]]]|[OUT A]].
  - destruct RUN as [[lb [mb [B REST]]]|[OUT B]].
    + left; exists lb, mb; split; [|exact REST].
      change E0 with (E0 ** E0).
      eapply exec_Sseq_1; eauto.
    + right; split; [exact OUT|].
      change E0 with (E0 ** E0).
      eapply exec_Sseq_1; eauto.
  - right; split; [exact OUT|].
    eapply exec_Sseq_2; eauto; discriminate.
Qed.

Lemma finish_if:
  forall e le m a b c v choice rest le' m' out,
  eval_expr ge e le m a v ->
  bool_val v (typeof a) m = Some choice ->
  finish_cursor e le m ((if choice then b else c) :: rest) le' m' out ->
  finish_cursor e le m (Sifthenelse a b c :: rest) le' m' out.
Proof.
  cbn [finish_cursor].
  intros e le m a b c v choice rest le' m' out EV BOOL
    [[l [m1 [RUN REST]]]|[OUT RUN]].
  - left; exists l, m1; split; [|exact REST].
    eapply exec_Sifthenelse; eauto.
  - right; split; [exact OUT|]. eapply exec_Sifthenelse; eauto.
Qed.

Lemma finish_after_normal:
  forall e le m s rest le1 m1 le' m' out,
  Clight2.exec_stmt ge e le m s E0 le1 m1 Out_normal ->
  finish_cursor e le1 m1 (Sskip :: rest) le' m' out ->
  finish_cursor e le m (s :: rest) le' m' out.
Proof.
  cbn [finish_cursor].
  intros e le m s rest le1 m1 le' m' out RUN
    [[l [m2 [SKIP REST]]]|[OUT SKIP]];
    inversion SKIP; subst.
  left; eauto.
Qed.

Lemma cursor_step:
  forall f k e le m s rest t after,
  forallb plain_statement (s :: rest) = true ->
  ~ cursor_end s rest ->
  step2 ge (State f s (pending_cont rest k) e le m) t after ->
  exists s' rest' le' m',
    t = E0 /\
    after = State f s' (pending_cont rest' k) e le' m' /\
    forallb plain_statement (s' :: rest') = true /\
    (cursor_cost (s' :: rest') < cursor_cost (s :: rest))%nat /\
    (forall l z o,
      finish_cursor e le' m' (s' :: rest') l z o ->
      finish_cursor e le m (s :: rest) l z o).
Proof.
  intros f k e le m s rest t after PLAIN OPEN STEP.
  destruct s; cbn [forallb plain_statement] in PLAIN; try discriminate.
  - destruct rest as [|s rest].
    { exfalso; apply OPEN; split; auto. }
    inversion STEP; subst; cbn [is_call_cont pending_cont] in *; try contradiction.
    exists s, rest, le, m; repeat split; auto using finish_skip.
  - inversion STEP; subst; try solve [intuition discriminate].
    exists Sskip, rest, le, m'; repeat split; try reflexivity; try exact PLAIN;
      try solve [cbn [cursor_cost statement_cost]; lia].
    intros; eapply finish_after_normal; [|eassumption].
    econstructor; eauto.
  - inversion STEP; subst; try solve [intuition discriminate].
    eexists Sskip, rest, _, m; repeat split; try reflexivity; try exact PLAIN;
      try solve [cbn [cursor_cost statement_cost]; lia].
    intros; eapply finish_after_normal; [|eassumption].
    econstructor; eauto.
  - inversion STEP; subst; try solve [intuition discriminate].
    eexists _, (_ :: rest), le, m; repeat split; try reflexivity.
    + cbn [forallb plain_statement] in *. rewrite andb_assoc. exact PLAIN.
    + cbn [cursor_cost statement_cost]; lia.
    + intros; apply finish_sequence; assumption.
  - inversion STEP; subst; try solve [intuition discriminate].
    eexists _, rest, le, m; repeat split; try reflexivity.
    + apply andb_true_iff in PLAIN as [BRANCH REST].
      apply andb_true_iff in BRANCH as [YES NO].
      destruct b; cbn [forallb]; now rewrite REST, ?YES, ?NO.
    + cbn [cursor_cost statement_cost].
      destruct b; lia.
    + intros; eapply finish_if; eauto.
  - destruct rest as [|s rest].
    { exfalso; apply OPEN; split; auto. }
    inversion STEP; subst; cbn [pending_cont] in *; try discriminate; try solve [intuition discriminate].
    exists Sbreak, rest, le, m; repeat split; try reflexivity.
    + cbn [forallb plain_statement] in *. apply andb_true_iff in PLAIN as [_ GOOD]; apply andb_true_iff in GOOD as [_ REST]; exact REST.
    + cbn [cursor_cost statement_cost]; lia.
    + intros l z o FIN. apply finish_break_inv in FIN as [A [B C]].
      subst; apply finish_break.
Qed.
End FRAGMENT.
