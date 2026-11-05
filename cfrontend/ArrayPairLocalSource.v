(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Extract the semantic effects of one recognised Clight loop iteration. *)
Require Import Coqlib AST Integers Values Memory Events Maps Smallstep.
Require Import Ctypes Cop Clight ClightBigstep ArrayPair ArrayPairLocalFacts.

Definition source_first (p: plan) : statement :=
  match source_loop p with Sloop body _ => body | _ => Sskip end.

Definition source_second (p: plan) : statement :=
  match source_loop p with Sloop _ advance => advance | _ => Sskip end.

Lemma source_loop_parts:
  forall p, source_loop p = Sloop (source_first p) (source_second p).
Proof. intros [ptr n shape c sign]; destruct shape; reflexivity. Qed.

Lemma source_plain:
  forall p, plain_statement (source_first p) = true /\
            plain_statement (source_second p) = true.
Proof. intros [ptr n shape c sign]; destruct shape; split; reflexivity. Qed.

Definition test_value (ge: genv) (e: env) (le: temp_env) (m: mem)
    (test: expr) (choice: bool) : Prop :=
  exists v, eval_expr ge e le m test v /\ bool_val v (typeof test) m = Some choice.

Definition source_turn (ge: genv) (p: plan) (e: env) (le: temp_env)
    (m: mem) (le': temp_env) (m': mem) : Prop :=
  test_value ge e le m (loop_test p) true /\
  Clight2.exec_stmt ge e le m (scalar_update p) E0 le m' Out_normal /\
  Clight2.exec_stmt ge e le m' (scalar_advance p) E0 le' m' Out_normal.

Lemma exec_sequence_normal:
  forall ge e le m a b le' m',
  Clight2.exec_stmt ge e le m (Ssequence a b) E0 le' m' Out_normal ->
  exists l z, Clight2.exec_stmt ge e le m a E0 l z Out_normal /\
              Clight2.exec_stmt ge e l z b E0 le' m' Out_normal.
Proof.
  intros ge e le m a b le' m' RUN; inversion RUN; subst; try contradiction.
  match goal with
  | H: _ ** _ = E0 |- _ => apply Eapp_E0_inv in H as [A B]; subst
  | H: E0 = _ ** _ |- _ => symmetry in H; apply Eapp_E0_inv in H as [A B]; subst
  end.
  eauto.
Qed.

Lemma exec_skip_inv:
  forall ge e le m le' m' o,
  Clight2.exec_stmt ge e le m Sskip E0 le' m' o ->
  le' = le /\ m' = m /\ o = Out_normal.
Proof. intros; inversion H; auto. Qed.

Lemma exec_with_skip_inv:
  forall ge e le m s le' m' o,
  Clight2.exec_stmt ge e le m (with_skip s) E0 le' m' o ->
  Clight2.exec_stmt ge e le m s E0 le' m' o.
Proof.
  intros ge e le m s le' m' o RUN.
  unfold with_skip in RUN. inversion RUN; subst.
  - match goal with H: _ ** _ = E0 |- _ => apply Eapp_E0_inv in H as [A B]; subst end.
    match goal with H: ClightBigstep.exec_stmt _ _ _ _ _ Sskip E0 _ _ Out_normal |- _ =>
      apply exec_skip_inv in H as [L [M _]]; subst; assumption end.
  - match goal with H: ClightBigstep.exec_stmt _ _ _ _ _ Sskip E0 _ _ _ |- _ =>
      apply exec_skip_inv in H as [L [M O]]; subst; contradiction end.
Qed.

Lemma exec_guard_inv:
  forall ge p e le m le' m' o,
  Clight2.exec_stmt ge e le m (guard p) E0 le' m' o ->
  le' = le /\ m' = m /\
  ((o = Out_normal /\ test_value ge e le m (loop_test p) true) \/
   (o = Out_break /\ test_value ge e le m (loop_test p) false)).
Proof.
  intros ge p e le m le' m' o RUN.
  unfold guard in RUN. inversion RUN; subst.
  destruct b; match goal with
  | H: ClightBigstep.exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion H; subst
  | H: ClightBigstep.exec_stmt _ _ _ _ _ Sbreak _ _ _ _ |- _ => inversion H; subst
  end; repeat split; auto; [left|right]; split; eauto; unfold test_value; eauto.
Qed.

Lemma exec_scalar_update_env:
  forall ge p e le m le' m',
  Clight2.exec_stmt ge e le m (scalar_update p) E0 le' m' Out_normal ->
  le' = le.
Proof. intros; unfold scalar_update in H; inversion H; reflexivity. Qed.

Ltac reject_non_lvalue :=
  match goal with
  | H: eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H
  | H: eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H
  | H: eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H
  end.

Lemma addr0_determinate:
  forall ge p e le m x y,
  eval_expr ge e le m (addr p 0) x ->
  eval_expr ge e le m (addr p 0) y ->
  x = y.
Proof.
  intros ge [ptr n shape c sign] e le m x y A B.
  destruct shape; cbn [addr layout] in A, B; unfold pointer_expr in A, B; cbn [pointer] in A, B.
  - inversion A; inversion B; subst; try reject_non_lvalue; congruence.
  - inversion A; inversion B; subst; try reject_non_lvalue; congruence.
  - inversion A; inversion B; subst; try reject_non_lvalue.
    repeat match goal with
    | H: eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inversion H; clear H; subst; try reject_non_lvalue
    end.
    repeat match goal with
    | H: ?le ! ?r = Some ?a, J: ?le ! ?r = Some ?b |- _ =>
        assert (a = b) by congruence; clear J; subst
    end.
    congruence.
Qed.

Lemma uint_add_defined:
  forall ce k sign m v res,
  sem_binary_operation ce Oadd v tuint (Vint k) (Tint I32 sign noattr) m = Some res ->
  exists x, v = Vint x /\ res = Vint (Int.add x k).
Proof.
  intros ce k sign m v res ADD.
  destruct sign, v; try discriminate.
  all: exists i; inversion ADD; auto.
Qed.

Lemma exec_scalar_update_inv:
  forall ge p e le m m',
  Clight2.exec_stmt ge e le m (scalar_update p) E0 le m' Out_normal ->
  exists b ofs lo,
    eval_expr ge e le m (addr p 0) (Vptr b ofs) /\
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint lo) /\
    Mem.storev Mint32 m (Vptr b ofs) (Vint (Int.add lo (increment p))) = Some m'.
Proof.
  intros ge p e le m m' RUN. unfold scalar_update in RUN.
  inversion RUN; subst; clear RUN.
  repeat match goal with
  | H: eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ =>
      inversion H; subst; clear H
  | H: eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
      inversion H; subst; clear H
  | H: eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
      inversion H; subst; clear H
  | H: eval_expr _ _ _ _ (Ederef _ _) _ |- _ =>
      inversion H; subst; clear H
  end; try reject_non_lvalue.
  match goal with
  | ADD: sem_binary_operation _ Oadd _ _ (Vint _) _ _ = Some _ |- _ =>
      apply uint_add_defined in ADD as [lo [A B]]; subst
  end.
  cbn [typeof] in *.
  repeat match goal with
  | H: deref_loc tuint _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H: assign_loc _ tuint _ _ _ _ _ _ |- _ =>
      inversion H; subst; clear H
  | H: access_mode tuint = ?rhs |- _ =>
      change (By_value Mint32 = rhs) in H; inversion H; subst; clear H
  | H: sem_cast (Vint _) tuint tuint _ = Some _ |- _ =>
      cbn [sem_cast classify_cast tuint cast_int_int] in H; inversion H; subst; clear H
  end; try reject_non_lvalue.
  match goal with
  | A: eval_expr _ _ _ _ (addr _ 0) (Vptr ?b ?ofs),
    B: eval_expr _ _ _ _ (addr _ 0) (Vptr ?b' ?ofs') |- _ =>
      pose proof (addr0_determinate _ _ _ _ _ _ _ A B) as EQ;
      inversion EQ; subst; clear EQ
  end.
  eauto 8.
Qed.

Lemma exec_sequence_break:
  forall ge e le m a b le' m',
  Clight2.exec_stmt ge e le m (Ssequence a b) E0 le' m' Out_break ->
  Clight2.exec_stmt ge e le m a E0 le' m' Out_break \/
  exists l z, Clight2.exec_stmt ge e le m a E0 l z Out_normal /\
              Clight2.exec_stmt ge e l z b E0 le' m' Out_break.
Proof.
  intros ge e le m a b le' m' RUN; inversion RUN; subst; auto.
  match goal with
  | H: _ ** _ = E0 |- _ => apply Eapp_E0_inv in H as [A B]; subst
  | H: E0 = _ ** _ |- _ => symmetry in H; apply Eapp_E0_inv in H as [A B]; subst
  end.
  right; eauto.
Qed.

Ltac unpack_normal :=
  repeat match goal with
  | H: Clight2.exec_stmt _ _ _ _ (with_skip _) E0 _ _ Out_normal |- _ =>
      apply exec_with_skip_inv in H
  | H: Clight2.exec_stmt _ _ _ _ (Ssequence _ _) E0 _ _ Out_normal |- _ =>
      let A := fresh "FIRST" in let B := fresh "SECOND" in
      destruct (exec_sequence_normal _ _ _ _ _ _ _ _ H) as [? [? [A B]]]; clear H
  | H: Clight2.exec_stmt _ _ _ _ Sskip E0 _ _ Out_normal |- _ =>
      apply exec_skip_inv in H as [? [? _]]; subst
  | H: Clight2.exec_stmt _ _ _ _ (guard _) E0 _ _ Out_normal |- _ =>
      apply exec_guard_inv in H as [? [? [[_ TEST]|[BAD _]]]]; subst; try discriminate
  end.

Lemma source_finish_turn:
  forall ge p e le m l z le' m',
  Clight2.exec_stmt ge e le m (source_first p) E0 l z Out_normal ->
  Clight2.exec_stmt ge e l z (source_second p) E0 le' m' Out_normal ->
  source_turn ge p e le m le' m'.
Proof.
  intros ge [ptr n shape c sign] e le m l z le' m' FIRST SECOND.
  destruct shape; cbn [source_first source_second source_loop layout] in FIRST, SECOND;
    unpack_normal.
  all: match goal with
  | H: Clight2.exec_stmt _ _ _ _ (scalar_update _) E0 _ _ Out_normal |- _ =>
      pose proof (exec_scalar_update_env _ _ _ _ _ _ _ H); subst
  end.
  all: repeat match goal with
  | H: Clight2.exec_stmt _ _ _ ?before ?cmd E0 _ ?after Out_normal |- _ =>
      tryif constr_eq before after then fail else
      let ins := eval hnf in cmd in
      lazymatch ins with
      | Sset _ _ => assert (after = before) by (inversion H; reflexivity); subst
      end
  end.
  all: unfold source_turn, scalar_advance, advance; cbn [layout].
  all: repeat split; try assumption.
  all: change E0 with (E0 ** E0); eapply exec_Sseq_1; eassumption.
Qed.

Ltac unpack_break :=
  repeat match goal with
  | H: Clight2.exec_stmt _ _ _ _ (with_skip _) E0 _ _ Out_break |- _ =>
      apply exec_with_skip_inv in H
  | H: Clight2.exec_stmt _ _ _ _ (Ssequence _ _) E0 _ _ Out_break |- _ =>
      let A := fresh "FIRST" in let B := fresh "SECOND" in
      destruct (exec_sequence_break _ _ _ _ _ _ _ _ H) as [A|[? [? [A B]]]]; clear H
  | H: Clight2.exec_stmt _ _ _ _ ?cmd E0 _ _ Out_break |- _ =>
      let ins := eval hnf in cmd in
      lazymatch ins with
      | Sset _ _ => inversion H
      | Sassign _ _ => inversion H
      | Sskip => inversion H
      end
  end.

Lemma source_finish_exit:
  forall ge p e le m le' m',
  Clight2.exec_stmt ge e le m (source_first p) E0 le' m' Out_break ->
  le' = le /\ m' = m /\ test_value ge e le m (loop_test p) false.
Proof.
  intros ge [ptr n shape c sign] e le m le' m' FIRST.
  destruct shape; cbn [source_first source_loop layout] in FIRST; unpack_break.
  all: match goal with
  | H: Clight2.exec_stmt _ _ _ _ (guard _) E0 _ _ Out_break |- _ =>
      apply exec_guard_inv in H as [L [M [[BAD _]|[_ TEST]]]]; try discriminate; auto
  end.
Qed.

Lemma source_second_cannot_break:
  forall ge p e le m le' m',
  ~ Clight2.exec_stmt ge e le m (source_second p) E0 le' m' Out_break.
Proof.
  intros ge [ptr n shape c sign] e le m le' m' RUN.
  destruct shape; cbn [source_second source_loop layout] in RUN; unpack_break.
Qed.
