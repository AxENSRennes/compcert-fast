(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Maps AST Integers Ctypes Cop Clight ArrayPair.

Definition well_formed (p: plan) : Prop :=
  pointer p <> bound p /\
  match layout p with
  | Indexed i => i <> pointer p /\ i <> bound p
  | _ => True
  end.

Local Ltac split_checks :=
  repeat match goal with
  | H: (_ && _) = true |- _ => apply Bool.andb_true_iff in H; destruct H
  | H: proj_sumbool ?test = true |- _ =>
      destruct test; [clear H | discriminate]
  end.

Lemma same_expr_sound : forall a b, same_expr a b = true -> a = b.
Proof.
  induction a; intros rhs; destruct rhs; cbn [same_expr]; intros H; try discriminate;
    split_checks; f_equal; eauto.
Qed.

Lemma same_stmt_sound : forall s t, same_stmt s t = true -> s = t.
Proof.
  induction s; intros rhs; destruct rhs; cbn [same_stmt]; intros H; try discriminate;
    split_checks; f_equal; eauto using same_expr_sound.
Qed.

Lemma matches_sound : forall f p body, matches f p body = true ->
  f = with_body (source_template p) body.
Proof.
  intros [ret cc params vars temps old] p body H.
  unfold matches in H. cbn [fn_return fn_callconv fn_params fn_vars fn_temps fn_body] in H.
  split_checks. unfold with_body, source_template. simpl. f_equal; auto using same_stmt_sound.
Qed.

Lemma distinct_sound : forall p, distinct p = true -> well_formed p.
Proof.
  intros p CHECK. unfold distinct in CHECK.
  apply Bool.andb_true_iff in CHECK as [D REST].
  split. destruct (peq (pointer p) (bound p)); simpl in D; discriminate || assumption.
  destruct (layout p); auto.
  destruct (peq index (pointer p)), (peq index (bound p)); simpl in REST;
    try discriminate; auto.
Qed.

Lemma checked_sound : forall f p p', checked f p = Some p' ->
  f = source_template p' /\ well_formed p' /\ pointer_wide p' = pointer_wide p.
Proof.
  intros f p p'. unfold checked.
  destruct (distinct p && matches f p (source_body p)) eqn:C; try discriminate.
  intros H. inv H. apply Bool.andb_true_iff in C as [D M].
  split; [now apply matches_sound in M|]. split; auto using distinct_sound.
Qed.

Lemma selected_plain_sound : forall f p, selected_plain f = Some p ->
  f = source_template p /\ well_formed p /\ pointer_wide p = false.
Proof.
  intros f p. unfold selected_plain.
  destruct (fn_params f) as [|[ptr t] [|[n t'] [|a rest]]]; try discriminate.
  - destruct (find_increment (fn_body f)) as [[k sign]|]; try discriminate.
    destruct (fn_temps f) as [|[i ti] [|a rest]]; try discriminate.
    destruct (find_array (fn_body f)) as [[base ty]|]; try discriminate.
    intros C; apply checked_sound in C; exact C.
  - destruct (find_increment (fn_body f)) as [[k sign]|]; try discriminate.
    destruct (fn_temps f) as [|[i ti] [|a rest]]; try discriminate.
    + destruct (checked f (Plan ptr n WhilePointer k sign None false)) eqn:H.
      * intros E; inv E. apply checked_sound in H; exact H.
      * intros C; apply checked_sound in C; exact C.
    + intros C; apply checked_sound in C; exact C.
Qed.

Lemma selected_guarded_sound : forall f p g, selected_guarded f = Some (p, g) ->
  f = source_function p (Some g) /\ well_formed p /\
  pointer_wide p = false /\ valid_guard g = true.
Proof.
  intros f p g. unfold selected_guarded.
  destruct (fn_params f) as [|[ptr pt] [|[n nt] [|x xs]]]; try discriminate.
  destruct (fn_temps f) as [|[i it] [|x xs]]; try discriminate.
  destruct (fn_body f); try discriminate.
  destruct s1; try discriminate. destruct s2; try discriminate.
  destruct (find_guard e) as [test|]; try discriminate.
  destruct (find_increment s2_1) as [[k sign]|]; try discriminate.
  set (q := Plan ptr n (Indexed i) k sign None false).
  destruct (valid_guard test && distinct q && matches f q (guarded_source q test))
    eqn:C; try discriminate.
  intros H; inv H. apply Bool.andb_true_iff in C as [C M].
  apply Bool.andb_true_iff in C as [V D].
  split; [exact (matches_sound _ _ _ M)|].
  split; [now apply distinct_sound|]. split; [reflexivity|exact V].
Qed.

Lemma selected_sound : forall f p g, selected f = Some (p, g) ->
  f = source_function p g /\ well_formed p /\ pointer_wide p = false /\
  match g with Some test => valid_guard test = true | None => True end.
Proof.
  intros f p g. unfold selected.
  destruct (selected_guarded f) as [[q test]|] eqn:G.
  - intros H; inv H. eapply selected_guarded_sound; eauto.
  - destruct (selected_plain f) as [q|] eqn:S; try discriminate.
    intros H; inv H. apply selected_plain_sound in S as [-> [WF NARROW]]. auto.
Qed.

Lemma scratch_pointer : forall p, scratch p <> pointer p.
Proof.
  intros p. unfold scratch. pose proof (Pos.le_max_l (pointer p)
    (Pos.max (bound p) (match layout p with Indexed i => i | _ => xH end))). lia.
Qed.

Lemma scratch_bound : forall p, scratch p <> bound p.
Proof.
  intros p. unfold scratch.
  set (i := match layout p with Indexed i => i | _ => xH end).
  pose proof (Pos.le_max_l (bound p) i).
  pose proof (Pos.le_max_r (pointer p) (Pos.max (bound p) i)). lia.
Qed.

Lemma scratch_index : forall p i, layout p = Indexed i -> scratch p <> i.
Proof.
  intros p i L. unfold scratch. rewrite L.
  pose proof (Pos.le_max_r (bound p) i).
  pose proof (Pos.le_max_r (pointer p) (Pos.max (bound p) i)). lia.
Qed.

Lemma metadata_preserved : forall f,
  fn_return (transf_function f) = fn_return f /\
  fn_callconv (transf_function f) = fn_callconv f /\
  fn_params (transf_function f) = fn_params f /\
  fn_vars (transf_function f) = fn_vars f.
Proof.
  intros f. unfold transf_function. destruct (selected f) as [[p g]|] eqn:S; auto.
  apply selected_sound in S as [-> _]. destruct g; repeat split.
Qed.
