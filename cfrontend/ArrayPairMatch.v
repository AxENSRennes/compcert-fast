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

Lemma matches_sound : forall f p, matches f p = true -> f = source_template p.
Proof.
  intros [ret cc params vars temps body] p H.
  unfold matches in H. cbn [fn_return fn_callconv fn_params fn_vars fn_temps fn_body] in H.
  split_checks. unfold source_template. f_equal; auto using same_stmt_sound.
Qed.

Lemma checked_sound : forall f p p', checked f p = Some p' ->
  f = source_template p' /\ well_formed p'.
Proof.
  intros f p p'. unfold checked.
  destruct (peq (pointer p) (bound p)); try discriminate.
  assert (W: forall b, (match layout p with
            | Indexed i => peq i (pointer p) || peq i (bound p)
            | _ => false end) = b -> b = false -> well_formed p).
  { intros b E ->. split; auto. destruct (layout p); auto.
    destruct (peq index (pointer p)), (peq index (bound p)); simpl in E;
      try discriminate; auto. }
  destruct (match layout p with
            | Indexed i => peq i (pointer p) || peq i (bound p)
            | _ => false end) eqn:E; try discriminate.
  destruct (matches f p) eqn:M; try discriminate. intros H; inv H.
  split. now apply matches_sound. eauto.
Qed.

Lemma selected_sound : forall f p, selected f = Some p ->
  f = source_template p /\ well_formed p.
Proof.
  intros f p. unfold selected.
  destruct (fn_params f) as [|[ptr t] [|[n t'] [|a rest]]]; try discriminate.
  destruct (find_increment (fn_body f)) as [[k sign]|]; try discriminate.
  destruct (fn_temps f) as [|[i ti] [|a rest]]; try discriminate.
  - destruct (checked f (Plan ptr n WhilePointer k sign)) eqn:H.
    + intros E; inv E. eapply checked_sound; eauto.
    + apply checked_sound.
  - apply checked_sound.
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
  intros f. unfold transf_function. destruct (selected f) eqn:S; auto.
  apply selected_sound in S as [-> _]. repeat split.
Qed.
