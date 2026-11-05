(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Maps AST Integers Values Memory Globalenvs Ctypes Clight ArrayPair.

Definition array_binding (ge: genv) (e: env) (id: ident) (ty: type) (b: block) : Prop :=
  match e!id with
  | Some binding => binding = (b, ty)
  | None => Genv.find_symbol ge id = Some b
  end.

(** Parameters may point at any offset. Named arrays start at offset zero. *)
Definition pointer_value (ge: genv) (e: env) (p: plan) (le: temp_env)
    (b: block) (ofs: ptrofs) : Prop :=
  match array_anchor p with
  | Some (len, al) => ofs = Ptrofs.zero /\ array_binding ge e (pointer p) (array_type len al) b
  | None => le!(pointer p) = Some (Vptr b ofs)
  end.

Lemma pointer_expr_typeconv : forall p, typeconv (typeof (pointer_expr p)) = tuint_ptr.
Proof. intros; unfold pointer_expr; destruct (array_anchor p) as [[len al]|]; reflexivity. Qed.

Lemma pointer_value_narrow : forall ge e p le b ofs,
  array_anchor p = None ->
  (pointer_value ge e p le b ofs <-> le!(pointer p) = Some (Vptr b ofs)).
Proof. intros; unfold pointer_value; now rewrite H. Qed.

Lemma pointer_value_anchor_zero : forall ge e p le b ofs,
  anchored p = true -> pointer_value ge e p le b ofs -> ofs = Ptrofs.zero.
Proof. intros; unfold anchored, pointer_value in *; destruct (array_anchor p) as [[len al]|]; intuition discriminate. Qed.

Lemma array_binding_eval : forall ge e le m id len al b,
  array_binding ge e id (array_type len al) b ->
  eval_expr ge e le m (Evar id (array_type len al)) (Vptr b Ptrofs.zero).
Proof.
  intros ge e le m id len al b BIND. unfold array_binding in BIND.
  eapply eval_Elvalue with (bf := Full).
  - destruct (e!id) as [[b' ty]|] eqn:E.
    + inv BIND. apply eval_Evar_local; exact E.
    + apply eval_Evar_global; assumption.
  - apply deref_loc_reference; reflexivity.
Qed.

Lemma pointer_value_eval : forall ge e p le b ofs m,
  pointer_value ge e p le b ofs -> eval_expr ge e le m (pointer_expr p) (Vptr b ofs).
Proof.
  intros ge e p le b ofs m PTR. unfold pointer_value, pointer_expr in *.
  destruct (array_anchor p) as [[len al]|]; [|now constructor].
  destruct PTR as [-> BIND]. now apply array_binding_eval.
Qed.

Lemma array_expr_inv : forall ge e le m id len al v,
  eval_expr ge e le m (Evar id (array_type len al)) v ->
  exists b, v = Vptr b Ptrofs.zero /\ array_binding ge e id (array_type len al) b.
Proof.
  intros until v. intros EV. inv EV.
  match goal with H: eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ => inv H end;
  match goal with H: deref_loc _ _ _ _ _ _ |- _ => inv H end;
    try discriminate; eexists; split; try reflexivity;
    unfold array_binding; match goal with H: e!id = _ |- _ => rewrite H end; auto.
Qed.

Lemma pointer_value_inv : forall ge e p le b ofs m,
  eval_expr ge e le m (pointer_expr p) (Vptr b ofs) -> pointer_value ge e p le b ofs.
Proof.
  intros ge e p le b ofs m EV. unfold pointer_expr, pointer_value in *.
  destruct (array_anchor p) as [[len al]|].
  - apply array_expr_inv in EV as [b' [EQ BIND]]. inv EQ; auto.
  - inv EV; auto.
    match goal with H: eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inv H end.
Qed.

Lemma pointer_expr_determinate : forall ge e p le m v w,
  eval_expr ge e le m (pointer_expr p) v ->
  eval_expr ge e le m (pointer_expr p) w -> v = w.
Proof.
  intros ge e p le m v w A B. unfold pointer_expr in *.
  destruct (array_anchor p) as [[len al]|].
  - apply array_expr_inv in A as [b [-> A]]. apply array_expr_inv in B as [b' [-> B]].
    unfold array_binding in *; destruct (e!(pointer p)) as [[x t]|]; congruence.
  - inv A; inv B; try congruence;
      match goal with H: eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inv H end.
Qed.

Lemma pointer_value_unique : forall ge e p le b ofs b' ofs',
  pointer_value ge e p le b ofs -> pointer_value ge e p le b' ofs' -> b = b' /\ ofs = ofs'.
Proof.
  intros ge e p le b ofs b' ofs' A B.
  pose proof (pointer_expr_determinate ge e p le Mem.empty _ _
    (pointer_value_eval ge e p le b ofs Mem.empty A)
    (pointer_value_eval ge e p le b' ofs' Mem.empty B)) as E.
  inv E; auto.
Qed.

Lemma pointer_value_set_other : forall ge e p le b ofs id v,
  id <> pointer p ->
  (pointer_value ge e p (PTree.set id v le) b ofs <-> pointer_value ge e p le b ofs).
Proof.
  intros; unfold pointer_value; destruct (array_anchor p) as [[len al]|]; [reflexivity|].
  rewrite PTree.gso by congruence; reflexivity.
Qed.

Lemma pointer_value_symbols : forall (ge tge: genv) e p le b ofs,
  (forall id, Genv.find_symbol tge id = Genv.find_symbol ge id) ->
  pointer_value ge e p le b ofs -> pointer_value tge e p le b ofs.
Proof.
  intros until ofs. intros SYMBOLS PTR. unfold pointer_value in *.
  destruct (array_anchor p) as [[len al]|]; auto.
  destruct PTR as [-> BIND]; split; auto.
  unfold array_binding in *. destruct (e!(pointer p)); auto. now rewrite SYMBOLS.
Qed.
