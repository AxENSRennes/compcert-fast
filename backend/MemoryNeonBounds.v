(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Structural certificates for the finite source template.  Every successor
    has a strictly smaller numeric rank; no external effects are hidden. *)
Require Import Coqlib Maps AST Integers Op RTL MemoryNeon.

Definition supported (i: instruction): bool :=
  match i with
  | Inop _ | Iop _ _ _ _ | Iload _ _ _ _ _ | Istore _ _ _ _ _
  | Icond _ _ _ _ | Ireturn None => true
  | _ => false
  end.
Definition checked_rank (f: function): bool :=
  forallb (fun item => supported (snd item) &&
    forallb (fun succ => Nat.ltb (Pos.to_nat succ) (Pos.to_nat (fst item)))
      (successors_instr (snd item))) (PTree.elements (fn_code f)).

Lemma source_checked_rank:
  forall p, checked_rank (source_template p) = true.
Proof. intros; reflexivity. Qed.

Lemma checked_rank_instruction:
  forall f pc i,
  checked_rank f = true -> (fn_code f)!pc = Some i ->
  supported i = true /\
  forall succ, In succ (successors_instr i) ->
    (Pos.to_nat succ < Pos.to_nat pc)%nat.
Proof.
  intros f pc i CHECK CODE.
  unfold checked_rank in CHECK.
  rewrite forallb_forall in CHECK.
  specialize (CHECK (pc,i) (PTree.elements_correct _ _ CODE)).
  simpl in CHECK. apply andb_true_iff in CHECK. destruct CHECK as [SUPPORT RANK].
  split; auto.
  intros succ IN. rewrite forallb_forall in RANK.
  apply Nat.ltb_lt. apply RANK; auto.
Qed.

Lemma source_supported:
  forall p pc i,
  (fn_code (source_template p))!pc = Some i -> supported i = true.
Proof.
  intros. eapply (proj1 (checked_rank_instruction _ _ _ (source_checked_rank p) H)).
Qed.

Lemma source_rank:
  forall p pc i succ,
  (fn_code (source_template p))!pc = Some i ->
  In succ (successors_instr i) ->
  (Pos.to_nat succ < Pos.to_nat pc)%nat.
Proof.
  intros. eapply (proj2 (checked_rank_instruction _ _ _ (source_checked_rank p) H)); eauto.
Qed.
