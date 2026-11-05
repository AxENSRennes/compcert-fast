(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Structural facts for the scalar source and its generated pair/tail CFG. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Experimental.
Require Import MemoryNeonBounds AutoPair.

Lemma code_equal:
  forall a b: code,
  PTree.beq (fun i j=>if instruction_eq i j then true else false) a b=true -> a=b.
Proof.
  intros a b CHECK. apply PTree.extensionality;intro pc.
  rewrite PTree.beq_correct in CHECK;specialize(CHECK pc).
  destruct a!pc as[i|],b!pc as[j|];auto;try contradiction.
  destruct(instruction_eq i j);congruence.
Qed.

Lemma selected_sound:
  forall f p, selected f=Some p -> f=source_template p.
Proof.
  intros f p. unfold selected.
  destruct(fn_code f)!5%positive as[i|]eqn:CODE;try discriminate.
  destruct i;try discriminate. destruct o;try discriminate.
  destruct(signature_eq(fn_sig f)scalar_sig);try discriminate.
  destruct(list_eq_dec peq(fn_params f)(2%positive::1%positive::nil));try discriminate.
  destruct(zeq(fn_stacksize f)0);try discriminate.
  destruct(peq(fn_entrypoint f)10%positive);try discriminate.
  destruct(PTree.beq _ (fn_code f) _)eqn:BEQ;try discriminate.
  intro EQ;inv EQ. apply code_equal in BEQ.
  destruct f;simpl in *;subst;reflexivity.
Qed.

Lemma metadata_preserved:
  forall f,
  fn_sig(transf_function f)=fn_sig f /\
  fn_params(transf_function f)=fn_params f /\
  fn_stacksize(transf_function f)=fn_stacksize f /\
  fn_entrypoint(transf_function f)=fn_entrypoint f.
Proof.
  intros f. unfold transf_function. destruct(selected f)eqn:SEL.
  - apply selected_sound in SEL;subst;repeat split;reflexivity.
  - repeat split;reflexivity.
Qed.

Lemma source_max_reg:
  forall p, max_reg_function(source_template p)=6%positive.
Proof. intros;reflexivity. Qed.

Lemma source_max_pc:
  forall p, max_pc_function(source_template p)=10%positive.
Proof. intros;reflexivity. Qed.

Lemma target_original_lookup:
  forall p pc i,
  (source_code p)!pc=Some i -> pc<>10%positive ->
  (target_code p)!pc=Some i.
Proof.
  intros p pc i SOURCE NE.
  assert(BOUND: Ple pc 10%positive).
  { rewrite <- (source_max_pc p). eapply max_pc_function_sound;exact SOURCE. }
  unfold target_code. cbn [fold_right fst snd].
  rewrite !PTree.gso by extlia. exact SOURCE.
Qed.

Lemma source_supported:
  forall p pc i,
  (source_code p)!pc=Some i -> MemoryNeonBounds.supported i=true.
Proof.
  intros p pc i SOURCE.
  assert(CHECK: forallb (fun item=>MemoryNeonBounds.supported(snd item))
    (PTree.elements(source_code p))=true) by reflexivity.
  rewrite forallb_forall in CHECK.
  exact(CHECK (pc,i)(PTree.elements_correct _ _ SOURCE)).
Qed.
