(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Entry and argument setup for an inlined array-pair worker. *)
Require Import Coqlib Maps AST Values Memory Events Smallstep.
Require Import Ctypes Clight ArrayPair ArrayPairMatch.

Definition caller_env (c: call_plan) (n: val) : temp_env :=
  PTree.set (call_count c) n (PTree.empty val).

Definition worker_env (p: plan) (ptr n: val) : temp_env :=
  PTree.set (bound p) n
    (PTree.set (pointer p) ptr (create_undef_temps (scalar_temps p))).

Definition target_caller_env (c: call_plan) (n: val) : temp_env :=
  let p := call_loop c in
  PTree.set (bound p) n
    (PTree.set (pointer p) Vundef
      (PTree.set (scratch p) Vundef (create_undef_temps (scalar_temps p)))).

Lemma caller_entry_inv : forall ge c args m e le m',
  function_entry2 ge (caller_source c) args m e le m' ->
  e = empty_env /\ m' = m /\ exists n, args = n :: nil /\ le = caller_env c n.
Proof.
  intros ge c args m e le m' ENTRY.
  inversion ENTRY as [VARS PARAMS DISJOINT ALLOC BIND].
  change (alloc_variables ge empty_env m nil e m') in ALLOC. inv ALLOC.
  change (bind_parameter_temps ((call_count c, tuint) :: nil) args
    (PTree.empty val) = Some le) in BIND.
  destruct args as [|n [|other rest]]; try discriminate.
  inv BIND. repeat split. exists n; auto.
Qed.

Lemma worker_entry_inv : forall ge p ptr n m e le m',
  array_anchor p = None ->
  function_entry2 ge (source_template p) (ptr :: n :: nil) m e le m' ->
  e = empty_env /\ m' = m /\ le = worker_env p ptr n.
Proof.
  intros ge p ptr n m e le m' NOARRAY ENTRY.
  inversion ENTRY as [VARS PARAMS DISJOINT ALLOC BIND].
  change (alloc_variables ge empty_env m nil e m') in ALLOC. inv ALLOC.
  cbn [source_template fn_params fn_temps] in BIND.
  unfold parameters, anchored in BIND. rewrite NOARRAY in BIND.
  inv BIND. repeat split.
Qed.

Lemma caller_entry_target : forall ge c n m i,
  well_formed (call_loop c) ->
  layout (call_loop c) = Indexed i ->
  function_entry2 ge (caller_target c) (n :: nil)
    m empty_env (target_caller_env c n) m.
Proof.
  intros ge c n m i WF LAYOUT.
  destruct WF as [PTR FRESH]. rewrite LAYOUT in FRESH.
  destruct FRESH as [IPTR IBOUND].
  constructor.
  - constructor.
  - cbn [caller_target fn_params var_names map fst]. constructor; [tauto|constructor].
  - cbn [caller_target fn_params fn_temps var_names map fst].
    unfold scalar_temps. rewrite LAYOUT.
    intros x y INX INY. simpl in INX, INY.
    pose proof (scratch_bound (call_loop c)).
    intuition congruence.
  - constructor.
  - reflexivity.
Qed.

Lemma caller_env_count : forall c n, (caller_env c n)!(call_count c) = Some n.
Proof. intros; apply PTree.gss. Qed.

Lemma worker_env_pointer : forall p ptr n,
  well_formed p -> (worker_env p ptr n)!(pointer p) = Some ptr.
Proof.
  intros p ptr n [DISTINCT _]. unfold worker_env.
  now rewrite PTree.gso, PTree.gss.
Qed.

Local Lemma caller_setup_env : forall c ptr n,
  well_formed (call_loop c) ->
  PTree.set (pointer (call_loop c)) ptr (target_caller_env c n) =
  PTree.set (scratch (call_loop c)) Vundef (worker_env (call_loop c) ptr n).
Proof.
  intros c ptr n [DISTINCT _].
  pose proof (scratch_pointer (call_loop c)).
  pose proof (scratch_bound (call_loop c)).
  unfold target_caller_env, worker_env.
  apply PTree.extensionality; intro id. repeat rewrite PTree.gsspec.
  destruct (peq id (pointer (call_loop c))),
    (peq id (bound (call_loop c))),
    (peq id (scratch (call_loop c))); try congruence.
Qed.

Lemma caller_setup_exec : forall ge c k m ptr n,
  well_formed (call_loop c) ->
  eval_expr ge empty_env (target_caller_env c n) m (guard_address (call_address c)) ptr ->
  plus step2 ge
    (State (caller_target c) (caller_setup c) k empty_env (target_caller_env c n) m)
    E0 (State (caller_target c) (target_body (aligned_pointer_plan (call_loop c)))
      k empty_env (PTree.set (scratch (call_loop c)) Vundef (worker_env (call_loop c) ptr n)) m).
Proof.
  intros ge c k m ptr n WF ADDRESS.
  unfold caller_setup. rewrite <- caller_setup_env by exact WF.
  eapply plus_three.
  - apply step_seq.
  - apply step_set. exact ADDRESS.
  - apply step_skip_seq.
  - reflexivity.
Qed.
