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

(** Byte-level foundation for correlated-lane memory widening. *)
Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memdata Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Scheduleproof MemVector.

Lemma encode_broadcast:
  forall v, encode_val Mint64 (Val.longofwords v v) = encode_val Mint32 v ++ encode_val Mint32 v.
Proof.
  intros v. destruct v as [|n|n|n|n|b ofs]; try reflexivity.
  change (map Byte (bytes_of_int 8 (Int64.unsigned (Int64.ofwords n n))) =
          map Byte (bytes_of_int 4 (Int.unsigned n)) ++ map Byte (bytes_of_int 4 (Int.unsigned n))).
  rewrite bytes_of_int64,Int64.lo_ofwords,Int64.hi_ofwords,map_app. reflexivity.
Qed.
Lemma store_broadcast:
  forall m b v m1 m2,
  Mem.store Mint32 m b 0 v = Some m1 ->
  Mem.store Mint32 m1 b 4 v = Some m2 ->
  Mem.store Mint64 m b 0 (Val.longofwords v v) = Some m2.
Proof.
  intros m b v m1 m2 S1 S2.
  apply Mem.store_storebytes in S1. apply Mem.store_storebytes in S2.
  apply Mem.storebytes_store.
  - rewrite encode_broadcast. eapply Mem.storebytes_concat; eauto.
    rewrite encode_val_length. simpl. exact S2.
  - change (8 | 0). exists 0; reflexivity.
Qed.
Lemma storev_broadcast:
  forall m b v m1 m2,
  Mem.storev Mint32 m (Vptr b Ptrofs.zero) v = Some m1 ->
  Mem.storev Mint32 m1 (Vptr b (Ptrofs.repr 4)) v = Some m2 ->
  Mem.storev Mint64 m (Vptr b Ptrofs.zero) (Val.longofwords v v) = Some m2.
Proof.
  intros m b v m1 m2 S1 S2.
  change (Mem.store Mint32 m b 0 v = Some m1) in S1.
  change (Mem.store Mint32 m1 b 4 v = Some m2) in S2.
  change (Mem.store Mint64 m b 0 (Val.longofwords v v) = Some m2).
  eapply store_broadcast; eauto.
Qed.

Record valid_pair (f: function) (p: store_pair): Prop := Valid_pair {
  pair_first: f.(fn_code)!(first_pc p) = Some(Istore Mint32 (Aglobal(global_id p)Ptrofs.zero) nil (source_reg p) (second_pc p));
  pair_second: f.(fn_code)!(second_pc p) = Some(Istore Mint32 (Aglobal(global_id p)(Ptrofs.repr 4)) nil (source_reg p) (after_pc p));
  pair_distinct: first_pc p <> second_pc p;
  pair_not_entry: second_pc p <> f.(fn_entrypoint);
  pair_unique: forall pc i, f.(fn_code)!pc = Some i -> In(second_pc p)(successors_instr i) -> pc=first_pc p
}.
Lemma candidate_at_sound:
  forall f a p, candidate_at f a = Some p -> valid_pair f p.
Proof.
  intros f a p. unfold candidate_at.
  destruct (fn_code f)!a as [i|] eqn:F; try discriminate.
  destruct i as [n|op args dst n|chunk addr args dst n|chunk addr args src n|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret]; try discriminate.
  destruct chunk; try discriminate.
  destruct addr as [ofs| |am|ext am|id ofs|ofs]; try discriminate.
  destruct args; try discriminate.
  destruct (fn_code f)!n as [i|] eqn:S; try discriminate.
  destruct i as [n2|op args dst n2|chunk addr args dst n2|chunk addr args src2 n2|sg ros args dst n2|sg ros args|ef args res n2|cond args yes no|arg tbl|ret]; try discriminate.
  destruct chunk; try discriminate.
  destruct addr as [ofs2| |am2|ext2 am2|id2 ofs2|ofs2]; try discriminate.
  destruct args; try discriminate.
  destruct (peq id id2); try discriminate; subst id2.
  destruct (peq src src2); try discriminate; subst src2.
  destruct (Ptrofs.eq ofs Ptrofs.zero) eqn:O1; try discriminate.
  destruct (Ptrofs.eq ofs2 (Ptrofs.repr 4)) eqn:O2; try discriminate.
  apply Ptrofs.same_if_eq in O1; subst ofs.
  apply Ptrofs.same_if_eq in O2; subst ofs2.
  destruct (peq a n); try discriminate.
  destruct (peq n (fn_entrypoint f)); try discriminate.
  destruct (Schedule.predecessor_check f a n) eqn:U; try discriminate.
  intro EQ; inv EQ. constructor; simpl; auto.
  eapply Scheduleproof.predecessor_check_sound; eauto.
Qed.
Lemma selected_sound: forall f p, selected f = Some p -> valid_pair f p.
Proof.
  intros f p. unfold selected.
  destruct (Nat.leb _ _) eqn:SIZE; try discriminate.
  generalize (PTree.elements (fn_code f)). induction l as [|[a i] tail]; simpl; try discriminate.
  destruct (candidate_at f a) as [p'|] eqn:C.
  - intro EQ; inv EQ. eapply candidate_at_sound; eauto.
  - apply IHtail.
Qed.
Lemma fresh_reg_use: forall f pc i r, (fn_code f)!pc=Some i -> In r (instr_uses i) -> Plt r (fresh_reg f).
Proof. unfold fresh_reg; intros. generalize (max_reg_function_use _ _ _ _ H H0). extlia. Qed.
Lemma fresh_reg_def: forall f pc i r, (fn_code f)!pc=Some i -> instr_defs i=Some r -> r<>fresh_reg f.
Proof. unfold fresh_reg; intros. generalize (max_reg_function_def _ _ _ _ H H0). extlia. Qed.
Lemma source_reg_bound: forall f p, selected f=Some p -> Plt(source_reg p)(fresh_reg f).
Proof.
  intros. eapply fresh_reg_use; [apply(pair_first _ _ (selected_sound _ _ H))|]. simpl; auto.
Qed.
Lemma transformed_fields: forall f,
  fn_sig(transf_function f)=fn_sig f /\ fn_params(transf_function f)=fn_params f /\
  fn_stacksize(transf_function f)=fn_stacksize f /\ fn_entrypoint(transf_function f)=fn_entrypoint f.
Proof. intros. unfold transf_function; destruct(selected f); repeat split; reflexivity. Qed.
Lemma transformed_code: forall f pc i, (fn_code f)!pc=Some i ->
  (fn_code(transf_function f))!pc=Some(transf_instr f pc i).
Proof.
  intros f pc i GET. unfold transf_function,transf_instr; destruct(selected f); auto.
  simpl. rewrite PTree.gmap,GET; reflexivity.
Qed.
Lemma code_first: forall f p, selected f=Some p ->
  (fn_code(transf_function f))!(first_pc p)=
    Some(Iop Omakelong(source_reg p::source_reg p::nil)(fresh_reg f)(second_pc p)).
Proof.
  intros. rewrite (transformed_code _ _ _ (pair_first _ _ (selected_sound _ _ H))).
  unfold transf_instr; rewrite H. unfold transf_instr_cached; destruct(peq _ _); congruence.
Qed.
Lemma code_second: forall f p, selected f=Some p ->
  (fn_code(transf_function f))!(second_pc p)=
    Some(Istore Mint64(Aglobal(global_id p)Ptrofs.zero)nil(fresh_reg f)(after_pc p)).
Proof.
  intros. rewrite(transformed_code _ _ _ (pair_second _ _ (selected_sound _ _ H))).
  unfold transf_instr; rewrite H. unfold transf_instr_cached.
  destruct(peq _ _); [pose proof(pair_distinct _ _ (selected_sound _ _ H)); congruence|].
  destruct(peq _ _); congruence.
Qed.
Lemma nonstore_unchanged:
  forall f pc i, (fn_code f)!pc=Some i -> (match i with Istore _ _ _ _ _=>False|_=>True end) ->
  (fn_code(transf_function f))!pc=Some i.
Proof.
  intros f pc i GET NS. rewrite(transformed_code _ _ _ GET). f_equal.
  unfold transf_instr; destruct(selected f)as[p|]eqn:SEL; auto.
  unfold transf_instr_cached. destruct(peq pc (first_pc p)); subst.
  - pose proof(pair_first _ _ (selected_sound _ _ SEL)); rewrite GET in H; inv H; contradiction.
  - destruct(peq pc (second_pc p)); subst; auto.
    pose proof(pair_second _ _ (selected_sound _ _ SEL)); rewrite GET in H; inv H; contradiction.
Qed.

Lemma global_broadcast:
  forall (F V: Type) (ge: Genv.t F V) m id v m1 m2,
  Mem.storev Mint32 m (Genv.symbol_address ge id Ptrofs.zero) v=Some m1 ->
  Mem.storev Mint32 m1 (Genv.symbol_address ge id (Ptrofs.repr 4)) v=Some m2 ->
  Mem.storev Mint64 m (Genv.symbol_address ge id Ptrofs.zero) (Val.longofwords v v)=Some m2.
Proof.
  intros F V ge m id v m1 m2 S1 S2. unfold Genv.symbol_address in *.
  destruct(Genv.find_symbol ge id); try discriminate.
  eapply storev_broadcast; eauto.
Qed.
Definition regs_match (f: function) (rs trs: regset): Prop :=
  forall r, Plt r (fresh_reg f) -> trs#r=rs#r.
Lemma regs_match_refl: forall f rs, regs_match f rs rs.
Proof. red; auto. Qed.
Lemma regs_match_list: forall f rs trs rl, regs_match f rs trs ->
  (forall r, In r rl -> Plt r (fresh_reg f)) -> trs##rl=rs##rl.
Proof. intros f rs trs rl R B. apply list_map_exten; intros. symmetry; apply R; auto. Qed.
Lemma regs_match_set: forall f rs trs r v, regs_match f rs trs ->
  regs_match f (rs#r <- v) (trs#r <- v).
Proof. unfold regs_match; intros. rewrite !Regmap.gsspec; destruct(peq r0 r); auto. Qed.
Lemma regs_match_fresh: forall f rs trs v, regs_match f rs trs ->
  regs_match f rs (trs#(fresh_reg f) <-v).
Proof. unfold regs_match; intros. rewrite Regmap.gso; auto. extlia. Qed.
Lemma regs_match_setres: forall f rs trs res v, regs_match f rs trs ->
  regs_match f (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto using regs_match_set. Qed.

Definition match_prog (p tp: program) := match_program (fun ctx f tf => tf=transf_fundef f) eq p tp.
Global Instance TransfMemVectorLink: TransfLink match_prog := TransfTotalLink transf_function.
Lemma transf_program_match: forall p, match_prog p (transf_program p).
Proof. intros; apply match_transform_program. Qed.
Section PRESERVATION.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Lemma functions_translated: forall v f, Genv.find_funct ge v=Some f -> Genv.find_funct tge v=Some(transf_fundef f).
Proof. exact(Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated: forall v f, Genv.find_funct_ptr ge v=Some f -> Genv.find_funct_ptr tge v=Some(transf_fundef f).
Proof. exact(Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved: forall id, Genv.find_symbol tge id=Genv.find_symbol ge id.
Proof. exact(Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact(Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig(transf_fundef f)=funsig f.
Proof. destruct f; simpl; auto. apply(proj1(transformed_fields f)). Qed.
Lemma find_function_translated: forall ros rs trs fd f,
  regs_match f rs trs ->
  (match ros with inl r => Plt r (fresh_reg f) | _ => True end) ->
  find_function ge ros rs=Some fd -> find_function tge ros trs=Some(transf_fundef fd).
Proof.
  unfold find_function; intros ros rs trs fd f REGS B FIND. destruct ros as[r|id].
  - rewrite REGS by auto. eapply functions_translated; eauto.
  - rewrite symbols_preserved; destruct(Genv.find_symbol ge id); try discriminate.
    eapply function_ptr_translated; eauto.
Qed.
Definition not_second f pc := forall p, selected f=Some p -> pc<>second_pc p.
Definition not_first f pc := forall p, selected f=Some p -> pc<>first_pc p.
Lemma entry_not_second: forall f, not_second f(fn_entrypoint f).
Proof. red; intros. pose proof(pair_not_entry _ _ (selected_sound _ _ H)); congruence. Qed.
Lemma special_successor: forall f p pc i s,
  selected f=Some p -> (fn_code f)!pc=Some i -> In s(successors_instr i) -> s=second_pc p ->
  pc=first_pc p /\ i=Istore Mint32(Aglobal(global_id p)Ptrofs.zero)nil(source_reg p)(second_pc p).
Proof.
  intros. pose proof(selected_sound _ _ H)as V.
  assert(pc=first_pc p)by(eapply pair_unique; eauto; congruence).
  subst pc; split; auto. pose proof(pair_first _ _ V); congruence.
Qed.
Lemma nonstore_successor: forall f pc i s, (fn_code f)!pc=Some i ->
  (match i with Istore _ _ _ _ _=>False|_=>True end) -> In s(successors_instr i) -> not_second f s.
Proof.
  unfold not_second; intros f pc i s CODE NS IN p SEL EQ.
  destruct(special_successor _ _ _ _ _ SEL CODE IN EQ)as[_ E]; subst i; contradiction.
Qed.
Lemma successor_not_first: forall f pc i s, (fn_code f)!pc=Some i -> In s(successors_instr i) ->
  not_first f pc -> not_second f s.
Proof.
  unfold not_first,not_second; intros f pc i s CODE IN NF p SEL EQ.
  destruct(special_successor _ _ _ _ _ SEL CODE IN EQ)as[A B]. exact(NF p SEL A).
Qed.
Lemma second_not_first: forall f p, selected f=Some p -> not_first f(second_pc p).
Proof.
  unfold not_first; intros f p SEL p' SEL'. rewrite SEL in SEL'; inv SEL'.
  pose proof(pair_distinct _ _ (selected_sound _ _ SEL)); congruence.
Qed.
Lemma builtin_arg_regs: forall f rs trs sp m arg v,
  regs_match f rs trs -> eval_builtin_arg ge (fun r=>rs#r) sp m arg v ->
  (forall r, In r(params_of_builtin_arg arg)->Plt r(fresh_reg f)) ->
  eval_builtin_arg ge (fun r=>trs#r) sp m arg v.
Proof.
  intros f rs trs sp m arg v R EV; induction EV; simpl; intros;
    try(constructor; eauto using in_or_app).
  rewrite <-R by eauto with coqlib; constructor.
Qed.
Lemma builtin_args_regs: forall f rs trs sp m args vl,
  regs_match f rs trs -> eval_builtin_args ge (fun r=>rs#r) sp m args vl ->
  (forall r, In r(params_of_builtin_args args)->Plt r(fresh_reg f)) ->
  eval_builtin_args ge (fun r=>trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl R EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs,in_or_app.
Qed.
Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
 | match_frames_intro: forall res f sp pc rs trs
     (NOT: not_second f pc) (REGS: regs_match f rs trs),
     match_frames(Stackframe res f sp pc rs)(Stackframe res(transf_function f)sp pc trs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
 | match_normal: forall stk stk' f sp pc rs trs m
     (STACKS: list_forall2 match_frames stk stk') (NOT: not_second f pc) (REGS: regs_match f rs trs),
     match_states(State stk f sp pc rs m)(State stk'(transf_function f)sp pc trs m)
 | match_special: forall stk stk' f sp rs trs m0 m1 p
     (STACKS: list_forall2 match_frames stk stk') (SELECT: selected f=Some p) (REGS: regs_match f rs trs)
     (STORE: Mem.storev Mint32 m0 (Genv.symbol_address ge (global_id p) Ptrofs.zero) rs#(source_reg p)=Some m1)
     (PACK: trs#(fresh_reg f)=Val.longofwords rs#(source_reg p) rs#(source_reg p)),
     match_states(State stk f sp(second_pc p)rs m1)(State stk'(transf_function f)sp(second_pc p)trs m0)
 | match_call: forall stk stk' fd args m
     (STACKS: list_forall2 match_frames stk stk'),
     match_states(Callstate stk fd args m)(Callstate stk'(transf_fundef fd)args m)
 | match_return: forall stk stk' v m
     (STACKS: list_forall2 match_frames stk stk'), match_states(Returnstate stk v m)(Returnstate stk' v m).
Ltac BOUNDS := match goal with CODE:(fn_code ?f)!?pc=Some ?i |- _ =>
  assert(USES:forall r, In r(instr_uses i)->Plt r(fresh_reg f))by(intros; eapply fresh_reg_use; eauto)
end.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try BOUNDS;
  try match goal with SEL:selected ?f=Some ?p, CODE:(fn_code ?f)!(second_pc ?p)=Some ?i |- _ =>
      pose proof(pair_second _ _ (selected_sound _ _ SEL))as SECOND;
      rewrite CODE in SECOND; discriminate end;
  try match goal with CODE:(fn_code ?f)!?pc=Some ?i |- _ =>
      pose proof(nonstore_unchanged _ _ _ CODE I)as TCODE end.
  - econstructor; split. eapply exec_Inop; eauto.
    constructor; auto. eapply nonstore_successor; eauto; simpl; auto.
  - econstructor; split. eapply exec_Iop; eauto.
    rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;auto).
    rewrite <-H0; apply eval_operation_preserved; exact symbols_preserved.
    constructor; auto using regs_match_set. eapply nonstore_successor; eauto; simpl; auto.
  - econstructor; split. eapply exec_Iload; eauto.
    rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;auto).
    rewrite <-H0; apply eval_addressing_preserved; exact symbols_preserved.
    constructor; auto using regs_match_set. eapply nonstore_successor; eauto; simpl; auto.
  - pose proof(transformed_code _ _ _ H)as TCODE.
    unfold transf_instr in TCODE. destruct(selected f)as[p|]eqn:SEL.
    + unfold transf_instr_cached in TCODE. destruct(peq pc(first_pc p))as[EQ|NE].
      * subst pc. pose proof(pair_first _ _ (selected_sound _ _ SEL))as FIRST.
        rewrite H in FIRST; inv FIRST. simpl in H0; inv H0.
        econstructor; split. eapply exec_Iop; eauto.
        simpl. rewrite REGS by(eapply source_reg_bound;eauto). reflexivity.
        eapply match_special; eauto using regs_match_fresh. apply Regmap.gss.
      * destruct(peq pc(second_pc p))as[EQ|NE2].
        { exfalso; exact(NOT p SEL EQ). }
        econstructor; split. eapply exec_Istore; eauto.
        rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;auto).
        rewrite <-H0; apply eval_addressing_preserved; exact symbols_preserved.
        rewrite REGS by(apply USES;simpl;auto); eauto.
        constructor; auto. eapply successor_not_first; eauto; simpl;auto.
        unfold not_first;intros q SE;rewrite SEL in SE;inv SE;auto.
    + econstructor; split. eapply exec_Istore; eauto.
      rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;auto).
      rewrite <-H0; apply eval_addressing_preserved; exact symbols_preserved.
      rewrite REGS by(apply USES;simpl;auto); eauto.
      constructor; auto. eapply successor_not_first; eauto; simpl;auto.
      unfold not_first;intros q SE;congruence.
  - pose proof(pair_second _ _ (selected_sound _ _ SELECT))as SECOND.
    rewrite H in SECOND; inv SECOND. simpl in H0; inv H0.
    econstructor; split. eapply exec_Istore.
    + eapply code_second; eauto.
    + reflexivity.
    + rewrite PACK. unfold Genv.symbol_address. rewrite symbols_preserved.
      eapply global_broadcast; eauto.
    + constructor; auto. eapply successor_not_first; eauto; simpl;auto.
      eapply second_not_first; eauto.
  - assert(FIND:find_function tge ros trs=Some(transf_fundef fd)).
    { eapply find_function_translated; eauto. destruct ros;simpl;auto. apply USES;simpl;auto. }
    econstructor; split. eapply exec_Icall with(fd:=transf_fundef fd);eauto.
    apply sig_preserved.
    rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;destruct ros;simpl;auto).
    constructor. constructor; auto. constructor;auto.
    eapply nonstore_successor;eauto;simpl;auto.
  - assert(FIND:find_function tge ros trs=Some(transf_fundef fd)).
    { eapply find_function_translated; eauto. destruct ros;simpl;auto. apply USES;simpl;auto. }
    econstructor;split. eapply exec_Itailcall with(fd:=transf_fundef fd);eauto.
    apply sig_preserved.
    rewrite(proj1(proj2(proj2(transformed_fields f))));eauto.
    rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;destruct ros;simpl;auto).
    constructor;auto.
  - econstructor;split. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with(ge1:=ge);eauto. exact symbols_preserved.
    eapply builtin_args_regs;eauto.
    eapply external_call_symbols_preserved;eauto. apply senv_preserved.
    constructor;auto using regs_match_setres. eapply nonstore_successor;eauto;simpl;auto.
  - econstructor;split. eapply exec_Icond;eauto.
    rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;auto);eauto.
    constructor;auto. eapply nonstore_successor;eauto;simpl;destruct b;auto.
  - econstructor;split. eapply exec_Ijumptable;eauto.
    rewrite REGS by(apply USES;simpl;auto);eauto.
    constructor;auto. eapply nonstore_successor;eauto;simpl;auto. eapply list_nth_z_in;eauto.
  - econstructor;split. eapply exec_Ireturn;eauto.
    rewrite(proj1(proj2(proj2(transformed_fields f))));eauto.
    destruct or;simpl. rewrite REGS by(apply USES;simpl;auto). constructor;auto.
    constructor;auto.
  - simpl. econstructor;split.
    replace(fn_entrypoint f)with(fn_entrypoint(transf_function f))by(apply(proj2(proj2(proj2(transformed_fields f))))).
    replace(fn_params f)with(fn_params(transf_function f))by(apply(proj1(proj2(transformed_fields f)))).
    eapply exec_function_internal;eauto.
    rewrite(proj1(transformed_fields f));auto.
    rewrite(proj1(proj2(proj2(transformed_fields f))));eauto.
    rewrite(proj2(proj2(proj2(transformed_fields f)))),(proj1(proj2(transformed_fields f))).
    constructor;auto using entry_not_second,regs_match_refl.
  - econstructor;split. eapply exec_function_external;eauto.
    eapply external_call_symbols_preserved;eauto. apply senv_preserved.
    constructor;auto.
  - inv STACKS. inv H1. econstructor;split. eapply exec_return;eauto.
    constructor;auto using regs_match_set.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 -> exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros;inv H. econstructor;split. econstructor.
  - eapply(Genv.init_mem_transf TRANSL);eauto.
  - rewrite symbols_preserved.
    exact(eq_trans (f_equal (Genv.find_symbol ge) (match_program_main TRANSL)) H1).
  - eapply function_ptr_translated;eauto.
  - rewrite <-H3;apply sig_preserved.
  - constructor;constructor.
Qed.
Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. intros;inv H0;inv H;inv STACKS;constructor. Qed.
Theorem transf_program_correct:
  forward_simulation(RTL.semantics prog)(RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - exact step_simulation.
Qed.

End PRESERVATION.

Module IndirectProof.
Import MemVector.Indirect.
Fixpoint valid_path (f: function) (id:ident) (base src: reg) (previous: node)
    (nodes: list node) (last exit: node): Prop :=
  match nodes with
  | nil => False
  | pc::rest =>
      pc<>fn_entrypoint f /\
      (forall q i, (fn_code f)!q=Some i -> In pc(successors_instr i)->q=previous) /\
      match rest with
      | nil => pc=last /\ (fn_code f)!pc=Some(Istore Mint32(Aindexed(Int64.repr 4))(base::nil)src exit)
      | next::tail => exists i, (fn_code f)!pc=Some i /\ transparent id base i=Some next /\
                                 valid_path f id base src pc rest last exit
      end
  end.
Lemma scan_tail_sound: forall f fuel previous pc id base src nodes last exit,
  scan_tail f fuel previous pc id base src=Some(nodes,last,exit) ->
  exists rest, nodes=pc::rest /\ valid_path f id base src previous nodes last exit.
Proof.
  intros f fuel; induction fuel; intros previous pc id base src nodes last exit; simpl; try discriminate.
  destruct(peq pc(fn_entrypoint f)); try discriminate.
  destruct(Schedule.predecessor_check f previous pc)eqn:U; try discriminate.
  destruct(fn_code f)!pc as[i|]eqn:CODE; try discriminate.
  destruct(transparent id base i)as[next|]eqn:T.
  - destruct(scan_tail f fuel pc next id base src)as[[[ns last']exit']|]eqn:REC; try discriminate.
    intro EQ;inv EQ. destruct(IHfuel _ _ _ _ _ _ _ _ REC)as(rest&HEAD&VALID).
    subst ns. eexists;split;[reflexivity|]. simpl. split;auto. split.
    eapply Scheduleproof.predecessor_check_sound;eauto.
    eexists;split;eauto.
  - destruct i as[n0|op args dst n0|chunk addr args dst n0|chunk addr args src2 n0|sg ros args dst n0|sg ros args|ef args res n0|cond args yes no|arg tbl|ret];try discriminate.
    destruct chunk;try discriminate. destruct addr as[ofs| |am|ext am|sym ofs|ofs];try discriminate.
    destruct args as[|r [|other more]];try discriminate.
    destruct(Int64.eq ofs (Int64.repr 4))eqn:OFF;try discriminate.
    apply Int64.same_if_eq in OFF;subst ofs.
    destruct(peq r base);try discriminate;subst r.
    destruct(peq src src2);try discriminate;subst src2.
    intro EQ;inv EQ. exists nil;split;[reflexivity|]. simpl;split;auto. split.
    eapply Scheduleproof.predecessor_check_sound;eauto. auto.
Qed.
Record valid_region (f: function) (p: region): Prop := Valid_region {
  region_producer: (fn_code f)!(producer_pc p)=Some(Iop(Oaddrsymbol(global_id p)Ptrofs.zero)nil(base_reg p)(first_pc p));
  region_first: (fn_code f)!(first_pc p)=Some(Istore Mint32(Aindexed Int64.zero)(base_reg p::nil)(source_reg p)
                    (match path p with hd::_=>hd|_=>second_pc p end));
  region_not_entry: first_pc p<>fn_entrypoint f;
  region_first_pred: forall q i, (fn_code f)!q=Some i ->In(first_pc p)(successors_instr i)->q=producer_pc p;
  region_path: valid_path f (global_id p)(base_reg p)(source_reg p)(first_pc p)(path p)(second_pc p)(after_pc p);
  region_exit_first: after_pc p<>first_pc p;
  region_exit_path: ~In(after_pc p)(path p)
}.
Lemma candidate_at_sound: forall f a p, candidate_at f a=Some p -> valid_region f p.
Proof.
  intros f a p. unfold candidate_at.
  destruct(fn_code f)!a as[i|]eqn:P;try discriminate.
  destruct i as[n|op args dst n|chunk addr args dst n|chunk addr args src n|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret];try discriminate.
  destruct op;try discriminate. destruct args;try discriminate.
  match goal with |- context[Ptrofs.eq ?ofs Ptrofs.zero] =>
    destruct(Ptrofs.eq ofs Ptrofs.zero)eqn:O;try discriminate;
    apply Ptrofs.same_if_eq in O;subst ofs end.
  destruct(peq n(fn_entrypoint f));try discriminate.
  destruct(Schedule.predecessor_check f a n)eqn:U;try discriminate.
  destruct(fn_code f)!n as[i|]eqn:F;try discriminate.
  destruct i as[n2|op args dst2 n2|chunk addr args dst2 n2|chunk addr args src n2|sg ros args dst2 n2|sg ros args|ef args res n2|cond args yes no|arg tbl|ret];try discriminate.
  destruct chunk;try discriminate. destruct addr as[delta| |am|ext am|sym ofs|ofs];try discriminate.
  destruct args as[|r [|other more]];try discriminate.
  destruct(Int64.eq delta Int64.zero)eqn:DELTA;try discriminate.
  apply Int64.same_if_eq in DELTA;subst delta.
  destruct(peq r dst);try discriminate;subst r.
  match goal with |- context[scan_tail f 32 n n2 ?id dst src] =>
    destruct(scan_tail f 32 n n2 id dst src)as[[[nodes last]exit]|]eqn:TAIL;try discriminate end.
  destruct(peq exit n);try discriminate.
  destruct(in_dec peq exit nodes);try discriminate.
  intro EQ;inv EQ. destruct(scan_tail_sound _ _ _ _ _ _ _ _ _ _ TAIL)as(rest&HEAD&VALID).
  constructor;simpl;auto.
  - rewrite HEAD;simpl;exact F.
  - eapply Scheduleproof.predecessor_check_sound;eauto.
Qed.
Lemma selected_sound: forall f p, selected f=Some p ->valid_region f p.
Proof.
  intros f p;unfold selected;destruct(Nat.leb _ _);try discriminate.
  generalize(PTree.elements(fn_code f)). induction l as[|[pc i]rest];simpl;try discriminate.
  destruct(candidate_at f pc)as[q|]eqn:C;auto.
  intro EQ;inv EQ;eapply candidate_at_sound;eauto.
Qed.
Lemma transparent_kind: forall id base i next,
  transparent id base i=Some next ->
  i=Inop next \/ (exists r, i=Iop Omove(r::nil)r next) \/
  i=Iop(Oaddrsymbol id Ptrofs.zero)nil base next.
Proof.
  intros id base i next. destruct i as[n|op args dst n|chunk addr args dst n|chunk addr args src n|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret];try discriminate;simpl.
  - intro E;inv E;auto.
  - destruct op;try discriminate.
    + destruct args as[|r [|r2 tail]];try discriminate.
      destruct(peq r dst);try discriminate;subst. intro E;inv E;right;left;eauto.
    + destruct args;try discriminate.
      match goal with |-context[peq id ?sym] => destruct(peq id sym);try discriminate;subst sym end.
      destruct(peq base dst);try discriminate;subst.
      match goal with |-context[Ptrofs.eq ?ofs Ptrofs.zero] => destruct(Ptrofs.eq ofs Ptrofs.zero)eqn:O;try discriminate;apply Ptrofs.same_if_eq in O;subst ofs end.
      intro E;inv E;auto.
Qed.
Lemma transparent_not_store: forall id base i next,
  transparent id base i=Some next -> (match i with Istore _ _ _ _ _=>False|_=>True end).
Proof. intros;destruct(transparent_kind _ _ _ _ H)as[EQ|[EX|EQ]];try(subst;exact I). destruct EX as[r EQ];subst;exact I. Qed.
Lemma path_nonempty: forall f id base src previous nodes last exit,
  valid_path f id base src previous nodes last exit -> nodes<>nil.
Proof. intros;destruct nodes;simpl in *;[contradiction|discriminate]. Qed.
Lemma path_last: forall f id base src previous nodes last exit,
  valid_path f id base src previous nodes last exit ->
  In last nodes /\ (fn_code f)!last=Some(Istore Mint32(Aindexed(Int64.repr 4))(base::nil)src exit).
Proof.
  intros f id base src previous nodes;revert previous;induction nodes as[|pc rest IH];simpl;intros;try contradiction.
  destruct H as[NE [PRE BODY]]. destruct rest as[|next tail].
  - destruct BODY as[-> GET];split;auto.
  - destruct BODY as(i&GET&T&VALID). destruct(IH _ _ _ VALID);split;auto.
Qed.
Lemma path_member: forall f id base src previous nodes last exit pc,
  valid_path f id base src previous nodes last exit ->In pc nodes ->
  pc<>fn_entrypoint f /\
  ((pc=last /\ (fn_code f)!pc=Some(Istore Mint32(Aindexed(Int64.repr 4))(base::nil)src exit)) \/
   exists i next, (fn_code f)!pc=Some i /\ transparent id base i=Some next).
Proof.
  intros f id base src previous nodes;revert previous;induction nodes as[|q rest IH];simpl;intros;try contradiction.
  destruct H as[NE[PRE BODY]]. destruct H0 as[EQ|IN].
  - subst q. split;auto. destruct rest as[|next tail];auto. right;destruct BODY as(i&GET&T&VALID);eauto.
  - destruct rest as[|next tail];try contradiction. destruct BODY as(i&GET&T&VALID);eapply IH;eauto.
Qed.
Lemma path_predecessor: forall f id base src previous nodes last exit pc i q,
  valid_path f id base src previous nodes last exit ->In q nodes ->
  (fn_code f)!pc=Some i ->In q(successors_instr i) -> pc=previous \/ In pc nodes.
Proof.
  intros f id base src previous nodes;revert previous;induction nodes as[|head rest IH];simpl;intros;try contradiction.
  destruct H as[NE[PRE BODY]]. destruct H0 as[EQ|IN].
  - subst q;left;eauto.
  - destruct rest as[|next tail];try contradiction. destruct BODY as(j&GET&T&VALID).
    destruct(IH _ _ _ _ _ _ VALID IN H1 H2);auto.
Qed.
Lemma different_offsets: Int64.zero<>Int64.repr 4.
Proof. intro H;apply(f_equal Int64.unsigned)in H;vm_compute in H;discriminate. Qed.
Lemma first_not_path: forall f p, valid_region f p -> ~In(first_pc p)(path p).
Proof.
  intros f p V IN. destruct(path_member _ _ _ _ _ _ _ _ _ (region_path _ _ V) IN)as[_ [[EQ GET]|(i&next&GET&T)]].
  - pose proof(region_first _ _ V)as F. rewrite GET in F;inv F;exact(different_offsets H1).
  - pose proof(region_first _ _ V)as F. rewrite GET in F;inv F;discriminate.
Qed.
Lemma path_successor_member: forall f id base src previous nodes last exit pc i next,
  valid_path f id base src previous nodes last exit ->In pc nodes ->
  (fn_code f)!pc=Some i ->transparent id base i=Some next ->In next nodes.
Proof.
  intros f id base src previous nodes;revert previous;induction nodes as[|q rest IH];simpl;intros;try contradiction.
  destruct H as[NE[PRE BODY]]. destruct H0 as[EQ|IN].
  - subst q. destruct rest as[|hd tail].
    + destruct BODY as[EQ GET];rewrite GET in H1;inv H1;discriminate.
    + destruct BODY as(j&GET&TR&VALID);rewrite GET in H1;inv H1;rewrite TR in H2;inv H2;simpl;auto.
  - destruct rest as[|hd tail];try contradiction. destruct BODY as(j&GET&TR&VALID).
    right;eapply IH;eauto.
Qed.
Lemma producer_not_sensitive: forall f p, valid_region f p ->
  producer_pc p<>first_pc p /\ ~In(producer_pc p)(path p).
Proof.
  intros f p V;split.
  - intro EQ;pose proof(region_producer _ _ V)as P;pose proof(region_first _ _ V)as F;congruence.
  - intro IN. apply(first_not_path _ _ V).
    eapply path_successor_member;eauto using region_path,region_producer.
    simpl. destruct(peq _ _);try congruence. destruct(peq _ _);try congruence.
    rewrite Ptrofs.eq_true;reflexivity.
Qed.
Definition not_sensitive f pc := forall p, selected f=Some p -> pc<>first_pc p /\ ~In pc(path p).
Lemma entry_not_sensitive: forall f, not_sensitive f(fn_entrypoint f).
Proof.
  red;intros. pose proof(selected_sound _ _ H)as V;split.
  - pose proof(region_not_entry _ _ V);congruence.
  - intro IN;pose proof(path_member _ _ _ _ _ _ _ _ _ (region_path _ _ V) IN)as[NE _];congruence.
Qed.
Lemma successor_safe: forall f pc i next,
  (fn_code f)!pc=Some i ->In next(successors_instr i) ->not_sensitive f pc ->
  (forall p, selected f=Some p ->pc<>producer_pc p) ->not_sensitive f next.
Proof.
  unfold not_sensitive;intros f pc i next CODE IN SAFE NPRO p SEL.
  pose proof(selected_sound _ _ SEL)as V. destruct(SAFE _ SEL)as[NF NP]. split.
  - intro EQ;subst next. apply(NPRO _ SEL). eapply region_first_pred;eauto.
  - intro MEM;destruct(path_predecessor _ _ _ _ _ _ _ _ _ _ _ (region_path _ _ V) MEM CODE IN);tauto.
Qed.
Lemma nonproducer: forall f pc i,
  (fn_code f)!pc=Some i ->
  (match i with Iop _ _ _ _=>False|_=>True end) ->
  forall p, selected f=Some p ->pc<>producer_pc p.
Proof. intros f pc i CODE NOP p SEL EQ;subst pc;pose proof(region_producer _ _ (selected_sound _ _ SEL));rewrite CODE in H;inv H;contradiction. Qed.
Lemma nonstore_safe: forall f pc i,
  (fn_code f)!pc=Some i ->
  (match i with Istore _ _ _ _ _=>False|_=>True end) ->
  (fn_code(transf_function f))!pc=Some i.
Proof.
  intros f pc i CODE NS. unfold transf_function;destruct(selected f)as[p|]eqn:SEL;auto.
  simpl. rewrite PTree.gmap,CODE;simpl. unfold transf_instr_cached.
  destruct(peq pc(first_pc p));subst.
  - pose proof(region_first _ _ (selected_sound _ _ SEL));rewrite CODE in H;inv H;contradiction.
  - destruct(peq pc(second_pc p));subst;auto.
    pose proof(path_last _ _ _ _ _ _ _ _ (region_path _ _ (selected_sound _ _ SEL)))as[_ LAST].
    rewrite CODE in LAST;inv LAST;contradiction.
Qed.
Lemma transformed_fields: forall f,
  fn_sig(transf_function f)=fn_sig f /\ fn_params(transf_function f)=fn_params f /\
  fn_stacksize(transf_function f)=fn_stacksize f /\ fn_entrypoint(transf_function f)=fn_entrypoint f.
Proof. intros;unfold transf_function;destruct(selected f);repeat split;reflexivity. Qed.
Lemma transformed_code: forall f pc i, (fn_code f)!pc=Some i ->
  (fn_code(transf_function f))!pc=Some(transf_instr f pc i).
Proof. intros;unfold transf_function,transf_instr;destruct(selected f);auto;simpl;rewrite PTree.gmap,H;reflexivity. Qed.
Lemma code_first: forall f p, selected f=Some p ->
  (fn_code(transf_function f))!(first_pc p)=Some(Iop Omakelong(source_reg p::source_reg p::nil)(fresh_reg f)
    (match path p with hd::_=>hd|_=>second_pc p end)).
Proof. intros;rewrite(transformed_code _ _ _ (region_first _ _ (selected_sound _ _ H))).
  unfold transf_instr;rewrite H;unfold transf_instr_cached;destruct(peq _ _);congruence. Qed.
Lemma code_second: forall f p, selected f=Some p ->
  (fn_code(transf_function f))!(second_pc p)=Some(Istore Mint64(Aindexed Int64.zero)(base_reg p::nil)(fresh_reg f)(after_pc p)).
Proof.
  intros;pose proof(selected_sound _ _ H)as V.
  destruct(path_last _ _ _ _ _ _ _ _ (region_path _ _ V))as[IN LAST].
  rewrite(transformed_code _ _ _ LAST). unfold transf_instr;rewrite H;unfold transf_instr_cached.
  destruct(peq (second_pc p)(first_pc p));[subst;exfalso;apply(first_not_path _ _ V);congruence|].
  destruct(peq _ _);congruence.
Qed.
Lemma source_reg_bound: forall f p, selected f=Some p ->Plt(source_reg p)(fresh_reg f).
Proof. intros;eapply fresh_reg_use;[apply(region_first _ _ (selected_sound _ _ H))|];simpl;auto. Qed.
Lemma base_reg_bound: forall f p, selected f=Some p ->Plt(base_reg p)(fresh_reg f).
Proof. intros;eapply fresh_reg_use;[apply(region_first _ _ (selected_sound _ _ H))|];simpl;auto. Qed.
Lemma path_exit_safe: forall f p, selected f=Some p ->not_sensitive f(after_pc p).
Proof. red;intros;rewrite H in H0;inv H0;pose proof(selected_sound _ _ H);split;eauto using region_exit_first,region_exit_path. Qed.
Lemma self_move_read: forall (rs:regset) r q, (rs#r <- (rs#r))#q=rs#q.
Proof. intros;rewrite Regmap.gsspec;destruct(peq q r);congruence. Qed.
Definition match_prog(p tp:program):=match_program(fun ctx f tf=>tf=transf_fundef f)eq p tp.
Global Instance TransfMemVectorIndirectLink: TransfLink match_prog :=TransfTotalLink transf_function.
Lemma transf_program_match: forall p, match_prog p(transf_program p).
Proof. intros;apply match_transform_program. Qed.
Section PRESERVATION.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Lemma functions_translated: forall v f, Genv.find_funct ge v=Some f -> Genv.find_funct tge v=Some(transf_fundef f).
Proof. exact(Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated: forall v f, Genv.find_funct_ptr ge v=Some f -> Genv.find_funct_ptr tge v=Some(transf_fundef f).
Proof. exact(Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved: forall id, Genv.find_symbol tge id=Genv.find_symbol ge id.
Proof. exact(Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact(Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig(transf_fundef f)=funsig f.
Proof. destruct f; simpl; auto. apply(proj1(transformed_fields f)). Qed.
Lemma find_function_translated: forall ros rs trs fd f,
  regs_match f rs trs ->
  (match ros with inl r => Plt r (fresh_reg f) | _ => True end) ->
  find_function ge ros rs=Some fd -> find_function tge ros trs=Some(transf_fundef fd).
Proof.
  unfold find_function; intros ros rs trs fd f REGS B FIND. destruct ros as[r|id].
  - rewrite REGS by auto. eapply functions_translated; eauto.
  - rewrite symbols_preserved; destruct(Genv.find_symbol ge id); try discriminate.
    eapply function_ptr_translated; eauto.
Qed.
Lemma builtin_arg_regs: forall f rs trs sp m arg v,
  regs_match f rs trs -> eval_builtin_arg ge (fun r=>rs#r) sp m arg v ->
  (forall r, In r(params_of_builtin_arg arg)->Plt r(fresh_reg f)) ->
  eval_builtin_arg ge (fun r=>trs#r) sp m arg v.
Proof.
  intros f rs trs sp m arg v R EV; induction EV; simpl; intros;
    try(constructor; eauto using in_or_app).
  rewrite <-R by eauto with coqlib; constructor.
Qed.
Lemma builtin_args_regs: forall f rs trs sp m args vl,
  regs_match f rs trs -> eval_builtin_args ge (fun r=>rs#r) sp m args vl ->
  (forall r, In r(params_of_builtin_args args)->Plt r(fresh_reg f)) ->
  eval_builtin_args ge (fun r=>trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl R EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs,in_or_app.
Qed.
Lemma indexed_global_zero: forall id sp rs base,
  rs#base=Genv.symbol_address ge id Ptrofs.zero ->
  eval_addressing ge sp(Aindexed Int64.zero)(rs##(base::nil))=Some(Genv.symbol_address ge id Ptrofs.zero).
Proof.
  intros;simpl;rewrite H;unfold Genv.symbol_address;destruct(Genv.find_symbol ge id);simpl;auto.
Qed.
Lemma indexed_global_four: forall id sp rs base,
  rs#base=Genv.symbol_address ge id Ptrofs.zero ->
  eval_addressing ge sp(Aindexed(Int64.repr 4))(rs##(base::nil))=Some(Genv.symbol_address ge id(Ptrofs.repr 4)).
Proof.
  intros;simpl;rewrite H;unfold Genv.symbol_address;destruct(Genv.find_symbol ge id);simpl;auto.
Qed.
Inductive match_frames: RTL.stackframe ->RTL.stackframe ->Prop :=
 | match_frames_intro: forall res f sp pc rs trs
     (NOT:not_sensitive f pc)(REGS:regs_match f rs trs),
     match_frames(Stackframe res f sp pc rs)(Stackframe res(transf_function f)sp pc trs).
Inductive match_states: RTL.state -> RTL.state ->Prop :=
 | match_normal: forall stk stk' f sp pc rs trs m
     (STACKS:list_forall2 match_frames stk stk')(NOT:not_sensitive f pc)(REGS:regs_match f rs trs),
     match_states(State stk f sp pc rs m)(State stk'(transf_function f)sp pc trs m)
 | match_prepared: forall stk stk' f sp rs trs m p
     (STACKS:list_forall2 match_frames stk stk')(SELECT:selected f=Some p)(REGS:regs_match f rs trs)
     (BASE:rs#(base_reg p)=Genv.symbol_address ge(global_id p)Ptrofs.zero),
     match_states(State stk f sp(first_pc p)rs m)(State stk'(transf_function f)sp(first_pc p)trs m)
 | match_pending: forall stk stk' f sp pc rest previous rs trs m0 m1 p
     (STACKS:list_forall2 match_frames stk stk')(SELECT:selected f=Some p)(REGS:regs_match f rs trs)
     (PATH:valid_path f(global_id p)(base_reg p)(source_reg p)previous(pc::rest)(second_pc p)(after_pc p))
     (MEMBER:In pc(path p))
     (BASE:rs#(base_reg p)=Genv.symbol_address ge(global_id p)Ptrofs.zero)
     (STORE:Mem.storev Mint32 m0(Genv.symbol_address ge(global_id p)Ptrofs.zero)rs#(source_reg p)=Some m1)
     (PACK:trs#(fresh_reg f)=Val.longofwords rs#(source_reg p)rs#(source_reg p)),
     match_states(State stk f sp pc rs m1)(State stk'(transf_function f)sp pc trs m0)
 | match_call: forall stk stk' fd args m(STACKS:list_forall2 match_frames stk stk'),
     match_states(Callstate stk fd args m)(Callstate stk'(transf_fundef fd)args m)
 | match_return: forall stk stk' v m(STACKS:list_forall2 match_frames stk stk'),
     match_states(Returnstate stk v m)(Returnstate stk' v m).
Lemma normal_nonop: forall f pc i next,
  (fn_code f)!pc=Some i ->In next(successors_instr i) ->not_sensitive f pc ->
  (match i with Iop _ _ _ _=>False|_=>True end) ->not_sensitive f next.
Proof. intros;eapply successor_safe;eauto using nonproducer. Qed.
Lemma pending_kind: forall f p pc previous rest,
  selected f=Some p ->
  valid_path f(global_id p)(base_reg p)(source_reg p)previous(pc::rest)(second_pc p)(after_pc p) ->
  (rest=nil /\ pc=second_pc p /\ (fn_code f)!pc=Some(Istore Mint32(Aindexed(Int64.repr 4))(base_reg p::nil)(source_reg p)(after_pc p))) \/
  exists next tail i, rest=next::tail /\ (fn_code f)!pc=Some i /\ transparent(global_id p)(base_reg p)i=Some next /\
     valid_path f(global_id p)(base_reg p)(source_reg p)pc rest(second_pc p)(after_pc p).
Proof. intros;simpl in H0;destruct H0 as[NE[PRE BODY]];destruct rest as[|next tail];[left;tauto|right;destruct BODY as(i&CODE&T&VALID);eauto 8]. Qed.
Lemma known_write_read: forall(rs:regset)r v q, v=rs#r ->(rs#r <- v)#q=rs#q.
Proof. intros;subst;apply self_move_read. Qed.
Lemma prepared_step: forall stk stk' f sp rs trs m p t S2,
  list_forall2 match_frames stk stk' ->selected f=Some p ->regs_match f rs trs ->
  rs#(base_reg p)=Genv.symbol_address ge(global_id p)Ptrofs.zero ->
  RTL.step ge(State stk f sp(first_pc p)rs m)t S2 ->
  exists S2', RTL.step tge(State stk'(transf_function f)sp(first_pc p)trs m)t S2' /\match_states S2 S2'.
Proof.
  intros stk stk' f sp rs trs m p t S2 STACKS SELECT REGS BASE STEP.
  pose proof(selected_sound _ _ SELECT)as V. pose proof(region_first _ _ V)as FIRST.
  inv STEP;match goal with C:(fn_code f)!_=Some _ |- _ => rewrite FIRST in C;inv C end.
  match goal with E:eval_addressing _ _ _ _=Some _ |- _ => rewrite(indexed_global_zero _ _ _ _ BASE)in E;inv E end.
  destruct(path p)as[|next tail]eqn:NODES.
  { pose proof(region_path _ _ V);rewrite NODES in H;simpl in H;contradiction. }
  econstructor;split.
  - eapply exec_Iop. pose proof(code_first _ _ SELECT)as C;rewrite NODES in C;exact C.
    simpl;rewrite REGS by(eapply source_reg_bound;eauto);reflexivity.
  - eapply match_pending with(previous:=first_pc p)(rest:=tail)(p:=p);eauto using regs_match_fresh.
    + pose proof(region_path _ _ V);rewrite NODES in H;exact H.
    + rewrite NODES;simpl;auto.
    + apply Regmap.gss.
Qed.
Lemma pending_step: forall stk stk' f sp pc rest previous rs trs m0 m1 p t S2,
  list_forall2 match_frames stk stk' ->selected f=Some p ->regs_match f rs trs ->
  valid_path f(global_id p)(base_reg p)(source_reg p)previous(pc::rest)(second_pc p)(after_pc p) ->
  In pc(path p) ->rs#(base_reg p)=Genv.symbol_address ge(global_id p)Ptrofs.zero ->
  Mem.storev Mint32 m0(Genv.symbol_address ge(global_id p)Ptrofs.zero)rs#(source_reg p)=Some m1 ->
  trs#(fresh_reg f)=Val.longofwords rs#(source_reg p)rs#(source_reg p) ->
  RTL.step ge(State stk f sp pc rs m1)t S2 ->
  exists S2', RTL.step tge(State stk'(transf_function f)sp pc trs m0)t S2' /\match_states S2 S2'.
Proof.
  intros stk stk' f sp pc rest previous rs trs m0 m1 p t S2 STACKS SELECT REGS PATH MEMBER BASE STORE PACK STEP.
  destruct(pending_kind _ _ _ _ _ SELECT PATH)as[[REST[PC CODE]]|(next&tail&i&REST&CODE&TR&TAIL)].
  - subst pc rest. inv STEP;match goal with C:(fn_code f)!_=Some _ |- _ => rewrite CODE in C;inv C end.
    match goal with E:eval_addressing _ _ _ _=Some _ |- _ => rewrite(indexed_global_four _ _ _ _ BASE)in E;inv E end.
    econstructor;split.
    + eapply exec_Istore with(a:=Genv.symbol_address ge(global_id p)Ptrofs.zero).
      apply code_second;auto.
      rewrite(regs_match_list _ _ _ _ REGS)by(intros r IN;simpl in IN;destruct IN as[EQ|[]];subst r;eapply base_reg_bound;eauto).
      rewrite <-(indexed_global_zero (global_id p) sp rs (base_reg p) BASE).
      apply eval_addressing_preserved;exact symbols_preserved.
      rewrite PACK;eapply global_broadcast;eauto.
    + constructor;eauto using path_exit_safe.
  - subst rest. assert(NEXTMEM:In next(path p)).
    { eapply path_successor_member;eauto using region_path,selected_sound. }
    destruct(transparent_kind _ _ _ _ TR)as[EQ|[EX|EQ]].
    + subst i. inv STEP;match goal with C:(fn_code f)!_=Some _ |- _ => rewrite CODE in C;inv C end.
      econstructor;split. eapply exec_Inop;eauto using nonstore_safe.
      eapply match_pending;eauto.
    + destruct EX as[r EQ];subst i. inv STEP;match goal with C:(fn_code f)!_=Some _ |- _ => rewrite CODE in C;inv C end.
      match goal with E:eval_operation _ _ _ _ _=Some _ |- _ => simpl in E;inv E end.
      assert(RB:Plt res(fresh_reg f))by(eapply fresh_reg_use;eauto;simpl;auto).
      assert(TCODE:(fn_code(transf_function f))!pc=Some(Iop Omove(res::nil)res pc'))by(eapply nonstore_safe;eauto;exact I).
      econstructor;split. eapply exec_Iop with(v:=trs#res);eauto;reflexivity.
      eapply match_pending with(p:=p)(previous:=pc)(rest:=tail);eauto.
      * rewrite REGS by auto;apply regs_match_set;auto.
      * rewrite self_move_read;auto.
      * rewrite self_move_read;auto.
      * rewrite Regmap.gso by(extlia).
        rewrite self_move_read;exact PACK.
    + subst i. inv STEP;match goal with C:(fn_code f)!_=Some _ |- _ => rewrite CODE in C;inv C end.
      match goal with E:eval_operation _ _ _ _ _=Some _ |- _ => simpl in E;inv E end.
      assert(TCODE:(fn_code(transf_function f))!pc=Some(Iop(Oaddrsymbol(global_id p)Ptrofs.zero)nil(base_reg p)pc'))by(eapply nonstore_safe;eauto;exact I).
      econstructor;split.
      eapply exec_Iop with(v:=Genv.symbol_address ge(global_id p)Ptrofs.zero);eauto.
      simpl;unfold Genv.symbol_address;rewrite symbols_preserved;reflexivity.
      eapply match_pending with(p:=p)(previous:=pc)(rest:=tail);eauto using regs_match_set.
      * rewrite Regmap.gss;reflexivity.
      * rewrite known_write_read by congruence;exact STORE.
      * rewrite Regmap.gso by(pose proof(base_reg_bound _ _ SELECT);extlia).
        rewrite known_write_read by congruence;exact PACK.
Qed.
Lemma normal_code: forall f pc i, (fn_code f)!pc=Some i ->not_sensitive f pc ->
 (fn_code(transf_function f))!pc=Some i.
Proof.
 intros f pc i CODE NOT;rewrite(transformed_code _ _ _ CODE).
 unfold transf_instr;destruct(selected f)as[p|]eqn:SEL;auto.
 destruct(NOT _ SEL)as[NF NP];unfold transf_instr_cached.
 destruct(peq pc(first_pc p));try congruence.
 destruct(peq pc(second_pc p));try congruence.
 exfalso;apply NP;subst pc;eapply path_last;eauto using region_path,selected_sound.
Qed.
Ltac BOUNDS := match goal with CODE:(fn_code ?f)!?pc=Some ?i |- _ =>
 assert(USES:forall r,In r(instr_uses i)->Plt r(fresh_reg f))by(intros;eapply fresh_reg_use;eauto)
end.
Lemma normal_step: forall stk stk' f sp pc rs trs m t S2,
 list_forall2 match_frames stk stk' ->not_sensitive f pc ->regs_match f rs trs ->
 RTL.step ge(State stk f sp pc rs m)t S2 ->
 exists S2',RTL.step tge(State stk'(transf_function f)sp pc trs m)t S2' /\ match_states S2 S2'.
Proof.
 intros stk stk' f sp pc rs trs m t S2 STACKS NOT REGS STEP.
 inv STEP;
 match goal with C:(fn_code f)!_=Some _ |- _ => rename C into CODE end;
 BOUNDS;
 pose proof(normal_code _ _ _ CODE NOT)as TCODE.
 - econstructor;split;eauto using exec_Inop.
   constructor;auto. eapply normal_nonop;eauto;simpl;auto.
 - match goal with E:eval_operation _ _ _ _ _=Some _ |- _ =>rename E into EVAL end.
   econstructor;split. eapply exec_Iop;eauto.
   rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;auto).
   rewrite <-EVAL;apply eval_operation_preserved;exact symbols_preserved.
   destruct(selected f)as[p|]eqn:SEL.
   + destruct(peq pc(producer_pc p))as[EQ|NE].
     * subst pc;pose proof(region_producer _ _ (selected_sound _ _ SEL))as PROD.
       rewrite CODE in PROD;inv PROD;simpl in EVAL;inv EVAL.
       eapply match_prepared;eauto using regs_match_set;apply Regmap.gss.
     * constructor;auto using regs_match_set. eapply successor_safe;eauto;simpl;auto.
       intros q Q;rewrite SEL in Q;inv Q;auto.
   + constructor;auto using regs_match_set. eapply successor_safe;eauto;simpl;auto.
     intros q Q;congruence.
 - match goal with E:eval_addressing _ _ _ _=Some _ |- _ =>rename E into EVAL end.
   econstructor;split. eapply exec_Iload;eauto.
   rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;auto).
   rewrite <-EVAL;apply eval_addressing_preserved;exact symbols_preserved.
   constructor;auto using regs_match_set. eapply normal_nonop;eauto;simpl;auto.
 - match goal with E:eval_addressing _ _ _ _=Some _ |- _ =>rename E into EVAL end.
   econstructor;split. eapply exec_Istore;eauto.
   rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;auto).
   rewrite <-EVAL;apply eval_addressing_preserved;exact symbols_preserved.
   rewrite REGS by(apply USES;simpl;auto);eauto.
   constructor;auto. eapply normal_nonop;eauto;simpl;auto.
 - assert(FIND:find_function tge ros trs=Some(transf_fundef fd)).
   {eapply find_function_translated;eauto;destruct ros;simpl;auto;apply USES;simpl;auto. }
   econstructor;split. eapply exec_Icall with(fd:=transf_fundef fd);eauto.
   apply sig_preserved.
   rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;destruct ros;simpl;auto).
   constructor. constructor;auto. constructor;auto.
   eapply normal_nonop;eauto;simpl;auto.
 - assert(FIND:find_function tge ros trs=Some(transf_fundef fd)).
   {eapply find_function_translated;eauto;destruct ros;simpl;auto;apply USES;simpl;auto. }
   econstructor;split. eapply exec_Itailcall with(fd:=transf_fundef fd);eauto.
   apply sig_preserved.
   rewrite(proj1(proj2(proj2(transformed_fields f))));eauto.
   rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;destruct ros;simpl;auto).
   constructor;auto.
 - econstructor;split. eapply exec_Ibuiltin;eauto.
   eapply eval_builtin_args_preserved with(ge1:=ge);eauto. exact symbols_preserved.
   eapply builtin_args_regs;eauto.
   eapply external_call_symbols_preserved;eauto;apply senv_preserved.
   constructor;auto using regs_match_setres. eapply normal_nonop;eauto;simpl;auto.
 - econstructor;split. eapply exec_Icond;eauto.
   rewrite(regs_match_list _ _ _ _ REGS)by(intros;apply USES;simpl;auto);eauto.
   constructor;auto. eapply normal_nonop;eauto;simpl;destruct b;auto.
 - econstructor;split. eapply exec_Ijumptable;eauto.
   rewrite REGS by(apply USES;simpl;auto);eauto.
   constructor;auto. eapply normal_nonop;eauto;simpl;auto. eapply list_nth_z_in;eauto.
 - econstructor;split. eapply exec_Ireturn;eauto.
   rewrite(proj1(proj2(proj2(transformed_fields f))));eauto.
   destruct or;simpl. rewrite REGS by(apply USES;simpl;auto). constructor;auto.
   constructor;auto.
Qed.
Lemma step_simulation:
 forall S1 t S2,RTL.step ge S1 t S2 ->forall S1',match_states S1 S1' ->
 exists S2',RTL.step tge S1' t S2' /\match_states S2 S2'.
Proof.
 intros S1 t S2 STEP S1' MS;inv MS.
 - eapply normal_step;eauto.
 - eapply prepared_step;eauto.
 - eapply pending_step;eauto.
 - inv STEP.
   + simpl. econstructor;split.
     replace(fn_entrypoint f)with(fn_entrypoint(transf_function f))by(apply(proj2(proj2(proj2(transformed_fields f))))).
     replace(fn_params f)with(fn_params(transf_function f))by(apply(proj1(proj2(transformed_fields f)))).
     eapply exec_function_internal;eauto.
     rewrite(proj1(transformed_fields f));auto.
     rewrite(proj1(proj2(proj2(transformed_fields f))));eauto.
     rewrite(proj2(proj2(proj2(transformed_fields f)))),(proj1(proj2(transformed_fields f))).
     constructor;auto using entry_not_sensitive,regs_match_refl.
   + econstructor;split. eapply exec_function_external;eauto.
     eapply external_call_symbols_preserved;eauto;apply senv_preserved.
     constructor;auto.
 - inv STEP. inv STACKS. inv H1. econstructor;split. eapply exec_return;eauto.
   constructor;auto using regs_match_set.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 -> exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros;inv H. econstructor;split. econstructor.
  - eapply(Genv.init_mem_transf TRANSL);eauto.
  - rewrite symbols_preserved.
    exact(eq_trans (f_equal (Genv.find_symbol ge) (match_program_main TRANSL)) H1).
  - eapply function_ptr_translated;eauto.
  - rewrite <-H3;apply sig_preserved.
  - constructor;constructor.
Qed.
Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. intros;inv H0;inv H;inv STACKS;constructor. Qed.
Theorem transf_program_correct:
  forward_simulation(RTL.semantics prog)(RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - exact step_simulation.
Qed.

End PRESERVATION.
End IndirectProof.
