Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Semantics.
Require Import Crypto.Assembly.Equivalence.

Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface. (* coercions *)
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Memory.
Require coqutil.Map.SortedListWord.
Require coqutil.Word.Naive.
Local Notation mem_state := (SortedListWord.map (Naive.word 64) Byte.byte).

Local Coercion ExprRef : idx >-> expr.

Section WithCtx.
Context (frame : mem_state).
Context (G : symbol -> option N).
Local Notation eval := (Symbolic.eval G).
Local Notation dag_ok := (Symbolic.dag_ok G).

Section WithDag.
Context (d : dag).
Local Notation eval := (Symbolic.eval G d).

Definition R_reg (x : option idx) (v : N) : Prop :=
  forall i, x = Some i -> eval i v.
Definition R_regs : Symbolic.reg_state -> Semantics.reg_state -> Prop :=
  Tuple.fieldwise R_reg.

Definition R_flag (x : option idx) (ob : option bool) : Prop :=
  forall i, x = Some i -> exists b, eval i (N.b2n b) /\ ob = Some b.
Definition R_flags : Symbolic.flag_state -> Semantics.flag_state -> Prop :=
  Tuple.fieldwise R_flag.


Definition R_cell64' (a v : Z) : mem_state -> Prop :=
  eq (OfListWord.map.of_list_word_at (word.of_Z a)
  (HList.tuple.to_list (LittleEndian.split 8 v))).

Definition R_cell64 (ia iv : idx) (m : mem_state) : Prop :=
  exists a, eval ia a /\
  exists v, eval iv v /\
  R_cell64' (Z.of_N a) (Z.of_N v) m.

Fixpoint R_mem (sm : Symbolic.mem_state) : mem_state -> Prop :=
  match sm with
  | nil => eq frame
  | cons (ia, iv) sm' => sep (R_cell64 ia iv) (R_mem sm')
  end.
End WithDag.

Axiom TODOmem : Semantics.mem_state -> mem_state.
Definition R (ss : symbolic_state) (ms : machine_state) : Prop :=
  let (mr, mf, mm) := ms in
  let (d, sr, sf, sm) := ss in
  dag_ok d /\ R_regs d sr mr /\ R_flags d sf mf /\ R_mem d sm (TODOmem mm).

Lemma get_flag_R s m f (HR : R s m) :
  forall i, Symbolic.get_flag s f = Some i ->
  exists b, eval s i (N.b2n b) /\
  Semantics.get_flag m f = Some b.
Proof.
  repeat (
    DestructHead.destruct_head @prod||
    DestructHead.destruct_head @Semantics.machine_state||
    DestructHead.destruct_head @Semantics.flag_state||
    DestructHead.destruct_head @Symbolic.symbolic_state||
    DestructHead.destruct_head @Symbolic.flag_state||
    DestructHead.destruct_head @FLAG
  );
  cbn [R_flags Tuple.fieldwise Tuple.fieldwise' fst snd] in *; intuition idtac.
Qed.

Lemma R_set_flag_internal s m f (HR : R s m) (i:idx) b (Hi : eval s i (N.b2n b)) :
  R_flags s (Symbolic.set_flag s f i) (Semantics.set_flag m f b).
Proof.
  repeat (
    DestructHead.destruct_head @prod||
    DestructHead.destruct_head @Semantics.machine_state||
    DestructHead.destruct_head @Semantics.flag_state||
    DestructHead.destruct_head @Symbolic.symbolic_state||
    DestructHead.destruct_head @Symbolic.flag_state||
    DestructHead.destruct_head @FLAG
  );
  cbv [R_flags Tuple.fieldwise Tuple.fieldwise' fst snd] in *; intuition idtac;
  cbv [R_flag]; intros ? HH; inversion HH; clear HH; subst; eauto.
Qed.

Lemma R_SetFlag s m f (HR : R s m) (i:idx) b (Hi : eval s i (N.b2n b)) :
  forall s', Symbolic.SetFlag f i s = Success (tt, s') ->
  R s' (SetFlag m f b).
Proof.
  destruct s; cbv [Symbolic.SetFlag Symbolic.update_flag_with Symbolic.set_flag] in *;
    intros; inversion_ErrorT_step; Prod.inversion_prod; subst.
  cbv [R].
  intuition idtac.
  all : try eapply R_set_flag_internal; eauto.
  all : cbv [R] in *; intuition idtac.
Qed.

Lemma R_HavocFlags s m (HR : R s m) :
  forall s', Symbolic.HavocFlags s = Success (tt, s') ->R s' (HavocFlags m).
Proof.
  destruct s; cbv [Symbolic.HavocFlags Symbolic.update_flag_with] in *;
    intros; inversion_ErrorT_step; Prod.inversion_prod; subst.
  cbv [R]; intuition idtac; try solve [cbv [R] in *; intuition idtac].
  cbv [R_flags Tuple.fieldwise Tuple.fieldwise' R_flag]; cbn;
    intuition idtac; Option.inversion_option.
Qed.

Local Arguments Tuple.tuple : simpl never.
Local Arguments Tuple.fieldwise : simpl never.
Local Arguments Tuple.from_list_default : simpl never.
Local Arguments Tuple.to_list : simpl never.
Local Arguments Tuple.nth_default ! _ _.
Local Arguments set_reg ! _ _.
Local Arguments N.ones ! _.

Notation subsumed d1 d2 := (forall i v, eval d1 i v -> eval d2 i v).
Local Infix ":<" := subsumed (at level 70, no associativity).

Lemma R_flag_subsumed d s m (HR : R_flag d s m) d' (Hlt : d :< d')
  : R_flag d' s m.
Proof.
  cbv [R_flag] in *; intros.
  case (HR i H) as (?&?&?); subst; eauto.
Qed.

Lemma R_flags_subsumed d s m (HR : R_flags d s m) d' (Hlt : d :< d')
  : R_flags d' s m.
Proof.
  cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *;
    intuition eauto using R_flag_subsumed.
Qed.

Lemma R_reg_subsumed d s m (HR : R_reg d s m) d' (Hlt : d :< d')
  : R_reg d' s m.
Proof. cbv [R_reg] in *; eauto. Qed.

Lemma R_regs_subsumed d s m (HR : R_regs d s m) d' (Hlt : d :< d')
  : R_regs d' s m.
Proof.
  cbv [R_regs Tuple.fieldwise Tuple.fieldwise'] in *;
    intuition eauto using R_reg_subsumed.
Qed.

Lemma R_mem_subsumed d s m (HR : R_mem d s m) d' (Hlt : d :< d')
  : R_mem d' s m. Admitted.

Lemma R_subsumed s m (HR : R s m) d' (Hd' : dag_ok d') (Hlt : s :< d')
  (s' := update_dag_with s (fun _ => d')) : R s' m.
Proof.
  destruct s, m; case HR as (Hd&Hr&Hf&Hm);
    cbv [update_dag_with] in *; cbn in *;
    intuition eauto using R_flags_subsumed, R_regs_subsumed, R_mem_subsumed.
Qed.

Lemma Tuple__nth_default_to_list {A} n (xs : Tuple.tuple A n) (d : A) :
  forall i, List.nth_default d (Tuple.to_list _ xs) i = Tuple.nth_default d i xs.
Proof.
Admitted.

Lemma get_reg_R s m (HR : R s m) ri :
  forall i, Symbolic.get_reg s ri = Some i ->
  exists v, eval s i v /\ Tuple.nth_default 0%N ri (m : reg_state) = v.
Proof.
  cbv [Symbolic.get_reg]; intros.
  rewrite <-Tuple__nth_default_to_list in H.
  cbv [nth_default] in H; BreakMatch.break_match_hyps; subst; [|solve[congruence] ].
  destruct s,m; cbn in *; destruct HR as (_&?&_); cbv [R_regs R_reg] in *.
  eapply Tuple.fieldwise_to_list_iff in H.
  eapply Forall.Forall2_forall_iff_nth_error in H; cbv [Option.option_eq] in H.

  rewrite Heqo in H.
  BreakMatch.break_match_hyps; [|solve[contradiction]].
  specialize (H _ eq_refl).
  eexists; split; [eassumption|].

  rewrite <-Tuple__nth_default_to_list.
  cbv [nth_default].
  rewrite Heqo0.
  trivial.
Qed.

Ltac step_symex0 :=
  match goal with
  | H : (x <- ?v; ?k)%x86symex ?s = Success _ |- _  =>
    unfold bind at 1 in H;
    let x := fresh x in
    let HH := fresh "HS" x in
    destruct v as [[x ?]|] eqn:HH in H;
    cbn [ErrorT.bind] in H; [|solve[exfalso;clear-H;inversion H]]
  end.
Ltac step_symex := step_symex0.

Lemma GetFlag_R s m (HR : R s m) f i s' (H : GetFlag f s = Success (i, s')) :
  exists b, eval s i (N.b2n b) /\ Semantics.get_flag m f = Some b /\ s = s'.
Proof.
  cbv [GetFlag some_or] in H.
  destruct (Symbolic.get_flag _ _) eqn:? in H;
    ErrorT.inversion_ErrorT; Prod.inversion_prod; subst; [].
  eapply get_flag_R in Heqo; eauto; destruct Heqo as (b&Hb&Hf); eauto.
Qed.

Ltac step_GetFlag :=
  match goal with
  | H : GetFlag ?f ?s = Success (?i0, _) |- _ =>
    let v := fresh "v" f in let Hv := fresh "H" v
    in let Hi := fresh "H" i0 in let Heq := fresh H "eq" in
    case (GetFlag_R s _ ltac:(eassumption) _ _ _ H) as (v&Hi&Hvcf&Heq); clear H;
    (let i := fresh "i" f in try rename i0 into i);
    (try match type of Heq with _ = ?s' => subst s' end)
  end.
Ltac step_symex1 := first [step_symex0 | step_GetFlag].
Ltac step_symex ::= step_symex1.

Lemma Merge_R s m (HR : R s m) e v (H : eval s e v) :
  forall i s', Merge e s = Success (i, s') ->
  R s' m /\ eval s' i v.
Proof.
  cbv [Merge].
  inversion 1; subst; match goal with H: ?x = ?x |- _ => clear H end.
  destruct s, m.
  case (eval_merge _ e _ dag_state (proj1 HR) H) as (He'&Hd'&Hes).
  intuition eauto using R_subsumed.
Qed.

Ltac step_Merge :=
  match goal with
  | H : Merge ?e ?s = Success (?i, ?s') |- _ =>
    let Hs' := fresh "H" s' in let v := fresh "v" i in let Hi := fresh "H" i in
    let t := open_constr:(fun A B => Merge_R s _ A e ?[v] B _ _ H) in
    unshelve (edestruct t as (Hs'&Hi); clear H); shelve_unifiable;
    [eassumption|..]
  end.
Ltac step_symex2 := first [step_symex1 | step_Merge].
Ltac step_symex ::= step_symex2.

Lemma App_R s m (HR : R s m) e v (H : eval_node G s e v) :
  forall i s', Symbolic.App e s = Success (i, s') ->
  R s' m /\ eval s' i v.
Proof.
  cbv [Symbolic.App]; intros.
  eapply Merge_R in H0; intuition eauto using eval_simplify.
Qed.

Ltac step_App :=
  match goal with
  | H : Symbolic.App ?n ?s = Success (?i, ?s') |- _ =>
    let Hs' := fresh "H" s' in let v := fresh "v" i in let Hi := fresh "H" i in
    let t := open_constr:(fun A B => App_R s _ A n ?[v] B _ _ H) in
    unshelve (edestruct t as (Hs'&Hi); clear H); shelve_unifiable;
    [eassumption|..]
  end.
Ltac step_symex3 := first [step_symex2 | step_App].
Ltac step_symex ::= step_symex3.

Import ListNotations.

Lemma R_SetOperand s m (HR : R s m)
  sz sa a i s' (H : @Symbolic.SetOperand sz sa a i s = Success (tt, s'))
  v (Hv : eval s i v)
  : exists m', SetOperand sa sz m a v = Some m' /\ R s' m'.
Proof.
  destruct a in *; cbn in H; [ | | solve [inversion H] ];
    cbv [SetOperand Crypto.Util.Option.bind SetReg64 update_reg_with Symbolic.update_reg_with] in *;
    repeat (BreakMatch.break_innermost_match_hyps; Prod.inversion_prod; ErrorT.inversion_ErrorT; subst).

  { eexists; split; [exact eq_refl|].
    destruct s; cbv [R] in *; cbn in *; intuition idtac.
    cbv [R_regs Symbolic.set_reg set_reg index_and_shift_and_bitcount_of_reg].
    eapply Tuple.fieldwise_to_list_iff.
    unshelve erewrite 2Tuple.from_list_default_eq, 2Tuple.to_list_from_list;
      try solve [rewrite ?Crypto.Util.ListUtil.length_set_nth, ?Crypto.Util.ListUtil.length_update_nth, ?Tuple.length_to_list; trivial].
    eapply Crypto.Util.ListUtil.Forall2_update_nth.
    { eapply Tuple.fieldwise_to_list_iff; eassumption. }
    cbv [R_reg bitmask_of_reg index_and_shift_and_bitcount_of_reg];
      intros; Option.inversion_option; subst.
    eapply Ndec.Neqb_complete in Heqb; rewrite Heqb.
    replace (reg_offset r) with 0%N by (destruct r;cbv;trivial||cbv in Heqb;inversion Heqb).
    rewrite (N.shiftl_0_r v), (N.shiftl_0_r (N.ones 64)).
    clear H6.
    rename v2 into x.
    assert (Hx64: N.ldiff (*reg*)x (N.ones 64) = 0%N) by admit.
    assert (Hv64: N.land (*val*)v (N.ones 64) = v) by admit.
    rewrite N.land_comm, Hv64, Hx64, N.lor_0_r; trivial. }
  { eexists; split; [exact eq_refl|].
    repeat (step_symex; []).
    cbv [GetReg64 some_or] in *.
    pose proof (get_reg_R s _ ltac:(eassumption) (reg_index r)) as Hr.
    destruct (Symbolic.get_reg _ _) in *; cbn [ErrorT.bind] in H;
      ErrorT.inversion_ErrorT; Prod.inversion_prod; subst;cbn [fst snd] in *.
    specialize (Hr _ eq_refl); case Hr as (?&?&?).
    step_App.
    { econstructor.
      { econstructor; try eassumption. econstructor; try eassumption. econstructor. }
      { (* interp_op set_slice *)
        instantiate (1:=N.lor (N.land (bitmask_of_reg r) (N.shiftl v (reg_offset r))) (N.ldiff x (bitmask_of_reg r))); exact eq_refl||admit. } }
    repeat (Prod.inversion_prod; ErrorT.inversion_ErrorT; subst).
    destruct s1; cbv [R] in *; cbn in *; intuition idtac.
    cbv [R_regs Symbolic.set_reg set_reg index_and_shift_and_bitcount_of_reg].
    eapply Tuple.fieldwise_to_list_iff.
    unshelve erewrite 2Tuple.from_list_default_eq, 2Tuple.to_list_from_list;
      try solve [rewrite ?Crypto.Util.ListUtil.length_set_nth, ?Crypto.Util.ListUtil.length_update_nth, ?Tuple.length_to_list; trivial].
    eapply Crypto.Util.ListUtil.Forall2_update_nth.
    { eapply Tuple.fieldwise_to_list_iff; eassumption. }
    cbv [R_reg]; intros; Option.inversion_option; subst.
    erewrite <-Tuple__nth_default_to_list in Hv0;
      unfold nth_default in Hv0; rewrite H6 in Hv0; exact Hv0. }
  admit. (* store *)
Admitted.

Ltac step_SetOperand :=
  match goal with
  | H : Symbolic.SetOperand ?a ?i ?s = Success (?i0, _) |- _ =>
      let m := fresh "m" in let Hm := fresh "H" m in let HR := fresh "HR" m in
      case (R_SetOperand s _ ltac:(eassumption) _ _ _ _ _ H _ ltac:(eassumption))
        as (m&?Hm&?HR); clear H
  end.
Ltac step_symex4 := first [step_symex3 | step_SetOperand].
Ltac step_symex ::= step_symex4.

Ltac step_SetFlag :=
  match goal with
  | H : Symbolic.SetFlag ?f ?i ?s = Success (?_tt, ?s') |- _ =>
    let i := fresh "i" in let b := fresh "b" in
    unshelve epose proof (R_SetFlag s _ f _ ?[i] ?[b] _ _ H); shelve_unifiable;
    [eassumption|..]
  end.
Ltac step_symex5 := first [step_symex4 | step_SetFlag ].
Ltac step_symex ::= step_symex4.

Lemma R_SymexNornalInstruction s m (HR : R s m) instr :
  forall s', Symbolic.SymexNormalInstruction instr s = Success (tt, s') ->
  exists m', Semantics.DenoteNormalInstruction m instr = Some m' /\
  R s' m'.
Proof.
  intros s' H.
  cbv [SymexNormalInstruction] in H.
  destruct instr; BreakMatch.break_innermost_match_hyps; cbv [ret err Syntax.args Syntax.op] in *; inversion_ErrorT; Prod.inversion_prod; subst.
  { repeat step_symex.
    { econstructor; econstructor. }
    repeat step_symex.
    step_SetFlag.
    { instantiate (1:=false); eassumption. }
    cbn; eauto. }
  1:admit. (* ret *)
  1:admit. (* dec *)
  1:admit. (* inc *)
  { inversion Heqo; subst. repeat step_symex; cbn. rewrite Hvcf; cbn. eauto. }
  { inversion Heqo; subst. repeat step_symex; cbn. rewrite Hvcf; cbn. eauto. }
  1:admit. (* adc *)
  1:admit. (* adcx *)
  1:admit. (* add *)
  1:admit. (* adox *)
  1:admit. (* and *)
  1:admit. (* cmovc *)
  1:admit. (* cmovnz *)
  1:admit. (* imul *)
  (* mov *)
Admitted.

End WithCtx.
