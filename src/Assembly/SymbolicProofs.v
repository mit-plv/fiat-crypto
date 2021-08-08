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
  | H : bind (Merge ?e) _ ?s = _ |- _ =>
      let i := fresh "i" in
      let s' := fresh "s'" in
      let Hs' := fresh "H" s' in
      unfold bind at 1 in H;
      destruct (Merge e s) as [(i,s')|] eqn:Hs' in H; [|solve [inversion H]];
      cbn [ErrorT.bind] in H;
      let H' := fresh H in
      unshelve (epose proof Merge_R s _ ltac:(eassumption) e _ _ _ _ Hs' as H'; destruct H'); shelve_unifiable
  end.

Lemma R_SymexNornalInstruction s m (HR : R s m) instr :
  forall s', Symbolic.SymexNormalInstruction instr s = Success (tt, s') ->
  exists m', Semantics.DenoteNormalInstruction m instr = Some m' /\
  R s' m'.
Proof.
  intros s' H.
  cbv [SymexNormalInstruction] in H.
  BreakMatch.break_innermost_match_hyps; cbv [ret err] in *; inversion_ErrorT.
  { destruct instr; cbn [Syntax.args Syntax.op] in *; subst.
    eexists; split; [exact eq_refl|].
    step_Merge.
    { econstructor; econstructor. }
    eauto using R_SetFlag. }
Admitted.

Abort.
