Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.
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
Context (G : symbol -> option Z).
Local Notation eval := (Symbolic.eval G).
Local Notation dag_ok := (Symbolic.dag_ok G).

Section WithDag.
Context (d : dag).
Local Notation eval := (Symbolic.eval G d).

Definition R_reg (x : option idx) (v : Z) : Prop :=
  (forall i, x = Some i -> eval i v) /\ (v = Z.land v (Z.ones 64)).
Definition R_regs : Symbolic.reg_state -> Semantics.reg_state -> Prop :=
  Tuple.fieldwise R_reg.

Definition R_flag (x : option idx) (ob : option bool) : Prop :=
  forall i, x = Some i -> exists b, eval i (Z.b2z b) /\ ob = Some b.
Definition R_flags : Symbolic.flag_state -> Semantics.flag_state -> Prop :=
  Tuple.fieldwise R_flag.


Definition R_cell64' (a v : Z) : mem_state -> Prop :=
  eq (OfListWord.map.of_list_word_at (word.of_Z a)
  (HList.tuple.to_list (LittleEndian.split 8 v))).

Definition R_cell64 (ia iv : idx) (m : mem_state) : Prop :=
  exists a, eval ia a /\
  exists v, eval iv v /\
  R_cell64' a v m.

Fixpoint R_mem (sm : Symbolic.mem_state) : mem_state -> Prop :=
  match sm with
  | nil => eq frame
  | cons (ia, iv) sm' => sep (R_cell64 ia iv) (R_mem sm')
  end.


Lemma R_flag_None_l f : R_flag None f.
Proof. inversion 1. Qed.
Lemma R_flag_None_r f : autoforward.autoforward (R_flag f None) (f = None).
Proof.
  destruct f; cbv; trivial. intros H.
  case (H _ eq_refl) as (?&?&HX); inversion HX.
Qed.
End WithDag.

Local Hint Resolve R_flag_None_l : core.
Local Hint Resolve R_flag_None_r : typeclass_instances.

Axiom TODOmem : Semantics.mem_state -> mem_state.
Definition R (ss : symbolic_state) (ms : machine_state) : Prop :=
  let (mr, mf, mm) := ms in
  let (d, sr, sf, sm) := ss in
  dag_ok d /\ R_regs d sr mr /\ R_flags d sf mf /\ R_mem d sm (TODOmem mm).

Lemma get_flag_R s m f (HR : R s m) :
  forall i, Symbolic.get_flag s f = Some i ->
  exists b, eval s i (Z.b2z b) /\
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

Lemma R_set_flag_internal s m f (HR : R s m) (i:idx) b (Hi : eval s i (Z.b2z b)) :
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

Notation subsumed d1 d2 := (forall i v, eval d1 i v -> eval d2 i v).
Local Infix ":<" := subsumed (at level 70, no associativity).

Local Arguments Tuple.tuple : simpl never.
Local Arguments Tuple.fieldwise : simpl never.
Local Arguments Tuple.from_list_default : simpl never.
Local Arguments Tuple.to_list : simpl never.
Local Arguments Tuple.nth_default ! _ _.
Local Arguments set_reg ! _ _.
Local Arguments Syntax.operation_size ! _.
Local Arguments N.modulo !_ !_.
Local Arguments N.add !_ !_.
Local Arguments N.b2n ! _.
Local Arguments N.ones ! _.
Local Arguments N.land !_ !_.
Local Arguments N.lor !_ !_.
Local Arguments N.shiftl !_ !_.
Local Arguments N.shiftr !_ !_.

Local Arguments Z.modulo !_ !_.
Local Arguments Z.add !_ !_.
Local Arguments Z.b2z ! _.
Local Arguments Z.ones ! _.
Local Arguments Z.land !_ !_.
Local Arguments Z.lor !_ !_.
Local Arguments Z.shiftl !_ !_.
Local Arguments Z.shiftr !_ !_.

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
Proof. cbv [R_reg] in *; intuition eauto. Qed.

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

Lemma Tuple__nth_default_to_list' {A} n (xs : Tuple.tuple' A n) (d : A) :
  forall i, nth_default d (Tuple.to_list' n xs) i = @Tuple.nth_default A (S n) d i xs.
Proof.
  revert xs; induction n, i; cbn; BreakMatch.break_match; intros;
    rewrite ?ListUtil.nth_default_cons_S; eauto using ListUtil.nth_default_nil.
Qed.
Lemma Tuple__nth_default_to_list {A} n (xs : Tuple.tuple A n) (d : A) :
  forall i, List.nth_default d (Tuple.to_list _ xs) i = Tuple.nth_default d i xs.
Proof.
  destruct n; cbv [Tuple.tuple Tuple.to_list] in *.
  { destruct i; reflexivity. }
  eapply Tuple__nth_default_to_list'.
Qed.

Lemma get_reg_R s m (HR : R s m) ri :
  forall i, Symbolic.get_reg s ri = Some i ->
  exists v, eval s i v /\ Tuple.nth_default 0 ri (m : reg_state) = v.
Proof.
  cbv [Symbolic.get_reg]; intros.
  rewrite <-Tuple__nth_default_to_list in H.
  cbv [nth_default] in H; BreakMatch.break_match_hyps; subst; [|solve[congruence] ].
  destruct s,m; cbn in *; destruct HR as (_&?&_); cbv [R_regs R_reg] in *.
  eapply Tuple.fieldwise_to_list_iff in H.
  eapply Forall.Forall2_forall_iff_nth_error in H; cbv [Option.option_eq] in H.

  rewrite Heqo in H.
  BreakMatch.break_match_hyps; [|solve[contradiction]].
  specialize (proj1 H _ eq_refl).
  eexists; split; [eassumption|].

  rewrite <-Tuple__nth_default_to_list.
  cbv [nth_default].
  rewrite Heqo0.
  trivial.
Qed.

Lemma bind_assoc {A B C} (v:M A) (k1:A->M B) (k2:B->M C) s
 : (y <- (x <- v; k1 x); k2 y)%x86symex s = (x<-v; y<-k1 x; k2 y)%x86symex s.
Proof. cbv; destruct v; trivial. Qed.

Ltac step_symex0 :=
  match goal with
  | H : (x <- ?v; ?k)%x86symex ?s = _ |- _  =>
    rewrite !bind_assoc in H
  | H : (x <- ?v; ?k)%x86symex ?s = Success _ |- _  =>
    unfold bind at 1 in H;
    let x := fresh x in
    let HH := fresh "HS" x in
    destruct v as [[x ?]|] eqn:HH in H;
    cbn [ErrorT.bind] in H; [|solve[exfalso;clear-H;inversion H]]
  end.
Ltac step_symex := step_symex0.

Lemma GetFlag_R s m (HR : R s m) f i s' (H : GetFlag f s = Success (i, s')) :
  exists b, eval s i (Z.b2z b) /\ Semantics.get_flag m f = Some b /\ s = s'.
Proof.
  cbv [GetFlag some_or] in H.
  destruct (Symbolic.get_flag _ _) eqn:? in H;
    ErrorT.inversion_ErrorT; Prod.inversion_prod; subst; [].
  eapply get_flag_R in Heqo; eauto; destruct Heqo as (b&Hb&Hf); eauto.
Qed.

Ltac step_GetFlag :=
  match goal with
  | H : GetFlag ?f ?s = Success (?i0, _) |- _ =>
    let v := fresh "v" f in let Hv := fresh "H" v in let Hvf := fresh "Hv" f in
    let Hi := fresh "H" i0 in let Heq := fresh H "eq" in
    case (GetFlag_R s _ ltac:(eassumption) _ _ _ H) as (v&Hi&Hvf&Heq); clear H;
    (let i := fresh "i" f in try rename i0 into i);
    (try match type of Heq with _ = ?s' => subst s' end)
  end.
Ltac step_symex1 := first [step_symex0 | step_GetFlag].
Ltac step_symex ::= step_symex1.

Lemma Merge_R s m (HR : R s m) e v (H : eval s e v) :
  forall i s', Merge e s = Success (i, s') ->
  R s' m /\ s :< s' /\ eval s' i v.
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
    let v := open_constr:(_) in let Hi := fresh "H" i in
    let Hs' := fresh "H" s' in let Hl := fresh "Hl" s' in
    let t := open_constr:(fun A B => Merge_R s _ A e v B _ _ H) in
    unshelve (edestruct t as (Hs'&Hl&Hi); clear H); shelve_unifiable;
    [eassumption|..]
  end.
Ltac step_symex2 := first [step_symex1 | step_Merge].
Ltac step_symex ::= step_symex2.

Lemma App_R s m (HR : R s m) e v (H : eval_node G s e v) :
  forall i s', Symbolic.App e s = Success (i, s') ->
  R s' m /\ s :< s' /\ eval s' i v.
Proof.
  cbv [Symbolic.App]; intros.
  eapply Merge_R in H0; intuition eauto using eval_simplify.
Qed.

Ltac step_App :=
  match goal with
  | H : Symbolic.App ?n ?s = Success (?i, ?s') |- _ =>
    let v := fresh "v" i in let Hi := fresh "H" i in
    let Hl := fresh "Hl" s' in let Hs' := fresh "H" s' in 
    let t := open_constr:(fun A B => App_R s _ A n ?[v] B _ _ H) in
    unshelve (edestruct t as (Hs'&Hl&Hi); clear H); shelve_unifiable;
    [eassumption|..]
  end.
Ltac step_symex3 := first [step_symex2 | step_App].
Ltac step_symex ::= step_symex3.

Ltac eval_same_expr_goal :=
  match goal with
   | |- eval ?d ?e ?v =>
       match goal with
         H : eval d e ?v' |- _ =>
             let Heq := fresh in
             enough (Heq : v = v') by (rewrite Heq; exact H);
             try clear H e
       end
   | |- eval ?d ?e ?v =>
       let H := fresh in
       let v' := open_constr:(_) in
       eassert (eval d e v') by (eauto 99 with nocore);
       let Heq := fresh in
       enough (Heq : v = v') by (rewrite Heq; exact H);
       try clear H e
   end.

Import ListNotations.

(* note: do the two SetOperand both truncate inputs or not?... *)
Lemma R_SetOperand s m (HR : R s m)
  sz sa a i _tt s' (H : @Symbolic.SetOperand sz sa a i s = Success (_tt, s'))
  v (Hv : eval s i v)
  : exists m', SetOperand sa sz m a v = Some m' /\ R s' m' /\ s :< s'.
Proof.
  destruct a in *; cbn in H; [ | | solve [inversion H] ];
    cbv [SetOperand Crypto.Util.Option.bind SetReg64 update_reg_with Symbolic.update_reg_with] in *;
    repeat (BreakMatch.break_innermost_match_hyps; Prod.inversion_prod; ErrorT.inversion_ErrorT; subst).

  { repeat step_symex.
    { repeat (eauto||econstructor). }
    inversion_ErrorT; Prod.inversion_prod; subst.
    rewrite Z.shiftr_0_r in *.
    eexists; split; [exact eq_refl|].
    destruct s0; cbv [R] in *; intuition try solve [cbn in *; intuition idtac].
    cbv [R_regs Symbolic.set_reg set_reg index_and_shift_and_bitcount_of_reg].
    eapply Tuple.fieldwise_to_list_iff.
    unshelve erewrite 2Tuple.from_list_default_eq, 2Tuple.to_list_from_list;
      try solve [rewrite ?Crypto.Util.ListUtil.length_set_nth, ?Crypto.Util.ListUtil.length_update_nth, ?Tuple.length_to_list; trivial].
    eapply Crypto.Util.ListUtil.Forall2_update_nth.
    { eapply Tuple.fieldwise_to_list_iff; eassumption. }
    cbv [R_reg bitmask_of_reg index_and_shift_and_bitcount_of_reg].
    intros. DestructHead.destruct_head'_and.
    eapply Ndec.Neqb_complete in Heqb; rewrite Heqb.
    replace (reg_offset r) with 0%N by (destruct r;cbv;trivial||cbv in Heqb;inversion Heqb).
    assert (Hx64: Z.ldiff v2 (Z.ones 64) = 0). {
      rewrite Z.land_ones in * by Lia.lia.
      rewrite Z.ldiff_ones_r, Z.shiftl_eq_0_iff, Z.shiftr_div_pow2 by (clear; Lia.lia).
      clear -H6. cbn in *; zify; Z.div_mod_to_equations; lia. }
    rewrite Z.shiftl_0_r, Z.shiftl_0_r. setoid_rewrite Hx64. setoid_rewrite Z.lor_0_r.
    intuition idtac; try Option.inversion_option; subst; trivial.
    { cbn -[Z.ones]; rewrite !Z.land_ones, Zmod_mod by (clear;lia); trivial. } }
  { eexists; split; [exact eq_refl|].
    repeat (step_symex; []).
    cbv [GetReg64 some_or] in *.
    pose proof (get_reg_R s _ ltac:(eassumption) (reg_index r)) as Hr.
    destruct (Symbolic.get_reg _ _) in *; cbn [ErrorT.bind] in H;
      ErrorT.inversion_ErrorT; Prod.inversion_prod; subst;cbn [fst snd] in *.
    specialize (Hr _ eq_refl); case Hr as (?&?&?).
    step_App.
    { repeat (eauto || econstructor). }
    repeat (Prod.inversion_prod; ErrorT.inversion_ErrorT; subst).
    destruct s1; cbv [R] in *; cbn in *; intuition idtac.
    cbv [R_regs Symbolic.set_reg set_reg index_and_shift_and_bitcount_of_reg].
    eapply Tuple.fieldwise_to_list_iff.
    unshelve erewrite 2Tuple.from_list_default_eq, 2Tuple.to_list_from_list;
      try solve [rewrite ?Crypto.Util.ListUtil.length_set_nth, ?Crypto.Util.ListUtil.length_update_nth, ?Tuple.length_to_list; trivial].
    eapply Crypto.Util.ListUtil.Forall2_update_nth.
    { eapply Tuple.fieldwise_to_list_iff; eassumption. }
    cbv [R_reg]; intuition idtac; try Option.inversion_option; subst; try eval_same_expr_goal;
    cbv [bitmask_of_reg index_and_shift_and_bitcount_of_reg].
    { rewrite <-Tuple__nth_default_to_list. cbv [nth_default]; rewrite H5. trivial. }
    assert (Z.of_N (reg_size r) + Z.of_N (reg_offset r) <= 64) by (destruct r; clear; cbv; discriminate).
    eapply Z.bits_inj_iff'; intros j Hj.
    rewrite Z.land_spec, Z.testbit_ones_nonneg by (clear -Hj; lia).
    destr.destr (j <? 64); rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; trivial; [].
    rewrite Z.lor_spec, Z.ldiff_spec, !Z.shiftl_spec, Z.land_spec, !Z.testbit_ones_nonneg by (assumption||lia).
    destr.destr (j - Z.of_N (reg_offset r) <? Z.of_N (reg_size r)); try (revert dependent j; clear -H6; lia).
    rewrite Bool.andb_true_r, Bool.andb_false_r, Bool.orb_false_l.
    rewrite H8, Z.land_spec, Z.ones_spec_high; revert dependent j; lia. }
  { progress cbv [Store] in *.
    admit. (* store *) }
Admitted.

Ltac step_SetOperand :=
  match goal with
  | H : Symbolic.SetOperand ?a ?i ?s = Success (?_tt, ?s') |- _ =>
      let m := fresh "m" in let Hm := fresh "H" m in
      let HR := fresh "H" s' in let Hl := fresh "Hl" s' in
      case (R_SetOperand s _ ltac:(eassumption) _ _ _ _ _ _ H _ ltac:(eauto 99 with nocore))
        as (m&?Hm&HR&Hl); clear H
  end.
Ltac step_symex4 := first [step_symex3 | step_SetOperand].
Ltac step_symex ::= step_symex4.

Lemma SetFlag_R s m f (HR : R s m) (i:idx) b (Hi : eval s i (Z.b2z b)) :
  forall _tt s', Symbolic.SetFlag f i s = Success (_tt, s') ->
  R s' (SetFlag m f b) /\ s :< s'.
Proof.
  destruct s; cbv [Symbolic.SetFlag Symbolic.update_flag_with Symbolic.set_flag] in *;
    intros; inversion_ErrorT_step; Prod.inversion_prod; subst.
  cbv [R].
  intuition idtac.
  all : try eapply R_set_flag_internal; eauto.
  all : cbv [R] in *; intuition idtac.
Qed.

Ltac step_SetFlag :=
  match goal with
  | H : Symbolic.SetFlag ?f ?i ?s = Success (?_tt, ?s') |- _ =>
    let i := open_constr:(_) in let b := open_constr:(_) in
    let Hs' := fresh "H" s' in let Hlt := fresh "He" s' in
    let t := open_constr:(fun A B => SetFlag_R s _ f A i b B _ _ H) in
    unshelve (edestruct t as (Hs'&Hlt); clear H); shelve_unifiable;
    [eassumption|..|clear H]
  end.
Ltac step_symex5 := first [step_symex4 | step_SetFlag ].
Ltac step_symex ::= step_symex5.

Lemma GetReg_R s m (HR: R s m) r i s'
  (H : @GetReg r s = Success (i, s'))
  : R s' m  /\ s :< s' /\ eval s' i (get_reg m r).
Proof.
  cbv [GetReg GetReg64 bind some_or get_reg index_and_shift_and_bitcount_of_reg] in *.
  pose proof (get_reg_R s _ ltac:(eassumption) (reg_index r)) as Hr.
  destruct Symbolic.get_reg in *; [|inversion H]; cbn in H.
  specialize (Hr _ eq_refl); case Hr as (v&Hi0&Hv).
  rewrite Hv; clear Hv.
  step_symex; eauto.
  repeat (eauto || econstructor); cbn [interp_op].
Qed.

Lemma Address_R s m (HR : R s m) sa o a s' (H : @Symbolic.Address sa o s = Success (a, s'))
  : R s' m /\ s :< s' /\ exists v, eval s' a v /\ @DenoteAddress sa m o = v.
Proof.
  destruct o as [? ? ? ?]; cbv [Address DenoteAddress] in *; repeat step_symex.
  eapply GetReg_R in HSbase; eauto; []; DestructHead.destruct_head'_and.
  destruct mem_extra_reg; cbn -[GetReg] in *.
  1: eapply GetReg_R in HSindex; eauto; []; DestructHead.destruct_head'_and.
  all: destruct mem_offset; cbn -[GetReg] in *.
  all: (step_symex; try solve [repeat (eauto || econstructor)]; []).
  all: (step_symex; try solve [repeat (eauto || econstructor)]; []).
  all: (step_symex; try solve [repeat (eauto || econstructor)]; []).
  3,4: (step_symex; try solve [repeat (eauto || econstructor)]; []).
  all : cbn in *.
  all : Tactics.ssplit; eauto 99 with nocore.
  all : eexists; split; eauto; [].
  all : cbv [DenoteConst].
  all : rewrite ?Z.add_0_r, ?Z.land_ones, ?Z.shiftr_div_pow2 by lia.
  all : push_Zmod; pull_Zmod; trivial.
Qed.

Ltac step_Address :=
  match goal with HSa: context[Address] |- _ =>
      eapply Address_R in HSa; [|eassumption];
          destruct HSa as (?&?&?&?&?)
  end.

Lemma GetOperand_R s m (HR: R s m) so sa a i s'
  (H : @GetOperand so sa a s = Success (i, s'))
  : R s' m /\ s :< s' /\ exists v, eval s' i v /\ DenoteOperand sa so m a = Some v.
Proof.
  cbv [GetOperand DenoteOperand] in *; BreakMatch.break_innermost_match.
  { eapply GetReg_R in H; intuition eauto. }
  1: {
    progress cbv [Load] in *.
    (* Load *) admit. }
  { step_symex; repeat (eauto || econstructor). }
Admitted.

Ltac step_GetOperand :=
  match goal with
  | H : GetOperand ?a ?s = Success (?i0, ?s') |- _ =>
    let v := fresh "v" (*a*) in let Hv := fresh "H" v
    in let Hi := fresh "H" i0 in let Heq := fresh H "eq" in
    let Hs' := fresh "H" s' in let Hl := fresh "Hl" s' in
    case (GetOperand_R s _ ltac:(eassumption) _ _ _ _ _ H) as (Hs'&Hl&(v&Hi&Hv)); clear H
  end.
Ltac step_symex6 := first [step_symex5 | step_GetOperand | step_Address ].
Ltac step_symex ::= step_symex6.

Lemma HavocFlags_R s m (HR : R s m) :
  forall _tt s', Symbolic.HavocFlags s = Success (_tt, s') ->
  R s' (HavocFlags m) /\ s :< s'.
Proof.
  destruct s; cbv [Symbolic.HavocFlags Symbolic.update_flag_with] in *;
    intros; inversion_ErrorT_step; Prod.inversion_prod; subst.
  cbv [R]; intuition idtac; try solve [cbv [R] in *; intuition idtac].
  all: cbv [R_flags Tuple.fieldwise Tuple.fieldwise' R_flag]; cbn;
    intuition idtac; Option.inversion_option.
Qed.
Ltac step_HavocFlags :=
  match goal with
  | H : Symbolic.HavocFlags ?s = Success (_, ?s') |- _ =>
    let Hs' := fresh "H" s' in
    let Hl := fresh "Hlt" s'  in
    let t := open_constr:(fun A => HavocFlags_R _ _ A _ _ H) in
    unshelve (edestruct t as (Hs'&Hl); clear H); shelve_unifiable;
    [eassumption|]
  end.
Ltac step_symex7 := first [step_symex6 | step_HavocFlags ].
Ltac step_symex ::= step_symex7.

Ltac him :=
  match goal with
  | |- context G [match ?x with _ => _ end] =>
    assert_fails (idtac; match x with context[match _ with _ => _ end] => idtac end);
    let ex := eval hnf in x in
    first [progress change x with ex; progress cbv match beta | destruct x eqn:?]
  end.

Global Existing Instance expr_beq_spec.

Ltac destr_expr_beq :=
  match goal with
  | H : context [expr_beq ?a ?b] |- _ => destr.destr (expr_beq a b)
  end.

Lemma standalone_operand_size_cases o n : standalone_operand_size o = Some n ->
  (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N.
Proof.
   destruct o; cbn.
   { destruct r; cbn; inversion 1; subst; eauto. }
   { destruct (mem_is_byte _); inversion 1; eauto. }
   { inversion 1. }
Qed.

Lemma operation_size_cases i n : Syntax.operation_size i = Some n ->
  (exists a, i = Build_NormalInstruction dec [a]) \/ (exists a, i = Build_NormalInstruction inc [a]) \/ (exists a b, i = Build_NormalInstruction Syntax.rcr [a; b]) \/ (exists a b c, i = Build_NormalInstruction Syntax.shrd [a; b; c]) \/ (exists a b, i = Build_NormalInstruction Syntax.sar [a;b])\/(exists a b, i = Build_NormalInstruction Syntax.add [a;b]) ->
  (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N.
Proof.
  intuition idtac; DestructHead.destruct_head'_ex; subst; cbn in *.
  all : repeat (repeat (let HH := fresh "H" in destruct (standalone_operand_size _) eqn:HH in H; repeat Option.inversion_option; try eapply standalone_operand_size_cases in HH); cbn in *; repeat Option.inversion_option; subst || Tactics.destruct_one_match_hyp).
  all : lia.
Qed.

Import UniquePose.
Ltac pose_operation_size_cases :=
  match goal with
  | H : Syntax.operation_size _ = Some _ |- _ =>
      unique pose proof (operation_size_cases _ _ H ltac:(eauto 99))
  end.

Ltac invert_eval :=
  match goal with
  | H : context[match reveal ?d ?n ?i with _ => _ end] |- _ => destruct (reveal d n i) as [?|[[] []]]eqn:? in *  (* kludge *)
  | H : reveal ?d _ ?i = ?rhs, G : eval ?d (ExprRef ?i) ?v |- _ =>
      let h := Head.head rhs in is_constructor h;
      let HH := fresh H in
      epose proof (eval_reveal _ d _ i v G _ H) as HH;
      clear H; rename HH into H
  | H : eval ?d (ExprApp ?n) ?v |- _ =>
      let HH := fresh H in
      let x := fresh "x" in (* COQBUG: using _ below clears unrelated hypothesis *)
      inversion E0 as [|? ? x ? [] HH ]; clear x;
      clear H; subst; rename HH into H
  | H : interp_op _ ?o ?a = Some ?v |- _ => inversion H; clear H; subst
  end.

Ltac resolve_match_using_hyp :=
  match goal with |- context[match ?x with _ => _ end] =>
  match goal with H : x = ?v |- _ =>
      let h := Head.head v in
      is_constructor h;
      rewrite H
  end end.

Ltac resolve_SetOperand_using_hyp :=
  match goal with
  | |- context[match SetOperand ?a ?b ?c ?d ?x with _ => _ end] =>
      match goal with H : SetOperand a b c d ?y = Some _ |- _ =>
          replace x with y; [rewrite H|]; cycle 1 end
  | |- context[SetOperand ?a ?b ?c ?d ?x = Some _] =>
      match goal with H : SetOperand a b c d ?y = Some _ |- _ =>
          replace x with y; [rewrite H|]; cycle 1 end
  end.

Ltac lift_let_goal :=
  match goal with
  | |- context G [let x := ?v in @?C x] =>
      let xH := fresh x in pose v as xH;
      let g := context G [C xH] in change g; cbv beta
  end.

Ltac step :=
  first
  [ lift_let_goal
  | resolve_match_using_hyp
  | progress (cbn beta iota delta [fst snd Syntax.op Syntax.args] in *; cbv beta iota delta [Reveal RevealConst Crypto.Util.Option.bind Symbolic.ret Symbolic.err Symeval mapM PreserveFlag] in *; subst)
  | Prod.inversion_prod_step
  | inversion_ErrorT_step
  | Option.inversion_option_step
  | invert_eval
  | step_symex
  | destr_expr_beq
  ].
Ltac step1 := step; (eassumption||trivial); [].
Ltac step01 := solve [step] || step1.

Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.

Lemma SetOperand_same n m a v m'
  (Hd : DenoteOperand 64 n m a = Some v) (Hs : SetOperand 64 n m a v = Some m')
  : m = m'.
Proof.
  destruct a, m; cbn -[DenoteAddress] in *; repeat (subst; Option.inversion_option).
  { cbv [update_reg_with set_reg]; cbn in *; f_equal.
    eapply Tuple.to_list_ext.
    rewrite <-Tuple__nth_default_to_list in Hd; rewrite <-Hd; clear Hd.
    unshelve erewrite Tuple.from_list_default_eq, Tuple.to_list_from_list.
    { abstract (rewrite Crypto.Util.ListUtil.length_update_nth; eapply Tuple.length_to_list). }
    eapply List.nth_error_ext; intro i; cbv [nth_default].
    rewrite Crypto.Util.ListUtil.nth_update_nth; destruct_one_match; subst; trivial.
    destruct_one_match; cbn; trivial; eapply f_equal.
    eapply Z.bits_inj_iff'; intros i Hi.
    repeat rewrite ?Z.land_spec, ?Z.ldiff_spec, ?Z.lor_spec, ?bitblast.Z.shiftr_spec', ?bitblast.Z.shiftl_spec', ?Z.testbit_ones, ?Z.testbit_0_l by (clear;lia).
    destr (i <? 0); cbn; try lia.
    destr (i - Z.of_N (reg_offset r) <? 0); cbn; try lia.
    { destr (0 <=? i - Z.of_N (reg_offset r)); cbn; rewrite ?Bool.andb_true_r; trivial.
      destr (i - Z.of_N (reg_offset r) <? Z.of_N (reg_size r)); cbn; try Btauto.btauto.
      lia. }
    destr (0 <=? i - Z.of_N (reg_offset r)); try lia; cbn.
    replace (i - Z.of_N (reg_offset r) + Z.of_N (reg_offset r)) with i by lia.
    destr (i - Z.of_N (reg_offset r) <? Z.of_N (reg_size r)); Btauto.btauto. }
  { destruct m'; cbv [update_mem_with Crypto.Util.Option.bind set_mem_error set_mem_bytes_error get_mem option_map] in *; repeat (destruct_one_match_hyp || Option.inversion_option).
    inversion Hs; clear Hs; subst; f_equal.
    clear E1.
    (* mem *)
Admitted.


Lemma Z__ones_nonneg n (H : 0 <= n)  : 0 <= Z.ones n.
Proof. rewrite Z.ones_equiv. pose proof Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(assumption); Lia.lia. Qed.

Lemma R_SymexNornalInstruction s m (HR : R s m) instr :
  forall s', Symbolic.SymexNormalInstruction instr s = Success (tt, s') ->
  exists m', Semantics.DenoteNormalInstruction m instr = Some m' /\ R s' m'.
Proof.
  intros s' H.
  case instr as [op args]; cbv [SymexNormalInstruction] in H.
  repeat destruct_one_match_hyp; repeat step01.

  all : repeat 
  match goal with
  | |- eval_node _ _ (?op, ?args) ?e =>
      solve [repeat (eauto 99 with nocore || econstructor)]
  | |- eval _ (ExprApp (?op, ?args)) ?e =>
      solve [repeat (eauto 99 with nocore || econstructor)]
  | _ => step
  | |- eval _ (ExprRef ?v) ?e => eval_same_expr_goal; try solve [ (* bashing *)
      exact eq_refl || rewrite Z.bit0_mod; trivial; rewrite  Z.mod_small; trivial; Lia.lia]
  end.

  all: cbv beta delta [DenoteNormalInstruction].
  all: repeat
  match goal with
  | x := ?v |- _ => let t := type of x in
      assert_fails (idtac; match v with context[match _ with _ => _ end] => idtac end);
          subst x
  | _ => step
  | _ => resolve_SetOperand_using_hyp
  | _ => rewrite (Bool.pull_bool_if Some)
  | |- exists _, Some _ = Some _ /\ _ => eexists; split; [f_equal|]
  | |- exists _, None   = Some _ /\ _ => exfalso
  end.

  all : cbn [fold_right map]; rewrite ?N2Z.id, ?Z.add_0_r, ?Z.add_assoc, ?Z.mul_1_r, ?Z.land_m1_r, ?Z.lxor_0_r;
    (congruence||eauto).
  all : try solve [rewrite Z.land_ones, Z.bit0_mod by Lia.lia; exact eq_refl].

  all: try solve[ (* bash flags weakening *)
  match goal with H : R ?s' _ |- R ?s' ?m' =>
      try (is_var s'; destruct s');
      try (is_var m'; destruct m');
      repeat match goal with
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; rewrite ?Z.add_0_r, ?Z.odd_opp; eauto; try Lia.lia
  end
  ].

  Unshelve. all : match goal with H : context[Syntax.sub] |- _ => idtac | _ => shelve end.
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. rewrite Z.add_opp_r; congruence. }

  Unshelve. all : match goal with H : context[Syntax.sbb] |- _ => idtac | _ => shelve end.
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. rewrite ?Z.sub_add_distr, ?Z.add_opp_r. congruence. }

  Unshelve. all : match goal with H : context[Syntax.dec] |- _ => idtac | _ => shelve end.
  { cbv [DenoteOperand DenoteConst] in Hv0. Option.inversion_option. subst v0.
    cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. replace v1 with v by congruence. exact eq_refl. }
  { cbv [Symbolic.PreserveFlag Symbolic.HavocFlags Symbolic.update_flag_with ret] in HSx4; cbn in HSx4; induction_path_ErrorT HSx4; Prod.inversion_prod; subst.
    inversion H; subst s'.
    destruct s6, m0;
      repeat match goal with
             | _ => Option.inversion_option_step
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags R_flag Tuple.fieldwise Tuple.fieldwise' Symbolic.get_flag get_flag ] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; eauto; try Lia.lia; try congruence.
             eexists. split. eauto.
             f_equal. f_equal.
             change Symbolic.signed with signed.
             rewrite ?Z.add_0_r.
             f_equal.
             1:congruence.
             rewrite <-Z.add_opp_r; f_equal.
             pose_operation_size_cases; intuition (subst; trivial). }

  Unshelve. all : match goal with H : context[Syntax.inc] |- _ => idtac | _ => shelve end.
  { cbv [DenoteOperand DenoteConst] in Hv0. Option.inversion_option. subst v0.
    cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. replace v1 with v by congruence. exact eq_refl. }
  { cbv [Symbolic.PreserveFlag Symbolic.HavocFlags Symbolic.update_flag_with ret] in HSx4; cbn in HSx4; induction_path_ErrorT HSx4; Prod.inversion_prod; subst.
    inversion H; subst s'.
    destruct s6, m0;
      repeat match goal with
             | _ => Option.inversion_option_step
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags R_flag Tuple.fieldwise Tuple.fieldwise' Symbolic.get_flag get_flag ] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; eauto; try Lia.lia; try congruence.
             eexists. split. eauto.
             f_equal. f_equal.
             change Symbolic.signed with signed.
             rewrite ?Z.add_0_r.
             f_equal.
             1:congruence.
             f_equal.
             pose_operation_size_cases; intuition (subst; trivial). }

  Unshelve. all : match goal with H : context[Syntax.add] |- _ => idtac | _ => shelve end.
  { destruct s';
      repeat match goal with
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; rewrite ?Z.add_0_r, ?Z.odd_opp; eauto; try Lia.lia; try congruence.
             replace (signed n 0) with 0; cycle 1.
             { pose_operation_size_cases. clear -H0; intuition (subst; cbv; trivial). }
             rewrite Z.add_0_r; cbv [signed Symbolic.signed]; congruence. }

  Unshelve. all : match goal with H : context[Syntax.adc] |- _ => idtac | _ => shelve end.
  { destruct s';
      repeat match goal with
             | x := ?v |- _ => subst x
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; rewrite ?Z.add_assoc, ?Z.add_0_r, ?Z.odd_opp; eauto; try Lia.lia; try congruence.
             change Symbolic.signed with signed. congruence. }

  Unshelve. all : match goal with H : context[Syntax.adcx] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.adox] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.cmovc] |- _ => idtac | _ => shelve end.
  { (* cmovc *)
    destruct vCF; cbn [negb Z.b2z Z.eqb] in *; eauto; [].
    enough (m = m0) by (subst; eauto).
    clear -Hm0 Hv frame G ; eauto using SetOperand_same. }

  Unshelve. all : match goal with H : context[Syntax.cmovnz] |- _ => idtac | _ => shelve end.
  { (* cmovnz *)
    destruct vZF; cbn [negb Z.b2z Z.eqb] in *; eauto; [].
    enough (m = m0) by (subst; eauto). 
    clear -Hm0 Hv0 frame G ; eauto using SetOperand_same. }

  Unshelve. all : match goal with H : context[Syntax.test] |- _ => idtac | _ => shelve end.
  { destruct (Equality.ARG_beq_spec a a0); try discriminate; subst a0.
    replace v0 with v in * by congruence; clear v0.
    rewrite Z.land_diag.
    case s', m in *; cbn;
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn in * ; subst)
             | _ => progress intuition eauto 1
    end. }

  Unshelve. all : match goal with H : context[Syntax.sar] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { rewrite Z.land_m1_r in *.
    subst st st0.
    rewrite <-H1; cbn.
    replace (1 <? Z.of_N n) with true; cycle 1. {
     pose_operation_size_cases; intuition (subst; cbn; clear; lia). }
    revert Hs'.
    repeat match goal with x:= _ |- _ => subst x end;
    destruct s';
    repeat match goal with
           | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
           | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
               let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
           | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
           | _ => destruct_one_match
           | _ => progress intuition idtac
           end; eauto. }

  Unshelve. all : match goal with H : context[Syntax.rcr] |- _ => idtac | _ => shelve end; shelve_unifiable.
  all : inversion Heqe as [|? ? ? ? []]; cbn [interp_op] in *; Option.inversion_option; subst; trivial.
  all : change Symbolic.rcrcnt with rcrcnt in *.
  { destruct_one_match_hyp; repeat step; eauto.
    { econstructor. econstructor. eauto 9. econstructor. cbn.
      rewrite Z.shiftr_0_r. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
      rewrite <-Z.bit0_mod. exact eq_refl. }
  all : destruct_one_match; try lia.
  all:
      destruct s';
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise' set_flag set_flag_internal] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; try eauto; try Lia.lia.
     destr (machine_flag_state m0); cbn [Tuple.tuple'] in *; DestructHead.destruct_head'_prod; subst; Prod.inversion_prod; subst.
     f_equal.
     rewrite E0; cbn.
     rewrite <-2Z.bit0_odd, Z.lor_spec, Z.shiftl_spec_low, Bool.orb_false_r; trivial.
     pose_operation_size_cases; intuition (subst; cbn; clear; lia). }

  Unshelve. all : match goal with H : context[Syntax.lea] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { (* lea *)
    cbv [SetOperand update_reg_with] in *; Option.inversion_option; subst; trivial. }

  Unshelve. all : match goal with H : context[Syntax.bzhi] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { (* bzhi *) inversion Heqe; subst. inversion H1; subst. inversion H3; congruence. }

  Unshelve. all : match goal with H : context[Syntax.shrd] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply Z.bits_inj_iff'; intros i Hi.
    inversion Hv2; subst; cbv [DenoteConst operand_size standalone_operand_size].
    repeat rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.shiftr_spec, ?Z.shiftl_spec, ?Z.testbit_ones_nonneg, ?Z.testbit_0_l; try lia.
    destr (i <? Z.of_N n); rewrite ?Bool.orb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r; trivial.
    replace v0 with v3 by congruence; f_equal; f_equal.
    rewrite Z.land_ones, Z.mod_small.
    1:ring_simplify; rewrite Z.add_sub_swap; exact eq_refl.
    3: enough (0 <= Z.land v3 (Z.of_N n - 1)) by lia; eapply Z.land_nonneg; right.
    1,2,3:pose_operation_size_cases; intuition (subst; cbn; clear; lia). }
  all : fail.
Admitted.

End WithCtx.
