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

Definition R_reg (x : option idx) (v : N) : Prop :=
  forall i, x = Some i -> eval i (Z.of_N v).
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
  exists v, eval s i (Z.of_N v) /\ Tuple.nth_default 0%N ri (m : reg_state) = v.
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
    let v := fresh "v" i in let Hi := fresh "H" i in
    let Hs' := fresh "H" s' in let Hl := fresh "Hl" s' in
    let t := open_constr:(fun A B => Merge_R s _ A e ?[v] B _ _ H) in
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
            clear H; try clear e
      end
  end.

Import ListNotations.

(* note: do the two SetOperand both truncate inputs or not?... *)
Lemma R_SetOperand s m (HR : R s m)
  sz sa a i _tt s' (H : @Symbolic.SetOperand sz sa a i s = Success (_tt, s'))
  v (Hv : eval s i v)
  : exists m', SetOperand sa sz m a (Z.to_N v) = Some m' /\ R s' m' /\ s :< s'.
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
    cbv [R_reg bitmask_of_reg index_and_shift_and_bitcount_of_reg];
      intros; Option.inversion_option; subst.
    eapply Ndec.Neqb_complete in Heqb; rewrite Heqb.
    replace (reg_offset r) with 0%N by (destruct r;cbv;trivial||cbv in Heqb;inversion Heqb).
    rewrite N.shiftl_0_r, N.shiftl_0_r.
    rename v2 into x.
    eval_same_expr_goal.
    assert (0 <= v) by admit.
    assert (Hx64: N.ldiff (*reg*)x (N.ones 64) = 0%N) by admit.
    rewrite N.land_comm, Hx64, N.lor_0_r.
    (* Z.of_N N.land Z.to_N *) admit. }
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
    cbv [R_reg]; intros; Option.inversion_option; subst.
    eval_same_expr_goal.
    (* Z&N bitwise *) admit. }
  admit. (* store *)
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
    let i := fresh "i" in let b := fresh "b" in
    let Hs' := fresh "H" s' in let Hlt := fresh "He" s' in
    let t := open_constr:(fun A B => SetFlag_R s _ f A ?[i] ?[b] B _ _ H) in
    unshelve (edestruct t as (Hs'&Hlt); clear H); shelve_unifiable;
    [eassumption|..|clear H]
  end.
Ltac step_symex5 := first [step_symex4 | step_SetFlag ].
Ltac step_symex ::= step_symex5.

Lemma GetReg_R s m (HR: R s m) r i s'
  (H : @GetReg r s = Success (i, s'))
  : R s' m  /\ s :< s' /\ eval s' i (Z.of_N (get_reg m r)).
Proof.
  cbv [GetReg GetReg64 bind some_or get_reg index_and_shift_and_bitcount_of_reg] in *.
  pose proof (get_reg_R s _ ltac:(eassumption) (reg_index r)) as Hr.
  destruct Symbolic.get_reg in *; [|inversion H]; cbn in H.
  specialize (Hr _ eq_refl); case Hr as (v&Hi0&Hv).
  rewrite Hv; clear Hv.
  step_symex; eauto.
  repeat (eauto || econstructor); cbn [interp_op].
  (* bitwise Z&N *) admit.
Admitted.

Lemma GetOperand_R s m (HR: R s m) so sa a i s'
  (H : @GetOperand so sa a s = Success (i, s'))
  : R s' m /\ s :< s' /\ exists v, eval s' i (Z.of_N v) /\ DenoteOperand sa so m a = Some v.
Proof.
  cbv [GetOperand DenoteOperand] in *; BreakMatch.break_innermost_match.
  { eapply GetReg_R in H; intuition eauto. }
  1: (* Load *) admit.
  step_symex; eauto.
  repeat (eauto || econstructor); unfold interp_op, DenoteConst; cbn.
  rewrite Z2N.id; trivial.
  { (* zconst*) repeat econstructor || admit. }
Admitted.

Ltac step_GetOperand :=
  match goal with
  | H : GetOperand ?a ?s = Success (?i0, ?s') |- _ =>
    let v := fresh "v" (*a*) in let Hv := fresh "H" v
    in let Hi := fresh "H" i0 in let Heq := fresh H "eq" in
    let Hs' := fresh "H" s' in let Hl := fresh "Hl" s' in
    case (GetOperand_R s _ ltac:(eassumption) _ _ _ _ _ H) as (Hs'&Hl&(v&Hi&Hv)); clear H
  end.
Ltac step_symex6 := first [step_symex5 | step_GetOperand ].
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

Global Instance expr_beq_spec: forall x y, BoolSpec (x = y) (x <> y) (expr_beq x y).
Admitted.

Ltac destr_expr_beq :=
  match goal with
  | H : context [expr_beq ?a ?b] |- _ => destr.destr (expr_beq a b)
  end.

Lemma operation_size_cases i n : Syntax.operation_size i = Some n ->
  (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N.
Proof.
Admitted.

Import UniquePose.
Ltac pose_operation_size_cases :=
  match goal with
  | H : Syntax.operation_size _ = Some _ |- _ =>
      unique pose proof (operation_size_cases _ _ H)
  end.

Ltac invert_eval :=
  match goal with
  | H : reveal ?d _ ?i = ?rhs, G : eval ?d (ExprRef ?i) ?v |- _ =>
      let h := Head.head rhs in is_constructor h;
      let HH := fresh H in
      epose proof (eval_reveal _ d _ i v G _ H) as HH;
      clear H; rename HH into H
  | H : eval ?d (ExprApp ?n) ?v |- _ =>
      let HH := fresh H in
      inversion H as [|? ? _ ? [] HH ];
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
  | |- context[SetOperand ?a ?b ?c ?d ?x] =>
      match goal with H : SetOperand a b c d ?y = Some _ |- _ =>
          replace x with y; [rewrite H|]; cycle 1
  end end.

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
  | progress (cbn beta iota delta [fst snd Syntax.op Syntax.args] in *; cbv beta iota delta [Reveal Crypto.Util.Option.bind Symbolic.ret Symbolic.err Symeval mapM] in *; subst)
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

Lemma R_SymexNornalInstruction s m (HR : R s m) instr :
  forall s', Symbolic.SymexNormalInstruction instr s = Success (tt, s') ->
  exists m', Semantics.DenoteNormalInstruction m instr = Some m' /\ R s' m'.
Proof.
  intros s' H.
  case instr as [op args]; cbv [SymexNormalInstruction] in H.
  repeat destruct_one_match_hyp; repeat step01.

  1:admit. (* adc *)
  1:admit. (* adcx *)
  1:admit. (* add *)
  1:admit. (* adox *)
  1:admit. (* and *)
  1:admit. (* bzhi *)

  { (* clc *) step.
    { (* eval *) repeat (eauto || econstructor). }
    step.
    { instantiate (1:=false); eassumption. }
    cbn; eauto. }
  { (* cmovc *)
    cbv [Symeval mapM] in *.
    repeat step.
    { (* eval *) repeat (eauto || econstructor). }
    cbv [DenoteNormalInstruction]; repeat step.
    repeat match goal with H : _ |- _ => rewrite Bool.pull_bool_if, ?N2Z.id in H end.
    eexists m0; rewrite <-Hm0; clear Hm0; split; [|eassumption].
    destruct vCF; cbn; trivial.
    symmetry; revert Hv.
    assert (DenoteOperand 64 n m a = Some v -> SetOperand 64 n m a v = Some m)
      by admit; trivial. }
  { (* cmovnz *)
    cbv [Symeval mapM] in *.
    repeat step.
    { (* eval *) repeat (eauto || econstructor). }
    cbv [DenoteNormalInstruction]; repeat step.
    repeat match goal with H : _ |- _ => rewrite Bool.pull_bool_if, ?N2Z.id in H end.
    rewrite Bool.if_negb.
    admit. (* stuck? *) }

  1:admit. (* dec *)
  1:admit. (* imul *)
  1:admit. (* imul *)
  1:admit. (* inc *)
  1:admit. (* lea *)

  { (* mov   *) cbv [DenoteNormalInstruction]; repeat step; rewrite N2Z.id in *; eauto. }
  { (* movzx *) cbv [DenoteNormalInstruction]; repeat step; rewrite N2Z.id in *; eauto. }
  { (* mulx *)
    repeat step.
    { repeat (eauto || econstructor). }
    { repeat (eauto || econstructor). }
    { repeat (eauto || econstructor). }
    cbv [DenoteNormalInstruction]; repeat step.
    repeat resolve_SetOperand_using_hyp; eauto.
    all : cbn [fold_right]; rewrite Z.mul_1_r.
    1: Lia.lia.
    rewrite Z.shiftr_div_pow2, N.shiftr_div_pow2 by Lia.lia.
    rewrite Z2N.inj_div, Z2N.inj_pow, N2Z.id;
      try eapply Z.pow_nonneg; eauto; try Lia.lia. }

  1:admit. (* ret -- note: strip from input, disallow in Symbolic *)

  { (* sar *)
    step.
    { repeat (eauto || econstructor). }

    destr_expr_beq; repeat step1.

    1: repeat step1; step.
    1: { (* eval *) repeat (eauto || econstructor). }
    1: repeat step1; step.
    1: { rewrite Z.bit0_mod. rewrite Z.land_ones in Hcf by (clear;Lia.lia). exact Hcf. }
    1: repeat step1; step.
    1: { repeat econstructor. }
    1: repeat step1; step.
    1: { instantiate (1:=false). eassumption. }

    all: unfold DenoteNormalInstruction; repeat step1.
    all : repeat resolve_SetOperand_using_hyp.
    1,3: (* bitwise Z&N *) admit.
    all : eexists; split; [exact eq_refl|].

    (* bash flag state weakening *)
    all: revert Hs'.
    all: (
      destruct s';
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn -[Syntax.operation_size] in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; eauto;
             pose_operation_size_cases;
             rewrite ?Z.shiftr_0_r, <-?Z.bit0_odd, <-?N2Z.inj_testbit;
             f_equal; try Lia.lia).  }
  { (* rcr *)
    step. 
    1: { repeat (eauto || econstructor). }
    destr_expr_beq; repeat step1.
    1:repeat step1; step.
    1: { repeat (eauto || econstructor). }
    1:repeat step1; step.
    1: { instantiate (1:=(Z.testbit (Z.of_N v) 0)).
         eval_same_expr_goal. rewrite Z.bit0_mod, Z.shiftr_0_r, Z.land_ones;
         cbn; Lia.lia. }

    all: cbv beta delta [DenoteNormalInstruction]; repeat step1.
    all: subst sa; repeat step1.

    all : repeat resolve_SetOperand_using_hyp.
    1,3: (* bitwise Z&N *) admit.

    1: replace cnt with 1%N in *. 2:{
      pose_operation_size_cases. subst cnt.
      replace v0 with 1%N in * by Lia.lia.
      repeat destruct_one_match; intuition (subst n; trivial). }

    all : eexists; split; [exact eq_refl|].

    (* bash flag state weakening *)
    all : revert Hs'.
    all:
      destruct s';
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | H : _ = None |- _ => progress (try rewrite H; try rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition idtac
             end; try eauto; try Lia.lia.
     cbv [set_flag set_flag_internal]; repeat (destruct_one_match||step1).
     subst v1c.
     rewrite N.lor_spec, N.shiftl_spec_low by admit. (* s <> 0 *)
     rewrite <-?Z.bit0_odd, Bool.orb_false_r, <-?N2Z.inj_testbit; trivial.
  }

  1: (* sbb *) admit.

  { (* setc *) cbv [DenoteNormalInstruction]; repeat step;
    resolve_SetOperand_using_hyp; eauto. destruct vCF; trivial. }
  { (* seto *) cbv [DenoteNormalInstruction]; repeat step;
    resolve_SetOperand_using_hyp; eauto. destruct vOF; trivial. } 
  { (* shr *) repeat step.
    1: { repeat (eauto || econstructor). }
    cbv beta delta [DenoteNormalInstruction]; repeat step. subst sa; repeat step.
    resolve_SetOperand_using_hyp; eauto.
    (* bitwise N&Z *)1:admit.

    eexists; split; [exact eq_refl|].
    (* bash flags weakening *)
    case s', m0 in *; cbn;
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn in * ; subst)
             | _ => destruct_one_match
             | _ => progress intuition eauto 1
             end. }

  1: (* shrd *) admit.

  1: (* sub *) {
    idtac.
    repeat step.
    1: { (* eval *) repeat (eauto || econstructor). }
    1: { (* eval *) repeat (eauto || econstructor). }
    1: { (* eval *) repeat (eauto || econstructor). }
    1: { rewrite Z.bit0_mod; eauto. }
    cbv [DenoteNormalInstruction]; repeat step.
    resolve_SetOperand_using_hyp.
    { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_0_r, ?N.add_0_r, ?Z.add_opp_r by Lia.lia).
      push_Zmod; pull_Zmod. rewrite Z.add_opp_r; congruence. }

    eexists; split; [exact eq_refl|].

    (* bash flags weakening *)
    case s', m in *; cbn;
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | H : R_flag ?d ?f (Some ?y) |- R_flag ?d ?f ?x =>
                 let HH := fresh in enough (HH : x = Some y) by (rewrite HH; exact H)
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn in * ; subst)
             | _ => progress intuition eauto 1
             end.
    { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_0_r, ?N.add_0_r, ?Z.add_opp_r, ?N2Z.id by Lia.lia).
      push_Zmod; pull_Zmod.
      replace v1 with v by congruence; replace v2 with v0 by congruence.
      rewrite Z.add_opp_r, Z.odd_opp, <-Z.bit0_odd, Z.shiftr_spec, Z.add_0_l by Lia.lia.
      set (Z.of_N v - Z.of_N v0) as d.
      rewrite Z2N.id by (eapply Z.mod_pos_bound, Z.pow_pos_nonneg; Lia.lia).
      f_equal.
      (* negb (d mod 2 ^ Z.of_N n =? d) = Z.testbit d (Z.of_N n) *)
      admit. } }

  { (* test r r *) repeat step.
    1: { (* eval *) repeat (eauto || econstructor). }
    1: { (* eval *) instantiate (1:=false). eauto. }
    repeat step.
    1: { (* eval *) instantiate (1:=false). eauto. }
    1: { (* eval *) repeat (eauto 6 || econstructor). }
    repeat step.
    1: { eval_same_expr_goal; trivial. }
    repeat step.
    cbv [DenoteNormalInstruction]; repeat step.
    eexists; split; [exact eq_refl|].

    destruct (Equality.ARG_beq_spec a a0); try discriminate; subst a0.
    replace v0 with v in * by congruence; clear v0.
    rewrite N.land_diag.

    replace (Z.of_N v =? 0) with (v =? 0)%N in * by admit.

    (* bash flags weakening *)
    case s', m in *; cbn;
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn in * ; subst)
             | _ => progress intuition eauto 1
             end.
  }

  { (* test *) repeat step.
    1: { (* eval *) repeat (eauto || econstructor). }
    1: { (* eval *) instantiate (1:=false). eauto. }
    repeat step.
    1: { (* eval *) instantiate (1:=false). eauto. }
    cbv [DenoteNormalInstruction]; repeat step.
    eexists; split; [exact eq_refl|].
    destruct s', m;
      repeat match goal with
             | H : R_flag _ ?f None |- _ => eapply R_flag_None_r in H; try (rewrite H in * )
             | _ => progress (cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *; cbn in * ; subst)
             | _ => progress intuition eauto 1
             end. }

  { (* xchg *)
    all: cbv beta delta [DenoteNormalInstruction]; repeat step.
    subst sa; repeat step; eauto.
    resolve_SetOperand_using_hyp; eauto using N2Z.id.
    resolve_SetOperand_using_hyp; eauto using N2Z.id. }
  (* xor *) admit.

Admitted.

End WithCtx.
