Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Import Coq.Lists.List. (* [map] is [List.map] not [ErrorT.map] *)
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.Tactics.WarnIfGoalsRemain.
Require Crypto.Util.Option.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import Crypto.Assembly.Equivalence.
Import Sorting.Permutation.

Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory. Import WithoutTuples.
Require Import coqutil.Map.Interface. (* coercions *)
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Import Word.Naive.

Section Memory.
  (* bedrock2/src/bedrock2/Memory.v Section WithoutTuples *)
  Import Word.Properties Word.Interface Coq.Init.Byte coqutil.Map.OfListWord Map.Properties coqutil.Tactics.Tactics.
  Context {width: Z} {word: word width} {mem: map.map word byte}.
  Context {mem_ok: map.ok mem} {word_ok: word.ok word}.
  Local Infix "$+" := map.putmany (at level 70).
  Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").
  Local Notation unchecked_store_bytes := (unchecked_store_bytes (mem:=mem) (word:=word)).
  Lemma unchecked_store_bytes_unchecked_store_bytes m a bs1 bs2 :
    length bs1 = length bs2 ->
    unchecked_store_bytes (unchecked_store_bytes m a bs1) a bs2 =
    unchecked_store_bytes m a bs2.
  Proof using mem_ok word_ok.
    cbv [unchecked_store_bytes]; intros.
    eapply map.map_ext; intros.
    rewrite !map.get_putmany_dec, !map.get_of_list_word_at;
      repeat (destruct_one_match; trivial).
    epose proof proj1 (List.nth_error_Some bs1 (BinInt.Z.to_nat (word.unsigned (word.sub k a)))) ltac:(congruence).
    rewrite H in H0.
    eapply List.nth_error_Some in E; intuition idtac.
  Qed.

  (* not sure where to put this since depends on sep *)
  Import Map.Interface Word.Interface BinInt.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion word.unsigned : word.rep >-> Z.
  Let sepclause_of_map {key value map} (m : @map.rep key value map)
    : map.rep -> Prop := Logic.eq m.
  Local Coercion sepclause_of_map : Interface.map.rep >-> Funclass.

  Lemma unchecked_store_bytes_of_sep
    m a bs1 bs2 R (Hsep : sep R (bs1$@a) m)
    (Hlen : length bs1 = length bs2)
    : sep R (bs2$@a) (unchecked_store_bytes m a bs2).
  Proof using mem_ok word_ok.
    destruct Hsep as (?&?&(?&Hd)&HR&?);
      cbv [sepclause_of_map] in *; subst.
    setoid_rewrite unchecked_store_bytes_unchecked_store_bytes; trivial.
    eexists _, _; split; split; try exact HR; try exact eq_refl.
    cbv [map.disjoint] in *; intros k v1 v2 Hv1 Hv2.
    pose proof map.get_of_list_word_at_domain a bs1 k as HA.
    pose proof map.get_of_list_word_at_domain a bs2 k as HB.
    rewrite Hlen, <-HB in HA; clear HB.
    destruct (map.get (bs2$@a) k) in *; try congruence.
    pose proof proj2 HA ltac:(congruence).
    destruct (map.get (bs1$@a) k) eqn:? in *; try congruence.
    eauto.
  Qed.
End Memory.


Require Import Crypto.Util.Prod.
From Crypto.Util.Tactics Require Import BreakMatch DestructHead UniquePose.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ZUtil.Ones.
Import coqutil.Tactics.autoforward coqutil.Decidable coqutil.Tactics.Tactics.

Local Coercion ExprRef : idx >-> expr.

Section WithFrame.
Context (frame : mem_state -> Prop).

Section WithCtx1.
Context (G : symbol -> option Z).
Local Notation eval := (Symbolic.eval G).
Local Notation gensym_dag_ok := (Symbolic.gensym_dag_ok G).
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

Definition R_cell64 (ia iv : idx) : mem_state -> Prop :=
  Lift1Prop.ex1 (fun a =>
  Lift1Prop.ex1 (fun bs => sep (emp (
      eval ia (word.unsigned a) /\
      length bs = 8%nat /\ eval iv (le_combine bs)))
    (eq (OfListWord.map.of_list_word_at a bs)))).

Fixpoint R_mem (sm : Symbolic.mem_state) : mem_state -> Prop :=
  match sm with
  | nil => frame
  | cons (ia, iv) sm' => sep (R_cell64 ia iv) (R_mem sm')
  end.
End WithDag.

Definition R (ss : symbolic_state) (ms : machine_state) : Prop :=
  let (mr, mf, mm) := ms in
  let (d, sr, sf, sm) := ss in
  gensym_dag_ok d /\ R_regs d sr mr /\ R_flags d sf mf /\ R_mem d sm mm.


Lemma R_flag_None_l d f : R_flag d None f.
Proof using Type. inversion 1. Qed.
Lemma R_flag_None_r d f : autoforward.autoforward (R_flag d f None) (f = None).
Proof using Type.
  destruct f; cbv; trivial. intros H.
  case (H _ eq_refl) as (?&?&HX); inversion HX.
Qed.

Local Hint Resolve R_flag_None_l : core.
Local Hint Resolve R_flag_None_r : typeclass_instances.

Lemma get_flag_R s m f (HR : R s m) :
  forall i, Symbolic.get_flag s f = Some i ->
  exists b, eval s i (Z.b2z b) /\
  Semantics.get_flag m f = Some b.
Proof using Type.
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
Proof using Type.
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
End WithCtx1.
Local Hint Resolve R_flag_None_l : core.
Local Hint Resolve R_flag_None_r : typeclass_instances.

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
Local Arguments Z.ones : simpl never.
Local Arguments Z.land !_ !_.
Local Arguments Z.lor !_ !_.
Local Arguments Z.shiftl !_ !_.
Local Arguments Z.shiftr !_ !_.

Section WithCtx2.
Context (G G' : symbol -> option Z).
Local Notation eval := (Symbolic.eval G).
Local Notation gensym_dag_ok := (Symbolic.gensym_dag_ok G).
Local Notation eval' := (Symbolic.eval G').
Local Notation gensym_dag_ok' := (Symbolic.gensym_dag_ok G').

Local Notation R_reg' := (R_reg G').
Local Notation R_reg := (R_reg G).
Local Notation R_regs' := (R_regs G').
Local Notation R_regs := (R_regs G).
Local Notation R_flag' := (R_flag G').
Local Notation R_flag := (R_flag G).
Local Notation R_flags' := (R_flags G').
Local Notation R_flags := (R_flags G).
Local Notation R_cell64' := (R_cell64 G').
Local Notation R_cell64 := (R_cell64 G).
Local Notation R_mem' := (R_mem G').
Local Notation R_mem := (R_mem G).
Local Notation R' := (R G').
Local Notation R := (R G).

Notation subsumed d1 d2 := (forall i v, eval d1 i v -> eval' d2 i v).
Local Infix ":<" := subsumed (at level 70, no associativity).

Lemma R_flag_subsumed d s m (HR : R_flag d s m) d' (Hlt : d :< d')
  : R_flag' d' s m.
Proof using Type.
  cbv [R_flag] in *; intros.
  case (HR i H) as (?&?&?); subst; eauto.
Qed.

Lemma R_flags_subsumed d s m (HR : R_flags d s m) d' (Hlt : d :< d')
  : R_flags' d' s m.
Proof using Type.
  cbv [R_flags Tuple.fieldwise Tuple.fieldwise'] in *;
    intuition eauto using R_flag_subsumed.
Qed.

Lemma R_reg_subsumed d s m (HR : R_reg d s m) d' (Hlt : d :< d')
  : R_reg' d' s m.
Proof using Type. cbv [R_reg] in *; intuition eauto. Qed.

Lemma R_regs_subsumed d s m (HR : R_regs d s m) d' (Hlt : d :< d')
  : R_regs' d' s m.
Proof using Type.
  cbv [R_regs Tuple.fieldwise Tuple.fieldwise'] in *;
    intuition eauto using R_reg_subsumed.
Qed.

Local Existing Instance Naive.word64_ok.
Local Existing Instance SortedListWord.ok.

Lemma R_cell64_subsumed d i i0 d' (Hd' : d :< d') m :
  R_cell64 d i i0 m -> R_cell64' d' i i0 m.
Proof using Type.
  clear frame; intros (?&?&?&(?&?&?&?)).
  eexists _, _, _, _; split; cbv [emp] in *; intuition eauto.
Qed.

Lemma R_mem_subsumed d s m (HR : R_mem d s m) d' (Hlt : d :< d')
  : R_mem' d' s m.
Proof using Type.
  revert dependent m; induction s; cbn; break_match; intuition idtac.
  eapply SeparationLogic.Proper_sep_impl1; try eassumption.
  intro; eauto using R_cell64_subsumed.
  Unshelve.
  { refine (SortedListWord.ok _ _). }
Qed.

Lemma R_subsumed s m (HR : R s m) d' (Hd' : gensym_dag_ok' d') (Hlt : s :< d')
  (s' := update_dag_with s (fun _ => d')) : R' s' m.
Proof using Type.
  destruct s, m; case HR as (Hd&Hr&Hf&Hm);
    cbv [update_dag_with] in *; cbn in *;
    intuition eauto using R_flags_subsumed, R_regs_subsumed, R_mem_subsumed.
Qed.
End WithCtx2.

Section WithCtx1'.
Context (G : symbol -> option Z).
Local Notation eval := (Symbolic.eval G).
Local Notation gensym_dag_ok := (Symbolic.gensym_dag_ok G).
Local Notation R_reg := (R_reg G).
Local Notation R_regs := (R_regs G).
Local Notation R_flag := (R_flag G).
Local Notation R_flags := (R_flags G).
Local Notation R_cell64 := (R_cell64 G).
Local Notation R_mem := (R_mem G).
Local Notation R := (R G).

Notation subsumed d1 d2 := (forall i v, eval d1 i v -> eval d2 i v).
Local Infix ":<" := subsumed (at level 70, no associativity).

Local Existing Instance Naive.word64_ok.
Local Existing Instance SortedListWord.ok.

Lemma R_mem_Permutation d s1 m (HR : R_mem d s1 m) s2
  (HP : Permutation s1 s2) : R_mem d s2 m.
Proof using Type.
  revert dependent m. induction HP; cbn; break_match; intros; eauto.
  { eapply SeparationLogic.Proper_sep_impl1; cbv [Lift1Prop.impl1]; eauto. }
  cbv [mem_state] in *.
  refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ HR); clear HR.
  SeparationLogic.cancel.
  SeparationLogic.cancel_seps_at_indices 0%nat 1%nat; try exact _.
  { refine (SortedListWord.ok _ _). }
  2: { epose proof Properties.word.eqb_spec. exact H. }
  trivial.
  reflexivity.
  Unshelve.
  { refine (SortedListWord.ok _ _). }
  { refine (SortedListWord.ok _ _). }
  2: { epose proof Properties.word.eqb_spec. exact H. }
Qed.

Lemma get_reg_R_regs d s m (HR : R_regs d s m) ri :
  forall i, Symbolic.get_reg s ri = Some i ->
  exists v, eval d i v /\ Tuple.nth_default 0 ri m = v.
Proof using Type.
  cbv [Symbolic.get_reg]; intros.
  rewrite <-Tuple.nth_default_to_list in H.
  cbv [nth_default] in H; BreakMatch.break_match_hyps; subst; [|solve[congruence] ].
  destruct s,m; cbn in *; cbv [R_regs R_reg] in *.
  eapply Tuple.fieldwise_to_list_iff in HR.
  eapply Forall.Forall2_forall_iff_nth_error in HR; cbv [Crypto.Util.Option.option_eq] in HR.

  rewrite Heqo in HR.
  BreakMatch.break_match_hyps; [|solve[contradiction]].
  specialize (proj1 HR _ eq_refl).
  eexists; split; [eassumption|].

  rewrite <-Tuple.nth_default_to_list.
  cbv [nth_default].
  rewrite Heqo0.
  trivial.
Qed.

Lemma get_reg_R s m (HR : R s m) ri :
  forall i, Symbolic.get_reg s ri = Some i ->
  exists v, eval s i v /\ Tuple.nth_default 0 ri (m : reg_state) = v.
Proof using Type.
  destruct s, m; apply get_reg_R_regs, HR.
Qed.

Lemma bind_assoc {A B C} (v:M A) (k1:A->M B) (k2:B->M C) s
 : (y <- (x <- v; k1 x); k2 y)%x86symex s = (x<-v; y<-k1 x; k2 y)%x86symex s.
Proof using Type. cbv; destruct v; trivial. Qed.

(* workaround: using cbn instead of this lemma makes Qed hang after next rewrite in same hyp *)
Lemma unfold_bind {A B} ma amb s :
  @bind A B ma amb s = ltac:(let t := eval unfold bind, ErrorT.bind in (@bind A B ma amb s) in exact t).
Proof using Type. exact eq_refl. Qed.

Ltac step_symex0 :=
  match goal with
  | H : (x <- ?v; ?k)%x86symex ?s = _ |- _  =>
    rewrite !bind_assoc in H
  | H : (x <- ?v; ?k)%x86symex ?s = Success _ |- _  =>
    rewrite unfold_bind in H;
    match type of H with (* workaround: rewrite sometimes reduces the match *)
    | match _ with _ => _ end = Success _ =>
      let x := fresh x in
      let HH := fresh "HS" x in
      destruct v as [[x ?]|] eqn:HH in H;
        [|solve[exfalso;clear-H;inversion H]]
    | _ => idtac
    end
  end.
Ltac step_symex := step_symex0.

Lemma GetFlag_R s m (HR : R s m) f i s' (H : GetFlag f s = Success (i, s')) :
  exists b, eval s i (Z.b2z b) /\ Semantics.get_flag m f = Some b /\ s = s'.
Proof using Type.
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

Lemma Merge_R {descr:description} s m (HR : R s m) e v (H : eval s e v) :
  forall i s', Merge e s = Success (i, s') ->
  R s' m /\ s :< s' /\ eval s' i v.
Proof using Type.
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

Lemma App_R {descr:description} s m (HR : R s m) e v (H : eval_node G s e v) :
  forall i s', Symbolic.App e s = Success (i, s') ->
  R s' m /\ s :< s' /\ eval s' i v.
Proof using Type.
  cbv [Symbolic.App]; intros.
  eapply Merge_R in H0; intuition eauto using eval_simplify.
Qed.

Ltac step_App :=
  match goal with
  | H : Symbolic.App ?n ?s = Success (?i, ?s') |- _ =>
    (*let v := fresh "v" i in*) let Hi := fresh "H" i in (* fresh does not generate fresh evar names *)
    let Hl := fresh "Hl" s' in let Hs' := fresh "H" s' in
    let t := open_constr:(fun A B => App_R s _ A n _(*?[v]*) B _ _ H) in
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

Lemma SetFlag_R s m f (HR : R s m) (i:idx) b (Hi : eval s i (Z.b2z b)) :
  forall _tt s', Symbolic.SetFlag f i s = Success (_tt, s') ->
  R s' (SetFlag m f b) /\ s :< s'.
Proof using Type.
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

Lemma GetReg_R {descr:description} s m (HR: R s m) r i s'
  (H : GetReg r s = Success (i, s'))
  : R s' m  /\ s :< s' /\ eval s' i (get_reg m r).
Proof using Type.
  cbv [GetReg GetReg64 bind some_or get_reg index_and_shift_and_bitcount_of_reg] in *.
  pose proof (get_reg_R s _ ltac:(eassumption) (reg_index r)) as Hr.
  destruct Symbolic.get_reg in *; [|inversion H]; cbn in H.
  specialize (Hr _ eq_refl); case Hr as (v&Hi0&Hv).
  rewrite Hv; clear Hv.
  step_symex; eauto.
  repeat (eauto || econstructor); cbn [interp_op].
Qed.

Ltac step_GetReg :=
  match goal with
  | H : Symbolic.GetReg ?r ?s = Success (?v, ?s') |- _ =>
    let Hs' := fresh "H" s' in let Hlt := fresh "He" s' in let Hv := fresh "Hv" s' in
    let t := open_constr:(fun A B => GetReg_R s _ A r v s' H) in
    unshelve (edestruct t as (Hs'&Hlt&Hv); clear H); shelve_unifiable;
    [eassumption|..|clear H]
  end.

Lemma Address_R {descr:description} s m (HR : R s m) (sa:AddressSize) o a s' (H : Symbolic.Address o s = Success (a, s'))
  : R s' m /\ s :< s' /\ exists v, eval s' a v /\ @DenoteAddress sa m o = v.
Proof using Type.
  destruct o as [? ? ? ?]; cbv [Address DenoteAddress Syntax.mem_base_reg Syntax.mem_offset Syntax.mem_scale_reg err ret] in *; repeat step_symex.
  all : repeat first [ progress inversion_ErrorT
                     | progress inversion_pair
                     | progress subst
                     | first [ step_symex | step_GetReg ]; try solve [repeat (eauto || econstructor)]; []
                     | break_innermost_match_hyps_step; cbn [fst snd] in * ].
  all : Tactics.ssplit; eauto 99.
  all : eexists; split; eauto; [].
  all : cbv [DenoteConst fold_right].
  all : rewrite !Z.land_ones by lia.
  all : push_Zmod; pull_Zmod.
  all : f_equal; lia.
  (* step_symex leaves over useless evars :-( *)
  Unshelve. all: try exact True.
Qed.

Ltac step_Address :=
  match goal with HSa: context[Address] |- _ =>
      eapply Address_R in HSa; [|eassumption];
          destruct HSa as (?&?&?&?&?)
  end.

Ltac step_symex4 := first [step_symex3 | step_SetFlag | step_Address].
Ltac step_symex ::= step_symex4.

Lemma load_bytes_Rcell64 d
  (a:idx) va (Ha : eval d a va)
  i m fr (HR : (R_cell64 d a i ⋆ fr)%sep m)
  : exists bs, load_bytes m (word.of_Z va) 8 = Some bs /\ eval d i (le_combine bs).
Proof using Type.
  cbn in HR. eapply SeparationLogic.sep_comm in HR.
  destruct HR as (?&?&(?&?)&?&?). rewrite H.
  destruct H2 as (?&?&?). eapply SeparationLogic.sep_emp_l in H2;
    destruct_head'_and.
  eapply eval_eval in Ha; [|eauto]; []; subst.
  eexists; split; try eassumption; cbv [get_mem Crypto.Util.Option.bind] in *.
  rewrite word.of_Z_unsigned.
  unshelve epose proof load_bytes_of_putmany_bytes_at _ x1 x _ H4 ltac:(clear;lia).
  destruct load_bytes eqn:?; simpl in *; try congruence; eassumption.
  Unshelve.
  { refine (SortedListWord.ok _ _). }
  2: { epose proof Properties.word.eqb_spec. exact H. }
Qed.

Lemma Load64_R s m (HR : R s m) (a : idx)
  va (Ha : eval s a va)
  i s' (H : Load64 a s = Success (i, s'))
  : s' = s /\ exists v, eval s i v /\ get_mem m va 8 = Some v /\ v = Z.land v (Z.ones 64).
Proof using Type.
  cbv [Load64 some_or Symbolic.load option_map] in *.
  destruct find as [(?&?)|] eqn:? in *;
    inversion_ErrorT; Prod.inversion_prod; subst.
  split;trivial.
  eapply ListUtil.find_some_iff in Heqo;
    repeat (cbn in *; destruct_head'_and; destruct_head'_ex).
  clear H1. autoforward with typeclass_instances in H0; subst.
  eapply nth_error_split in H;
    repeat (cbn in *; destruct_head'_and; destruct_head'_ex).
  destruct s'; cbn in *; destruct_head'_and; subst.
  progress unfold machine_mem_state in *.
  eapply R_mem_Permutation in H4;
    [|symmetry; eapply Permutation.Permutation_middle].
  cbv [get_mem Crypto.Util.Option.bind].
  eapply load_bytes_Rcell64 in H4; eauto; [];
    repeat (destruct_head'_and; destruct_head'_ex).
  eexists; split; try eassumption; split.
  { destruct_one_match; simpl in *; try congruence. }
  { epose proof le_combine_bound x as HH.
    erewrite length_load_bytes in HH by eassumption.
    rewrite Z.land_ones, Z.mod_small; lia. }
Qed.

Lemma store_R d s m (HR : R_mem d s m)
  (a : idx) va (Ha : eval d a va)
  (i : idx) v (Hi :eval d i v) (Hv : v = Z.land v (Z.ones 64))
  v' (Hv' : Z.land v' (Z.ones 64) = v)
  s' (H : Symbolic.store a i s = Some s')
  : exists m', set_mem m va 8 v' = Some m' /\ R_mem d s' m'.
Proof using Type.
  cbv [Symbolic.store Crypto.Util.Option.bind ] in *.
  destruct List.indexof eqn:Hfound; Option.inversion_option.
  eapply List.indexof_Some in Hfound; destruct_head_ex; destruct_head_and.
  autoforward with typeclass_instances in H1; subst a s'.
  pose H0 as H0'; eapply nth_error_split in H0';
    repeat (destruct_head_and; destruct_head_ex); subst s n.
  destruct x; cbn [fst snd] in *.
  eapply R_mem_Permutation in HR;
    [|symmetry; eapply Permutation.Permutation_middle].
  cbv [set_mem store_bytes].
  pose proof split_le_combine (le_split 8 v').
  rewrite length_le_split, le_combine_split, <-Z.land_ones in H by lia.
  setoid_rewrite Hv' in H; clear Hv'; rewrite <-H; clear H.
  cbn in HR.
  rewrite length_le_split.
  pose proof HR as HR'; eapply load_bytes_Rcell64 in HR'; eauto; [];
    repeat (destruct_head'_and; destruct_head'_ex).
  rewrite H.
  eexists; split; trivial; [].
  erewrite <-Crypto.Util.ListUtil.splice_nth_equiv_update_nth_update
    by (rewrite app_length; cbn; clear; lia); instantiate (1:=(0,0)%N).
  cbv [Crypto.Util.ListUtil.splice_nth].
  rewrite ListUtil.firstn_app_sharp by trivial.
  rewrite (ListUtil.app_cons_app_app _ _ _ x1) at 2.
  rewrite ListUtil.skipn_app_sharp by (rewrite app_length; cbn; clear; lia).
  cbv [nth_default]; destruct_one_match; setoid_rewrite H0 in E;
    Option.inversion_option; destruct p; Prod.inversion_prod; subst;
    cbn [fst snd].
  eapply R_mem_Permutation; [|eapply Permutation.Permutation_middle];
  cbn [R_mem]; cbv [R_cell64] in *.
  eapply SeparationLogic.sep_ex1_l in HR. destruct HR as [? HR].
  (* COQBUG: semicolon on previous line fails *)
  eapply SeparationLogic.sep_ex1_l in HR. destruct HR as [? HR].
  eapply SeparationLogic.sep_assoc in HR;
  eapply SeparationLogic.sep_emp_l in HR. destruct HR as [(?&?&?) HR].
  eapply eval_eval in Ha; [|eauto]; []; subst.
  eapply SeparationLogic.sep_ex1_l; eexists.
  eapply SeparationLogic.sep_ex1_l; eexists.
  rewrite word.of_Z_unsigned.
  eapply SeparationLogic.sep_assoc, SeparationLogic.sep_emp_l; split.
  2:{ eapply SeparationLogic.sep_comm in HR.
    eapply SeparationLogic.sep_comm, unchecked_store_bytes_of_sep; eauto. }
  rewrite le_combine_split, Z.mod_small; eauto.
  rewrite Z.land_ones in Hv by (clear;lia).
  clear -Hv; cbn in *; Z.div_mod_to_equations; lia.

  all : fail. Unshelve. all : shelve_unifiable.
  all : try refine (SortedListWord.ok _ _).
  all : try (epose proof Properties.word.eqb_spec as HH; exact HH).
Qed.

Lemma Store64_R s m (HR : R s m)
  (a : idx) va (Ha : eval s a va)
  (i : idx) v (Hi :eval s i v) (Hv : v = Z.land v (Z.ones 64))
  v' (Hv' : Z.land v' (Z.ones 64) = v)
  s' _tt (H : Store64 a i s = Success (_tt, s'))
  : exists m', SetMem m va 8 v' = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  cbv [Store64 bind some_or Crypto.Util.Option.bind ErrorT.bind] in *.
  destruct Symbolic.store eqn:? in H; inversion_ErrorT; Prod.inversion_prod; subst.
  destruct s, m; cbv [R] in *; destruct_head'_and.
  eapply store_R in Heqo; try eassumption; trivial; try lia;
    destruct_head_ex; destruct_head_and.
  cbv [SetMem]. setoid_rewrite H3; cbv [update_mem_with]; cbn; eauto 9.
Qed.

Lemma store8 m a
  old (Hold : get_mem m a 8 = Some old) b
  m'  (Hm': set_mem m a 8 (Z.lor (Z.land b (Z.ones 8)) (Z.ldiff old (Z.ones 8))) = Some m')
  : set_mem m a 1 b = Some m'.
Proof using Type.
  clear frame.
  cbv [set_mem store_bytes] in *.
  destruct_one_match_hyp; Option.inversion_option.
  epose proof length_load_bytes _ _ _ _ E as H;
    do 9 (destruct l; try solve [inversion H]); clear H.
  epose proof nth_error_load_bytes _ _ _ _ E as H.
  rewrite length_le_split in *.
  destruct_one_match; cycle 1.
  { eapply load_bytes_None in E0; destruct E0 as (?&?&?).
    destruct x; [|lia].
    specialize (H 0%nat ltac:(lia));
    rewrite H1 in H; inversion H. }
  f_equal; rewrite <-Hm'; clear Hm'.
  cbv [unchecked_store_bytes]; eapply map.map_ext; intros k.
  setoid_rewrite OfListWord.map.of_list_word_singleton.
  rewrite 2 Properties.map.get_putmany_dec, Properties.map.get_put_dec, map.get_empty, OfListWord.map.get_of_list_word_at.
  break_innermost_match_step;
    autoforward with typeclass_instances in Heqb8; subst.
  { rewrite word.unsigned_sub, word.unsigned_of_Z, Z.sub_diag.
    cbv [le_split]; cbn -[Z.ones]; f_equal.
    eapply Byte.byte.unsigned_inj;
      rewrite !Byte.byte.unsigned_of_Z; cbv [Byte.byte.wrap];
      rewrite <-!Z.land_ones by lia.
      bitblast.Z.bitblast. }
  destruct_one_match; trivial.
  epose proof Crypto.Util.ListUtil.nth_error_value_length _ _ _ _ E1 as I.
  rewrite length_le_split in *. specialize (H _ I); clear I.
  rewrite Z2Nat.id in H by (eapply Properties.word.unsigned_range).
  rewrite word.of_Z_unsigned in H.
  replace (word.add (word.of_Z a) (word.sub k (word.of_Z a)))
     with k in H by ring.
  rewrite <-H, <-E1; clear H E1.
  remember (Z.to_nat (word.unsigned (word.sub k (word.of_Z a)))) as i.
  destruct i.
  { destruct Heqb8. eapply Properties.word.unsigned_inj.
    epose proof Properties.word.unsigned_range (word.sub k (word.of_Z a)).
    assert (word.unsigned (word.sub k (word.of_Z a)) = 0) by lia.
    change (word.unsigned (word.sub k (word.of_Z a)) = word.unsigned (word.of_Z 0: Naive.word 64)) in H0.
    rewrite word.unsigned_sub, Properties.word.unsigned_of_Z_0 in H0.
    cbv [word.wrap] in H0.
    pose proof Properties.word.unsigned_range k.
    pose proof Properties.word.unsigned_range (word.of_Z a).
    Z.div_mod_to_equations.
    lia. }
  cbv [get_mem Crypto.Util.Option.bind] in *;
    destruct load_bytes in *; repeat Option.inversion_option; subst.
  change (le_combine (cons ?x ?y))
  with (Z.lor (Byte.byte.unsigned x) (Z.shiftl (le_combine y) 8)).
  change (le_split 8 ?x)
  with (Byte.byte.of_Z x:: le_split 7 (Z.shiftr x 8)).
  progress cbn [nth_error]; f_equal.
  rewrite Z.shiftr_lor, Z.shiftr_land, Z.land_0_r, Z.lor_0_l.
  rewrite Z.shiftr_ldiff, Z.ldiff_0_r.
  rewrite <-(Byte.byte.wrap_unsigned b0);
    cbv [Byte.byte.wrap]; rewrite <-!Z.land_ones by lia.
  rewrite Z.shiftr_lor, Z.shiftr_land, Z.land_0_r, Z.lor_0_l.
  rewrite Z.shiftr_shiftl_l, Z.shiftl_0_r by lia.
  setoid_rewrite (split_le_combine [b1; b2; b3; b4; b5; b6; b7]); trivial.
Qed.


Lemma GetOperand_R {descr:description} s m (HR: R s m) (so:OperationSize) (sa:AddressSize) a i s'
  (H : GetOperand a s = Success (i, s'))
  : R s' m /\ s :< s' /\ exists v, eval s' i v /\ DenoteOperand sa so m a = Some v.
Proof using Type.
  cbv [GetOperand DenoteOperand err] in *; break_innermost_match; inversion_ErrorT.
  { eapply GetReg_R in H; intuition eauto. }
  { progress cbv [Load ret] in *.
    repeat (cbv [err] in *; cbn [fst snd] in * || step_symex || Tactics.destruct_one_match_hyp || inversion_ErrorT || Prod.inversion_prod || subst).
    eapply Load64_R in HSv; try eassumption; [];
      repeat (subst; destruct_head'_and; destruct_head'_ex).
    repeat step_symex.
    { repeat (eauto||econstructor). }
    split; eauto; [].
    split; eauto; [].
    rewrite Z.shiftr_0_r in Hi by lia.
    eapply Bool.negb_false_iff, Bool.orb_true_iff in E; case E as [E|E];
      eapply Ndec.Neqb_complete in E; rewrite E in *; simpl Z.of_N in *.
    { cbv [get_mem Crypto.Util.Option.bind] in *.
      destruct_one_match_hyp; Option.inversion_option.
      epose proof length_load_bytes _ _ _ _ E0.
      do 1 (destruct l; try solve [inversion H]).
      eapply @nth_error_load_bytes with (i:=0%nat) in E0; [|clear;lia].
      symmetry in E0; cbn [nth_error] in E0; simpl Z.of_nat in E0.
      simpl load_bytes.
      change (Pos.to_nat 1) with 1%nat.
      cbv [load_bytes footprint List.map seq List.option_all].
      setoid_rewrite E0.
      eexists; split; eauto.
      cbv [le_combine].
      rewrite Z.shiftl_0_l, Z.lor_0_r.
      change (Z.lor (Byte.byte.unsigned b) (Z.shiftl (le_combine l) 8) = x) in H4.
      rewrite <-H4 in H5 at 2; rewrite H5; clear H4 H5.
      f_equal.
      rewrite <-Byte.byte.wrap_unsigned at 1; setoid_rewrite <-Z.land_ones; [|clear;lia].
      rewrite <-Z.land_assoc.
      change (Z.land (Z.ones 64) (Z.ones 8)) with (Z.ones 8).
      rewrite Z.land_lor_distr_l.
      bitblast.Z.bitblast. subst.
      rewrite (Z.testbit_neg_r _ (_-8)) by lia; Btauto.btauto. }
    { setoid_rewrite H4.
      eexists; split; eauto; f_equal.
      rewrite H5 at 1; trivial. } }
  { step_symex; repeat (eauto||econstructor). }
Qed.

Ltac step_GetOperand :=
  match goal with
  | H : GetOperand ?a ?s = Success (?i0, ?s') |- _ =>
    let v := fresh "v" (*a*) in let Hv := fresh "H" v
    in let Hi := fresh "H" i0 in let Heq := fresh H "eq" in
    let Hs' := fresh "H" s' in let Hl := fresh "Hl" s' in
    case (GetOperand_R s _ ltac:(eassumption) _ _ _ _ _ H) as (Hs'&Hl&(v&Hi&Hv)); clear H
  end.

(* note: do the two SetOperand both truncate inputs or not?... *)
Lemma R_SetOperand {descr:description} s m (HR : R s m)
  (sz:OperationSize) (sa:AddressSize) a i _tt s' (H : Symbolic.SetOperand a i s = Success (_tt, s'))
  v (Hv : eval s i v)
  : exists m', SetOperand sa sz m a v = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  destruct a in *; cbn in H; cbv [err] in *; inversion_ErrorT; [ | ];
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
    { rewrite <-Tuple.nth_default_to_list. cbv [nth_default]; rewrite H5. trivial. }
    assert (Z.of_N (reg_size r) + Z.of_N (reg_offset r) <= 64) by (destruct r; clear; cbv; discriminate).
    eapply Z.bits_inj_iff'; intros j Hj.
    rewrite Z.land_spec, Z.testbit_ones_nonneg by (clear -Hj; lia).
    destr.destr (j <? 64); rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; trivial; [].
    rewrite Z.lor_spec, Z.ldiff_spec, !Z.shiftl_spec, Z.land_spec, !Z.testbit_ones_nonneg by (assumption||lia).
    destr.destr (j - Z.of_N (reg_offset r) <? Z.of_N (reg_size r)); try (revert dependent j; clear -H6; lia).
    rewrite Bool.andb_true_r, Bool.andb_false_r, Bool.orb_false_l.
    rewrite H8, Z.land_spec, Z.ones_spec_high; revert dependent j; lia. }
  { progress cbv [Store] in *.
    destruct_one_match_hyp; cbv [err] in *; inversion_ErrorT.
    repeat (step_symex; cbn [fst snd] in * ).
    eapply Load64_R in HSold; eauto;
      repeat (subst; destruct_head'_ex; destruct_head'_and).
    repeat (step_symex; cbn [fst snd] in * ).
    { repeat (eauto || econstructor). }
    { repeat (eauto || econstructor). }
    rewrite !Z.shiftl_0_r, ?Z.shiftr_0_r, <-Z.land_assoc, Z.land_diag in *.
    eapply Bool.negb_false_iff, Bool.orb_true_iff in E; case E as [E|E];
      eapply Ndec.Neqb_complete in E; rewrite E in *; simpl Z.of_N in *.
    { eapply Store64_R with (v':=Z.lor (Z.land v (Z.ones 8)) (Z.ldiff x (Z.ones 8))) in H;
        try eassumption; eauto with nocore; try solve [rewrite H5; bitblast.Z.bitblast].
      destruct_head'_ex; destruct_head'_and.
      cbv [SetMem Crypto.Util.Option.bind update_mem_with] in *;
        destruct set_mem eqn:? in *; Option.inversion_option; subst.
      erewrite store8; eauto 9. }
    { eapply Store64_R with (v':=v) in H;
        try eassumption; eauto with nocore; try solve [rewrite H5; bitblast.Z.bitblast].
      destruct_head'_ex; destruct_head'_and. setoid_rewrite H. eauto 9. } }
Qed.

Ltac step_SetOperand :=
  match goal with
  | H : Symbolic.SetOperand ?a ?i ?s = Success (?_tt, ?s') |- _ =>
      let m := fresh "m" in let Hm := fresh "H" m in
      let HR := fresh "H" s' in let Hl := fresh "Hl" s' in
      case (R_SetOperand s _ ltac:(eassumption) _ _ _ _ _ _ H _ ltac:(eauto 99 with nocore))
        as (m&?Hm&HR&Hl); clear H
  end.

Lemma HavocFlags_R s m (HR : R s m) :
  forall _tt s', Symbolic.HavocFlags s = Success (_tt, s') ->
  R s' (HavocFlags m) /\ s :< s'.
Proof using Type.
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

Ltac step_symex5 := first [step_symex4 | step_GetOperand | step_SetOperand | step_HavocFlags ].
Ltac step_symex ::= step_symex5.

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
Proof using Type.
   destruct o; cbn; try congruence.
   { destruct r; cbn; inversion 1; subst; eauto. }
   { destruct (mem_bits_access_size _) as [ [] | ]; inversion 1; subst; eauto. }
Qed.

Lemma opcode_size_cases o n : opcode_size o = Some n ->
  ((o = clc /\ n = 1) \/ n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N.
Proof using Type.
  destruct o; cbn; intros; Option.inversion_option; try now subst; eauto.
Qed.

Lemma lift_map_standalone_operand_size_cases_Forall args ls
      (H : Crypto.Util.OptionList.Option.List.lift
             (map standalone_operand_size args) =
             Some ls)
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N)
  : Forall P ls.
Proof using Type.
  revert ls H; induction args as [|x xs IH]; intros; cbn in *; cbv [Crypto.Util.Option.bind] in *; break_match_hyps; repeat Option.inversion_option; subst; try now constructor.
  specialize (IH _ ltac:(eassumption)).
  match goal with H : _ |- _ => apply standalone_operand_size_cases in H end.
  constructor; subst P; eauto.
Qed.

Lemma lift_map_standalone_operand_size_cases_fold_right args x xs f init
      (H : Crypto.Util.OptionList.Option.List.lift
             (map standalone_operand_size args) =
             Some (x :: xs))
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N)
      (Hf : forall a b, P a -> (b = init \/ P b) -> P (f a b))
      (n := fold_right f init (x :: xs))
  : P n.
Proof using Type.
  apply lift_map_standalone_operand_size_cases_Forall in H.
  inversion H; clear H; subst.
  subst n; cbn [fold_right].
  apply Hf; try assumption.
  induction xs as [|x' xs IH]; inversion_one_head Forall; eauto.
Qed.

Lemma map_id_map_standalone_operand_size_cases_Forall args ls
      (H : Crypto.Util.OptionList.Option.List.map id
             (map standalone_operand_size args) =
             ls)
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N)
  : Forall P ls.
Proof using Type.
  subst.
  induction args as [|x xs IH]; intros; cbn in *; cbv [Crypto.Util.Option.bind] in *; break_match; repeat Option.inversion_option; subst; try (now constructor); eauto.
  constructor; subst P; eauto.
  eapply standalone_operand_size_cases; eassumption.
Qed.

Lemma map_id_map_standalone_operand_size_cases_fold_right args x xs f init
      (H : Crypto.Util.OptionList.Option.List.map id
             (map standalone_operand_size args) =
             x :: xs)
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64)%N)
      (Hf : forall a b, P a -> (b = init \/ P b) -> P (f a b))
      (n := fold_right f init (x :: xs))
  : P n.
Proof using Type.
  apply map_id_map_standalone_operand_size_cases_Forall in H.
  inversion H; clear H; subst.
  subst n; cbn [fold_right].
  apply Hf; try assumption.
  induction xs as [|x' xs IH]; inversion_one_head Forall; eauto.
Qed.

Lemma operation_size_cases i n : Syntax.operation_size i = Some n ->
  (((exists prefix ls, i = Build_NormalInstruction prefix Syntax.clc ls) /\ n = 1) \/ (n = 8 \/ n = 16 \/ n = 32 \/ n = 64))%N.
Proof using Type.
  clear G.
  intuition idtac; DestructHead.destruct_head'_ex; subst; cbn in *.
  cbv [Syntax.operation_size] in H.
  break_match_hyps; Option.inversion_option; subst.
  all: repeat first [ progress destruct_head'_or
                    | progress destruct_head'_and
                    | progress subst
                    | solve [ eauto ]
                    | eapply lift_map_standalone_operand_size_cases_fold_right; [ eassumption | intros ]
                    | eapply map_id_map_standalone_operand_size_cases_fold_right; [ eassumption | intros ]
                    | apply N.min_case_strong; intros
                    | match goal with
                      | [ H : Syntax.op ?i = _ |- _ ] => is_var i; destruct i; cbn in H
                      | [ H : opcode_size _ = Some _ |- _ ] => apply opcode_size_cases in H
                      | [ |- (_ /\ _) \/ _ ] => right
                      end ].
Qed.

Ltac pose_operation_size_cases :=
  match goal with
  | H : Syntax.operation_size _ = Some _ |- _ =>
      unique pose proof (operation_size_cases _ _ H)
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
  | H : eval _ (ExprApp _) _ |- _ =>
      inversion H; clear H; subst
  | H : Forall2 _ nil _ |- _
    => inversion H; clear H; subst
  | H : Forall2 _ _ nil |- _
    => inversion H; clear H; subst
  | H : Forall2 _ (_ :: _) _ |- _
    => inversion H; clear H; subst
  | H : Forall2 _ _ (_ :: _) |- _
    => inversion H; clear H; subst
  | H : interp_op _ ?o ?a = Some ?v |- _ => inversion H; clear H; subst
  end.

Ltac resolve_match_using_hyp :=
  let rewrite_for x
    := match goal with
       | [ H : x = ?v |- _ ]
         => let h := Head.head v in
            is_constructor h;
            rewrite H
       end in
  match goal with
  | [ |- context[match ?x with _ => _ end] ] => rewrite_for x
  | [ |- context[match (if _ then ?x else ?y) with _ => _ end] ]
    => progress (try rewrite_for x; try rewrite_for y)
  end.

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
  | progress (cbn beta iota delta [fst snd Syntax.op Syntax.args] in *; cbv beta iota delta [Reveal RevealConst Crypto.Util.Option.bind Symbolic.ret Symbolic.err Symeval mapM PreserveFlag some_or] in *; subst)
  | Prod.inversion_prod_step
  | inversion_ErrorT_step
  | Option.inversion_option_step
  | invert_eval
  | step_symex
  | destr_expr_beq
  | rewrite N.eqb_refl (* TODO: should this live elsewhere? *)
  ].
Ltac step1 := step; (eassumption||trivial); [].
Ltac step01 := solve [step] || step1.

Lemma SetOperand_same n m a v m'
  (Hd : DenoteOperand 64 n m a = Some v) (Hs : SetOperand 64 n m a v = Some m')
  : m = m'.
Proof using Type.
  destruct a, m; cbn -[DenoteAddress] in *; repeat (subst; Option.inversion_option).
  { cbv [update_reg_with set_reg]; cbn in *; f_equal.
    eapply Tuple.to_list_ext.
    rewrite <-Tuple.nth_default_to_list in Hd; rewrite <-Hd; clear Hd.
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
  { destruct m'; cbv [SetMem update_mem_with Crypto.Util.Option.bind get_mem option_map set_mem store_bytes unchecked_store_bytes] in *; repeat (destruct_one_match_hyp || Option.inversion_option).
    inversion Hs; clear Hs; subst; f_equal.
    clear E0.
    change (@map.putmany ?K ?V ?M ?m) with (@map.putmany K V M machine_mem_state).
    set (word.of_Z _) as a in *; clearbody a.
    rename n into n'; set (N.to_nat (operand_size m0 n' / 8)) as n in *; clearbody n; clear n'.
    epose proof (length_load_bytes _ _ _ _ E1) as Hl; rewrite <-Hl, split_le_combine.
    eapply (@map.map_ext _ _ mem_state _); intro k.
    rewrite Properties.map.get_putmany_dec, OfListWord.map.get_of_list_word_at.
    destruct_one_match; trivial.
    epose proof ListUtil.nth_error_value_length _ _ _ _ E.
    rewrite <-E; clear E.
    rewrite (nth_error_load_bytes _ _ _ _ E1 (Z.to_nat (word.unsigned (word.sub k a))) ltac:(lia)).
    rewrite Z2Nat.id, word.of_Z_unsigned by (eapply Properties.word.unsigned_range).
    f_equal. ring. }
Qed.


Lemma SymexNornalInstruction_R {descr:description} s m (HR : R s m) instr :
  forall _tt s', Symbolic.SymexNormalInstruction instr s = Success (_tt, s') ->
  exists m', Semantics.DenoteNormalInstruction m instr = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  intros [] s' H.
  case instr as [op args]; cbv [SymexNormalInstruction OperationSize] in H.
  repeat (repeat destruct_one_match_hyp; repeat step01).

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

  all: cbv beta delta [DenoteNormalInstruction];
       repeat
  match goal with
  | x := ?v |- _ => let t := type of x in
      assert_fails (idtac; match v with context[match _ with _ => _ end] => idtac end);
          subst x
  | _ => step
  | _ => resolve_SetOperand_using_hyp
  | _ => rewrite (Bool.pull_bool_if Some)
  | |- context[if (?x =? ?y)%N then _ else _] => destruct (x =? y)%N eqn:?; reflect_hyps; subst; try congruence
  | |- exists _, Some _ = Some _ /\ _ => eexists; split; [f_equal|]
  | |- exists _, None   = Some _ /\ _ => exfalso
  | |- _ /\ _ :< _ => split; [|solve[eauto 99 with nocore] ]
  end.

  all: repeat first [ match goal with
                      | [ H : DenoteOperand _ _ _ (Syntax.const _) = Some _ |- _ ] => cbv [DenoteOperand DenoteConst operand_size standalone_operand_size CONST_of_Z] in H
                      end
                    | progress Option.inversion_option
                    | progress subst ].

  all : cbn [fold_right map]; rewrite ?N2Z.id, ?Z.add_0_r, ?Z.add_assoc, ?Z.mul_1_r, ?Z.land_m1_r, ?Z.lxor_0_r;
    (congruence||eauto).
  all: rewrite ?Z.land_ones_low_alt by now try split; try apply Zpow_facts.Zpower2_lt_lin; lia.
  all: rewrite ?(fun x => Z.land_ones_low_alt (x / 8) x) by now split; try (eapply Z.le_lt_trans; [ | apply Zpow_facts.Zpower2_lt_lin ]); try lia; Z.to_euclidean_division_equations; nia.
  all: try exact eq_refl.
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
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. replace v1 with v by congruence. exact eq_refl. }
  { cbv [Symbolic.PreserveFlag Symbolic.HavocFlags Symbolic.update_flag_with ret] in HSx4; cbn in HSx4; induction_path_ErrorT HSx4; Prod.inversion_prod; subst.
    inversion H; clear H; subst s'.
    split; [|solve[eauto 99 with nocore] ].
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
             change Symbolic.signed with Semantics.signed.
             rewrite ?Z.add_0_r.
             f_equal.
             1:congruence.
             rewrite <-Z.add_opp_r; f_equal.
             pose_operation_size_cases; intuition (subst; trivial). }

  Unshelve. all : match goal with H : context[Syntax.inc] |- _ => idtac | _ => shelve end.
  { cbn; repeat (rewrite ?Z.land_ones, ?Z.add_opp_r by Lia.lia).
    push_Zmod; pull_Zmod. replace v1 with v by congruence. exact eq_refl. }
  { cbv [Symbolic.PreserveFlag Symbolic.HavocFlags Symbolic.update_flag_with ret] in HSx4; cbn in HSx4; induction_path_ErrorT HSx4; Prod.inversion_prod; subst.
    inversion H; subst s'.
    split; [|solve[eauto 99 with nocore] ].
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
             change Symbolic.signed with Semantics.signed.
             rewrite ?Z.add_0_r.
             f_equal.
             1:congruence.
             f_equal.
             pose_operation_size_cases; intuition (destruct_head'_ex; subst; try discriminate; trivial). }

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
             replace (Semantics.signed n 0) with 0; cycle 1.
             { pose_operation_size_cases. clear -H0; intuition (subst; cbv; trivial). }
             rewrite Z.add_0_r; cbv [Semantics.signed Symbolic.signed]; congruence. }

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
             change Symbolic.signed with Semantics.signed. congruence. }

  Unshelve. all : match goal with H : context[Syntax.adcx] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.adox] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.cmovc] |- _ => idtac |  H : context[Syntax.cmovb] |- _ => idtac | _ => shelve end.
  (* cmovc / cmovb *)
  all: destruct vCF; cbn [negb Z.b2z Z.eqb] in *; eauto 9; [].
  all: enough (m = m0) by (subst; eauto 9).
  all: clear -Hm0 Hv frame G ; eauto using SetOperand_same.
  all: fail.

  Unshelve. all : match goal with H : context[Syntax.cmovnz] |- _ => idtac | _ => shelve end.
  { (* cmovnz *)
    destruct vZF; cbn [negb Z.b2z Z.eqb] in *; eauto 9; [].
    enough (m = m0) by (subst; eauto 9).
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
     pose_operation_size_cases; intuition (subst; destruct_head'_ex; subst; try discriminate; cbn; clear; lia). }
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
  all : change Symbolic.rcrcnt with rcrcnt in *.
  { repeat destruct_one_match; try lia.
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
     let E0 := match goal with H : rcrcnt _ _ = _ |- _ => H end in
     rewrite E0; cbn.
     rewrite <-2Z.bit0_odd, Z.lor_spec, Z.shiftl_spec_low, Bool.orb_false_r; trivial.
     pose_operation_size_cases; intuition (subst; cbn; clear; lia). }

  Unshelve. all : match goal with H : context[Syntax.lea] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { (* lea *)
    cbv [SetOperand update_reg_with] in *; Option.inversion_option; subst; trivial. }

  Unshelve. all : match goal with H : context[Syntax.shrd] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eapply Z.bits_inj_iff'; intros i Hi.
    repeat rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.shiftr_spec, ?Z.shiftl_spec, ?Z.testbit_ones_nonneg, ?Z.testbit_0_l; try lia.
    destr (i <? Z.of_N n); rewrite ?Bool.orb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r; trivial.
    replace v0 with v3 by congruence; f_equal; f_equal.
    rewrite Z.land_ones, Z.mod_small.
    1: lia.
    3: enough (0 <= Z.land v3 (Z.of_N n - 1)) by lia; eapply Z.land_nonneg; right.
    1,2,3:pose_operation_size_cases; intuition (subst; cbn; clear; lia). }

  Unshelve. all : match goal with H : context[Syntax.shlx] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { rewrite <- Z.land_assoc.
    f_equal; f_equal; [].
    pose_operation_size_cases; intuition subst; reflexivity. }

  Unshelve. all : match goal with H : context[push] |- _ => idtac | H : context[pop] |- _ => idtac | _ => shelve end; shelve_unifiable.
  all: rewrite !Z.land_ones by lia; push_Zmod; pull_Zmod; f_equal; lia.

  Unshelve. all: shelve_unifiable.
  all: fail_if_goals_remain ().
Qed.

Lemma SymexLines_R s m (HR : R s m) asm :
  forall _tt s', Symbolic.SymexLines asm s = Success (_tt, s') ->
  exists m', Semantics.DenoteLines m asm = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  revert dependent m; revert dependent s; induction asm; cbn [SymexLines DenoteLines]; intros.
  { inversion H; subst; eauto. }
  destruct a.
  rewrite unfold_bind in H; destruct_one_match_hyp; inversion_ErrorT.
  cbv [SymexLine SymexRawLine DenoteLine DenoteRawLine ret err Crypto.Util.Option.bind] in *; cbn in *.
  destruct_one_match_hyp; inversion_ErrorT; subst; eauto; destruct v.
  eapply SymexNornalInstruction_R in E; eauto. destruct E as (m1&Hm1&Rm1&?). rewrite Hm1.
  eapply IHasm in H; eauto. destruct H as (?&?&?&?). eauto 9.
Qed.
End WithCtx1'.
End WithFrame.
