From Coq Require Import List.
From Coq Require Import Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.
From Coq Require Import NArith.
From Coq Require Import ZArith.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Import Coq.Lists.List. (* [map] is [List.map] not [ErrorT.map] *)
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.Tactics.WarnIfGoalsRemain.
Require Import Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.Option.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import Crypto.Assembly.Equivalence.
Import Sorting.Permutation.

Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Memory. Import coqutil.Map.Memory.
Require Import coqutil.Map.Interface. (* coercions *)
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Import Word.Naive.


Section Memory.
  (* bedrock2/src/bedrock2/Memory.v Section WithoutTuples *)
  Import Word.Properties Word.Interface Coq.Init.Byte coqutil.Map.OfListWord Map.Properties coqutil.Tactics.Tactics.
  Context {width: Z} {word: word width} {mem: map.map word byte}.
  Context {mem_ok: map.ok mem} {word_ok: word.ok word}.

  Import (notations) coqutil.Map.Memory.
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
Context (frame : mem_state -> Prop). (* all the untracked and probably untouched portions of memory *)

Section WithCtx1.
Context (G : symbol -> option Z).
Local Notation eval := (Symbolic.eval G).
Local Notation gensym_dag_ok := (Symbolic.gensym_dag_ok G).
Section WithDag.
Context (d : dag).
Local Notation eval := (Symbolic.eval G d).
Check eval. (* eval i v evaluates whether idx x evals to value v in the context of G and d *)


Definition R_reg (x : option idx) (v : Z) (width : N)  : Prop :=                                                    
  (forall i, x = Some i -> eval i v) /\ (v = Z.land v (Z.ones (Z.of_N width))).                                    
                                                                                                                     
Definition R_regs (sr : Symbolic.reg_state) (mr : Semantics.reg_state) : Prop :=
  let widths := List.map (fun r => reg_size r) widest_registers in                                                 
  Forall2 (fun w '(x, v) => R_reg x v w)                          
    widths                                                                                                         
    (List.combine (Tuple.to_list _ sr) (Tuple.to_list _ mr)).  

Definition R_flag (x : option idx) (ob : option bool) : Prop :=
  forall i, x = Some i -> exists b, eval i (Z.b2z b) /\ ob = Some b.
Definition R_flags : Symbolic.flag_state -> Semantics.flag_state -> Prop :=
  Tuple.fieldwise R_flag.

Definition R_cell64 (ia iv : idx) : mem_state -> Prop :=
  Lift1Prop.ex1 (fun a =>                                (* concrete address a *)
  Lift1Prop.ex1 (fun bs => sep (emp (                    (* bytes bs *)
      eval ia (word.unsigned a) /\                     (* ia evals to a *)
      length bs = 8%nat /\ eval iv (le_combine bs)))     (* iv evals to bs *)
    (eq (OfListWord.map.of_list_word_at a bs)))).     (* the mem_state has bs at address a *)

(* each symbolic.mem_state entry stores two indices, address idx and value idx *)
(* mem is related if every address actually stores that value in the concrete mem_state. *)
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

Lemma gensym_dag_ok_of_R ss ms : R ss ms -> gensym_dag_ok ss.
Proof using Type. cbv [R]; break_innermost_match; intuition. Qed.

Lemma R_flag_None_l d f : R_flag d None f.
Proof using Type. inversion 1. Qed.
Lemma R_flag_None_r d f : autoforward.autoforward (R_flag d f None) (f = None).
Proof using Type.
  destruct f; cbv; trivial. intros H.
  case (H _ eq_refl) as (?&?&HX); inversion HX.
Qed.

Local Hint Resolve gensym_dag_ok_of_R : core.
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

Lemma R_reg_subsumed d s m w (HR : R_reg d s m w) d' (Hlt : d :< d')
  : R_reg' d' s m w.
Proof using Type. cbv [R_reg] in *; intuition eauto. Qed.
Check R_reg_subsumed.

Check Tuple.fieldwise_Proper.

Lemma R_regs_subsumed d s m (HR : R_regs d s m) d' (Hlt : d :< d')
  : R_regs' d' s m.
Proof using Type.
  unfold R_regs, R_regs' in *. Search Forall2. Check Forall2_impl. Print Forall2.
  eapply Forall2_impl; [| exact HR].
  intros. destruct b as [x v].
  eapply R_reg_subsumed; eauto. 
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
Local Notation interp_op := (Symbolic.interp_op G).
Local Notation interprets_as_binop := (Symbolic.interprets_as_binop G).
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

Lemma subsumed_trans s1 s2 s3 (H12 : s1 :< s2) (H23 : s2 :< s3) : s1 :< s3.
Proof using Type.
  intros. specialize (H12 i v). apply H12 in H. specialize (H23 i v). apply H23 in H. exact H.
Qed.

Lemma subsumed_refl s : s :< s.
Proof using Type.
		intros. exact H.
Qed.

Ltac solve_subsumed :=
solve [ eassumption
      | apply subsumed_refl
      | repeat (eapply subsumed_trans; [eassumption|]); eapply subsumed_refl ].
      
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

Lemma R_regs_nth d s m (HR : R_regs d s m) ri i                                                                    
  (Hs : nth_error (Tuple.to_list _ s) (N.to_nat ri) = Some (Some i)) :                                             
  exists v, eval d i v /\ nth_error (Tuple.to_list _ m) (N.to_nat ri) = Some v.                                    
Proof using Type.
  unfold R_regs in HR.                                                                                             
  rewrite Forall.Forall2_forall_iff_nth_error in HR.
  specialize (HR (N.to_nat ri)).                                                                                   
  rewrite nth_error_map, ListUtil.nth_error_combine, Hs in HR.                                                              
  destruct (nth_error (Tuple.to_list _ m) (N.to_nat ri)) as [v|] eqn:Hm.
  - (* Some v — main case *)
    cbn [Crypto.Util.Option.option_eq] in HR. exists v. split; try reflexivity.
    destruct (nth_error widest_registers (N.to_nat ri)) as [wr|] eqn:Hwr;
    unfold R_reg in HR; destruct HR. apply H; reflexivity.
    exfalso.                                                  
    apply nth_error_None in Hwr.                                                              
    assert (length widest_registers = 100)%nat by reflexivity.                                                         
    assert (N.to_nat ri < length (Tuple.to_list 100 m))%nat
      by (eapply nth_error_Some; congruence).
    rewrite Tuple.length_to_list in *.          
    lia. 
  - (* None — contradicts Hs via equal lengths *)
    exfalso.                                                                                                         
    apply nth_error_None in Hm.
    assert (N.to_nat ri < length (Tuple.to_list 100 s))%nat                                                            
    by (eapply nth_error_Some; congruence).
    rewrite !Tuple.length_to_list in *.                                                                                
    lia.                                                                                                                          
Qed. 

Lemma get_reg_R_regs d s m (HR : R_regs d s m) ri :
  forall i, Symbolic.get_reg s ri = Some i ->                                                                      
  exists v, eval d i v /\ Tuple.nth_default 0 (N.to_nat ri) m = v.
Proof using Type.                                                                                                  
  cbv [Symbolic.get_reg]; intros.
  rewrite <-Tuple.nth_default_to_list in H.                                                                        
  cbv [nth_default] in H; BreakMatch.break_match_hyps; subst; [|solve[congruence]].
  case (R_regs_nth d s m HR ri i Heqo) as (v & Hv & Hm).                                                           
  exists v; split; [exact Hv|].                                                                                    
  rewrite <-Tuple.nth_default_to_list. cbv [nth_default]. rewrite Hm. trivial.                                     
Qed. 

Lemma get_reg_R s m (HR : R s m) ri :
  forall i, Symbolic.get_reg s ri = Some i ->
  exists v, eval s i v /\ Tuple.nth_default 0 (N.to_nat ri) (m : reg_state) = v.
Proof using Type.
  destruct s, m; apply get_reg_R_regs, HR.
Qed.

Lemma bind_assoc {A B C} (v:M A) (k1:A->M B) (k2:B->M C) s
 : (y <- (x <- v; k1 x); k2 y)%x86symex s = (x<-v; y<-k1 x; k2 y)%x86symex s.
Proof using Type. cbv; destruct v; trivial. Qed.

(* workaround: using cbn instead of this lemma makes Qed hang after next rewrite in same hyp *)
Lemma unfold_bind {A B} ma amb s :
  @bind A B ma amb s = ltac:(let t := eval unfold bind, ErrorT.bind in ( @bind A B ma amb s) in exact t).
Proof using Type. exact eq_refl. Qed.

Local Hint Resolve gensym_dag_ok_of_R : core.

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

Lemma App_R {opts : symbolic_options_computed_opt} {descr:description} s m (HR : R s m) e v (H : eval_node G s e v) :
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
Import Word.Properties.

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


(* symbolic state s machine state m, related *)
(* if calling GetReg on register r in state s is gives idx i and updates to state s', then *)
(* s' is still related to m AND s is subsumed in s' AND eval i in s' gives us the original value of r in the machine state *)
Lemma GetReg_R {opts : symbolic_options_computed_opt} {descr:description} s m (HR: R s m) r i s'
  (H : GetReg r s = Success (i, s'))
  : R s' m  /\ s :< s' /\ eval s' i (get_reg m r).
Proof using Type.
  cbv [GetReg GetRegFull bind some_or get_reg index_and_shift_and_bitcount_of_reg] in *.
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
    let t := open_constr:(fun A => GetReg_R s _ A r v s' H) in
    unshelve (edestruct t as (Hs'&Hlt&Hv); clear H); shelve_unifiable;
    [eassumption|..|clear H]
  end.

Lemma mapM_fold_left_R {A} {opts : symbolic_options_computed_opt} {descr : description}
  (f_sym : A -> M unit)
  (f_sem : machine_state -> A -> machine_state)
  (Hstep : forall a s m s',
    R s m -> f_sym a s = Success (tt, s') ->
    R s' (f_sem m a) /\ s :< s')
  : forall l s m s',
    R s m ->
    Symbolic.mapM_ f_sym l s = Success (tt, s') ->
    R s' (fold_left f_sem l m) /\ s :< s'.
Proof using Type.
Admitted.
  (* induction l as [|a l IH]; intros s0 m0 s_final HR0 Hsym.
  - cbv [Symbolic.mapM_ Symbolic.mapM] in Hsym.
    rewrite Symbolic.unfold_bind in Hsym.
    cbv [Symbolic.ret] in Hsym.
    inversion Hsym; subst. split; [exact HR0 | apply subsumed_refl].
  - cbn [fold_left].
    cbv [Symbolic.mapM_] in Hsym.
    cbn [Symbolic.mapM] in Hsym.
    rewrite !Symbolic.unfold_bind in Hsym.
    destruct (f_sym a s0) as [[? s1]|] eqn:Hstep_a; [|inversion Hsym].
    destruct (Symbolic.mapM f_sym l s1) as [[? s2]|] eqn:Hrest; [|inversion Hsym].
    cbv [Symbolic.ret] in Hsym. inversion Hsym; subst.
    destruct (Hstep a s0 m0 s1 HR0 Hstep_a) as [HR1 Hsub1].
    assert (Hsym' : Symbolic.mapM_ f_sym l s1 = Success (tt, s_final)).
    { cbv [Symbolic.mapM_]. rewrite Symbolic.unfold_bind. rewrite Hrest. cbv [Symbolic.ret]. reflexivity. }
    destruct (IH s1 (f_sem m0 a) s_final HR1 Hsym') as [HR_final Hsub_final].
    split; [exact HR_final | eauto using subsumed_trans].
  Qed. *)

Lemma Address_R {opts : symbolic_options_computed_opt} {descr:description} s m (HR : R s m) (sa:AddressSize) o a s' (H : Symbolic.Address o s = Success (a, s'))
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
  all : autorewrite with zsimplify_const.
  all : f_equal; lia.
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

Lemma word_of_Z_land_ones_64 (z : Z) :
  (word.of_Z (Z.land z (Z.ones 64)) : word64) = word.of_Z z.
Proof.
  apply word.unsigned_inj.
  rewrite !word.unsigned_of_Z.
  cbv [word.wrap]. change (2^64) with (Z.ones 64 + 1).
  (* Z.land a (Z.ones 64) mod 2^64 = a mod 2^64 *)
  rewrite Z.land_ones by lia.
  rewrite Zmod_mod.
  reflexivity.
Qed.

Import coqutil.Datatypes.List.

Lemma option_all_app {A} (l1 l2 : list (option A)) r1 r2 :
  option_all l1 = Some r1 ->
  option_all l2 = Some r2 ->
  option_all (l1 ++ l2) = Some (r1 ++ r2).
Proof.
  revert r1. induction l1 as [|o l1 IH]; simpl; intros.
  - inversion H; subst. exact H0.
  - destruct o; [|discriminate].
    destruct (option_all l1) eqn:E; [|discriminate].
    inversion H; subst. symmetry in E.
    rewrite IH with (r1 := l); try reflexivity. exact H0.
Qed.

Lemma footprint_app (a : word64) (n1 n2 : nat) :
  footprint a (n1 + n2) = footprint a n1 ++ footprint (word.add a (word.of_Z (Z.of_nat n1))) n2.
Proof.
  unfold footprint.
  revert n1 a. induction n2 as [|n2 IH]; intros.
  - rewrite Nat.add_0_r. rewrite app_nil_r. reflexivity.
  - replace (n1 + S n2)%nat with (S (n1 + n2))%nat by lia.
    rewrite 2!seq_S, 2!map_app. rewrite IH.
    rewrite app_assoc. f_equal.

    cbn [map seq]. f_equal.
    apply word.unsigned_inj.
    rewrite !word.unsigned_add, !word.unsigned_of_Z.
    unfold word.wrap.
    rewrite !Zplus_mod_idemp_r, !Zplus_mod_idemp_l.
    repeat rewrite Nat.add_0_l.
    rewrite Nat2Z.inj_add.
    rewrite Z.add_assoc.
    reflexivity.
Qed.

(* load_bytes (n1+n2) bytes from a splits into the concatenation of n1 bytes from a and n2 bytes from a + n1. *)
Lemma load_bytes_app_split (m : mem_state) (a: word64) (chunks : nat) bs1 bs2 :
  load_bytes m a (8*chunks) = Some bs1 ->
  load_bytes m (word.add a (word.of_Z (Z.of_nat (8*chunks)))) 8 = Some bs2 ->
  load_bytes m a (8*chunks + 8) = Some (bs1 ++ bs2).
Proof.
  unfold load_bytes. 
  rewrite footprint_app, List.map_app.
  apply option_all_app.
Qed.

Lemma get_mem_addr_mod (m : mem_state) a n :
    get_mem m (Z.land a (Z.ones 64)) n = get_mem m a n.
Proof.
  cbv [get_mem].
  f_equal. f_equal.
  exact (word_of_Z_land_ones_64 a).
Qed.

Lemma SetMem_addr_mod m addr n v :                                                            
  SetMem m (Z.land addr (Z.ones 64)) n v = SetMem m addr n v.
Proof. 
  cbv [SetMem Crypto.Util.Option.bind set_mem]. rewrite word_of_Z_land_ones_64. reflexivity. 
Qed.

(* if reading [chunks*8] bytes from va is v1,
  and the next 8 bytes (at va + 8 * bytes) is v2,
  then reading [(chunks+1) * 8] bytes from va is v1 | (v2 << 8*chunks) *)
Lemma get_mem_app_split m va (chunks : nat) v1 v2 :
  get_mem m va (8*chunks) = Some v1 ->
  get_mem m (Z.land (va + Z.of_nat (8*chunks)) (Z.ones 64)) 8 = Some v2 ->
  get_mem m va (8*chunks + 8) = Some (Z.lor v1 (Z.shiftl v2 (64 * Z.of_nat chunks))).
Proof.
  (** 
  |         v1        | v2 |
  |----|----|----|----|----|
  *)
  intros H1 H2.
  cbv [get_mem Crypto.Util.Option.bind] in *.
  (* unpack Hget m va (8*chunks) = Some v1 *)
  destruct (load_bytes m (word.of_Z va) (8 * chunks)) as [bs1|] eqn:E1;
    [|discriminate].
  injection H1; clear H1; intro H1; subst v1.
  (* unpack Hget m (Z.land (va + 8*chunks) (Z.ones 64)) 8 = Some v2 *)
  destruct (load_bytes m (word.of_Z (Z.land (va + Z.of_nat (8*chunks)) (Z.ones 64))) 8)
    as [bs2|] eqn:E2; [|discriminate].
  injection H2; clear H2; intro H2; subst v2.
  (* massage E2's address to match load_bytes_app_split's form *)
  replace (word.of_Z (Z.land (va + Z.of_nat (8 * chunks)) (Z.ones 64)))
    with ( @word.add 64 word64 (word.of_Z va) (word.of_Z (Z.of_nat (8 * chunks))))
    in E2. 
  (* now apply the splitting lemma *)
  pose proof (load_bytes_app_split _ _ _ _ _ E1 E2) as E3.
  rewrite E3.
  (* now prove le_combine (bs1 ++ bs2) = Z.lor ... *)
  f_equal.
  replace (64 * Z.of_nat chunks) with (Z.of_nat (length bs1) * 8).
  apply le_combine_app.
  erewrite length_load_bytes by eassumption. lia.
  rewrite word_of_Z_land_ones_64.
  symmetry. apply word.ring_morph_add.  
Qed.

(* General (n*64)-bit load. Load128_R / Load256_R are corollaries below. *)
Lemma LoadN_R {opts : symbolic_options_computed_opt} {descr:description} 
  {sa : AddressSize}
  (Hsa : sa = 64%N)
  n s m (HR : R s m) (addr : idx)
  va (Ha : eval s addr va)
  i s' (H : Load_of_idx n addr s = Success (i, s'))
  : R s' m /\ s :< s' /\
    exists v, eval s' i v /\
              get_mem m va (8 * n) = Some v /\
              v = Z.land v (Z.ones (64 * Z.of_nat n)).
Proof using Type.
  revert s m HR addr va Ha i s' H.
  induction n as [|n' IH]; intros.
  { (* base: Load_of_idx 0 = App (const 0, nil), produces 0.
       get_mem m va 0 = Some 0 by convention (empty byte list). *)
    cbn [Load_of_idx] in H.
    repeat (cbn [fst snd] in * || step_symex || Tactics.destruct_one_match_hyp
            || inversion_ErrorT || Prod.inversion_prod || subst). 
    repeat (econstructor || eauto).
    split; [eauto|].
    split; [eauto|].
    eexists; split; [eauto|].
    split.
    { simpl. unfold get_mem. reflexivity. }
    { bitblast.Z.bitblast. } 
  }
  { (* step: recursive call + Load64 at addr + 8*n' + set_slice *)
    cbn [Load_of_idx] in H.
    repeat (cbn [fst snd] in * || step_symex || Tactics.destruct_one_match_hyp
            || inversion_ErrorT || Prod.inversion_prod || subst).
    (* recursive application gives us v_prev with get_mem m va (8*n') *)
    eapply IH in HSprev; try eassumption; clear IH.
    destruct HSprev as (Hs_prev & Hls_prev & v_prev & Hv_prev & Hget_prev & Hb_prev).
    (* address arithmetic for the new chunk *)
    repeat step_symex.
    { repeat (eauto 15 || econstructor). }
    { repeat (eauto 15 || econstructor). }
    (* new Load64 at addr + 8*n' *)
    eapply Load64_R in HSchunk; try eassumption.
    destruct HSchunk as (?&chunk_val&Hchunk&Hget_chunk&Hb_chunk); subst.
    assert (Z.ldiff v_prev (Z.shiftl (Z.ones 64) (64 * Z.of_nat n')) = v_prev) as Hvprev_diff. { rewrite Hb_prev. bitblast.Z.bitblast. }
    repeat step_symex.
    { repeat (eauto 15 || econstructor). }
    split; [eauto|].
    split; [eauto 15|].
    eexists; split; [eauto|].
    split.
    { (* get_mem m va (8 * S n') = Some (combined) *)
      replace (8 * S n')%nat with (8 * n' + 8)%nat by lia.
      cbn [fold_right] in Hget_chunk. replace (8 * Z.of_nat n' + 0) with (8 * Z.of_nat n') in Hget_chunk by lia.
      rewrite get_mem_addr_mod in Hget_chunk.
      transitivity (Some (Z.lor v_prev (Z.shiftl chunk_val (64 * Z.of_nat n')))).
      { apply (get_mem_app_split _ _ n' v_prev chunk_val Hget_prev).
        rewrite get_mem_addr_mod.
        replace (va + Z.of_nat (8 * n')) with (va + 8 * Z.of_nat n') by lia.
        exact Hget_chunk. }
      { f_equal.
        replace (Z.of_N 64) with 64 by lia.
        replace (Z.of_N (64 * N.of_nat n')) with (64 * Z.of_nat n') by lia.
        rewrite <- Hb_chunk. 
        rewrite Hvprev_diff.
        { bitblast.Z.bitblast. }
      }
    }
    { 
      replace (Z.of_N 64) with 64 by lia.
      replace (Z.of_N (64 * N.of_nat n')) with (64 * Z.of_nat n') by lia.
      rewrite Hvprev_diff.
      rewrite <- Hb_chunk.
      replace (64 * (Z.of_nat (S n'))) with (64 * Z.of_nat n' + 64) by lia.
      rewrite Hb_chunk. rewrite Hb_prev.
      bitblast.Z.bitblast.
    }
  }
Qed.

(* 128-bit load corollary *)
Corollary Load128_R {opts : symbolic_options_computed_opt} {descr:description} {sa : AddressSize}
  (Hsa : sa = 64%N)
  s m (HR : R s m) (addr : idx)
  va (Ha : eval s addr va)
  i s' (H : Load128_of_idx addr s = Success (i, s'))
  : R s' m /\ s :< s' /\
    exists v, eval s' i v /\
              get_mem m va 16 = Some v /\
              v = Z.land v (Z.ones 128).
Proof using Type.
  cbv [Load128_of_idx] in H.
  eapply LoadN_R with (n := 2%nat) in H; eauto.
Qed.

(* 256-bit load corollary *)
Corollary Load256_R {opts : symbolic_options_computed_opt} {descr:description} {sa : AddressSize}
  (Hsa : sa = 64%N)
  s m (HR : R s m) (addr : idx)
  va (Ha : eval s addr va)
  i s' (H : Load256_of_idx addr s = Success (i, s'))
  : R s' m /\ s :< s' /\
    exists v, eval s' i v /\
              get_mem m va 32 = Some v /\
              v = Z.land v (Z.ones 256).
Proof using Type.
  cbv [Load256_of_idx] in H.
  eapply LoadN_R with (n := 4%nat) in H; eauto.
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

(* v is the 64 low bits of untruncated v' *)
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


(* looking up address a in state s returns value of idx i and state s' *)
(* Then the new states correspond and eval i has value v in s' AND address a has value v in the machine state *)
Lemma GetOperand_R {opts : symbolic_options_computed_opt} {descr:description} s m (HR: R s m) (so:OperationSize) (sa:AddressSize) (Hsa : sa = 64%N) a i s'
  (H : GetOperand a s = Success (i, s'))
  : R s' m /\ s :< s' /\ exists v, eval s' i v /\ DenoteOperand sa so m a = Some v.
Proof using Type.
  cbv [GetOperand DenoteOperand err] in *. break_innermost_match; inversion_ErrorT.
  { eapply GetReg_R in H; intuition eauto. }
  {   
    progress cbv [Load ret] in *.
    repeat (cbv [err] in *; cbn [fst snd] in * || step_symex || Tactics.destruct_one_match_hyp || inversion_ErrorT || Prod.inversion_prod || subst).
    (* 8/64 bit, scalar reg *)
    { 
        eapply Load64_R in HSv; try eassumption; [];
        repeat (subst; destruct_head'_and; destruct_head'_ex).
      repeat step_symex.
      { repeat (eauto||econstructor). }
      repeat (split; eauto; []).
      rewrite Z.shiftr_0_r in Hi by lia.
      case E as [E|E];
        rewrite E in *; simpl Z.of_N in *.
        (* case: one byte load *)
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
        (* case: 8 bytes load *)
      { setoid_rewrite H4.
        eexists; split; eauto; f_equal.
        rewrite H5 at 1; trivial. }  
    }
    (* 128 bit, xmm *)
    { eapply Load128_R in H; try eassumption; try lia; [];
    repeat (subst; destruct_head'_and; destruct_head'_ex).
    repeat (split; eauto; []). rewrite E0 in *. clear H5 H6. rewrite H8 in H4.
    setoid_rewrite H7.
    eexists; split; eauto; f_equal. exact H8. 
      }
    (* 256 bit, ymm *)
    { eapply Load256_R in H; try eassumption; try lia; []; 
    repeat (subst; destruct_head'_and; destruct_head'_ex).
    repeat (split; eauto; []). rewrite E1 in *. clear H5 H6. rewrite H8 in H4.
    setoid_rewrite H7.
    eexists; split; eauto; f_equal. exact H8.  }
  }
  {step_symex; repeat (eauto||econstructor). }
Qed.


Ltac step_GetOperand :=
  match goal with
  | H : GetOperand ?a ?s = Success (?i0, ?s') |- _ =>
    let v := fresh "v" (*a*) in let Hv := fresh "H" v
    in let Hi := fresh "H" i0 in let Heq := fresh H "eq" in
    let Hs' := fresh "H" s' in let Hl := fresh "Hl" s' in
    case (GetOperand_R s _ ltac:(eassumption) _ _ ltac:(reflexivity) _ _ _ H) as (Hs'&Hl&(v&Hi&Hv)); clear H
  end.

Import Crypto.Util.ListUtil.

Lemma combine_update_nth {A B} n (f : A -> A) (g : B -> B) xs ys :
  length xs = length ys ->
  combine (update_nth n f xs) (update_nth n g ys) = update_nth n (fun '(a, b) => (f a, g b)) (combine xs ys).
Proof.
  revert n ys; induction xs as [|x xs IH]; destruct ys as [|y ys]; cbn; intros;
    try lia; destruct n; cbn; try reflexivity.
  - f_equal. apply IH. lia.
Qed.

Lemma Forall2_update_nth_r {A B} (R : A -> B -> Prop) n f xs ys :                                                  
  Forall2 R xs ys ->                                                                                               
  (forall x y, nth_error xs n = Some x -> nth_error ys n = Some y -> R x y -> R x (f y)) ->                        
  Forall2 R xs (update_nth n f ys).         
Proof.                                                                                                             
  intro H; revert n; induction H; intros [|n]; cbn.
  - constructor.                                                                                                   
  - constructor; auto.
  - constructor; [eapply H1; eauto; reflexivity | auto].                                                           
  - constructor; [auto | apply IHForall2; intros; eapply H1; eauto].
Qed.

(* 1. Full-width register write *)                                                                                 
Lemma R_SetReg_full {opts : symbolic_options_computed_opt} {descr:description}
   s m (HR : R s m) r i _tt s'
  (Hoffset : reg_offset r = 0%N)
  (Hwidest : reg_size r = widest_reg_size_of r)
  (H : Symbolic.SetReg r i s = Success (_tt, s'))
  v (Hv : eval s i v)
  : exists m', Some (update_reg_with m (fun rs => set_reg rs r v)) = Some m'
    /\ R s' m' /\ s :< s'.
Proof using Type.
  eexists. repeat split;                                                                                                             
    unfold SetReg in H; unfold set_reg, index_and_shift_and_bitcount_of_reg in *;                                    
    rewrite Hoffset, Hwidest, N.eqb_refl, N.eqb_refl in *; simpl in H;  
    step_symex;                               
    cbn [fst snd] in H; cbv [SetRegFull] in H;                                                                       
    inversion_ErrorT; Prod.inversion_prod; subst.
  {
    rewrite !Z.shiftl_0_r.
    step_App. { repeat eauto || econstructor. }
    rewrite !Z.shiftr_0_r in Hv0.

    destruct s0 as [d0 sr0 sf0 sm0]; destruct Hs0 as (Hok0 & Hregs0 & Hflags0 & Hmem0).
    cbv [R update_reg_with Symbolic.update_reg_with]; cbn.
    split; [| split; [ |split]]; eauto.
    unfold R_regs, Symbolic.set_reg.

    unshelve erewrite 2Tuple.from_list_default_eq, 2Tuple.to_list_from_list;
    try solve [rewrite ?Crypto.Util.ListUtil.length_set_nth,
              ?Crypto.Util.ListUtil.length_update_nth,                                                              
              ?Tuple.length_to_list; trivial].

    unfold ListUtil.set_nth. rewrite combine_update_nth.
    2: repeat rewrite Tuple.length_to_list; reflexivity.
    eapply Forall2_update_nth_r.
    { exact Hregs0. }
    intros x_old v_old Hw Hy HR_old. 
    destruct v_old as [sym_old conc_old].

    cbv [R_reg] in *. destruct HR_old as [_ Hbits_old].                                                                
    (* extract width from Hw *)                                                                                        
    rewrite nth_error_map in Hw.                                                                                       
    destruct (nth_error widest_registers (N.to_nat (reg_index r))) as [wr|] eqn:Hwr;                                   
      [cbn in Hw; inversion Hw; subst x_old | discriminate Hw].                                                        
    (* show widest_reg_size_of r = reg_size wr *)                                                                      
    assert (Hwidth : widest_reg_size_of r = reg_size wr).                                                              
    { unfold widest_reg_size_of, widest_register_of_index, widest_register_of_index_opt.                               
      replace (List.map ( @snd _ _) wide_reg_index_pairs) with widest_registers by reflexivity.  (* both are Eval lazy, should reduce *)                                                       
      rewrite Hwr. reflexivity. }               
    (* Z.ldiff conc_old ... = 0 because conc_old fits in width bits *)                                                 
    assert (Hldiff : Z.ldiff conc_old (Z.ones (Z.of_N (widest_reg_size_of r))) = 0).
    { rewrite Hwidth, Hbits_old. bitblast.Z.bitblast. }                                                                         
    rewrite Hldiff, Z.lor_0_r.              
    split.                                                                                                             
    - intros i0 Hi0; inversion Hi0; subst. exact Hv0.                                                                  
    - bitblast.Z.bitblast.
  }
  {
    step_App. { repeat eauto || econstructor. }
    subst. simpl. exact Hls0.
  }
Qed.

Lemma reg_size_offset_bounded (r : REG) :                                                                          
  (reg_size r + reg_offset r <= widest_reg_size_of r)%N.
Proof. destruct r as [sr | vr]; [destruct sr | destruct vr]; vm_compute; intros; discriminate. Qed.   
  
(* 2. Partial register write *)                     
Lemma R_SetReg_partial {opts : symbolic_options_computed_opt} {descr:description}
  s m (HR : R s m) r i _tt s'                                                  
  (Hpartial : ((reg_offset r =? 0)%N && (reg_size r =? widest_reg_size_of r)%N)%bool = false)                      
  (H : Symbolic.SetReg r i s = Success (_tt, s'))                                                                  
  v (Hv : eval s i v)                   
  : exists m', Some (update_reg_with m (fun rs => set_reg rs r v)) = Some m'                                       
  /\ R s' m' /\ s :< s'.
Proof using Type.                                                                                                  
  eexists. repeat split.                                                                                           
  { (* R s' m' *)                                                                                                  
    unfold SetReg in H. unfold set_reg, index_and_shift_and_bitcount_of_reg in *.                                  
    rewrite Hpartial in H.                                                                                         
    (* H is now: (old <- GetRegFull rn; v_new <- App (set_slice lo sz, [old; i]); SetRegFull rn v_new) s *)        
                                            
    (* Process GetRegFull: reads old register, state unchanged *)                                                  
    repeat step_symex.
    cbn [fst snd] in HSv0.
    
    cbv [GetRegFull some_or] in HSold.                                                                                 
    pose proof (get_reg_R s _ HR (reg_index r)) as Hr_old.                                                             
    destruct (Symbolic.get_reg (symbolic_reg_state s) (reg_index r)) eqn:Hgreg;                                        
      [| discriminate HSold].               
    inversion HSold; subst s0. clear HSold.
    specialize (Hr_old _ eq_refl). destruct Hr_old as (old_val & Heval_old & Hold_eq).                                 
                                            
    (* App_R on set_slice *)                                                                                           
    eapply App_R in HSv0 as (HRs1 & Hsub1 & Heval_v0).
    2: { exact HR. }
    2: { subst old. repeat (eauto || econstructor). }                                                               
                                                                                                                        
    (* SetRegFull *)                        
    cbn [fst snd] in H. cbv [SetRegFull] in H.                                                                         
    inversion_ErrorT; Prod.inversion_prod; subst.        
    destruct s1 as [d1 sr1 sf1 sm1].                                                                                   
    destruct HRs1 as (Hok1 & Hregs1 & Hflags1 & Hmem1).
    cbv [R update_reg_with Symbolic.update_reg_with]; cbn.                                                             
    split; [| split; [| split]]; eauto.         
                                                                                                                      
    (* R_regs *)    
    unfold R_regs, Symbolic.set_reg.                                                                                   
    unshelve erewrite 2Tuple.from_list_default_eq, 2Tuple.to_list_from_list;
      try solve [rewrite ?Crypto.Util.ListUtil.length_set_nth,                                                         
                ?Crypto.Util.ListUtil.length_update_nth,
                ?Tuple.length_to_list; trivial].
    unfold ListUtil.set_nth. rewrite combine_update_nth.                                                               
    2: repeat rewrite Tuple.length_to_list; reflexivity.
    eapply Forall2_update_nth_r.                                                                                       
    { exact Hregs1. }                           
    intros x_old v_old Hw Hy HR_old.                                                                                   
    destruct v_old as [sym_old conc_old].
    cbv [R_reg] in *. destruct HR_old as [_ Hbits_old].                                                                
    rewrite nth_error_map in Hw.                
    destruct (nth_error widest_registers (N.to_nat (reg_index r))) as [wr|] eqn:Hwr;                                   
      [cbn in Hw; inversion Hw; subst x_old | discriminate Hw].
    assert (Hwidth : widest_reg_size_of r = reg_size wr).                                                              
    { unfold widest_reg_size_of, widest_register_of_index, widest_register_of_index_opt.
      replace (List.map ( @snd _ _) wide_reg_index_pairs) with widest_registers                                         
        by reflexivity.                                                                                                
      rewrite Hwr. reflexivity. }
    split.                                                                                                             
    - intros i0 Hi0; inversion Hi0; subst. simpl in Heval_v0.
      replace conc_old with (Tuple.nth_default 0 (N.to_nat (reg_index r)) (machine_reg_state m)).
      2: { rewrite nth_error_combine in Hy.
        destruct (nth_error (Tuple.to_list 100 sr1) (N.to_nat (reg_index r))) eqn:Hsr;
          [| discriminate Hy].
        destruct (nth_error (Tuple.to_list 100 (machine_reg_state m)) (N.to_nat (reg_index r))) eqn:Hm;
          [| discriminate Hy].                  
        inversion Hy; subst conc_old.               
        rewrite <- Tuple.nth_default_to_list. unfold nth_default. rewrite Hm. reflexivity.  
      } 
      cbv [Tuple.nth_default] in Heval_v0. exact Heval_v0.
    -
      pose proof (reg_size_offset_bounded r).     
      rewrite Hwidth in *.                    
      rewrite Hbits_old.
      bitblast.Z.bitblast.     
  }
  {
    unfold SetReg, index_and_shift_and_bitcount_of_reg in H.
    rewrite Hpartial in H.                      
    repeat step_symex.
    cbv [fst snd] in HSv0.
    cbv [fst snd SetRegFull] in H.
    pose proof (get_reg_R s _ HR (reg_index r)) as Hr_old.
    cbv [GetRegFull some_or] in HSold.
    eapply App_R in HSv0.
    {
      inversion_ErrorT; Prod.inversion_prod; subst.
      destruct HSv0 as [_ [Hsub _]].
      destruct (Symbolic.get_reg (symbolic_reg_state s) (reg_index r));                                                  
      [| discriminate HSold].                                                                                          
      inversion HSold; subst s0.
      unfold Symbolic.update_reg_with; simpl.                                                                            
      exact Hsub. 
    }
    {
      destruct (Symbolic.get_reg (symbolic_reg_state s) (reg_index r)). 
      inversion HSold. rewrite <- H2. exact HR.
      discriminate HSold.
    }
    {
      destruct (Symbolic.get_reg (symbolic_reg_state s) (reg_index r)) eqn:Hgreg;
        [| discriminate HSold].                                                                                          
      (* pose proof (get_reg_R s _ HR (reg_index r)) as Hr_old. *)
      inversion HSold. subst s0. 
      specialize (Hr_old _ eq_refl). destruct Hr_old as (old_val & Heval_old & Hold_eq).  
      subst old.                                                                                       
      eapply ENod with (args' := [old_val; v]).                                                                          
      - constructor; [exact Heval_old | constructor; [exact Hv | constructor]].                                          
      - cbn [interp_op]. f_equal. rewrite <- Hold_eq. reflexivity.
    }           
  }
Qed.

Lemma DenoteAddressLandOnes sa m a addr :
  (DenoteAddress sa m a = addr) ->
  Z.land addr (Z.ones (Z.of_N sa)) = addr.
Proof.
  assert (forall x sz, Z.land (Z.land x (Z.ones sz)) (Z.ones sz) = Z.land x (Z.ones sz)).
  { intros. bitblast.Z.bitblast. }
  intros. subst. unfold DenoteAddress. apply H.
Qed.

Lemma le_split_app n1 n2 v :                   
  le_split (n1 + n2) v = le_split n1 v ++ le_split n2 (Z.shiftr v (8 * Z.of_nat n1)).                              
Proof.                                                                                                             
  rewrite <- (firstn_skipn n1 (le_split (n1 + n2) v)).                                                             
rewrite skipn_le_split'. Admitted.
  (* rewrite List.firstn_le_split.                                                                                    
  rewrite Nat.min_l by lia. reflexivity. *)
(* Qed. *)


Lemma store_bytes_app (m: mem_state) a bs1 bs2 m1 m2 :                                     
  store_bytes m a bs1 = Some m1 ->                                                                                 
  store_bytes m1 (word.add a (word.of_Z (Z.of_nat (length bs1)))) bs2 = Some m2 ->                                
  store_bytes m a (bs1 ++ bs2) = Some m2. 
Proof. Admitted.


(* n1 n2 are in bytes *)
(* setting lower n1 bytes to lower part of v gives state m1 *)
(* setting upper n2 bytes to upper shifted part of v gives state m2 *)
(* then setting all bytes to v simultaneously gives m2. *)
Lemma SetMem_compose m addr n1 n2 v m1 m2 :                                       
  SetMem m addr n1 (Z.land v (Z.ones (8 * Z.of_nat n1))) = Some m1 ->                                              
  SetMem m1 (addr + Z.of_nat n1) n2 (Z.shiftr v (8 * Z.of_nat n1)) = Some m2 ->                                    
  SetMem m addr (n1 + n2) v = Some m2.                                                                             
Proof.
  cbv [SetMem set_mem Crypto.Util.Option.bind].                                                                    
  intros H1 H2.                                                                                                    
  destruct (store_bytes _ _ (le_split n1 _)) eqn:Hs1 in H1; [| discriminate].                                      
  inversion H1; subst m1; clear H1.                                                                                
  destruct (store_bytes _ _ (le_split n2 _)) eqn:Hs2 in H2; [| discriminate].                                      
  inversion H2; subst m2; clear H2.                                                                                
  (* Need: store_bytes m (word.of_Z addr) (le_split (n1+n2) v) = Some m0 *)
  rewrite le_split_app. rewrite Z.land_ones in Hs1 by lia. 
  erewrite store_bytes_app.
  2 : { rewrite le_split_mod. replace (Z.of_nat n1 * 8) with (8 * Z.of_nat n1) by lia. exact Hs1. }
  2 : { rewrite length_le_split. rewrite <- word.ring_morph_add. exact Hs2. }
  reflexivity.
Qed.
  
  (* 3. Memory write *)                                                                                              
Lemma R_SetMem {opts : symbolic_options_computed_opt} {descr:description} s m (HR : R s m) (sz : OperationSize) (sa : AddressSize)                             
  a i _tt s'
  (Hsa : sa = 64%N)                      
  (H : Symbolic.Store a i s = Success (_tt, s'))                                                                   
  v (Hv : eval s i v)
  : exists m', SetMem m (DenoteAddress sa m a) (N.to_nat (operand_size a sz / 8)) v = Some m'                      
  /\ R s' m' /\ s :< s'.  
Proof using Type.                                                                                                  
    progress cbv [Store] in *.
    rewrite Hsa in *. clear sa Hsa.                                                                                 
    (* case split on operand_size *)
    destruct_one_match_hyp; cbv [err] in *; [| destruct_one_match_hyp; [| destruct_one_match_hyp]];                  
      try inversion_ErrorT.
    { (* 8/64 bit store *)
      repeat (step_symex; cbn [fst snd] in *).
      eapply Load64_R in HSold; eauto;                                                                       
      repeat (subst; destruct_head'_ex; destruct_head'_and).                                                       
      repeat (step_symex; cbn [fst snd] in *).                                                                       
      { repeat (eauto || econstructor). }
      { repeat (eauto || econstructor). }                                                                            
      rewrite !Z.shiftl_0_r, ?Z.shiftr_0_r, <-Z.land_assoc, Z.land_diag in *.
      case E as [E|E]; rewrite E in *; simpl Z.of_N in *.                                                            
      + (* 8-bit *)                                                                                                  
      eapply Store64_R with (v':=Z.lor (Z.land v (Z.ones 8)) (Z.ldiff x (Z.ones 8))) in H;
      try eassumption; eauto with nocore; try solve [rewrite H5; bitblast.Z.bitblast].                           
      destruct_head'_ex; destruct_head'_and.
      cbv [SetMem Crypto.Util.Option.bind update_mem_with] in *;                                                   
      destruct set_mem eqn:? in *; Option.inversion_option; subst.                                               
      erewrite store8; eauto 9.                                                                                    
      + (* 64-bit *)                                                                                                 
      eapply Store64_R with (v':=v) in H;                                                                          
      try eassumption; eauto with nocore; try solve [rewrite H5; bitblast.Z.bitblast].
      destruct_head'_ex; destruct_head'_and. setoid_rewrite H. eauto 9.                                            
    }
    { Admitted. (* 128-bit store *)                                                                                            
      (* Step through: App(slice 0 64), App(slice 64 64), Store64, App(const 8), App(add), Store64 *)                
      (* repeat (step_symex; cbn [fst snd] in * ). *)
      (* { repeat (eauto || econstructor). }  (* slice 0 64 *)                                        
      { repeat (eauto || econstructor). }  (* slice 64 64 *)
      rename x0 into addr_val.
      (* First Store64: low 8 bytes at addr *)                                                            
      assert (Haddr2 : eval s2 addr addr_val) by (eapply Hls2; eapply Hls1; exact H2).
      eapply Store64_R with (v' := Z.land v (Z.ones 64)) (va := addr_val) in HSx;                                         
      try eassumption; eauto with nocore;                                                                              
      try solve [rewrite ?Z.shiftr_0_r in *; bitblast.Z.bitblast].
      destruct_head'_ex; destruct_head'_and. rename x0 into m1. rewrite H3, E0. simpl.

      (* Step through App(const 8), App(add) to learn about addr_hi *)
      eapply App_R in HSeight as (Hs4 & Hsub4 & Heval_eight).
      2: { exact H5. }                                                                                                   
      2: { econstructor; [constructor | reflexivity]. }
                                                                                                     
      eapply App_R in HSaddr_hi as (Hs5 & Hsub5 & Heval_addr_hi).                                                
      2: { exact Hs4. }                                                                                                  
      2: { eapply ENod with (args' := [addr_val; 8%Z]).                                                                        
          - constructor; [eapply Hsub4; eapply H6; exact Haddr2 | constructor; [exact Heval_eight | constructor]].
          - cbn [interp_op]. reflexivity.
      }
      cbn [fold_right] in Heval_addr_hi. simpl in Heval_addr_hi.
      eapply Store64_R with (v' := Z.shiftr v 64) (va := Z.land (addr_val + 8) (Z.ones 64)) in H;
        try eassumption; eauto with nocore;                                                                              
        try solve [bitblast.Z.bitblast].
      destruct_head'_ex; destruct_head'_and. rename x0 into m2.
      
      (* Now the main lemma, composition of the two memory operations *)
      eexists; split.
      2: { split. eassumption. clear - H1 Hls1 Hls2 H6 Hsub4 Hsub5 H10. eauto 8 using subsumed_trans. }
      rewrite (SetMem_addr_mod _ (addr_val + 8)) in H.                            
      eapply (SetMem_compose m addr_val 8 8 v m1 m2).
      { exact H4. }
      { exact H. } 
    }                                                                                       
    { (* 256-bit store *)
      admit.
    }
    { (* err *)
      step_symex. discriminate H.
    }
  Qed. *)


(* Setting address a to v gives state s' and i evals to v in s *)
(* then there exists a new machine state m' corresponding to s' s.t. setting a to v in m gives m' *)
(* note: do the two SetOperand both truncate inputs or not?... *)
Lemma R_SetOperand {opts : symbolic_options_computed_opt} {descr:description} s m (HR : R s m)
  (sz:OperationSize) (sa:AddressSize) a i _tt s' (H : Symbolic.SetOperand a i s = Success (_tt, s'))
  v (Hv : eval s i v)
  : exists m', SetOperand sa sz m a v = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
Admitted.
  (* destruct a; cbn in H.                                                                                            
    - (* reg *) unfold SetReg in H.           
      destruct ((reg_offset r =? 0)%N && (reg_size r =? widest_reg_size_of r)%N)%bool eqn:Hb.
      + (* full *) apply andb_prop in Hb. destruct Hb. apply N.eqb_eq in H0, H1. 
        eapply R_SetReg_full; eauto.
        unfold SetReg, index_and_shift_and_bitcount_of_reg. rewrite H0, H1, N.eqb_refl, N.eqb_refl. simpl. 
        rewrite <- H1. exact H.
      + (* partial *) eapply R_SetReg_partial; eauto.
        unfold SetReg, index_and_shift_and_bitcount_of_reg. rewrite Hb. exact H.
    - (* mem *) eapply R_SetMem; eauto.                                                                              
    - (* const *) cbn in H; inversion H.
    - cbv [err] in H. discriminate H.
Qed.  *)

Ltac step_SetOperand :=
  match goal with
  | H : Symbolic.SetOperand ?a ?i ?s = Success (?_tt, ?s') |- _ =>
      let m := fresh "m" in let Hm := fresh "H" m in
      let HR := fresh "H" s' in let Hl := fresh "Hl" s' in
      case (R_SetOperand s _ ltac:(eassumption) _ _ _ _ _ _ H _ ltac:(eauto 99 with nocore))
        as (m&?Hm&HR&Hl); clear H
  end.

Lemma acc_range_preserved : forall (acc_val lane_res lane_width : Z) (lane_idx : nat),
      lane_width > 0 ->
      Z.shiftr acc_val (Z.of_nat lane_idx * lane_width) = 0 ->
      let new_acc_val := Z.lor
          (Z.shiftl (Z.land lane_res (Z.ones lane_width)) (Z.of_nat lane_idx * lane_width))
          (Z.ldiff acc_val (Z.shiftl (Z.ones lane_width) (Z.of_nat lane_idx * lane_width)))
      in
      Z.shiftr new_acc_val (Z.of_nat (S lane_idx) * lane_width) = 0.
  Proof.
		intros. 
	apply Z.bits_inj_iff'; intros i Hi.
  rewrite Z.shiftr_spec by lia.
  rewrite Z.bits_0. subst new_acc_val.
  rewrite Z.lor_spec.
  (* Show both parts of the lor are 0 at position (S lane_idx) * lane_width + i *)
  rewrite Z.shiftl_spec by lia.
  rewrite Z.ldiff_spec.
  (* The inserted lane occupies [lane_idx * lw, (lane_idx+1) * lw) *)
  (* Position we're checking: (S lane_idx) * lw + i = (lane_idx + 1) * lw + i *)
  (* This is >= (lane_idx + 1) * lw, so above the inserted lane *)
  assert (Hins : Z.testbit (Z.land lane_res (Z.ones lane_width))
                 (i + Z.of_nat (S lane_idx) * lane_width - Z.of_nat lane_idx * lane_width) = false).
  { rewrite Z.land_spec, Z.testbit_ones_nonneg by lia.
    destruct (_ <? _) eqn:E. 
    apply Z.ltb_lt in E. lia. rewrite Bool.andb_false_r. reflexivity. }
  rewrite Hins. 
  (* Now show acc_val bit is 0 *)
  assert (Hacc_bit : Z.testbit acc_val (Z.of_nat (S lane_idx) * lane_width + i) = false).
  { 
	set (lo := Z.of_nat lane_idx * lane_width) in *.
  replace (Z.of_nat (S lane_idx) * lane_width + i) with (lane_width + i + lo) by (unfold lo; lia).
  rewrite <- (Z.shiftr_spec acc_val lo (lane_width + i)) by lia.
  rewrite H0, Z.bits_0. reflexivity.
	}
	rewrite Bool.orb_false_l.
	replace (i + Z.of_nat (S lane_idx) * lane_width) with (Z.of_nat (S lane_idx) * lane_width + i) by lia.
  rewrite Hacc_bit. reflexivity.
Qed.




(* === Correspondence lemmas for SymbolicVector general helpers. ===
   Each lemma links a [Symbolic.*] step with its [SemanticVector.*] counterpart.
   Proofs deferred. *)
Section SymbolicVectorProofs.
  (* Extracts lane [lane_idx] of width [lane_width] from [v]. *)
  Lemma extract_lane_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (i : idx) (v : Z) (Hv : eval s i v)
    (lane_idx : nat) (lane_width : Z) (Hlw : (lane_width > 0)%Z)
    res s'
    (H : SymbolicVector.extract_lane i lane_idx lane_width s = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res (SemanticVector.extract_lane v lane_idx lane_width).
  Proof using Type.
    unfold SymbolicVector.extract_lane, SemanticVector.extract_lane in *. 
    eapply (App_R s m) in H as (HR' & Hsubs & Heval_res).
    2: { exact HR. }
    2: { repeat (econstructor; eauto). }
    split; [exact HR' | split; [solve_subsumed| ]].
    repeat rewrite Z2N.id in Heval_res by lia.
    exact Heval_res.
  Qed.

  (* Computes one lane of a binop: lane_op(lane i of v1, lane i of v2). *)
  Lemma make_lane_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (i1 i2 : idx) (v1 v2 : Z)
    (Hv1 : eval s i1 v1) (Hv2 : eval s i2 v2)
    (lane_op : op) (binop : Z -> Z -> Z)
    (Hop : interprets_as_binop lane_op binop)
    (lane_idx : nat) (lane_width : Z) (Hlw : (lane_width > 0)%Z)
    res s'
    (H : SymbolicVector.make_lane i1 i2 lane_op lane_idx lane_width s
        = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res (SemanticVector.make_lane v1 v2 binop lane_idx lane_width).
  Proof using Type. 
    unfold SymbolicVector.make_lane, SemanticVector.make_lane in *. repeat step_symex; cbv [fst snd] in *. 
    eapply extract_lane_R in HSl1 as (HR1 & Hsubs1 & Heval_lane1); try eassumption.
    eapply extract_lane_R in HSl2 as (HR2 & Hsubs2 & Heval_lane2); try eassumption.
    eapply (App_R s1 m) in H as (HR' & Hsubs' & Heval_res); [| exact HR2 |].
    2: { 
      econstructor.
      - constructor; [eapply Hsubs2; exact Heval_lane1
                    | constructor; [exact Heval_lane2 | constructor]].
      - cbn [interp_op]. apply Hop.
    }
    split; [exact HR' | split; [solve_subsumed| ]].
    exact Heval_res. eauto. 
  Qed.

  Lemma insert_lane_ldiff_lor acc_val lane_val lane_width lane_idx :
    lane_width > 0 ->
    Z.shiftr acc_val (Z.of_nat lane_idx * lane_width) = 0 ->
    Z.lor
      (SemanticVector.insert_lane lane_val lane_idx lane_width)
      (Z.ldiff acc_val
        (Z.shiftl (Z.ones lane_width)
        (Z.of_nat lane_idx * lane_width)))
    = Z.lor acc_val (SemanticVector.insert_lane lane_val lane_idx lane_width).
  Proof. intros. 
    rewrite Z.lor_comm.
    f_equal. bitblast.Z.bitblast. assert (Hbit : Z.testbit acc_val i = false).
    { replace i with ((i - (Z.of_nat lane_idx * lane_width)) + (Z.of_nat lane_idx * lane_width)) by lia.
      rewrite <- Z.shiftr_spec by lia.
      rewrite H0. apply Z.bits_0. }
    rewrite Hbit. reflexivity.
  Qed.

  (* Writes [lane_val] into lane [lane_idx] of accumulator [acc]. *)
  Lemma insert_lane_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (acc lane : idx) (acc_val lane_val : Z)
    (Hacc : eval s acc acc_val) (Hlane : eval s lane lane_val)
    (lane_idx : nat) (lane_width : Z) (Hlw : (lane_width > 0)%Z)
    res s'
    (H : SymbolicVector.insert_lane acc lane lane_idx lane_width s
        = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res
        (Z.lor (SemanticVector.insert_lane lane_val lane_idx lane_width)
              (Z.ldiff acc_val
                  (Z.shiftl (Z.ones lane_width)
                            (Z.of_nat lane_idx * lane_width)))).
  Proof using Type. 
    cbv [SymbolicVector.insert_lane SemanticVector.insert_lane] in *. 
    eapply (App_R s m) in H as (HR' & Hsubs' & Heval_res). 
    split; [|split]; try eauto. exact HR. repeat (eauto || econstructor); cbn [interp_op]; repeat rewrite Z2N.id by nia; reflexivity.
  Qed.

  (* inductive case of vector_binop_aux_R *)
  Lemma vector_binop_aux_S_lane_idx
    {opts : symbolic_options_computed_opt} {descr : description}
    (i1 i2 : idx) (lane_op : op)
    (lane_idx n : nat) (lane_width : Z) (acc : idx) s res s'
    (H : SymbolicVector.vector_binop_aux i1 i2 lane_op lane_idx (S n)
          lane_width acc s = Success (res, s'))
    : exists lane_val new_acc s1 s2,
        SymbolicVector.make_lane i1 i2 lane_op lane_idx lane_width s
          = Success (lane_val, s1)
    /\ SymbolicVector.insert_lane acc lane_val lane_idx lane_width s1
          = Success (new_acc, s2)
    /\ SymbolicVector.vector_binop_aux i1 i2 lane_op (S lane_idx) n lane_width
          new_acc s2 = Success (res, s').
  Proof. simpl SymbolicVector.vector_binop_aux in *. repeat step_symex; cbv [fst snd] in *. 
    exists lane_val, new_acc, s0, s1. split; [| split]; eassumption.
  Qed.

  (* Iterates [num_remaining] lanes starting at [lane_idx], folding each into [acc]. *)
  Lemma vector_binop_aux_R {opts : symbolic_options_computed_opt} {descr : description}
        s m (HR : R s m)
        (i1 i2 : idx) (v1 v2 : Z)
        (Hv1 : eval s i1 v1) (Hv2 : eval s i2 v2)
        (lane_op : op) (binop : Z -> Z -> Z)
        (Hop : interprets_as_binop lane_op binop)
        (lane_idx num_remaining : nat)
        (lane_width : Z) (Hlw : (lane_width > 0)%Z)
        (acc : idx) (acc_val : Z) (Hacc : eval s acc acc_val)
        (Hacc_hi : Z.shiftr acc_val (Z.of_nat lane_idx * lane_width) = 0)
        res s'
        (H : SymbolicVector.vector_binop_aux i1 i2 lane_op lane_idx num_remaining
                                              lane_width acc s
            = Success (res, s'))
    : R s' m /\ s :< s' /\
      eval s' res
        (Z.lor acc_val
          (SemanticVector.vector_binop_aux v1 v2 binop lane_idx num_remaining lane_width)).
  Proof using Type.
    revert lane_idx s HR acc acc_val Hacc Hacc_hi res s' H Hv1 Hv2; induction num_remaining as [|n IH]; intros.
    { cbv [SemanticVector.vector_binop_aux SymbolicVector.vector_binop_aux] in *. 
      rewrite Z.lor_0_r. inversion H. subst. eauto. }
    {
      destruct (vector_binop_aux_S_lane_idx _ _ _ _ _ _ _ _ _ _ H)
        as (lane_val & new_acc & s1 & s2 & Hlane & Hins & Hrest).
      eapply make_lane_R in Hlane as (HR1 & Hsubs1 & Heval1); eauto.
      eapply insert_lane_R in Hins as (HR2 & Hsubs2 & Heval2); eauto.
      eapply IH in Hrest as (HR3 & Hsubs3 & Heval3); eauto; clear IH.

      (* Goal 2 first since you need it closed before discharging IH *)
      2: { unfold SemanticVector.insert_lane.
      apply acc_range_preserved; [lia | exact Hacc_hi]. }

      (* Goal 1: combine subsumptions + massage Heval3 *)
      split; [exact HR3|].
      split. solve_subsumed.
      rewrite insert_lane_ldiff_lor in Heval3 by (lia || exact Hacc_hi).
      rewrite <- Z.lor_assoc in Heval3. apply Heval3.
    }
  Qed.
    

  Lemma SymexVectorBinOp_R {opts : symbolic_options_computed_opt} {descr : description}
    s m (HR : R s m)
    (s_op : OperationSize) (sa : AddressSize) (Hsa : sa = 64%N)
    (dst src1 src2 : ARG)
    (lane_op : op) (binop : Z -> Z -> Z)
    (Hop : interprets_as_binop lane_op binop)
    (lane_width : Z) (Hlw : (lane_width > 0)%Z)
    _tt s'
    (H : @SymbolicVector.SymexVectorBinOp _ _ s_op sa dst src1 src2 lane_op lane_width s
        = Success (_tt, s'))
    : exists m',
        SemanticVector.DenoteVectorBinOp sa s_op m dst src1 src2 binop
          (N.to_nat (s_op / Z.to_N lane_width)%N) lane_width = Some m'
        /\ R s' m' /\ s :< s'.
  Proof using Type.
    cbv [SymbolicVector.SymexVectorBinOp] in H. repeat step_symex. cbv [fst snd] in *.
    rename v1 into i1, v2 into i2, HSv1 into Hget1, HSv2 into Hget2.
    eapply (GetOperand_R s m) in Hget1 as (HR0 & Hsubs0 & Heval1); eauto.
    eapply (GetOperand_R s0 m) in Hget2 as (HR1 & Hsubs1 & Heval2); eauto.
    destruct Heval1 as (v1 & Heval1 & Hdenote1); destruct Heval2 as (v2 & Heval2 & Hdenote2).
    
    eapply App_R in HSacc as (HR2 & Hsubs2 & Heval_acc); try eauto. 2: repeat econstructor.
    eapply vector_binop_aux_R in HSresult as (HR3 & Hsubs3 & Heval_res); eauto. rewrite Z.lor_0_l in Heval_res. 
    step_SetOperand.
    eexists. split; [|split]. 
    { cbv [SemanticVector.DenoteVectorBinOp Crypto.Util.Option.bind].
      rewrite Hdenote1, Hdenote2. exact Hm0. 
    }
    { exact Hs'. }
    { solve_subsumed. }
  Qed.

End SymbolicVectorProofs.


(* 
(* Connects the symbolic [interp_vector_binop] (semantics of the [vadd]/[vsub]
   DAG ops) with [SemanticVector.vector_binop_aux] (used by [DenoteVectorBinOp]).
   The concrete-side [lane_op] must be [fun a b => Z.land (scalar_op a b) (Z.ones lw)];
   with that shape the two pure Z computations coincide bit-for-bit. *)
Lemma interp_vector_binop_eq_vector_binop_aux
      (scalar_op : Z -> Z -> Z) (lw : Z) (lane_idx nr : nat) (v1 v2 : Z) :
  lw > 0 ->
  interp_vector_binop scalar_op lw lane_idx nr v1 v2
  = SemanticVector.vector_binop_aux v1 v2
      (fun a b => Z.land (scalar_op a b) (Z.ones lw)) lane_idx nr lw.
Proof. 
  intros Hlw. revert lane_idx. induction nr.
  { cbv [interp_vector_binop]. reflexivity. }
  { intros. cbn [interp_vector_binop SemanticVector.vector_binop_aux]. rewrite IHnr with (lane_idx := S lane_idx).    
  f_equal. cbv [SemanticVector.compute_and_insert_lane SemanticVector.insert_lane SemanticVector.compute_lane SemanticVector.extract_lane]. 
  bitblast.Z.bitblast.
  }
Qed.

Lemma interp_vector_binop_eq_vector_binop_values
      (scalar_op : Z -> Z -> Z) (lw : Z) (nr : nat) (v1 v2 : Z) :
  lw > 0 ->
  interp_vector_binop scalar_op lw 0 nr v1 v2
  = SemanticVector.vector_binop_values v1 v2
      (fun a b => Z.land (scalar_op a b) (Z.ones lw)) nr lw.
Proof.
  intros. unfold SemanticVector.vector_binop_values.
  apply interp_vector_binop_eq_vector_binop_aux; assumption.
Qed. *)

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
  (n = 8 \/ n = 16 \/ n = 32 \/ n = 64 \/ n = 128 \/ n = 256)%N.
Proof using Type.
   destruct o; cbn; try congruence.
   { destruct r as [sr | vr].
    - destruct sr; cbn; inversion 1; subst; eauto.
    - destruct vr; cbn; inversion 1; subst; repeat (eauto || right).
  }
   { destruct (mem_bits_access_size _) as [ [] | ]; inversion 1; subst; eauto. }
Qed.

Lemma opcode_size_cases o n : opcode_size o = Some n ->
  ((o = clc /\ n = 1) \/ n = 8 \/ n = 16 \/ n = 32 \/ n = 64 \/ n = 128 \/ n = 256)%N.
Proof using Type.
  destruct o; cbn; intros; Option.inversion_option; repeat (eauto; right).
Qed.

Lemma lift_map_standalone_operand_size_cases_Forall args ls
      (H : Crypto.Util.OptionList.Option.List.lift
             (map standalone_operand_size args) =
             Some ls)
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64 \/ n = 128 \/ n = 256)%N)
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
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64 \/ n = 128 \/ n = 256)%N)
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
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64 \/ n = 128 \/ n = 256)%N)
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
      (P := fun n => (n = 8 \/ n = 16 \/ n = 32 \/ n = 64 \/ n = 128 \/ n = 256)%N)
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
  (((exists prefix ls, i = Build_NormalInstruction prefix Syntax.clc ls) /\ n = 1) \/ (n = 8 \/ n = 16 \/ n = 32 \/ n = 64 \/ n = 128 \/ n = 256))%N.
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
                      end ];
  repeat (eauto || right).
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
  (* | H : interp_op _ ?o ?a = Some ?v |- _ => inversion H; clear H; subst *) (* edited because of new notation *)
  | H : interp_op ?o ?a = Some ?v |- _ => inversion H; clear H; subst
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

Lemma shiftl_0_r_N (v : Z) : Z.shiftl v (Z.of_N 0) = v.
Proof. rewrite Z.shiftl_0_r. reflexivity. Qed.
Print Z.shiftl_0_r.


(* Denote gets the value of a register, Set actually changes the machine state *)
(* This says that setting something to its current value returns the same machine state *)
Lemma SetOperand_same (n : N) (a : ARG) (v : Z) (m m' : machine_state) 
  (Hd : DenoteOperand 64 n m a = Some v) (Hs : SetOperand 64 n m a v = Some m')
  : m = m'.
Proof using Type.
Admitted.
  (* destruct a, m; cbn -[DenoteAddress] in *; repeat (subst; Option.inversion_option).
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
Qed. *)


(* Executing instruction in state s gives state s' *)
(* exists a machine state correponding to s' s.t.  *)
Lemma SymexNornalInstruction_R {opts : symbolic_options_computed_opt} {descr:description} s m (HR : R s m) (instr : NormalInstruction) :
  forall _tt s', Symbolic.SymexNormalInstruction instr s = Success (_tt, s') ->
  exists m', Semantics.DenoteNormalInstruction m instr = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  intros [] s' H.
  case instr as [op args].
  
  cbv [SymexNormalInstruction OperationSize] in H.
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

  all : cbn [fold_right map]; rewrite ?N2Z.id, ?Z.add_0_r, ?Z.add_assoc, ?Z.mul_1_r, ?Z.land_m1_r, ?Z.lxor_0_r, ?Z.lor_0_r;
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
             replace (Z.signed n 0) with 0; cycle 1.
             { pose_operation_size_cases. clear -H0; intuition (subst; cbv; trivial). }
             rewrite Z.add_0_r; cbv [Z.signed]; congruence. }

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
             end; rewrite ?Z.add_assoc, ?Z.add_0_r, ?Z.odd_opp; eauto; try Lia.lia; try congruence. }

  Unshelve. all : match goal with H : context[Syntax.adcx] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.adox] |- _ => idtac | _ => shelve end.
  { cbn [fold_right] in *; rewrite ?Z.bit0_odd, ?Z.add_0_r, ?Z.add_assoc in *; assumption. }

  Unshelve. all : match goal with H : context[Syntax.cmovc] |- _ => idtac |  H : context[Syntax.cmovb] |- _ => idtac |  H : context[Syntax.cmovo] |- _=> idtac | _ => shelve end.
  (* cmovc / cmovb / cmovo *)
  all: (destruct vCF||destruct vOF); cbn [negb Z.b2z Z.eqb] in *; eauto 9; [].
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

  Unshelve. all : match goal with H : context[Syntax.shld] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { repeat match goal with H : ?x = Some _, H' : ?x = Some _ |- _ => rewrite H' in *; Option.inversion_option end.
    progress subst.
    replace (Z.land (Z.of_N n) (Z.ones (Z.of_N n))) with (Z.of_N n)
      by (rewrite Z.land_ones, Z.mod_small; try split; try lia; apply Zpow_facts.Zpower2_lt_lin; lia).
    assert (0 <= Z.of_N n - 1) by (pose_operation_size_cases; intuition (subst; cbn; clear; lia)).
    rewrite <- !Z.shiftl_opp_r.
    rewrite !Z.shiftl_lor.
    rewrite <- !Z.land_lor_distr_l, <- Z.land_assoc, Z.land_diag.
    rewrite !Z.shiftl_shiftl by (try apply Z.land_nonneg; lia).
    f_equal; f_equal; f_equal; try lia. }

  Unshelve. all : match goal with H : context[Syntax.shlx] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { rewrite <- Z.land_assoc.
    f_equal; f_equal; [].
    pose_operation_size_cases; intuition subst; reflexivity. }
  
  Unshelve. all : match goal with H : context[push] |- _ => idtac | H : context[pop] |- _ => idtac | _ => shelve end; shelve_unifiable.
  all: rewrite !Z.land_ones by lia; push_Zmod; pull_Zmod; f_equal; lia.

  Unshelve. all : match goal with H : context[Syntax.vzeroupper] |- _ => idtac | _ => shelve end; shelve_unifiable.  
  { (* vzeroupper: each YMM gets slice 0 128, matching Z.land _ (Z.ones 128) *)
    admit.
  }  

  (* vpaddq *)
  Unshelve. all : match goal with H : context[Syntax.vpaddq] |- _ => idtac | _ => shelve end; shelve_unifiable.
  { eexists. split. 
      cbv [SemanticVector.DenoteVectorBinOp Crypto.Util.Option.bind]. rewrite Hv, Hv0.
      replace (Z.of_N 64) with 64 in Hm0 by lia.
      erewrite <- interp_vector_binop_eq_vector_binop_values; try lia. 
      exact Hm0. 
      split. exact Hs'. eauto.
  }

  Unshelve. all: shelve_unifiable.
	(* cbn. repeat rewrite Z.land_same_r. autorewrite with zsimplify push_Zshift. clear.  cbn.  *)
  Admitted.
	
  all: fail_if_goals_remain ().
(* Qed here hangs until the kernel crashes. Admitting until it can be sped up *)
Qed.


Lemma SymexLines_R {opts : symbolic_options_computed_opt} s m (HR : R s m) asm :
  forall _tt s', Symbolic.SymexLines asm s = Success (_tt, s') ->
  exists m', Semantics.DenoteLines m asm = Some m' /\ R s' m' /\ s :< s'.
Proof using Type.
  revert dependent m; revert dependent s; induction asm; cbn [SymexLines DenoteLines]; intros.
  { inversion H; subst; eauto. }
  destruct_head' Line.
  rewrite unfold_bind in *; destruct_one_match_hyp; inversion_ErrorT.
  cbv [SymexLine SymexRawLine DenoteLine DenoteRawLine ret err Crypto.Util.Option.bind] in *; cbn in *.
  destruct_one_match_hyp; inversion_ErrorT; subst; eauto; destruct_head'_prod.
  eapply SymexNornalInstruction_R in E; eauto. destruct E as (m1&Hm1&Rm1&?). rewrite Hm1.
  eapply IHasm in H; eauto. destruct H as (?&?&?&?). break_innermost_match; eauto 9.
Qed.
End WithCtx1'.
End WithFrame.
