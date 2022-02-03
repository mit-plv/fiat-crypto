Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.Language.API.
Require Import Crypto.Language.APINotations.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Assembly.Syntax.
Require Import Crypto.Assembly.WithBedrock.Semantics.
Require Import Crypto.Assembly.WithBedrock.SymbolicProofs.
Require Import Crypto.Assembly.Symbolic.
Require Import Crypto.Assembly.Equivalence.
Require Import Crypto.CastLemmas.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldMap.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.LandLorBounds.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.PrintContext.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers.
Import ListNotations.
Local Open Scope list_scope.

Definition eval_idx_Z (G : symbol -> option Z) (dag : dag) (idx : idx) (v : Z) : Prop
  :=  eval G dag (ExprRef idx) v.
Definition eval_idx_or_list_idx (G : symbol -> option Z) (d : dag) (v1 : idx + list idx) (v2 : Z + list Z)
  : Prop
  := match v1, v2 with
     | inl idx, inl v => eval_idx_Z G d idx v
     | inr idxs, inr vs => Forall2 (eval_idx_Z G d) idxs vs
     | inl _, inr _ | inr _, inl _ => False
     end.

Lemma lift_eval_idx_Z_impl G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall v n, eval_idx_Z G1 d1 v n -> eval_idx_Z G2 d2 v n.
Proof using Type.
  cbv [eval_idx_Z]; intros; destruct_head'_ex; destruct_head'_and; eauto.
Qed.

Lemma lift_eval_idx_or_list_idx_impl G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall v n, eval_idx_or_list_idx G1 d1 v n -> eval_idx_or_list_idx G2 d2 v n.
Proof using Type.
  cbv [eval_idx_or_list_idx]; intros; break_innermost_match; eauto using lift_eval_idx_Z_impl, Forall2_weaken.
Qed.

Lemma eval_eval_gen G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall e v1 v2, eval G1 d1 e v1 -> eval G2 d2 e v2 -> v1 = v2.
Proof. intros; eapply eval_eval; (idtac + apply H); eassumption. Qed.

Lemma eval_eval_Forall2_gen G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall e v1 v2, Forall2 (eval G1 d1) e v1 -> Forall2 (eval G2 d2) e v2 -> v1 = v2.
Proof. intros; eapply eval_eval_Forall2; (idtac + (eapply Forall2_weaken; [ apply H | ])); eassumption. Qed.

Lemma eval_eval_idx_Z G d
  : forall e v1 v2, eval_idx_Z G d e v1 -> eval_idx_Z G d e v2 -> v1 = v2.
Proof. cbv [eval_idx_Z]. intros; eapply eval_eval; eassumption. Qed.

Lemma eval_eval_idx_Z_gen G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall e v1 v2, eval_idx_Z G1 d1 e v1 -> eval_idx_Z G2 d2 e v2 -> v1 = v2.
Proof. intros; eapply eval_eval_idx_Z; (idtac + (eapply lift_eval_idx_Z_impl; [ apply H | ])); eassumption. Qed.

Lemma eval_eval_idx_Z_Forall2 G d
  : forall e v1 v2, Forall2 (eval_idx_Z G d) e v1 -> Forall2 (eval_idx_Z G d) e v2 -> v1 = v2.
Proof.
  intros *; rewrite <- Forall2_eq; rewrite !@Forall2_forall_iff_nth_error.
  intros H1 H2 i; specialize (H1 i); specialize (H2 i); revert H1 H2.
  cbv [option_eq]; break_innermost_match; try intuition congruence.
  apply eval_eval_idx_Z.
Qed.

Lemma eval_eval_idx_Z_Forall2_gen G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall e v1 v2, Forall2 (eval_idx_Z G1 d1) e v1 -> Forall2 (eval_idx_Z G2 d2) e v2 -> v1 = v2.
Proof. intros; eapply eval_eval_idx_Z_Forall2; (idtac + (eapply Forall2_weaken; [ apply lift_eval_idx_Z_impl, H | ])); eassumption. Qed.

Lemma eval_eval_idx_or_list_idx G d
  : forall e v1 v2, eval_idx_or_list_idx G d e v1 -> eval_idx_or_list_idx G d e v2 -> v1 = v2.
Proof.
  cbv [eval_idx_or_list_idx]; intros *; break_innermost_match; try intuition congruence; intros; apply f_equal.
  { eapply eval_eval_idx_Z; eassumption. }
  { eapply eval_eval_idx_Z_Forall2; eassumption. }
Qed.

Lemma eval_eval_idx_or_list_idx_gen G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall e v1 v2, eval_idx_or_list_idx G1 d1 e v1 -> eval_idx_or_list_idx G2 d2 e v2 -> v1 = v2.
Proof. intros; eapply eval_eval_idx_or_list_idx; (idtac + (eapply lift_eval_idx_or_list_idx_impl; [ apply H | ])); eassumption. Qed.

Lemma eval_eval_idx_or_list_idx_Forall2 G d
  : forall e v1 v2, Forall2 (eval_idx_or_list_idx G d) e v1 -> Forall2 (eval_idx_or_list_idx G d) e v2 -> v1 = v2.
Proof.
  intros *; rewrite <- Forall2_eq; rewrite !@Forall2_forall_iff_nth_error.
  intros H1 H2 i; specialize (H1 i); specialize (H2 i); revert H1 H2.
  cbv [option_eq]; break_innermost_match; try intuition congruence.
  apply eval_eval_idx_or_list_idx.
Qed.

Lemma eval_eval_idx_or_list_idx_Forall2_gen G1 G2 d1 d2
      (H : forall v n, eval G1 d1 v n -> eval G2 d2 v n)
  : forall e v1 v2, Forall2 (eval_idx_or_list_idx G1 d1) e v1 -> Forall2 (eval_idx_or_list_idx G2 d2) e v2 -> v1 = v2.
Proof. intros; eapply eval_eval_idx_or_list_idx_Forall2; (idtac + (eapply Forall2_weaken; [ apply lift_eval_idx_or_list_idx_impl, H | ])); eassumption. Qed.

Section WithFixedCtx.
Context (G : symbol -> option Z).

Fixpoint eval_base_var (dag : dag) {t : base.type} : base_var t -> API.interp_type (type.base t) -> Prop :=
  match t with
  | base.type.unit => fun _ _ => True
  | base.type.type_base base.type.Z => fun idx v => eval G dag (ExprRef idx) v
  | base.type.prod _ _ => fun a b => eval_base_var dag (fst a) (fst b) /\ eval_base_var dag (snd a) (snd b)
  | base.type.list _ => List.Forall2 (eval_base_var dag)
  | base.type.type_base base.type.nat => @eq _
  | base.type.type_base base.type.zrange => @eq _
  | _ => fun (bad : Empty_set) _ => match bad with end
  end%bool.

Definition eval_var (dag : dag) {t : API.type} : var t -> API.interp_type t -> Prop
  := match t with
     | type.base _ => eval_base_var dag
     | type.arrow _ _ => fun (bad : Empty_set) _ => match bad with end
     end.

Local Lemma ex_Z_of_N_iff P v
  : (exists n, Z.of_N n = v /\ P n) <-> (0 <= v /\ P (Z.to_N v))%Z.
Proof using Type.
  split; [ intros [n [H1 H2] ] | intros [H1 H2]; exists (Z.to_N v) ]; subst; rewrite ?N2Z.id, ?Z2N.id by lia.
  all: split; eauto; lia.
Qed.

Local Lemma ex_Z_of_N_iff' P v (H : (0 <= v)%Z)
  : (exists n, Z.of_N n = v /\ P n) <-> P (Z.to_N v).
Proof using Type. rewrite ex_Z_of_N_iff; intuition lia. Qed.

Lemma symex_T_app_curried_symex_T_error {t} err v d
  : @symex_T_app_curried t (symex_T_error err) v d = Error err.
Proof using Type. induction t; cbn in *; break_innermost_match; try reflexivity; eauto. Qed.

Lemma symex_T_app_curried_symex_T_bind_base_split T t v1 v2 v3 d rets d''
      (H : symex_T_app_curried (@symex_T_bind_base T t v1 v2) v3 d = Success (rets, d''))
  : exists rets' d',
    v1 d = Success (rets', d')
    /\ symex_T_app_curried (v2 rets') v3 d' = Success (rets, d'').
Proof using Type.
  induction t; cbn [symex_T symex_T_bind_base symex_T_app_curried] in *.
  all: cbv [symex_bind ErrorT.bind] in *.
  all: break_innermost_match_hyps; try discriminate; eauto.
Qed.

Lemma symex_T_app_curried_symex_T_bind_base_split_err T t v1 v2 v3 d err
      (H : symex_T_app_curried (@symex_T_bind_base T t v1 v2) v3 d = Error err)
  : v1 d = Error err
    \/ exists rets' d',
      v1 d = Success (rets', d')
      /\ symex_T_app_curried (v2 rets') v3 d' = Error err.
Proof using Type.
  induction t; cbn [symex_T symex_T_bind_base symex_T_app_curried] in *.
  all: cbv [symex_bind ErrorT.bind] in *.
  all: break_innermost_match_hyps; try discriminate; eauto.
  left; congruence.
Qed.

Lemma lift_eval_base_var_impl d1 d2
      (H : forall v n, eval G d1 v n -> eval G d2 v n)
  : forall t v n, @eval_base_var d1 t v n -> @eval_base_var d2 t v n.
Proof using Type.
  induction t; cbn [base_var eval_base_var]; break_innermost_match; intros; destruct_head'_ex; destruct_head'_and; subst; eauto using Forall2_weaken.
Qed.
Lemma lift_eval_var_impl d1 d2
      (H : forall v n, eval G d1 v n -> eval G d2 v n)
  : forall t v n, @eval_var d1 t v n -> @eval_var d2 t v n.
Proof using Type.
  induction t; cbn [var eval_var]; eauto using lift_eval_base_var_impl.
Qed.

Lemma RevealConstant_correct idx d d' v
      (H : RevealConstant idx d = Success (v, d'))
      (d_ok : gensym_dag_ok G d)
  : eval G d (ExprRef idx) (Z.of_N v) /\ d = d'.
Proof using Type.
  cbv [RevealConstant] in *; break_innermost_match_hyps;
    inversion_ErrorT; inversion_prod; subst; split; trivial; [].
  pose proof Heqe as Hx.
  cbv [reveal reveal_step] in Hx.
  break_innermost_match_hyps; inversion Hx; subst.
  eapply map_eq_nil in H1; subst.
  repeat (eauto || econstructor).
  rewrite Z2N.id; eauto using Zle_bool_imp_le.
Qed.

Lemma RevealWidth_correct idx d d' v
      (H : RevealWidth idx d = Success (v, d'))
      (d_ok : gensym_dag_ok G d)
  : eval G d (ExprRef idx) (2 ^ Z.of_N v) /\ d = d'.
Proof using Type.
  cbv [RevealWidth symex_bind ErrorT.bind symex_return symex_error] in *.
  break_innermost_match_hyps; inversion_ErrorT; inversion_prod; subst.
  eapply RevealConstant_correct in Heqe; intuition idtac.
  eapply Neqb_ok in Heqb; subst.
  epose proof N2Z.inj_pow 2 (N.log2 n) as HH.
  rewrite <-Heqb in HH. rewrite HH in H. exact H.
Qed.

(** Makes use of [eval_merge] and [eval_merge_node] lemmas, leaving
over evars for unknown evaluation values, reading off which [merge]
and [merge_node] constructs to pose proofs about from the goal and
hypotheses *)
Local Ltac saturate_eval_merge_step :=
  first [ eassumption
        | let saturate_lem eval_lem mergev do_change do_clear :=
              (** ensure that we do innermost merge first *)
              (let e := lazymatch mergev with
                        | merge_node ?e ?d => e
                        | merge ?e ?d => e
                        end in
               lazymatch e with
               | context[merge_node] => fail
               | context[merge] => fail
               | _ => idtac
               end);
              let n := open_constr:(_) in
              let G := open_constr:(_) in
              let T := open_constr:(_) in
              cut T;
              [ let H := fresh in
                intro H;
                let T' := open_constr:(_) in
                cut T';
                [ let H' := fresh in
                  intro H';
                  let H'' := fresh in
                  pose proof (eval_lem G n H' H); cbv beta zeta in *;
                  do_change ();
                  let k := fresh in
                  set (k := mergev) in *; clearbody k
                | do_clear () ]
              | do_clear () ]
          in
          let saturate_of T do_clear :=
              match T with
              | context[merge_node (@pair ?A ?B ?op ?args) ?d]
                => saturate_lem (fun G n H' H => eval_merge_node G d H' op args n H) (merge_node (@pair A B op args) d)
                                ltac:(fun _ => progress change (op, args) with (@pair A B op args) in * ) do_clear
              | context[merge ?e ?d]
                => saturate_lem (fun G n H' H => eval_merge G e n d H' H) (merge e d)
                                ltac:(fun _ => idtac) do_clear
              end in
          match goal with
          | [ |- ?T ] => saturate_of T ltac:(fun _ => idtac)
          | [ H : ?T |- _ ] => saturate_of T ltac:(fun _ => clear H)
          end
        | progress destruct_head'_and
        | solve [ eauto 100 ] ].
Local Ltac saturate_eval_merge := repeat saturate_eval_merge_step.

Lemma App_correct n d (Hdag : gensym_dag_ok G d) i d' (H : App n d = Success (i, d'))
  v (Heval : eval_node G d n v)
  : eval G d' (ExprRef i) v /\ gensym_dag_ok G d' /\ (forall e n, eval G d e n -> eval G d' e n).
Proof using Type.
  cbv [App] in *. inversion_ErrorT.
  do 2
  match goal with
  | H : context [simplify ?d ?n] |- _ =>
      unique pose proof (eval_simplify _ d n _ ltac:(eassumption))
  | H : context [merge ?e ?d] |- _ =>
      case (eval_merge _ e _ d ltac:(eassumption) ltac:(eassumption)) as (?&?&?)
  end.
  inversion_prod; subst; eauto 9.
Qed.

(* workaround: using cbn instead of this lemma makes Qed hang after next destruct *)
Lemma unfold_symex_bind {A B} ma amb :
  @symex_bind A B ma amb = ltac:(let t := eval cbv [symex_bind ErrorT.bind] in (@symex_bind A B ma amb) in exact t).
Proof using Type. exact eq_refl. Qed.

Theorem symex_ident_correct
        {t} (idc : ident t)
        (d : dag)
        (input_var_data : type.for_each_lhs_of_arrow var t)
        (input_runtime_var : type.for_each_lhs_of_arrow API.interp_type t)
        (* N.B. We need [Hinput] for the [gensym_dag_ok] conclusion, because
            we need to know that we can evaluate the indices in the
            arguments w.r.t. the dag for, e.g., [eval_merge_node] *)
        (Hinput : type.and_for_each_lhs_of_arrow (@eval_var d) input_var_data input_runtime_var)
        (rets : base_var (type.final_codomain t))
        (d' : dag)
        (H : symex_T_app_curried (symex_ident idc) input_var_data d = Success (rets, d'))
        (d_ok : gensym_dag_ok G d)
  : eval_base_var d' rets (type.app_curried (Compilers.ident_interp idc) input_runtime_var)
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof using Type.
  cbv [symex_ident] in H; break_innermost_match_hyps.
  all: cbn [type.app_curried type.and_for_each_lhs_of_arrow Compilers.ident_interp symex_T_app_curried type.for_each_lhs_of_arrow] in *.
  all: cbn [API.interp_type base_var type.final_codomain var] in *.
  all: destruct_head'_prod; destruct_head'_unit.
  all: cbv [symex_T_error symex_error symex_return ident.eagerly ident.literal] in *.
  all : repeat match goal with
        | H : context[symex_bind _ _] |- _ => rewrite !unfold_symex_bind in H
        | _ => destruct_one_head'_and
        | _ => inversion_ErrorT_step
        | H : App ?e ?d = Success (?i, ?d') |- _ =>
            eapply (App_correct e d ltac:(eassumption)) in H; [|clear H..]
        | [ H : RevealWidth _ _ = Success _ |- _ ]
          => eapply RevealWidth_correct in H; [ | clear H; try eassumption .. ]
        | [ H : RevealConstant _ _ = Success _ |- _ ]
          => eapply RevealConstant_correct in H; [ | clear H; try eassumption .. ]
        | H : eval ?a ?b ?c ?x, G : eval ?a ?b ?c ?y |- _ => epose proof eval_eval _ _ _ _ H _ G; clear G
        | _ => inversion_prod_step
        | _ => break_innermost_match_hyps_step
        | _ => progress cbn [eval_base_var eval_var fst snd List.map] in *
        | _ => progress subst
        |  |- eval _ _ (ExprRef _) _ => solve[eauto 99 with nocore]
        | |- eval_node _ _ (?op, ?args) _ => let h := Head.head op in is_constructor h; econstructor
        | |- interp_op _ ?op ?args = Some _ => let h := Head.head op in is_constructor h; exact eq_refl
        | |- Forall2 _ _ _ => econstructor
        end.
  all : Tactics.ssplit; eauto 9.
  all : match goal with
        | |- context[eval _ _ _ _] => idtac (* solve below *)
        | _ => solve [ repeat first [ solve [ eauto using length_Forall2, Forall.Forall2_firstn, Forall.Forall2_skipn, Forall.Forall2_combine, Forall2_app, Forall2_rev ]
                                | rewrite Forall2_eq
                                | rewrite Forall.Forall2_repeat_iff
                                | now apply Forall.Forall2_forall_iff'' ] ] end.
  all: match goal with (* eval_same_expr_goal *)
        | |- eval G ?d ?e ?v =>
            match goal with
              H : eval G d e ?v' |- _ =>
                  let Heq := fresh in
                  enough (Heq : v = v') by (rewrite Heq; exact H);
                  try clear H e
            end
        | |- eval G ?d ?e ?v =>
            let H := fresh in
            let v' := open_constr:(_) in
            eassert (eval G d e v') by (eauto 99 with nocore);
            let Heq := fresh in
            enough (Heq : v = v') by (rewrite Heq; exact H);
            try clear H e
        end.
  all : cbv [fold_right Z.add_with_carry Z.truncating_shiftl] in *.
  all : repeat (rewrite ?Z.mul_split_mod, ?Z.mul_split_div, ?Z.mul_high_div,
    ?Z.add_get_carry_full_div, ?Z.add_get_carry_full_mod, ?Z.sub_add_distr,
    ?Z.add_with_get_carry_full_div, ?Z.add_with_get_carry_full_mod,
    ?Z.sub_get_borrow_full_div, ?Z.sub_get_borrow_full_mod, ?Z.sub_0_r,
    ?Z.sub_with_get_borrow_full_div, ?Z.sub_with_get_borrow_full_mod,
    ?Z.add_0_r, ?Z.mul_1_r, ?Z.lor_0_r, ?Z.land_m1_r, ?Z.add_opp_r,
    ?Z.add_assoc, ?Z.shiftr_0_r,  ?Z.shiftr_div_pow2, ?Z.land_ones;
    push_Zmod; pull_Zmod);
    try Lia.lia.
  all: repeat first [ progress cbn [fst snd List.map] in *
                    | progress subst
                    | progress split_andb
                    | progress reflect_hyps
                    | progress cbv [ident.cast2]
                    | match goal with
                      | [ H : _ = fst ?x |- _ ] => is_var x; destruct x
                      | [ H : _ = snd ?x |- _ ] => is_var x; destruct x
                      end ].
  all : match goal with
        | [ |- context[ident.cast ?r ?v] ]
         => rewrite !ident.platform_specific_cast_0_is_mod
           by match goal with
              | [ H : Z.succ ?v = (2^Z.log2 (Z.succ ?v))%Z |- (0 <= ?v)%Z ]
                => clear -H; destruct v; try lia; rewrite Z.log2_nonpos, Z.pow_0_r in H by lia; lia
              end
        end.
  all : rewrite Z2N.id by eapply Z.log2_nonneg.
  all : match goal with H : Z.succ _=_|-_=> rewrite <-H, Z.add_1_r end; trivial.
  all : fail.
Qed.
Theorem symex_expr_correct
        {t} (expr1 : API.expr (var:=var) t) (expr2 : API.expr (var:=API.interp_type) t)
        (d : dag)
        (input_var_data : type.for_each_lhs_of_arrow var t) (input_runtime_var : type.for_each_lhs_of_arrow API.interp_type t)
        (Hinputs : type.and_for_each_lhs_of_arrow (@eval_var d) input_var_data input_runtime_var)
        (rets : base_var (type.final_codomain t))
        (d' : dag)
        GG
        (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) GG -> eval_var d v1 v2)
        (Hwf : API.wf GG expr1 expr2)
        (H : symex_T_app_curried (symex_expr expr1) input_var_data d = Success (rets, d'))
        (d_ok : gensym_dag_ok G d)
  : eval_base_var d' rets (type.app_curried (API.interp expr2) input_runtime_var)
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof using Type.
  revert dependent d; revert dependent d'; revert dependent input_var_data; revert dependent input_runtime_var.
  induction Hwf; intros; cbn [symex_expr] in *.
  all: repeat first [ match goal with
                      (* ident case *)
                      | [ |- context[expr.Ident] ] => eapply symex_ident_correct; eassumption
                      (* var case *)
                      | [ HIn : List.In (existT _ ?t (?v1, ?v2)) _ |- context[expr.Var] ]
                        => is_var t; specialize (HG t _ _ HIn); destruct t
                      (* abs case, eventually *)
                      | [ H : context[_ /\ gensym_dag_ok _ /\ (forall e n, _ -> _)] |- context[expr.Abs] ]
                        => eapply H; try eassumption; clear H; []
                      end
                    | match goal with
                      | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                      | [ H : Error _ = Success _ |- _ ] => now inversion H
                      | [ H : symex_T_app_curried (symex_T_bind_base _ _) _ _ = Success _ |- _ ]
                        => apply symex_T_app_curried_symex_T_bind_base_split in H
                      end
                    | match goal with
                      | [ IH : forall rets d' d, _ -> symex_expr ?x d = Success (rets, d') -> _, H : symex_expr ?x _ = Success (_, _) |- _ ]
                        => specialize (fun H' => IH _ _ _ H' H)
                      | [ IH : forall rets irv c ivd e d' d0, _ -> _ -> _ -> symex_T_app_curried (symex_expr ?f ivd) e d0 = Success (rets, d') -> _,
                            H : symex_T_app_curried (symex_expr ?f _) _ _ = Success (_, _) |- _ ]
                        => specialize (fun irv c H1 H2 H3 => IH _ irv c _ _ _ _ H1 H2 H3 H)
                      | [ IH : forall v1 v2 rets irv ivd d' d, _ -> _ -> symex_T_app_curried (symex_expr (?f v1)) ivd d = Success (rets, d') -> _,
                            H : symex_T_app_curried (symex_expr (?f _)) _ _ = Success (_, _) |- _ ]
                        => specialize (fun v2 irv H1 H2 => IH _ v2 _ irv _ _ _ H1 H2 H)
                      | [ IH : forall irv c, eval_base_var ?a ?b irv -> _, H : eval_base_var ?a ?b _ |- _ ]
                        => specialize (fun c => IH _ c H)
                      | [ IH : forall c, type.and_for_each_lhs_of_arrow ?x ?ivd c -> _, H : type.and_for_each_lhs_of_arrow ?y ?ivd ?cv |- _ ]
                        => specialize (fun H' => IH cv ltac:(eapply Wf.Compilers.type.and_for_each_lhs_of_arrow_Proper_impl; [ .. | eexact H ]; try reflexivity; cbv [Morphisms.forall_relation Morphisms.pointwise_relation Basics.impl]; eapply lift_eval_var_impl; eassumption))
                      | [ IH : forall v2 c, type.and_for_each_lhs_of_arrow ?x ?ivd c -> _, H : type.and_for_each_lhs_of_arrow ?y ?ivd ?cv |- _ ]
                        => specialize (fun v2 H' => IH v2 cv ltac:(eapply Wf.Compilers.type.and_for_each_lhs_of_arrow_Proper_impl; [ .. | eexact H ]; try reflexivity; cbv [Morphisms.forall_relation Morphisms.pointwise_relation Basics.impl]; eapply lift_eval_var_impl; eassumption))
                      | [ H : forall v, ?T -> (forall t v1 v2, existT _ _ _ = _ \/ _ -> _) -> _ |- _ ]
                        => specialize (fun H1 H3 v H2 => H v H1 (fun t v1 v2 pf => match pf with
                                                                                   | or_introl pf => H2 t v1 v2 pf
                                                                                   | or_intror pf => H3 t v1 v2 pf
                                                                                   end))
                      | [ H : forall v, (forall t v1 v2, existT _ _ _ = existT _ t (v1, v2) -> _) -> _ |- _ ]
                        => specialize (H _ ltac:(intros; inversion_sigma; subst; cbn [eq_rect] in *; inversion_prod; subst; eassumption))
                      end
                    | match goal with
                      | [ H : forall a (b : unit), _ |- _ ] => specialize (fun a => H a tt)
                      | [ H : forall a b, True -> _ |- _ ] => specialize (fun a b => H a b I)
                      | [ H : forall a b c, True -> _ |- _ ] => specialize (fun a b c => H a b c I)
                      | [ H : forall a (b : _ * _), _ |- _ ] => specialize (fun a b c => H a (b, c))
                      | [ H : forall a b c (d : _ * _), _ |- _ ] => specialize (fun a b c d e => H a b c (d, e))
                      | [ H : forall a b c d e f, _ /\ _ -> _ |- _ ] => specialize (fun a b c d e f g h => H a b c d e f (conj g h))
                      | [ H : forall a b c d e f g, _ /\ _ -> _ |- _ ] => specialize (fun a b c d e f g h i => H a b c d e f g (conj h i))
                      end
                    | exfalso; assumption
                    | progress subst
                    | progress destruct_head_hnf' unit
                    | progress destruct_head_hnf' True
                    | progress destruct_head_hnf' prod
                    | progress destruct_head'_and
                    | progress destruct_head'_ex
                    | progress cbn [symex_T_app_curried symex_T_return eval_var type.app_curried] in *
                    | progress cbn [type.and_for_each_lhs_of_arrow type.for_each_lhs_of_arrow fst snd List.In eq_rect] in *
                    | progress cbn [type.final_codomain base_var] in *
                    | progress cbv [symex_return] in *
                    | rewrite @symex_T_app_curried_symex_T_error in *
                    | solve [ auto ]
                    | progress inversion_sigma
                    | progress inversion_prod
                    | progress break_innermost_match_hyps
                    | progress destruct_head'_or
                    | progress intros
                    | progress specialize_by_assumption
                    | progress specialize_by (eauto using lift_eval_var_impl) ].
Qed.

Lemma symex_expr_App_curried {t} (e : API.expr t) input_var_data d
  : symex_expr (invert_expr.App_curried e (type.map_for_each_lhs_of_arrow (fun t v => ($v)%expr) input_var_data)) d
    = symex_T_app_curried (symex_expr e) input_var_data d.
Proof using Type.
  induction t; cbn [invert_expr.App_curried symex_T_app_curried type.map_for_each_lhs_of_arrow];
    destruct_head_hnf' prod; destruct_head_hnf' unit; cbn [fst snd]; try reflexivity.
  match goal with H : _ |- _ => rewrite H; clear H end.
  repeat first [ progress cbn [symex_expr var] in *
               | progress break_innermost_match
               | solve [ destruct_head'_Empty_set ] ].
  cbv [symex_T_return symex_return] in *.
  let LHS := match goal with |- ?LHS = _ => LHS end in
  destruct LHS as [ [? ?] | ? ] eqn:H;
    [ apply symex_T_app_curried_symex_T_bind_base_split in H | apply symex_T_app_curried_symex_T_bind_base_split_err in H ].
  all: destruct_head'_or; destruct_head'_ex; destruct_head'_and; congruence.
Qed.

Lemma symex_expr_smart_App_curried {t} (e : API.expr t) input_var_data d
  : symex_expr (invert_expr.smart_App_curried e input_var_data) d
    = symex_T_app_curried (symex_expr e) input_var_data d.
Proof using Type.
  induction e; cbn [invert_expr.smart_App_curried];
    rewrite ?symex_expr_App_curried; try reflexivity.
  match goal with H : _ |- _ => rewrite H; clear H end.
  cbn [symex_expr symex_T_app_curried]; break_innermost_match; cbn [fst snd]; reflexivity.
Qed.

Theorem symex_PHOAS_PHOAS_correct
        {t} (expr : API.Expr t)
        (d : dag)
        (input_var_data : type.for_each_lhs_of_arrow var t) (input_runtime_var : type.for_each_lhs_of_arrow API.interp_type t)
        (Hinputs : type.and_for_each_lhs_of_arrow (@eval_var d) input_var_data input_runtime_var)
        (rets : base_var (type.final_codomain t))
        (d' : dag)
        (Hwf : API.Wf expr)
        (H : symex_PHOAS_PHOAS expr input_var_data d = Success (rets, d'))
        (d_ok : gensym_dag_ok G d)
  : eval_base_var d' rets (type.app_curried (API.Interp expr) input_runtime_var)
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof using Type.
  cbv [symex_PHOAS_PHOAS] in H.
  rewrite symex_expr_smart_App_curried in H.
  eapply symex_expr_correct with (GG:=[]); try eassumption; cbn [List.In]; try eapply Hwf; try now intros; exfalso.
Qed.

Fixpoint build_base_runtime (t : base.type) (values : list (Z + list Z))
  : option (base.interp t * list (Z + list Z))
  := match t, values return option (base.interp t * list (Z + list Z)) with
     | base.type.unit, _
       => Some (tt, values)
     | base.type.type_base base.type.Z, inl val :: values
       => Some (val, values)
     | base.type.prod A B, _
       => (vA <- build_base_runtime A values;
          let '(vA, values) := vA in
          vB <- build_base_runtime B values;
          let '(vB, values) := vB in
          Some ((vA, vB), values))
     | base.type.list (base.type.type_base base.type.Z), inr value :: values
       => Some (value, values)
     | base.type.type_base base.type.Z, inr _ :: _
     | base.type.list (base.type.type_base base.type.Z), inl _ :: _
     | base.type.type_base _, []
     | base.type.list _, []
     | base.type.type_base _, _
     | base.type.option _, _
     | base.type.list _, _ :: _
       => None
     end%option.
Definition build_runtime (t : API.type) (values : list (Z + list Z))
  : option (API.interp_type t * list (Z + list Z))
  := match t with
     | type.base t => build_base_runtime t values
     | type.arrow _ _ => None
     end.
Fixpoint build_input_runtime (t : API.type) (values : list (Z + list Z))
  : option (type.for_each_lhs_of_arrow API.interp_type t * list (Z + list Z))
  := match t with
     | type.base _ => Some (tt, values)
     | type.arrow A B
       => (vA <- build_runtime A values;
          let '(vA, values) := vA in
          vB <- build_input_runtime B values;
          let '(vB, values) := vB in
          Some ((vA, vB), values))
     end%option.

Fixpoint simplify_base_runtime {t : base.type} : base.interp t -> option (list (Z + list Z))
  := match t return base.interp t -> option (list (Z + list Z)) with
     | base.type.unit
       => fun 'tt => Some []
     | base.type.type_base base.type.Z => fun val => Some [inl val]
     | base.type.prod A B => fun ab => (a <- simplify_base_runtime (fst ab); b <- simplify_base_runtime (snd ab); Some (a ++ b))
     | base.type.list (base.type.type_base base.type.Z)
       => fun ls : list Z => Some [inr ls]
     | base.type.list _
     | base.type.type_base _
     | base.type.option _
       => fun _ => None
     end%option.

Lemma build_base_var_runtime_gen
      d
      (inputs : list (idx + list idx)) (runtime_inputs : list (Z + list Z))
      (Hinputs : Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
      t
  : match build_base_var t inputs, build_base_runtime t runtime_inputs with
    | Success (v1, ls1), Some (v2, ls2)
      => eval_base_var d v1 v2
         /\ Forall2 (eval_idx_or_list_idx G d) ls1 ls2
    | Success _, None | Error _, Some _ => False
    | Error _, None => True
    end.
Proof using Type.
  revert inputs runtime_inputs Hinputs; induction t; cbn [build_base_var build_base_runtime]; intros; break_innermost_match.
  all: repeat first [ exact I
                    | progress subst
                    | progress cbn [eval_idx_or_list_idx eval_base_var] in *
                    | progress cbv [Crypto.Util.Option.bind Rewriter.Util.Option.bind ErrorT.bind] in *
                    | exfalso; assumption
                    | solve [ auto ]
                    | match goal with
                      | [ H : Forall2 _ [] _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ _ [] |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ _ (_ :: _) |- _ ] => inversion H; clear H
                      end
                    | progress break_innermost_match_hyps
                    | progress specialize_by_assumption
                    | progress destruct_head'_and
                    | match goal with
                      | [ H : context[match build_base_var ?t1 _ with _ => _ end] |- context[build_base_var ?t1 ?inputs] ]
                        => specialize (H inputs)
                      | [ H : context[match build_base_runtime ?t1 _ with _ => _ end] |- context[build_base_runtime ?t1 ?inputs] ]
                        => specialize (H inputs)
                      end ].
Qed.

Lemma build_var_runtime_gen
      d
      (inputs : list (idx + list idx)) (runtime_inputs : list (Z + list Z))
      (Hinputs : Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
      t
  : match build_var t inputs, build_runtime t runtime_inputs with
    | Success (v1, ls1), Some (v2, ls2)
      => eval_var d v1 v2
         /\ Forall2 (eval_idx_or_list_idx G d) ls1 ls2
    | Success _, None | Error _, Some _ => False
    | Error _, None => True
    end.
Proof using Type.
  destruct t as [t|s d']; [ pose proof (build_base_var_runtime_gen _ _ _ Hinputs t) | ].
  all: cbv [build_var build_runtime]; break_innermost_match; try assumption; try exact I.
Qed.

Lemma build_input_var_runtime_gen
      d
      (inputs : list (idx + list idx)) (runtime_inputs : list (Z + list Z))
      (Hinputs : Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
      t
  : match build_input_var t inputs, build_input_runtime t runtime_inputs with
    | Success (v1, ls1), Some (v2, ls2)
      => type.and_for_each_lhs_of_arrow (@eval_var d) v1 v2
         /\ Forall2 (eval_idx_or_list_idx G d) ls1 ls2
    | Success _, None | Error _, Some _ => False
    | Error _, None => True
    end.
Proof using Type.
  revert inputs runtime_inputs Hinputs; induction t as [|s _ d' IHd];
    cbn [build_input_runtime build_input_var build_var type.and_for_each_lhs_of_arrow] in *; intros; auto; [].
  cbv [Crypto.Util.Option.bind Rewriter.Util.Option.bind ErrorT.bind].
  pose proof (build_var_runtime_gen _ _ _ Hinputs s).
  break_innermost_match_hyps; try exact I; try (now exfalso); [].
  destruct_head'_and.
  let l := match goal with |- context[build_input_var _ ?l] => l end in
  specialize (IHd l _ ltac:(eassumption)).
  break_innermost_match_hyps; try exact I; try (now exfalso); [].
  destruct_head'_and; auto.
Qed.

Lemma simplify_base_var_runtime_gen {t} d b v
      (H : eval_base_var d b v)
  : match @simplify_base_var t b, @simplify_base_runtime t v with
    | Success rets, Some val => Forall2 (eval_idx_or_list_idx G d) rets val
    | Success _, None | Error _, Some _ => False
    | Error _, None => True
    end.
Proof using Type.
  induction t; cbn [eval_base_var simplify_base_var simplify_base_runtime] in *; break_innermost_match.
  all: repeat first [ assumption
                    | exact I
                    | match goal with
                      | [ |- Forall2 _ _ _ ] => constructor
                      end
                    | progress destruct_head'_and
                    | progress destruct_head_hnf' prod
                    | progress cbn [fst snd] in *
                    | progress cbv [Crypto.Util.Option.bind Rewriter.Util.Option.bind ErrorT.bind] in *
                    | match goal with
                      | [ IH : context[simplify_base_var _] |- context[simplify_base_var ?b] ]
                        => specialize (IH b _ ltac:(eassumption))
                      end
                    | progress break_innermost_match_hyps
                    | rewrite Forall.Forall2_map_map_iff
                    | solve [ eauto using Forall2_app ] ].
Qed.

Theorem symex_PHOAS_correct
        {t} (expr : API.Expr t)
        (d : dag)
        (inputs : list (idx + list idx)) (runtime_inputs : list (Z + list Z))
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
        (rets : list (idx + list idx))
        (d' : dag)
        (Hwf : API.Wf expr)
        (H : symex_PHOAS expr inputs d = Success (rets, d'))
        (d_ok : gensym_dag_ok G d)
  : (exists (input_runtime_var : type.for_each_lhs_of_arrow API.interp_type t)
            (runtime_rets : list (Z + list Z)),
        build_input_runtime t runtime_inputs = Some (input_runtime_var, [])
        /\ simplify_base_runtime (type.app_curried (API.Interp expr) input_runtime_var) = Some runtime_rets
        /\ List.Forall2 (eval_idx_or_list_idx G d') rets runtime_rets)
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof using Type.
  cbv [symex_PHOAS ErrorT.bind] in H; break_innermost_match_hyps; try discriminate.
  destruct (build_input_runtime t runtime_inputs) as [ [input_runtime_var [|] ] | ] eqn:H'; [ | exfalso.. ].
  all: lazymatch goal with
       | [ H : symex_PHOAS_PHOAS _ _ _ = Success _,
               input_runtime_var : type.for_each_lhs_of_arrow API.interp_type _
           |- _ ] => apply (@symex_PHOAS_PHOAS_correct _ _ _ _ input_runtime_var) in H; try assumption; [ | clear H .. ]
       | [ |- False ] => idtac
       end.
  all: repeat first [ progress break_innermost_match_hyps
                    | progress destruct_head'_and
                    | progress subst
                    | progress inversion_option
                    | progress inversion_prod
                    | discriminate
                    | assumption
                    | apply (f_equal (@Some _))
                    | apply (f_equal2 (@pair _ _))
                    | reflexivity
                    | progress reflect_hyps
                    | match goal with
                      | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                      | [ H : symex_PHOAS_PHOAS _ _ _ = _ |- _ ] => apply symex_PHOAS_PHOAS_correct in H; [ | assumption.. ]
                      | [ |- exists a b, ?v = Some (a, _) /\ _ = Some b /\ _ ]
                        => let av := fresh in destruct v as [ [av ?] |] eqn:?; [ exists av | exfalso ]
                      | [ |- exists a, _ /\ ?v = Some a /\ _ ]
                        => let av := fresh in destruct v as [ av |] eqn:?; [ exists av | exfalso ]
                      | [ H : List.length ?l = 0%nat |- _ ] => is_var l; destruct l; cbn in H
                      | [ H : Forall2 _ [] _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ _ [] |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ _ (_ :: _) |- _ ] => inversion H; clear H
                      end
                    | apply conj
                    | progress intros
                    | match goal with
                      | [ H : build_input_runtime ?t ?ri = _, H' : build_input_var ?t ?i = _ |- _ ]
                        => let H'' := fresh in
                           pose proof (build_input_var_runtime_gen _ i ri ltac:(eassumption) t) as H'';
                           rewrite H, H' in H''; clear H H'
                      | [ H : simplify_base_var ?b = _, H' : simplify_base_runtime ?v = _ |- _ ]
                        => let H'' := fresh in
                           pose proof (simplify_base_var_runtime_gen _ b v ltac:(eassumption)) as H'';
                           rewrite H, H' in H''; clear H H'
                      end ].
Qed.
End WithFixedCtx.

Lemma empty_gensym_dag_ok : gensym_dag_ok (fun _ => None) empty_dag.
Proof using Type.
  cbv [empty_dag gensym_dag_ok gensym_ok dag_ok node_ok]; repeat split; try congruence;
    exfalso; eapply List.nth_error_nil_Some; eassumption.
Qed.


Definition val_or_list_val_matches_spec (arg : Z + list Z) (spec : option nat)
  := match arg, spec with
     | inl _, None => True
     | inr ls, Some len => List.length ls = len
     | inl _, Some _ | inr _, None => False
     end.



Local Ltac build_runtime_ok_t_step :=
  first [ progress subst
        | progress destruct_head'_unit
        | progress inversion_option
        | progress inversion_prod
        | progress destruct_head'_prod
        | progress destruct_head'_and
        | progress destruct_head'_ex
        | progress cbv [Crypto.Util.Option.bind Rewriter.Util.Option.bind ErrorT.bind] in *
        | progress cbn [val_or_list_val_matches_spec] in *
        | progress cbn [fst snd ZRange.type.base.option.is_bounded_by type.andb_bool_for_each_lhs_of_arrow] in *
        | progress split_andb
        | progress break_innermost_match_hyps
        | rewrite <- !List.app_assoc in *
        | discriminate
        | progress specialize_by_assumption
        | match goal with
          | [ H : ?x = Some _ |- context[?x] ] => rewrite H
          | [ H : forall extra, ?f (?x ++ extra) = Some _ |- context[?f (?x ++ _)] ] => rewrite !H
          | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
          | [ |- exists args, ?extra = args ++ ?extra /\ _ /\ _ ]
            => exists nil
          | [ |- exists args, ?x :: ?extra = args ++ ?extra /\ _ /\ _ ]
            => exists (x :: nil)
          | [ |- exists args, ?x ++ ?extra = args ++ ?extra /\ _ /\ _ ]
            => exists x
          | [ |- exists args, ?x ++ (?y ++ ?extra) = args ++ ?extra /\ _ /\ _ ]
            => exists (x ++ y); rewrite !List.app_assoc
          | [ IH : forall a b c d e, simplify_base_type _ _ = Success _ -> build_base_runtime _ _ = Some _ -> _ |- _ ]
            => specialize (IH _ _ _ _ _ ltac:(eassumption) ltac:(eassumption))
          | [ IH : forall a b c d e, simplify_type _ _ = Success _ -> build_runtime _ _ = Some _ -> _ |- _ ]
            => specialize (IH _ _ _ _ _ ltac:(eassumption) ltac:(eassumption))
          | [ IH : forall a b c d e, simplify_input_type _ _ = Success _ -> build_input_runtime _ _ = Some _ -> _ |- _ ]
            => specialize (IH _ _ _ _ _ ltac:(eassumption) ltac:(eassumption))
          | [ |- Forall2 _ (_ ++ _) (_ ++ _) ] => apply Forall2_app
          | [ H : FoldBool.fold_andb_map _ _ _ = true |- List.length _ = List.length _ ]
            => apply FoldBool.fold_andb_map_length in H
          end
        | progress intros
        | apply conj
        | reflexivity
        | (idtac + symmetry); assumption ].

Lemma build_base_runtime_ok t arg_bounds args types PHOAS_args extra
      (H : simplify_base_type t arg_bounds = Success types)
      (Hargs : build_base_runtime t args = Some (PHOAS_args, extra))
      (HPHOAS_args : ZRange.type.base.option.is_bounded_by arg_bounds PHOAS_args = true)
  : exists args',
    args = args' ++ extra
    /\ (forall extra', build_base_runtime t (args' ++ extra') = Some (PHOAS_args, extra'))
    /\ Forall2 val_or_list_val_matches_spec args' types.
Proof using Type.
  revert args extra types H Hargs HPHOAS_args; induction t; intros;
    cbn [simplify_base_type build_base_runtime type.for_each_lhs_of_arrow Language.Compilers.base.interp] in *;
    break_innermost_match_hyps;
    repeat first [ build_runtime_ok_t_step
                 | constructor ].
Qed.

Lemma build_runtime_ok t arg_bounds args types PHOAS_args extra
      (H : simplify_type t arg_bounds = Success types)
      (Hargs : build_runtime t args = Some (PHOAS_args, extra))
      (HPHOAS_args : ZRange.type.option.is_bounded_by arg_bounds PHOAS_args = true)
  : exists args',
    args = args' ++ extra
    /\ (forall extra', build_runtime t (args' ++ extra') = Some (PHOAS_args, extra'))
    /\ Forall2 val_or_list_val_matches_spec args' types.
Proof using Type.
  revert args extra types H Hargs HPHOAS_args; induction t; intros;
    cbn [simplify_type build_runtime type.for_each_lhs_of_arrow] in *;
    [ eapply build_base_runtime_ok; eassumption | discriminate ].
Qed.

Lemma build_input_runtime_ok t arg_bounds args input_types PHOAS_args extra
      (H : simplify_input_type t arg_bounds = Success input_types)
      (Hargs : build_input_runtime t args = Some (PHOAS_args, extra))
      (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
  : exists args',
    args = args' ++ extra
    /\ (forall extra', build_input_runtime t (args' ++ extra') = Some (PHOAS_args, extra'))
    /\ Forall2 val_or_list_val_matches_spec args' input_types.
Proof using Type.
  revert args extra input_types H Hargs HPHOAS_args; induction t as [|t1 ? t2]; intros;
    [ eexists [] | pose proof (build_runtime_ok t1) ];
    cbn [simplify_input_type build_input_runtime type.for_each_lhs_of_arrow] in *;
    repeat first [ build_runtime_ok_t_step
                 | constructor ].
Qed.

Lemma build_input_runtime_ok_nil t arg_bounds args input_types PHOAS_args
      (H : simplify_input_type t arg_bounds = Success input_types)
      (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
      (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
  : Forall2 val_or_list_val_matches_spec args input_types.
Proof using Type.
  pose proof (build_input_runtime_ok t arg_bounds args input_types PHOAS_args [] H Hargs HPHOAS_args).
  destruct_head'_ex; destruct_head'_and; subst; rewrite app_nil_r; assumption.
Qed.

Definition ctx_set (s : symbol) (v : Z) (G : symbol -> option Z) : symbol -> option Z
  := fun idx => if (idx =? s)%N then Some v else G idx.

Module dagG.
  Definition M A := (symbol -> option Z) * dag -> A * ((symbol -> option Z) * dag).
End dagG.

Definition merge_fresh_symbol_G (v : Z) : dagG.M idx
  := fun '(G, d) => let '(idx, d) := merge_fresh_symbol d in (idx, (ctx_set idx v G, d)).

Definition build_inputarray_G (vals : list Z) : dagG.M (list idx)
  := List.foldmap merge_fresh_symbol_G vals.

Fixpoint build_inputs_G (vals : list (Z + list Z))
  : dagG.M (list (idx + list idx))
  := match vals with
     | [] => fun st => ([], st)
     | inr vs :: args
       => fun st
          => let '(idxs, st) := build_inputarray_G vs st in
             let '(rest, st) := build_inputs_G args st in
             (inr idxs :: rest, st)
     | inl v :: args
       => fun st
          => let '(idx, st) := merge_fresh_symbol_G v st in
             let '(rest, st) := build_inputs_G args st in
             (inl idx :: rest, st)
     end.

Fixpoint dag_gensym_n_G (vals : list Z) : dagG.M (list idx)
  := match vals with
     | nil => fun st => ([], st)
     | v :: vs
       => fun st
          => let '(idx, st) := merge_fresh_symbol_G v st in
             let '(rest, st) := dag_gensym_n_G vs st in
             (idx :: rest, st)
     end.

Module G.
  Definition M A := (symbol -> option Z) * symbolic_state -> option (A * ((symbol -> option Z) * symbolic_state)).
  Definition lift {A} (v : Symbolic.M A) : M A
    := fun '(G, s) => match v s with
                      | Success (v, s) => Some (v, (G, s))
                      | Error _ => None
                      end.
  Definition ret {A} (v : A) : M A := fun s => Some (v, s).
  Definition bind {A B} (v : M A) (f : A -> M B) : M B
    := fun s => (v <- v s; let '(v, s) := v in f v s)%option.
End G.
Delimit Scope GM_scope with GM.
Bind Scope GM_scope with G.M.
Notation "x <- y ; f" := (G.bind y (fun x => f%GM)) : GM_scope.

Definition lift_dag_G {A} (v : dagG.M A) : G.M A
  := fun '(G, s) => let '(v, (G, d)) := v (G, s.(dag_state)) in
                    Some (v, (G, update_dag_with s (fun _ => d))).

Definition SetRegFresh_G (r : REG) (v : Z) : G.M idx
  := (idx <- lift_dag_G (merge_fresh_symbol_G v);
      _ <- G.lift (SetReg r idx);
      G.ret idx)%GM.

Fixpoint build_merge_base_addresses_G
         (items : list (idx + list idx)) (reg_available : list REG) (runtime_reg : list Z) {struct items}
  : G.M (list (option idx))
  := match items, reg_available, runtime_reg with
     | [], _, _ | _, [], _ => G.ret []
     | _, _, []
       => fun _ => None
     | inr idxs :: xs, r :: reg_available, rv :: runtime_reg
       => (base <- SetRegFresh_G r rv; (* note: overwrites initial value *)
           addrs <- G.lift (build_merge_array_addresses base idxs);
           rest <- build_merge_base_addresses_G xs reg_available runtime_reg;
           G.ret (Some base :: rest))
     | inl idx :: xs, r :: reg_available, rv :: runtime_reg =>
          (_ <- G.lift (SetReg r idx); (* note: overwrites initial value *)
           rest <- build_merge_base_addresses_G xs reg_available runtime_reg;
           G.ret (None :: rest))
     end%GM%N%x86symex.

Definition build_merge_stack_placeholders_G (rsp_val : Z) (stack_vals : list Z)
  : G.M unit
  := (let stack_size := List.length stack_vals in
      stack_placeholders <- lift_dag_G (build_inputarray_G stack_vals);
      rsp_idx <- SetRegFresh_G rsp rsp_val;
      stack_size <- G.lift (Symbolic.App (zconst 64 (-8 * Z.of_nat stack_size), []));
      stack_base <- G.lift (Symbolic.App (add 64%N, [rsp_idx; stack_size]));
      _ <- G.lift (build_merge_array_addresses stack_base stack_placeholders);
     G.ret tt)%GM.

(* TODO: Move to SymbolicProofs? *)
Local Lemma mapM_Proper_inv {A B B'} R (Hinv : _ -> Prop)
      (f : A -> M B) (f' : A -> M B')
      (Hf : forall a st,
          Hinv st
          -> match f a st, f' a st with
             | Success (v, st), Success (v', st') => R v v' /\ st = st' /\ Hinv st
             | Error err, Error err' => err = err'
             | Success _, Error _ | Error _, Success _ => False
             end)
      (l1 : list A) (l2 : list A) (Hl : l1 = l2)
  : forall st,
    Hinv st
    -> match mapM f l1 st, mapM f' l2 st with
       | Success (v, st), Success (v', st') => Forall2 R v v' /\ st = st' /\ Hinv st
       | Error err, Error err' => err = err'
       | Success _, Error _ | Error _, Success _ => False
       end.
Proof.
  subst l2; induction l1 as [|x xs IHxs]; intros st Hst; cbn [mapM]; cbv [ret]; eauto.
  cbv [Symbolic.bind Crypto.Util.Option.bind ErrorT.bind].
  specialize (Hf x st Hst).
  break_match_hyps; try tauto.
  cbn [fst snd].
  destruct_head'_and; subst.
  let s := match goal with |- context[mapM f xs ?s] => s end in
  specialize (IHxs s ltac:(assumption)).
  break_match_hyps; try tauto.
  repeat first [ progress cbn [fst snd]
               | progress destruct_head'_and
               | progress subst
               | constructor
               | assumption ].
Qed.

(* TODO: Move to SymbolicProofs? *)
Local Lemma mapM_Proper {A B B'} R
      (f : A -> M B) (f' : A -> M B')
      (Hf : forall a st,
          match f a st, f' a st with
          | Success (v, st), Success (v', st') => R v v' /\ st = st'
          | Error err, Error err' => err = err'
          | Success _, Error _ | Error _, Success _ => False
          end)
      (l1 : list A) (l2 : list A) (Hl : l1 = l2)
  : forall st,
    match mapM f l1 st, mapM f' l2 st with
    | Success (v, st), Success (v', st') => Forall2 R v v' /\ st = st'
    | Error err, Error err' => err = err'
    | Success _, Error _ | Error _, Success _ => False
    end.
Proof.
  intro st.
  unshelve epose proof ((fun H => @mapM_Proper_inv A B B' R (fun _ => True) f f' (fun a st _ => H a st (Hf a st)) l1 l2 Hl st I) _) as H'.
  all: intros; break_match; intuition.
Qed.

(* TODO: Move to SymbolicProofs? *)
Local Lemma mapM__Proper_inv {A B B'} (Hinv : _ -> Prop)
      (f : A -> M B) (f' : A -> M B')
      (Hf : forall a st,
          Hinv st
          -> match f a st, f' a st with
             | Success (_, st), Success (_, st') => st = st' /\ Hinv st
             | Error err, Error err' => err = err'
             | Success _, Error _ | Error _, Success _ => False
             end)
      (l1 : list A) (l2 : list A) (Hl : l1 = l2)
  : forall st, Hinv st -> mapM_ f l1 st = mapM_ f' l2 st.
Proof.
  intros st Hst.
  unshelve epose proof ((fun H => @mapM_Proper_inv A B B' (fun _ _ => True) Hinv f f' (fun a st pf => H a st (Hf a st pf)) l1 l2 Hl st Hst) _).
  { intros; break_match; intuition. }
  { cbv [mapM_ Symbolic.bind ErrorT.bind].
    break_match_hyps; destruct_head'_and; subst; cbn [fst snd] in *; intuition. }
Qed.

(* TODO: Move to SymbolicProofs? *)
Local Lemma mapM__Proper {A B B'}
      (f : A -> M B) (f' : A -> M B')
      (Hf : forall a st,
          match f a st, f' a st with
          | Success (_, st), Success (_, st') => st = st'
          | Error err, Error err' => err = err'
          | Success _, Error _ | Error _, Success _ => False
          end)
      (l1 : list A) (l2 : list A) (Hl : l1 = l2)
  : forall st, mapM_ f l1 st = mapM_ f' l2 st.
Proof.
  intro st.
  unshelve epose proof ((fun H => @mapM__Proper_inv A B B' (fun _ => True) f f' (fun a st _ => H a st (Hf a st)) l1 l2 Hl st I) _) as H'.
  all: intros; break_match; intuition.
Qed.

Lemma merge_fresh_symbol_eq_G G d v
      (res := merge_fresh_symbol_G v (G, d))
  : merge_fresh_symbol d = (fst res, snd (snd res)).
Proof.
  subst res; cbv [merge_fresh_symbol_G]; break_innermost_match; reflexivity.
Qed.

Lemma big_old_node_absent n d w args
      (H : forall i r, nth_error d (N.to_nat i) = Some r -> node_ok i r)
      (Hn : (N.of_nat (List.length d) <= n)%N)
  : List.indexof (node_beq N.eqb (old w n, args)) d = None.
Proof.
  revert dependent n; induction d as [|v d IHd] using List.rev_ind; [ reflexivity | ];
    rewrite ?app_length in *; cbn [List.indexof List.length] in *; intros.
  rewrite List.indexof_app.
  rewrite IHd; cbv [Crypto.Util.Option.sequence]; cbv [List.indexof option_map].
  { break_innermost_match; reflect_hyps; subst; try reflexivity.
    specialize (H (N.of_nat (List.length d))).
    rewrite nth_error_app in H; break_innermost_match_hyps; try lia; [].
    rewrite Nat2N.id, Nat.sub_diag in H; specialize (H _ eq_refl _ _ _ eq_refl).
    lia. }
  { intros ? ? Hi; apply H; rewrite nth_error_app, Hi; break_innermost_match; try reflexivity.
    apply nth_error_value_length in Hi; tauto. }
  { lia. }
Qed.

Lemma gensym_node_absent G d w args
      (H : gensym_dag_ok G d)
  : List.indexof (node_beq N.eqb (old w (gensym d), args)) d = None.
Proof.
  apply big_old_node_absent; try apply H.
  cbv [gensym]; reflexivity.
Qed.

Lemma merge_fresh_symbol_G_ok G d v G' d' idx
      (Hd : gensym_dag_ok G d)
      (H : merge_fresh_symbol_G v (G, d) = (idx, (G', d')))
  : eval_idx_Z G' d' idx (Z.land v (Z.ones (Z.of_N 64)))
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  cbv [merge_fresh_symbol_G merge_fresh_symbol merge_symbol merge_node] in *.
  erewrite gensym_node_absent in * by eauto.
  assert (forall e n, eval G d e n -> eval G' d' e n).
  1: inversion_prod; subst; intros e n H; induction H; econstructor.
  all: repeat first [ progress inversion_prod
                    | progress split_and
                    | progress subst
                    | progress destruct_head'_and
                    | progress cbv [eval_idx_Z gensym_dag_ok gensym_ok ctx_set gensym dag_ok node_ok] in *
                    | rewrite Nat2N.id, nth_error_app, Nat.sub_diag
                    | progress break_innermost_match
                    | progress break_innermost_match_hyps
                    | progress inversion_option
                    | lia
                    | progress cbn [nth_error List.map interp_op List.length fst snd] in *
                    | progress reflect_hyps
                    | reflexivity
                    | rewrite app_length
                    | progress intros
                    | rewrite @nth_error_app in *
                    | match goal with
                      | [ H : nth_error ?d ?i = Some _, H' : ~?i < List.length ?d |- _ ]
                        => exfalso; apply nth_error_value_length in H; clear -H H'; tauto
                      | [ H : interp_op _ ?op ?args = Some ?n |- interp_op _ ?op ?args = Some ?n ]
                        => revert H; destruct op; cbn [interp_op]; break_innermost_match
                      | [ H : forall s _v, ?G s = Some _v -> (s < ?v)%N, H' : ?G ?v = Some _ |- _ ]
                        => exfalso; specialize (H _ _ H'); clear -H
                      | [ |- _ /\ _ ] => split
                      | [ |- eval _ (?d ++ _) (ExprRef (N.of_nat (length ?d))) _ ] => econstructor
                      | [ |- Forall2 _ nil _ ] => constructor
                      | [ H : fst ?x = _ |- _ ] => is_var x; destruct x
                      | [ H : _ = snd ?x |- _ ] => is_var x; destruct x
                      | [ H : nth_error (_ :: _) ?x = Some _ |- _ ] => destruct x eqn:?; cbn [nth_error] in H
                      | [ H : nth_error nil ?x = Some _ |- _ ] => destruct x eqn:?; cbn [nth_error] in H
                      | [ H : old _ _ = old _ _ |- _ ] => inversion H; clear H
                      | [ H : ?x - ?y = 0, H' : ~?x < ?y |- _ ] => assert (x = y) by lia; clear H H'
                      | [ H : N.to_nat ?x = ?y |- _ ] => is_var x; assert (x = N.of_nat y) by lia; clear H
                      | [ |- exists v, eval _ (?d ++ _) (ExprRef (N.of_nat (length ?d))) v ]
                        => eexists; econstructor
                      | [ H : Forall2 _ ?xs _ |- Forall2 _ ?xs _ ] => eapply Forall2_weaken; [ | eassumption ]; intuition tauto
                      | [ H : forall i r, nth_error ?d (N.to_nat i) = Some r -> exists v, eval _ ?d (ExprRef i) v,
                            H' : nth_error ?d (N.to_nat ?idx) = Some _
                            |- exists v', eval _ (?d ++ _) (ExprRef ?idx) v' ]
                        => let v := fresh "v" in specialize (H _ _ H'); destruct H as [v H]; exists v
                      end
                    | solve [ eauto ]
                    | solve [ firstorder lia ] ].
Qed.

Local Lemma land_ones_eq_of_bounded v n
      (H : (0 <= v < 2 ^ (Z.of_N n))%Z)
  : Z.land v (Z.ones (Z.of_N n)) = v.
Proof.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma merge_fresh_symbol_G_ok_bounded G d v G' d' idx
      (Hd : gensym_dag_ok G d)
      (H : merge_fresh_symbol_G v (G, d) = (idx, (G', d')))
      (Hv : (0 <= v < 2^64)%Z)
  : eval_idx_Z G' d' idx v
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  replace v with (Z.land v (Z.ones (Z.of_N 64))); [ now apply merge_fresh_symbol_G_ok | rewrite land_ones_eq_of_bounded by assumption ].
  reflexivity.
Qed.

Lemma build_inputarray_eq_G G d vals (len := List.length vals)
  : build_inputarray len d = (fst (build_inputarray_G vals (G, d)), snd (snd (build_inputarray_G vals (G, d)))).
Proof.
  cbv [build_inputarray build_inputarray_G].
  generalize (seq_length len 0); generalize (seq 0 len); subst len; intro l; revert l.
  induction vals, l; cbn [List.length List.foldmap fst snd]; try congruence; try reflexivity.
  intro H; inversion H; clear H; specialize (IHvals _ ltac:(eassumption)).
  rewrite !IHvals; clear IHvals.
  clear dependent l.
  edestruct List.foldmap; destruct_head'_prod; cbn [fst snd].
  repeat f_equal.
  all: erewrite !@merge_fresh_symbol_eq_G; cbn [fst snd]; reflexivity.
Qed.


Lemma build_inputarray_G_ok G d vals G' d' ia
      (Hd : gensym_dag_ok G d)
      (H : build_inputarray_G vals (G, d) = (ia, (G', d')))
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) vals)
  : Forall2 (eval_idx_Z G' d') ia vals
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  cbv [build_inputarray_G] in *.
  revert ia G d G' d' Hd H.
  induction vals as [|v vals IHvals], ia as [|i ia]; cbn [List.foldmap]; intros;
    inversion_prod; subst; eauto; try congruence.
  { set (res := List.foldmap _ _ _) in *.
    destruct res eqn:Hres; subst res; destruct_head'_prod; cbn [fst snd] in *.
    inversion Hbounds; subst.
    specialize (IHvals ltac:(assumption) _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    repeat first [ progress subst
                 | progress destruct_head'_and
                 | match goal with
                   | [ H : ?x :: ?xs = ?y :: ?ys |- _ ] => assert (x = y /\ xs = ys) by (now inversion H; split); clear H
                   end ].
    let lem := match goal with |- context[merge_fresh_symbol_G ?v (?G, ?d)] => constr:(merge_fresh_symbol_G_ok_bounded G d v) end in
    pose proof (lem _ _ _ ltac:(assumption) ltac:(repeat rewrite <- surjective_pairing; reflexivity) ltac:(lia)).
    repeat first [ progress subst
                 | progress destruct_head'_and
                 | assumption
                 | solve [ eauto ]
                 | match goal with
                   | [ |- _ /\ _ ] => split
                   | [ |- Forall2 _ (_ :: _) (_ :: _) ] => constructor
                   | [ H : Forall2 _ ?l1 ?l2 |- Forall2 _ ?l1 ?l2 ] => eapply Forall2_weaken; [ clear H | exact H ]
                   | [ |- forall a b, eval_idx_Z _ _ a b -> eval_idx_Z _ _ a b ] => apply lift_eval_idx_Z_impl
                   end ]. }
Qed.

Lemma build_inputarray_ok G d len idxs args d'
      (d_ok : gensym_dag_ok G d)
      (H : build_inputarray len d = (idxs, d'))
      (Hargs : List.length args = len)
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) args)
  : exists G',
    Forall2 (eval_idx_Z G' d') idxs args
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  subst len; erewrite build_inputarray_eq_G in H; inversion_prod.
  eexists; eapply build_inputarray_G_ok; try eassumption.
  repeat first [ eassumption | apply path_prod | reflexivity ].
Qed.

Lemma dag_gensym_n_eq_G G d vals (len := List.length vals)
  : dag_gensym_n len d = (fst (dag_gensym_n_G vals (G, d)), snd (snd (dag_gensym_n_G vals (G, d)))).
Proof.
  subst len.
  revert G d; induction vals as [|v vals IHvals]; cbn [dag_gensym_n dag_gensym_n_G fst snd List.length]; [ reflexivity | ]; intros.
  cbv [dag.bind dag.ret]; eta_expand; cbn [fst snd].
  erewrite !@merge_fresh_symbol_eq_G, IHvals; cbn [fst snd]; eta_expand; reflexivity.
Qed.

Lemma dag_gensym_n_G_ok G d vals G' d' ia
      (Hd : gensym_dag_ok G d)
      (H : dag_gensym_n_G vals (G, d) = (ia, (G', d')))
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) vals)
  : Forall2 (eval_idx_Z G' d') ia vals
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  revert ia G d G' d' Hd H.
  induction vals as [|v vals IHvals], ia as [|i ia]; cbn [dag_gensym_n_G]; intros;
    try solve [ inversion_prod; subst; eta_expand; cbn [fst snd] in *; eauto; try congruence ].
  { break_innermost_match_hyps.
    inversion Hbounds; subst; clear Hbounds.
    destruct_head'_prod.
    specialize (fun H => IHvals ltac:(assumption) _ _ _ _ _ H ltac:(eassumption)).
    match goal with H : pair _ _ = pair _ _ |- _ => inversion H; clear H end; subst.
    let lem := match goal with H : context[merge_fresh_symbol_G ?v (?G, ?d)] |- _ => constr:(merge_fresh_symbol_G_ok_bounded G d v) end in
    pose proof (lem _ _ _ ltac:(assumption) ltac:(eassumption) ltac:(lia)).
    destruct_head'_and; specialize_by_assumption.
    repeat first [ progress subst
                 | progress destruct_head'_and
                 | assumption
                 | solve [ eauto ]
                 | match goal with
                   | [ |- _ /\ _ ] => split
                   | [ |- Forall2 _ (_ :: _) (_ :: _) ] => constructor
                   | [ H : Forall2 _ ?l1 ?l2 |- Forall2 _ ?l1 ?l2 ] => eapply Forall2_weaken; [ clear H | exact H ]
                   | [ |- forall a b, eval_idx_Z _ _ a b -> eval_idx_Z _ _ a b ] => apply lift_eval_idx_Z_impl
                   | [ |- eval_idx_Z _ _ _ _ ] => eapply lift_eval_idx_Z_impl; now eauto
                   end ]. }
Qed.

Lemma dag_gensym_n_ok G d len idxs args d'
      (d_ok : gensym_dag_ok G d)
      (H : dag_gensym_n len d = (idxs, d'))
      (Hargs : List.length args = len)
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) args)
  : exists G',
    Forall2 (eval_idx_Z G' d') idxs args
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  subst len; erewrite dag_gensym_n_eq_G in H; inversion_prod.
  eexists; eapply dag_gensym_n_G_ok; try eassumption.
  repeat first [ eassumption | apply path_prod | reflexivity ].
Qed.

Definition type_spec_of_runtime {A} (ls : list (A + list A)) : list (option nat)
  := List.map (fun v => match v with inl _ => None | inr ls => Some (List.length ls) end) ls.

Lemma type_spec_of_runtime_val_or_list_val_matches_spec vals types
  : types = type_spec_of_runtime vals <-> Forall2 val_or_list_val_matches_spec vals types.
Proof.
  split.
  { intro; subst; induction vals; cbn; constructor; break_innermost_match; cbn; eauto. }
  { intro H; induction H;
    repeat (subst || cbn in * || destruct_head' option || break_innermost_match || intuition). }
Qed.

Lemma build_inputs_eq_G G d vals (types := type_spec_of_runtime vals)
  : build_inputs types d = (fst (build_inputs_G vals (G, d)), snd (snd (build_inputs_G vals (G, d)))).
Proof.
  revert G d; subst types; induction vals as [|v vals IHvals]; [ reflexivity | ].
  cbn [build_inputs type_spec_of_runtime List.map build_inputs_G]; fold (type_spec_of_runtime vals); intros.
  cbv [dag.bind dag.ret]; break_innermost_match; destruct_head'_prod; cbn [fst snd].
  all: repeat first [ progress cbn [fst snd] in *
                    | progress subst
                    | reflexivity
                    | match goal with
                      | [ H : pair _ _ = pair _ _ |- _ ] => inversion H; clear H
                      | [ H : merge_fresh_symbol _ = _, H' : merge_fresh_symbol_G _ _ = _ |- _ ] => erewrite merge_fresh_symbol_eq_G, H' in H
                      | [ H : build_inputarray _ _ = _, H' : build_inputarray_G _ _ = _ |- _ ] => erewrite build_inputarray_eq_G, H' in H
                      | [ H : build_inputs _ _ = _, H' : build_inputs_G _ _ = _ |- _ ] => erewrite IHvals, H' in H
                      end ].
Qed.

Lemma build_inputs_G_ok G d vals G' d' inputs
      (Hd : gensym_dag_ok G d)
      (H : build_inputs_G vals (G, d) = (inputs, (G', d')))
      (Hbounds : Forall (fun v => match v with
                                  | inl v => (0 <= v < 2^64)%Z
                                  | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                                  end) vals)
  : Forall2 (eval_idx_or_list_idx G' d') inputs vals
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  revert inputs G d G' d' Hd H.
  induction vals as [|v vals IHvals], inputs as [|i inputs]; cbn [build_inputs_G]; intros;
    inversion_prod; subst; eauto; try (break_innermost_match; cbn [fst snd] in *; congruence).
  { break_innermost_match; destruct_head'_prod; cbn [fst snd] in *.
    all: repeat first [ progress subst
                      | progress destruct_head'_and
                      | solve [ eauto ]
                      | match goal with
                        | [ H : ?x :: ?xs = ?y :: ?ys |- _ ] => assert (x = y /\ xs = ys) by (now inversion H; split); clear H
                        | [ H : merge_fresh_symbol_G _ _ = _ |- _ ] => apply merge_fresh_symbol_G_ok_bounded in H; [ | (assumption  + lia) .. ]
                        | [ H : build_inputarray_G _ _ = _ |- _ ] => apply build_inputarray_G_ok in H; [ | assumption .. ]
                        | [ H : build_inputs_G _ _ = _ |- _ ] => apply IHvals in H; [ | assumption .. ]
                        | [ H : Forall _ (_ :: _) |- _ ] => inversion H; clear H
                        | [ |- _ /\ _ ] => split
                        | [ |- Forall2 _ (_ :: _) (_ :: _) ] => constructor
                        | [ H : eval_idx_Z _ _ ?e ?n |- eval_idx_Z _ _ ?e ?n ] => revert H; apply lift_eval_idx_Z_impl; assumption
                        | [ H : Forall2 (eval_idx_Z _ _) ?e ?n |- Forall2 (eval_idx_Z _ _) ?e ?n ] => revert H; apply Forall2_weaken, lift_eval_idx_Z_impl; assumption
                        end
                      | progress cbv [eval_idx_or_list_idx] ]. }
Qed.

Lemma build_inputs_ok G d types inputs args d'
      (d_ok : gensym_dag_ok G d)
      (H : build_inputs types d = (inputs, d'))
      (Hbounds : Forall (fun v => match v with
                                  | inl v => (0 <= v < 2^64)%Z
                                  | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                                  end) args)
      (Hargs : Forall2 val_or_list_val_matches_spec args types)
  : exists G',
    Forall2 (eval_idx_or_list_idx G' d') inputs args
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  apply type_spec_of_runtime_val_or_list_val_matches_spec in Hargs; subst types.
  erewrite build_inputs_eq_G in H; inversion_prod.
  eexists; eapply build_inputs_G_ok; try eassumption.
  repeat first [ eassumption | apply path_prod | reflexivity ].
Qed.

Lemma lift_dag_eq_G {A} G v_G v s s' res
      (Hv : v s.(dag_state) = (fst (v_G (G, s.(dag_state))), snd (snd (v_G (G, s.(dag_state))))))
      (H : lift_dag v s = Success (res, s'))
  : exists G',
    @lift_dag_G A v_G (G, s) = Some (res, (G', s')).
Proof.
  revert H; cbv [lift_dag lift_dag_G] in *; break_innermost_match.
  intros; inversion_ErrorT; inversion_option; inversion_prod; subst.
  set (vs := v s) in *; clearbody vs; clear v; destruct vs; cbn [fst snd] in *; subst.
  eexists; reflexivity.
Qed.

Lemma SetRegFresh_eq_G G r s v idx s'
      (H : SetRegFresh r s = Success (idx, s'))
  : exists G',
    SetRegFresh_G r v (G, s) = Some (idx, (G', s')).
Proof.
  revert H; cbv [SetRegFresh SetRegFresh_G G.bind Symbolic.bind ErrorT.bind Crypto.Util.Option.bind G.lift Symbolic.ret G.ret].
  repeat first [ progress inversion_ErrorT
               | progress inversion_option
               | progress subst
               | progress destruct_head'_ex
               | progress cbn [fst snd] in *
               | progress inversion_prod
               | eexists; reflexivity
               | discriminate
               | match goal with
                 | [ H : lift_dag _ _ = Success _ |- _ ]
                   => eapply lift_dag_eq_G in H; [ | clear H ]
                 | [ H : ?x = _, H' : ?x = _ |- _ ] => rewrite H in H'
                 | [ H : lift_dag_G ?x ?y = _, H' : lift_dag_G ?x' ?y' = _ |- _ ]
                   => unify x x'; unify y y'; rewrite H in H'
                 end
               | break_innermost_match_step
               | progress intros
               | apply merge_fresh_symbol_eq_G
               | progress destruct_head'_prod ].
Qed.

Lemma build_merge_base_addresses_eq_G G items reg_available runtime_reg s res s'
      (Hreg : Nat.min (List.length items) (List.length reg_available) <= List.length runtime_reg)
      (H : build_merge_base_addresses items reg_available s = Success (res, s'))
  : exists G',
    build_merge_base_addresses_G items reg_available runtime_reg (G, s) = Some (res, (G', s')).
Proof.
  move H at top; move items at top; repeat match goal with H : _ |- _ => revert H end.
  induction items as [|? ? IH]; cbn [build_merge_base_addresses build_merge_base_addresses_G].
  all: cbv [G.ret Symbolic.ret Symbolic.bind ErrorT.bind G.bind Crypto.Util.Option.bind G.lift]; intros.
  all: repeat first [ progress destruct_head'_ex
                    | match goal with
                      | [ H : SetRegFresh _ _ = Success _ |- _ ]
                        => eapply SetRegFresh_eq_G in H
                      | [ H : SetRegFresh_G ?r ?v ?s = _, H' : SetRegFresh_G ?r' ?v' ?s' = _ |- _ ]
                        => unify r r'; unify v v'; unify s s'; rewrite H in H'
                      end
                    | progress subst
                    | progress inversion_ErrorT
                    | progress inversion_option
                    | progress inversion_prod
                    | eexists; reflexivity
                    | progress cbn [List.length fst snd] in *
                    | discriminate
                    | break_innermost_match_step
                    | break_innermost_match_hyps_step
                    | progress specialize_by_assumption
                    | progress destruct_head'_ex
                    | rewrite <- Nat.succ_min_distr in *
                    | exfalso; (assumption + lia)
                    | match goal with
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ [] _ |- _ ] => inversion H; clear H
                      | [ H : S ?x <= S ?y |- _ ] => assert (x <= y) by lia; clear H
                      | [ H : build_merge_base_addresses _ _ _ = _ |- _ ]
                        => specialize (IH _ _ _ _ H)
                      | [ IH : forall G rr, _ -> exists G', build_merge_base_addresses_G ?it ?ra rr (G, ?s) = _,
                            H' : build_merge_base_addresses_G ?it ?ra ?rrv (?Gv, ?s) = _ |- _ ]
                        => specialize (IH Gv rrv)
                      | [ H : ?x = _, H' : ?x = _ |- _ ] => rewrite H in H'
                      | [ H : context[match mapM ?f ?l ?s with _ => _ end] |- context[match mapM ?f ?l ?s with _ => _ end] ]
                        => destruct (mapM f l s) eqn:?
                      end
                    | progress destruct_head'_prod ].
Qed.

Lemma build_merge_stack_placeholders_eq_G G rsp_val stack_vals s res s'
      (H : build_merge_stack_placeholders (List.length stack_vals) s = Success (res, s'))
  : exists G',
    build_merge_stack_placeholders_G rsp_val stack_vals (G, s) = Some (res, (G', s')).
Proof.
  revert H; cbv [build_merge_stack_placeholders_G build_merge_stack_placeholders G.bind G.ret Crypto.Util.Option.bind Symbolic.bind ErrorT.bind G.lift Symbolic.ret].
  repeat first [ progress intros
               | progress cbn [fst snd] in *
               | progress subst
               | progress inversion_ErrorT
               | progress inversion_option
               | progress destruct_head'_prod
               | progress subst_prod
               | progress destruct_head'_ex
               | eexists; reflexivity
               | match goal with
                 | [ H : SetRegFresh _ _ = Success _ |- _ ]
                   => eapply SetRegFresh_eq_G in H
                 | [ H : SetRegFresh_G ?r ?v ?s = _, H' : SetRegFresh_G ?r' ?v' ?s' = _ |- _ ]
                   => unify r r'; unify v v'; unify s s'; rewrite H in H'
                 | [ H : lift_dag _ _ = Success _ |- _ ]
                   => eapply lift_dag_eq_G in H; [ | clear H ]
                 | [ H : lift_dag_G ?x ?y = _, H' : lift_dag_G ?x' ?y' = _ |- _ ]
                   => unify x x'; unify y y'; rewrite H in H'
                 | [ H : ?x = Success _ |- context[?x] ] => rewrite H
                 end
               | apply build_inputarray_eq_G
               | break_innermost_match_hyps_step
               | break_innermost_match_step ].
Qed.

Lemma SetReg_ok G s s' reg idx rn lo sz v
      (Hreg : index_and_shift_and_bitcount_of_reg reg = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : SetReg reg idx s = Success (tt, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hidx : eval_idx_Z G d idx v)
  : ((exists idx',
         set_reg r rn idx' = r'
         /\ eval_idx_Z G d' idx' (Z.land v (Z.ones 64)))
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv [SetReg Symbolic.bind ErrorT.bind Crypto.Util.Option.bind GetReg SetReg64] in *.
  break_match_hyps.
  all: repeat first [ progress inversion_option
                    | progress cbn [fst snd dag_state symbolic_reg_state symbolic_flag_state symbolic_mem_state] in *
                    | progress subst
                    | progress inversion_prod
                    | progress destruct_head'_prod
                    | progress destruct_head'_and
                    | progress inversion_ErrorT
                    | progress reflect_hyps
                    | tauto
                    | progress cbv [update_reg_with]
                    | match goal with
                      | [ H := _ |- _ ] => subst H
                      end ].
  (* dealing with App *)
  cbv [Symbolic.App Merge] in *.
  (* need to do this early to deal with conversion slowness *)
  repeat match goal with
         | [ H : context[simplify ?s ?n] |- _ ]
           => unshelve epose proof (@eval_simplify _ s n _ _); shelve_unifiable;
              [ solve [ repeat first [ eassumption | exactly_once econstructor ] ] | ];
              generalize dependent (simplify s n); intros
         | [ H : context[merge ?e ?d] |- _ ]
           => pose proof (@eval_merge _ e _ d ltac:(eassumption) ltac:(eassumption));
              generalize dependent (merge e d); intros
         end.
  repeat first [ progress inversion_ErrorT
               | progress inversion_prod
               | progress subst
               | progress destruct_head'_and
               | progress cbn [fst snd dag_state symbolic_reg_state symbolic_flag_state symbolic_mem_state] in *
               | progress cbv [update_dag_with eval_idx_Z] in *
               | solve [ eauto ]
               | apply conj
               | eapply ex_intro ].
Qed.

Lemma SetReg_ok_bounded G s s' reg idx rn lo sz v
      (Hreg : index_and_shift_and_bitcount_of_reg reg = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : SetReg reg idx s = Success (tt, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hidx : eval_idx_Z G d idx v)
      (Hv : (0 <= v < 2^64)%Z)
  : ((exists idx',
         set_reg r rn idx' = r'
         /\ eval_idx_Z G d' idx' v)
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  replace v with (Z.land v (Z.ones (Z.of_N 64))); [ eapply SetReg_ok; eassumption | rewrite land_ones_eq_of_bounded by assumption ].
  reflexivity.
Qed.

Lemma SetRegFresh_G_ok G G' s s' reg idx rn lo sz v
      (Hreg : index_and_shift_and_bitcount_of_reg reg = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : SetRegFresh_G reg v (G, s) = Some (idx, (G', s')))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
  : (eval_idx_Z G' d' idx (Z.land v (Z.ones 64))
     /\ (exists idx',
            set_reg r rn idx' = r'
            /\ eval_idx_Z G' d' idx' (Z.land v (Z.ones 64)))
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  cbv [SetRegFresh_G lift_dag_G G.lift G.bind Crypto.Util.Option.bind G.ret] in H.
  break_innermost_match_hyps; inversion_option; [].
  repeat first [ progress inversion_option
               | progress subst
               | progress destruct_head'_and
               | progress destruct_head'_ex
               | progress destruct_head'_unit
               | progress subst_prod
               | progress cbv [update_dag_with] in *
               | progress cbn [dag_state symbolic_reg_state symbolic_flag_state symbolic_mem_state] in *
               | rewrite Z.land_same_r in *
               | solve [ cbv [eval_idx_Z] in *; eauto ]
               | match goal with
                 | [ H := _ |- _ ] => subst H
                 | [ H : merge_fresh_symbol_G _ _ = _ |- _ ]
                   => apply merge_fresh_symbol_G_ok in H; [ | assumption .. ]
                 | [ H : SetReg _ _ _ = _ |- _ ]
                   => eapply SetReg_ok in H;
                      [ | first [ eassumption | reflexivity ] .. ]
                 end
               | apply conj
               | eapply ex_intro ].
Qed.

Lemma SetRegFresh_G_ok_bounded G G' s s' reg idx rn lo sz v
      (Hreg : index_and_shift_and_bitcount_of_reg reg = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : SetRegFresh_G reg v (G, s) = Some (idx, (G', s')))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hv : (0 <= v < 2^64)%Z)
  : (eval_idx_Z G' d' idx v
     /\ (exists idx',
            set_reg r rn idx' = r'
            /\ eval_idx_Z G' d' idx' v)
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  replace v with (Z.land v (Z.ones (Z.of_N 64))); [ eapply SetRegFresh_G_ok; eassumption | rewrite land_ones_eq_of_bounded by assumption ].
  reflexivity.
Qed.

Lemma GetReg_ok G s s' reg idx rn lo sz v
      (Hreg : index_and_shift_and_bitcount_of_reg reg = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : GetReg reg s = Success (idx, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hr : forall idx', get_reg r rn = Some idx' -> eval_idx_Z G d idx' v)
  : ((exists idx',
         get_reg r rn = Some idx'
         /\ eval_idx_Z G d idx' v)
     /\ eval_idx_Z G d' idx (Z.land v (Z.ones 64))
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv [GetReg GetReg64 some_or Symbolic.bind ErrorT.bind Symbolic.App Merge] in *.
  subst sz.
  assert (lo = 0%N) by (
      clear -Hreg; inversion_prod; subst;
      destruct reg; vm_compute in *; try reflexivity; discriminate
    ).
  subst lo.
  rewrite Hreg in *.
  break_innermost_match_hyps; cbn [fst snd] in *; inversion_ErrorT.
  specialize (Hr _ ltac:(eassumption)).
  (* need to do this early to deal with conversion slowness *)
  repeat match goal with
         | [ H : context[simplify ?s ?n] |- _ ]
           => unshelve epose proof (@eval_simplify _ s n _ _); shelve_unifiable;
              [ solve [ repeat first [ eassumption | exactly_once econstructor ] ] | ];
              generalize dependent (simplify s n); intros
         | [ H : context[merge ?e ?d] |- _ ]
           => pose proof (@eval_merge _ e _ d ltac:(eassumption) ltac:(eassumption));
              generalize dependent (merge e d); intros
         end.
  all: repeat first [ progress inversion_ErrorT
                    | progress inversion_prod
                    | progress subst
                    | progress destruct_head'_and
                    | progress destruct_head'_prod
                    | progress cbv [update_dag_with eval_idx_Z] in *
                    | progress cbn [fst snd dag_state symbolic_reg_state symbolic_flag_state symbolic_mem_state] in *
                    | solve [ eauto ]
                    | match goal with
                      | [ H := _ |- _ ] => subst H
                      end
                    | apply conj
                    | eapply ex_intro ].
Qed.

Lemma GetReg_ok_bounded G s s' reg idx rn lo sz v
      (Hreg : index_and_shift_and_bitcount_of_reg reg = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : GetReg reg s = Success (idx, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hr : forall idx', get_reg r rn = Some idx' -> eval_idx_Z G d idx' v)
      (Hv : (0 <= v < 2^64)%Z)
  : ((exists idx',
         get_reg r rn = Some idx'
         /\ eval_idx_Z G d idx' v)
     /\ eval_idx_Z G d' idx v
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  replace v with (Z.land v (Z.ones (Z.of_N 64))) at 1; [ eapply GetReg_ok; eassumption | rewrite land_ones_eq_of_bounded by assumption ].
  reflexivity.
Qed.

Local Lemma mapM_ok_via_upd
      G {A B} (f : A -> M B) ls s v s'
      (H : mapM f ls s = Success (v, s'))
      upd_mem upd_reg upd_flag (R_static : _ -> Prop) (R_inv : _ -> Prop) (R : _ -> _ -> _ -> Prop)
      (d := s.(dag_state))
      (d' := s'.(dag_state))

      (Hd : gensym_dag_ok G d)
      (Hf : forall s' s'' x v,
          let d' := s'.(dag_state) in
          let d'' := s''.(dag_state) in
          f x s' = Success (v, s'')
          -> gensym_dag_ok G s'
          -> R_inv s'
          -> R_static x
          -> (forall e n, eval G d e n -> eval G d' e n)
          -> upd_mem s'.(symbolic_mem_state) (x, v) = s''.(symbolic_mem_state)
             /\ upd_reg s'.(symbolic_reg_state) (x, v) = s''.(symbolic_reg_state)
             /\ upd_flag s'.(symbolic_flag_state) (x, v) = s''.(symbolic_flag_state)
             /\ (forall e n, eval G d' e n -> eval G d'' e n)
             /\ R s'' x v
             /\ (forall x v, R s' x v -> R s'' x v)
             /\ gensym_dag_ok G s''
             /\ R_inv s'')
      (Hinv : R_inv s)
      (Hstatic : Forall R_static ls)
  : ((Forall2 (R s') ls v
      /\ fold_left upd_mem (List.combine ls v) s.(symbolic_mem_state) = s'.(symbolic_mem_state)
      /\ fold_left upd_reg (List.combine ls v) s.(symbolic_reg_state) = s'.(symbolic_reg_state)
      /\ fold_left upd_flag (List.combine ls v) s.(symbolic_flag_state) = s'.(symbolic_flag_state)
      /\ forall x v, R s x v -> R s' x v)
     /\ R_inv s')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv beta iota zeta in *.
  subst d d'.
  revert v s' H.
  remember s as s0 eqn:Hs in |- *.
  assert (Hs0 : forall e n, eval G s e n -> eval G s0 e n) by now subst s0.
  assert (Hd0 : gensym_dag_ok G s0) by now subst s0.
  assert (Hinv0 : R_inv s0) by now subst s0.
  clear Hs; revert s0 Hs0 Hd0 Hinv0.
  induction ls as [|x xs IHxs]; cbn [mapM]; cbv [ret Symbolic.bind ErrorT.bind].
  { intros; inversion_ErrorT; inversion_prod; subst; cbn [fold_left]; eauto 10. }
  { repeat first [ progress intros
                 | progress inversion_ErrorT
                 | progress inversion_prod
                 | progress subst
                 | progress break_innermost_match_hyps
                 | progress destruct_head'_prod
                 | progress cbn [fst snd fold_left] in *
                 | match goal with
                   | [ H : Forall _ (_ :: _) |- _ ] => inversion H; clear H
                   end ].
    specialize (Hf _ _ _ _ ltac:(eassumption)); specialize_by_assumption.
    destruct_head'_and; subst.
    unshelve epose proof (IHxs _ _ _ _ _ _ ltac:(eassumption)) as IHxs'; clear IHxs; eauto; [].
    cbn [List.combine fold_left].
    destruct_head'_and; repeat first [ solve [ eauto ] | apply conj ].
    all: destruct_head symbolic_state; subst; reflexivity. }
Qed.

(* TODO: this is Symbolic.get_reg; move to SymbolicProofs? *)
Local Lemma get_reg_set_reg_full s rn rn' v
  : get_reg (set_reg s rn v) rn'
    = if ((rn <? ((fun n (_ : Tuple.tuple _ n) => n) _ s)) && (rn =? rn'))%nat%bool
      then Some v
      else get_reg s rn'.
Proof.
  cbv [get_reg set_reg].
  break_innermost_match; split_andb; reflect_hyps; subst.
  all: rewrite <- !Tuple.nth_default_to_list.
  all: rewrite ?@Tuple.length_to_list in *.
  all: unshelve erewrite Tuple.from_list_default_eq, Tuple.to_list_from_list, set_nth_nth_default_full;
    rewrite ?length_set_nth, ?Tuple.length_to_list; try easy.
  all: break_innermost_match; try lia; try reflexivity.
  now rewrite nth_default_out_of_bounds by now rewrite Tuple.length_to_list; lia.
Qed.

(* TODO: this is Symbolic.get_reg; move to SymbolicProofs? *)
Local Lemma get_reg_set_reg_same s rn v
      (H : (rn < (fun n (_ : Tuple.tuple _ n) => n) _ s)%nat)
  : get_reg (set_reg s rn v) rn = Some v.
Proof.
  rewrite get_reg_set_reg_full; break_innermost_match; reflect_hyps; cbv beta in *; try reflexivity; lia.
Qed.

Lemma compute_array_address_ok G s s' base i idx base_val
      (H : compute_array_address base i s = Success (idx, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hidx : eval_idx_Z G d base base_val)
  : (eval_idx_Z G d' idx (Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64))
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv [compute_array_address Symbolic.App Merge Symbolic.bind] in H.
  subst d d'.
  repeat first [ progress inversion_ErrorT
               | progress destruct_head'_prod
               | progress inversion_option
               | progress cbn [fst snd] in *
               | progress destruct_head'_and
               | progress cbv [update_dag_with] in *
               | match goal with
                 | [ H : ErrorT.bind ?x _ = _ |- _ ]
                   => destruct x eqn:?; unfold ErrorT.bind at 1 in H
                 | [ H : ?v = Success _ |- _ ]
                   => match v with
                      | context[match ?x with Some _ => _ | _ => _ end]
                        => destruct x eqn:?
                      end
                 end ].
  (* need to do this early to deal with conversion slowness *)
  repeat first [ match goal with
                 | [ H : context[simplify ?s ?n] |- _ ]
                   => unshelve epose proof (@eval_simplify _ s n _ _); shelve_unifiable;
                      [ solve [ repeat first [ eassumption | solve [ eauto ] | exactly_once econstructor ] ] | ];
                      generalize dependent (simplify s n); intros
                 | [ H : context[merge ?e ?d] |- _ ]
                   => pose proof (@eval_merge _ e _ d ltac:(eassumption) ltac:(eassumption));
                      generalize dependent (merge e d); intros
                 | [ H : (?x, ?y) = (?z, ?w) |- _ ] => is_var x; is_var z; is_var w; inversion H; clear H
                 end
               | progress destruct_head'_prod
               | progress destruct_head'_and
               | progress subst
               | progress cbn [fst snd symbolic_reg_state symbolic_flag_state symbolic_mem_state dag_state fold_right] in *
               | break_innermost_match_hyps_step ].
  all: repeat first [ solve [ eauto 10 ]
                    | apply conj
                    | progress cbv [eval_idx_Z]
                    | match goal with
                      | [ H : eval ?G ?d ?e ?v |- eval ?G ?d' ?e ?v' ]
                        => cut (v' = v);
                           [ solve [ intros ->; eauto 10 ]
                           | ]
                      end
                    | progress change (Z.of_N 64) with 64%Z
                    | rewrite !Z.land_ones by lia
                    | progress autorewrite with zsimplify_const
                    | progress (push_Zmod; pull_Zmod) ].
Qed.

Lemma compute_array_address_ok_bounded G s s' base i idx base_val
      (H : compute_array_address base i s = Success (idx, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hidx : eval_idx_Z G d base base_val)
      (Hv : (0 <= base_val + 8 * Z.of_nat i < 2^64)%Z)
  : (eval_idx_Z G d' idx (base_val + 8 * Z.of_nat i)
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  set (v := (base_val + 8 * Z.of_nat i)%Z) in *.
  replace v with (Z.land v (Z.ones (Z.of_N 64))); [ eapply compute_array_address_ok; eassumption | rewrite land_ones_eq_of_bounded by assumption ].
  reflexivity.
Qed.

Lemma build_merge_array_addresses_ok G s s'
      base base_val items addrs
      (H : build_merge_array_addresses base items s = Success (addrs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (addrs_vals := List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length items)))
      (Hbase : eval_idx_Z G d base base_val)
  : (r = r'
     /\ f = f'
     /\ (Forall2 (eval_idx_Z G d') addrs addrs_vals
         /\ (* TODO: Is this too specific a spec? *) List.rev (List.combine addrs items) ++ m = m'))
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv [build_merge_array_addresses ret Symbolic.bind ErrorT.bind Crypto.Util.Option.bind] in H.
  apply (@mapM_ok_via_upd G) with
    (upd_mem := fun st v => cons (let '((i, array_val_idx), array_addr_idx) := ((fst (fst v), snd (fst v)), snd v) in (array_addr_idx, array_val_idx)) st)
    (R_inv := fun st => eval_idx_Z G st base base_val)
    (R_static := fun _ => True)
    (R := fun st i_array_val_idx array_addr_idx
          => eval_idx_Z G st.(dag_state) array_addr_idx (Z.land (base_val + 8 * Z.of_nat (fst (i_array_val_idx))) (Z.ones 64)))
    (upd_flag := fun st _ => st)
    (upd_reg := fun st _ => st)
    in H;
    [ | clear H .. ].
  all: repeat first [ progress inversion_option
                    | progress inversion_ErrorT
                    | progress subst
                    | progress destruct_head'_and
                    | progress destruct_head'_prod
                    | progress subst_prod
                    | progress cbn [fst snd dag_state update_dag_with update_mem_with symbolic_reg_state symbolic_flag_state symbolic_mem_state] in *
                    | progress destruct_head'_ex
                    | assumption
                    | progress intros
                    | solve [ eauto ]
                    | rewrite @fold_left_id in *
                    | match goal with
                      | [ H : compute_array_address _ _ _ = _ |- _ ]
                        => eapply compute_array_address_ok in H; [ | solve [ eassumption | cbv [eval_idx_Z] in *; eauto ] .. ]
                      | [ H := _ |- _ ] => assert_fails constr_eq H offset; subst H
                      | [ H : context[match ?x with Success _ => _ | _ => _ end] |- _ ] => destruct x eqn:?
                      | [ |- Forall (fun _ => True) _ ] => rewrite Forall_forall
                      end ].
  { cbv [eval_idx_Z update_mem_with symbolic_reg_state dag_state symbolic_mem_state symbolic_flag_state update_dag_with reg_index] in *; destruct_head' symbolic_state; subst.
    repeat (apply conj; eauto; []).
    setoid_rewrite <- fold_left_map with (f:=fun xs x => cons x xs).
    rewrite <- (map_swap_combine (enumerate _)), List.map_map; cbn [fst snd]; cbv [enumerate] in *.
    rewrite <- combine_map_r, map_snd_combine, seq_length, List.firstn_all, fold_left_cons.
    repeat esplit; eauto using Forall2_weaken;
      try solve [ eapply Forall2_weaken; [ | eassumption ]; eauto ];
      [].
    rewrite Forall2_map_r_iff.
    apply Forall2_flip.
    replace (seq 0 (length items)) with (List.map fst (enumerate items))
      by now cbv [enumerate]; rewrite map_fst_combine, firstn_all2 by now rewrite seq_length.
    cbv [enumerate] in *.
    rewrite Forall2_map_l_iff; eapply Forall2_weaken; [ | eassumption ]; intros *; cbv beta.
    rewrite !Z.land_ones by lia; push_Zmod; pull_Zmod.
    trivial. }
  { (* addressing / loop body *)
    cbv [eval_idx_Z update_mem_with symbolic_reg_state dag_state symbolic_mem_state symbolic_flag_state update_dag_with reg_index] in *; destruct_head' symbolic_state; subst.
    eauto 20. }
Qed.

(* TODO: move or remove *)
Lemma Address_ok G s s' (sa:AddressSize:=64%N) a rn lo sz idx base_val
      (Hreg : index_and_shift_and_bitcount_of_reg (mem_reg a) = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : @Address sa a s = Success (idx, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hr : forall idx', get_reg r rn = Some idx' -> eval_idx_Z G d idx' base_val)
      (Hindex : mem_extra_reg a = None)
      (offset := match mem_offset a with
                 | Some s => s
                 | None => 0%Z
                 end)
  : (eval_idx_Z G d' idx (Z.land (base_val + offset) (Z.ones 64))
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv [Address Symbolic.App Merge Symbolic.bind] in H.
  subst sa offset d d'.
  repeat first [ progress inversion_ErrorT
               | progress destruct_head'_prod
               | progress inversion_option
               | progress cbn [fst snd] in *
               | progress destruct_head'_and
               | progress cbv [update_dag_with] in *
               | match goal with
                 | [ H : GetReg _ _ = _ |- _ ]
                   => eapply GetReg_ok in H; [ | eassumption .. ]
                 | [ H : ErrorT.bind ?x _ = _ |- _ ]
                   => destruct x eqn:?; unfold ErrorT.bind at 1 in H
                 | [ H : ?v = Success _ |- _ ]
                   => match v with
                      | context[match ?x with Some _ => _ | _ => _ end]
                        => destruct x eqn:?
                      end
                 end ].
  (* need to do this early to deal with conversion slowness *)
  repeat first [ match goal with
                 | [ H : context[simplify ?s ?n] |- _ ]
                   => unshelve epose proof (@eval_simplify _ s n _ _); shelve_unifiable;
                      [ solve [ repeat first [ eassumption | solve [ eauto ] | exactly_once econstructor ] ] | ];
                      generalize dependent (simplify s n); intros
                 | [ H : context[merge ?e ?d] |- _ ]
                   => pose proof (@eval_merge _ e _ d ltac:(eassumption) ltac:(eassumption));
                      generalize dependent (merge e d); intros
                 | [ H : (?x, ?y) = (?z, ?w) |- _ ] => is_var x; is_var z; is_var w; inversion H; clear H
                 end
               | progress destruct_head'_prod
               | progress destruct_head'_and
               | progress subst
               | progress cbn [fst snd symbolic_reg_state symbolic_flag_state symbolic_mem_state dag_state fold_right] in *
               | break_innermost_match_hyps_step ].
  all: repeat first [ solve [ eauto 10 ]
                    | apply conj
                    | progress cbv [eval_idx_Z]
                    | match goal with
                      | [ H : eval ?G ?d ?e ?v |- eval ?G ?d' ?e ?v' ]
                        => cut (v' = v);
                           [ solve [ intros ->; eauto 10 ]
                           | ]
                      end
                    | progress change (Z.of_N 64) with 64%Z
                    | rewrite !Z.land_ones by lia
                    | progress autorewrite with zsimplify_const
                    | progress (push_Zmod; pull_Zmod) ].
Qed.

(* TODO: move or remove *)
Lemma Address_ok_bounded G s s' (sa:AddressSize:=64%N) a rn lo sz idx base_val
      (Hreg : index_and_shift_and_bitcount_of_reg (mem_reg a) = (rn, lo, sz))
      (H64 : sz = 64%N)
      (H : @Address sa a s = Success (idx, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hr : forall idx', get_reg r rn = Some idx' -> eval_idx_Z G d idx' base_val)
      (Hindex : mem_extra_reg a = None)
      (offset := match mem_offset a with
                 | Some s => s
                 | None => 0%Z
                 end)
      (Hv : (0 <= base_val + offset < 2^64)%Z)
  : (eval_idx_Z G d' idx (base_val + offset)
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  set (v := (base_val + offset)%Z) in *.
  replace v with (Z.land v (Z.ones (Z.of_N 64))); [ eapply Address_ok; eassumption | rewrite land_ones_eq_of_bounded by assumption ].
  reflexivity.
Qed.

Lemma build_merge_stack_placeholders_G_ok G G' s s'
      (rsp_val : Z) (stack_vals : list Z)
      (H : build_merge_stack_placeholders_G rsp_val stack_vals (G, s) = Some (tt, (G', s')))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hstack_vals_bounded : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_vals)
      (stack_addr_vals := List.map (fun i => Z.land (rsp_val - 8 * Z.of_nat (List.length stack_vals) + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length stack_vals)))
  : ((exists rsp_idx,
         set_reg r (reg_index rsp) rsp_idx = r'
         /\ eval_idx_Z G' d' rsp_idx (Z.land rsp_val (Z.ones 64)))
     /\ f = f'
     /\ (exists stack_addr_idxs stack_idxs,
            Forall2 (eval_idx_Z G' d') stack_addr_idxs stack_addr_vals
            /\ Forall2 (eval_idx_Z G' d') stack_idxs stack_vals
            /\ (* TODO: Is this too specific a spec? *) List.rev (List.combine stack_addr_idxs stack_idxs) ++ m = m'))
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  cbv [build_merge_stack_placeholders_G ret Symbolic.bind ErrorT.bind G.bind G.lift Crypto.Util.Option.bind lift_dag_G G.ret] in H.
  break_match_hyps.
  all: repeat first [ progress inversion_option
                    | progress inversion_ErrorT
                    | progress subst
                    | progress destruct_head'_and
                    | progress destruct_head'_prod
                    | progress cbn [fst snd dag_state update_dag_with update_mem_with symbolic_reg_state symbolic_flag_state] in *
                    | progress destruct_head'_prod
                    | progress destruct_head'_ex
                    | assumption
                    | progress intros
                    | solve [ eauto ]
                    | progress break_innermost_match_hyps
                    | rewrite @fold_left_id in *
                    | progress cbv [Symbolic.App Merge] in *
                    | progress cbn [fold_right update_dag_with Symbolic.dag_state Symbolic.symbolic_mem_state] in *
                    | progress change (Z.of_N 64) with 64%Z in *
                    | match goal with
                      | [ H : (?x, ?y) = (?x', ?y') |- _ ]
                        => first [ is_var x | is_var y ]; is_var x'; is_var y'; inversion H; clear H
                      | [ H : (?x, (?y, ?z)) = (?x', (?y', ?z')) |- _ ]
                        => is_var x; is_var y; is_var x'; is_var y'; is_var z'; inversion H; clear H
                      | [ H : (tt, (?y, ?z)) = (tt, (?y', ?z')) |- _ ]
                        => is_var y; is_var z; is_var y'; is_var z'; inversion H; clear H
                      | [ H : context[simplify ?s ?n] |- _ ]
                        => unshelve epose proof (@eval_simplify _ s n _ _); shelve_unifiable;
                           [ solve [ repeat first [ eassumption | solve [ eauto ] | exactly_once econstructor ] ] | ];
                           generalize dependent (simplify s n); intros
                      | [ H : context[merge ?e ?d] |- _ ]
                        => pose proof (@eval_merge _ e _ d ltac:(eassumption) ltac:(eassumption));
                           generalize dependent (merge e d); intros
                      | [ H : SetRegFresh_G _ _ _ = _ |- _ ]
                        => eapply SetRegFresh_G_ok in H;
                           [
                           | lazymatch goal with
                             | [ |- index_and_shift_and_bitcount_of_reg _ = _ ] => cbv; reflexivity
                             | _ => idtac
                             end .. ];
                           [ | solve [ reflexivity | assumption | split; assumption ] .. ]
                      | [ H : build_inputarray_G _ _ = _ |- _ ]
                        => apply build_inputarray_G_ok in H; [ | assumption .. ]
                      | [ H : build_merge_array_addresses _ _ _ = _ |- _ ]
                        => eapply build_merge_array_addresses_ok in H;
                           [ | try solve [ assumption | lia ] .. ]
                      | [ H := _ |- _ ] => subst H
                      end ].
  { cbv [eval_idx_Z update_mem_with symbolic_reg_state dag_state symbolic_mem_state symbolic_flag_state update_dag_with reg_index] in *; destruct_head' symbolic_state; subst.
    repeat (apply conj; eauto 10; []).
    repeat esplit; eauto using Forall2_weaken;
      try solve [ eapply Forall2_weaken; [ | eassumption ]; eauto ];
      [].
    lazymatch goal with
    | [ H : Forall2 ?R ?l1 (List.map ?f (seq 0 ?n))
        |- Forall2 ?R ?l1 (List.map ?f' (seq 0 ?n')) ]
      => cut (n = n'); [ intros <-; erewrite map_ext; [ eexact H | cbv beta ] | ]
    end.
    { intros; rewrite !Z.land_ones by lia; push_Zmod; pull_Zmod.
      (* saturate with length congruences *)
      repeat match goal with
             | [ H : Forall2 _ ?y ?x |- _ ]
               => unique assert (length y = length x) by eapply eq_length_Forall2, H
             | [ |- context[length (@List.map ?A ?B ?f ?x)] ]
               => unique assert (length (@List.map A B f x) = length x) by apply map_length
             end.
      f_equal; lia. }
    { eapply eq_length_Forall2; eassumption. } }
Qed.

Lemma build_merge_base_addresses_G_ok
  : forall (idxs : list (idx + list idx))
           (reg_available : list REG)
           (runtime_reg : list Z)
           G s G' s'
           outputaddrs
           (H : build_merge_base_addresses_G idxs reg_available runtime_reg (G, s) = Some (outputaddrs, (G', s')))
           (d := s.(dag_state))
           (Hvals : Forall2 (fun it rv
                             => match it with
                                | inl idx => eval_idx_Z G d idx rv
                                | inr _ => True
                                end)
                            idxs (List.firstn (List.length idxs) runtime_reg))
           (Hreg : Nat.min (List.length idxs) (List.length reg_available) <= List.length runtime_reg)
           (Henough_reg : List.length idxs <= List.length reg_available)
           (d' := s'.(dag_state))
           (r := s.(symbolic_reg_state))
           (r' := s'.(symbolic_reg_state))
           (f := s.(symbolic_flag_state))
           (f' := s'.(symbolic_flag_state))
           (m := s.(symbolic_mem_state))
           (m' := s'.(symbolic_mem_state))
           (Hd : gensym_dag_ok G d)
           (Hreg_available_wide : Forall (fun reg => let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available),
    ((exists (outputaddrs' : list (idx + idx * list idx)),
         let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
         fold_left (fun rst '(r, idx')
                    => set_reg rst (reg_index r)
                               match idx' with
                               | inl idx' => idx'
                               | inr (base_idx', idxs') => base_idx'
                               end)
                   (List.combine reg_available outputaddrs')
                   r
         = r'
         /\ ((* TODO: Is this too specific a spec? *)
             List.rev (List.flat_map
                         (fun '(idx', idx)
                          => match idx', idx with
                             | inl _, inl _ => []
                             | inl _, _ | _, inl _ => []
                             | inr (base', addrs'), inr items
                               => List.combine addrs' items
                             end)
                         (List.combine outputaddrs' idxs))
                      ++ m)
            = m'
         /\ (* outputaddrs' base / array *)
           Forall2
             (fun idx' v =>
                match idx' with
                | inl idx' (* scalars *)
                  => eval_idx_Z G' d' idx' (Z.land v (Z.ones 64))
                | inr (base', addrs')
                  (* arrays: (exists base',
                    (* set_reg r rn base' = r'
                    /\ *) eval_idx_Z G' d' base' (Z.land base_reg_val (Z.ones 64))) *)
                  => eval_idx_Z G' d' base' (Z.land v (Z.ones 64))
                     /\ (* arrays : Forall2 (eval_idx_Z G' d') addrs addrs_vals *)
                       Forall2 (eval_idx_Z G' d') addrs' (addrs_vals_of v addrs')
                end)
             outputaddrs'
             (List.firstn (List.length outputaddrs') runtime_reg)
         /\ (* outputaddrs base:
              arrays: eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64)) *)
           Forall2
             (fun idx base_reg_val =>
                match idx with
                | Some base => eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64))
                | None => True
                end)
             outputaddrs
             (List.firstn (List.length outputaddrs) runtime_reg)
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | inl _, inl _ => True
                       | inr (_, ls), inr ls' => List.length ls = List.length ls'
                       | inl _, inr _ | inr _, inl _ => False
                       end)
                    outputaddrs' idxs
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | None, inl _ => True
                       | Some _, inr _ => True
                       | None, inr _ | Some _, inl _ => False
                       end)
                    outputaddrs outputaddrs')
     /\ f = f')
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  induction idxs as [|idx idxs IH],
      reg_available as [|reg_available reg_availables],
        runtime_reg as [|runtime_reg runtime_regs];
    try specialize (IH reg_availables runtime_regs).
  all: repeat first [ progress cbn [build_merge_base_addresses_G List.length firstn] in *
                    | progress cbv [G.ret G.lift G.bind Crypto.Util.Option.bind] in *
                    | progress intros
                    | progress inversion_option
                    | progress inversion_prod
                    | progress subst
                    | lia
                    | apply conj; eauto; []
                    | solve [ exists nil; cbn [List.combine fold_left flat_map rev List.app length firstn]; eauto 10 ] ].
  all: [ > ]. (* only one goal left *)
  all: repeat
         first [ progress subst
               | progress inversion_option
               | progress destruct_head'_prod
               | progress destruct_head'_unit
               | progress destruct_head'_and
               | progress destruct_head'_ex
               | assumption
               | progress specialize_by_assumption
               | progress specialize_by (eapply Forall2_weaken; [ | eassumption ]; intros; break_innermost_match; eauto using lift_eval_idx_Z_impl)
               | progress cbn [length firstn List.combine fold_left flat_map rev Symbolic.dag_state Symbolic.symbolic_reg_state Symbolic.symbolic_mem_state Symbolic.symbolic_flag_state] in *
               | progress destruct_head' symbolic_state
               | match goal with
                 | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
                 | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                 | [ H : Forall2 _ [] _ |- _ ] => inversion H; clear H
                 | [ H : Forall _ (_ :: _) |- _ ] => inversion H; clear H
                 | [ H : Forall _ [] |- _ ] => clear H
                 | [ H : context[Nat.min (S _) (S _)] |- _ ]
                   => rewrite <- Nat.succ_min_distr in H
                 | [ H : S ?x <= S ?y |- _ ] =>
                     assert (x <= y) by (clear -H; lia); clear H
                 | [ H : SetReg _ _ _ = _ |- _ ]
                   => eapply SetReg_ok in H; [ | solve [ eassumption | reflexivity ] .. ]
                 | [ H : SetRegFresh_G _ _ _ = _ |- _ ]
                   => eapply SetRegFresh_G_ok in H;
                      [ | solve [ reflexivity | assumption | split; assumption | cbv [index_and_shift_and_bitcount_of_reg] in *; congruence ] .. ]
                 | [ H : build_merge_array_addresses _ _ _ = _ |- _ ]
                   => eapply build_merge_array_addresses_ok in H;
                      [ | solve [ eassumption | reflexivity ] .. ]
                 | [ IH : forall G s G' s' outputaddrs, build_merge_base_addresses_G ?idxs ?reg_availables ?runtime_regs (G, s) = Some (outputaddrs, (G', s')) -> _,
                       H : build_merge_base_addresses_G ?idxs ?reg_availables ?runtime_regs (?Gv, ?sv) = Some (?outputaddrsv, (?G'v, ?s'v))
                       |- _ ]
                   => specialize (IH _ _ _ _ _ H); clear H
                 (*
                      | [ H : symbolic_flag_state _ = symbolic_flag_state ?x, H' : symbolic_flag_state ?x = _ |- _ ]
                        => is_var x; destruct x*)
                 end
               | break_innermost_match_hyps_step
               | apply conj; eauto 10; [] ].
  (* above is all reversible, evar-free; below is irreversible *)
  all: [ > eexists (inl _ :: _) | eexists (inr (_, _) :: _) ].
  all: repeat
         repeat
         first [ rewrite rev_app_distr
               | rewrite !app_assoc
               | rewrite app_nil_r
               | progress cbv [index_and_shift_and_bitcount_of_reg] in *
               | progress cbn [length firstn List.combine fold_left flat_map rev] in *
               | progress inversion_prod
               | progress subst
               | reflexivity
               | eassumption
               | solve [ eauto using Forall2_weaken, lift_eval_idx_Z_impl ]
               | apply conj
               | match goal with
                 | [ |- Forall2 _ (_ :: _) (_ :: _) ] => constructor
                 | [ |- fold_left ?f _ _ = fold_left ?f _ _ ] => f_equal
                 | [ |- ?x ++ ?y = ?x' ++ ?y ] => f_equal
                 | [ |- ?x ++ ?y = ?x ++ ?y' ] => f_equal
                 | [ |- rev _ = rev _ ] => apply f_equal
                 | [ |- ?x ++ ?y = ?y ] => cut (x = []); [ now intros -> | ]
                 | [ |- ?y ++ ?x = ?y ] => cut (x = []); [ now intros ->; rewrite app_nil_r | ]
                 | [ |- rev ?x = nil ] => cut (x = []); [ now intros -> | ]
                 (*| [ |- match ?e with inl _ => ?v | inr _ => _ end = ?v' ]
                   => assert_fails unify v v'; instantiate (1:=ltac:(right; repeat exactly_once  econstructor)); reflexivity*)
                 | [ H : Forall2 _ ?l (List.map _ (seq 0 (length ?l'))) |- _ ]
                   => is_var l; is_var l'; assert_fails constr_eq l l';
                      let H' := fresh in
                      assert (H' : length l' = length l) by (now apply eq_length_Forall2 in H; rewrite H, map_length, seq_length);
                      rewrite H' in *
                 | [ H : Forall2 _ ?l (List.map ?f ?ls) |- Forall2 _ ?l (List.map ?f' ?ls) ]
                   => erewrite map_ext; [ eapply Forall2_weaken; [ | exact H ] | cbv beta ];
                      [ eauto using lift_eval_idx_Z_impl
                      | intros; rewrite !Z.land_ones by lia; push_Zmod; pull_Zmod ]
                 end ].
Qed.

Lemma build_merge_stack_placeholders_ok G s s'
      (rsp_val : Z) (stack_vals : list Z)
      (H : build_merge_stack_placeholders (List.length stack_vals) s = Success (tt, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hstack_vals_bounded : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_vals)
      (stack_addr_vals := List.map (fun i => Z.land (rsp_val - 8 * Z.of_nat (List.length stack_vals) + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length stack_vals)))
  : exists G',
    ((exists rsp_idx,
         set_reg r (reg_index rsp) rsp_idx = r'
         /\ eval_idx_Z G' d' rsp_idx (Z.land rsp_val (Z.ones 64)))
     /\ f = f'
     /\ (exists stack_addr_idxs stack_idxs,
            Forall2 (eval_idx_Z G' d') stack_addr_idxs stack_addr_vals
            /\ Forall2 (eval_idx_Z G' d') stack_idxs stack_vals
            /\ (* TODO: Is this too specific a spec? *) List.rev (List.combine stack_addr_idxs stack_idxs) ++ m = m'))
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  eapply build_merge_stack_placeholders_eq_G in H.
  destruct H as [G' H]; exists G'.
  eapply build_merge_stack_placeholders_G_ok in H; try eassumption.
Qed.

Lemma build_merge_base_addresses_ok
      (idxs : list (idx + list idx))
      (reg_available : list REG)
      (runtime_reg : list Z)
      G s
      (d := s.(dag_state))
      (Hvals : Forall2 (fun it rv
                        => match it with
                           | inl idx => eval_idx_Z G d idx rv
                           | inr _ => True
                           end)
                       idxs (List.firstn (List.length idxs) runtime_reg))
      (Hreg : Nat.min (List.length idxs) (List.length reg_available) <= List.length runtime_reg)
      (Henough_reg : List.length idxs <= List.length reg_available)
      s'
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      outputaddrs
      (H : build_merge_base_addresses idxs reg_available s = Success (outputaddrs, s'))
      (Hd : gensym_dag_ok G d)
      (Hreg_available_wide : Forall (fun reg => let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available)
  : exists G',
    ((exists (outputaddrs' : list (idx + idx * list idx)),
         let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
         fold_left (fun rst '(r, idx')
                    => set_reg rst (reg_index r)
                               match idx' with
                               | inl idx' => idx'
                               | inr (base_idx', idxs') => base_idx'
                               end)
                   (List.combine reg_available outputaddrs')
                   r
         = r'
         /\ ((* TODO: Is this too specific a spec? *)
             List.rev (List.flat_map
                         (fun '(idx', idx)
                          => match idx', idx with
                             | inl _, inl _ => []
                             | inl _, _ | _, inl _ => []
                             | inr (base', addrs'), inr items
                               => List.combine addrs' items
                             end)
                         (List.combine outputaddrs' idxs))
                      ++ m)
            = m'
         /\ (* outputaddrs' base / array *)
           Forall2
             (fun idx' v =>
                match idx' with
                | inl idx' (* scalars *)
                  => eval_idx_Z G' d' idx' (Z.land v (Z.ones 64))
                | inr (base', addrs')
                  (* arrays: (exists base',
                    (* set_reg r rn base' = r'
                    /\ *) eval_idx_Z G' d' base' (Z.land base_reg_val (Z.ones 64))) *)
                  => eval_idx_Z G' d' base' (Z.land v (Z.ones 64))
                     /\ (* arrays : Forall2 (eval_idx_Z G' d') addrs addrs_vals *)
                       Forall2 (eval_idx_Z G' d') addrs' (addrs_vals_of v addrs')
                end)
             outputaddrs'
             (List.firstn (List.length outputaddrs') runtime_reg)
         /\ (* outputaddrs base:
              arrays: eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64)) *)
           Forall2
             (fun idx base_reg_val =>
                match idx with
                | Some base => eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64))
                | None => True
                end)
             outputaddrs
             (List.firstn (List.length outputaddrs) runtime_reg)
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | inl _, inl _ => True
                       | inr (_, ls), inr ls' => List.length ls = List.length ls'
                       | inl _, inr _ | inr _, inl _ => False
                       end)
                    outputaddrs' idxs
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | None, inl _ => True
                       | Some _, inr _ => True
                       | None, inr _ | Some _, inl _ => False
                       end)
                    outputaddrs outputaddrs')
     /\ f = f')
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  eapply build_merge_base_addresses_eq_G in H; [ | eassumption .. ].
  destruct H as [G' H]; exists G'.
  eapply build_merge_base_addresses_G_ok in H; try eassumption.
Qed.

Lemma LoadArray_ok G s s' base base_val len idxs
      (H : LoadArray base len s = Success (idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Hbase : eval_idx_Z G d base base_val)
  : ((exists addrs : list idx,
         Forall2 (eval_idx_Z G d') addrs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
         /\ Some idxs = Option.List.lift (List.map (fun a => load a s') addrs))
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv [LoadArray Symbolic.bind ErrorT.bind] in H.
  subst d d' r r' f f' m m'.
  revert H Hd Hbase.
  generalize (seq 0 len); intros indices; clear len.
  revert indices idxs s s'.
  induction indices as [|i indices IH], idxs as [|idx idxs];
    try specialize (IH idxs).
  all: repeat first [ progress intros
                    | progress inversion_ErrorT
                    | progress inversion_prod
                    | progress subst
                    | progress cbn [List.map Crypto.Util.Option.bind fold_right mapM fst snd Symbolic.dag_state Symbolic.symbolic_reg_state Symbolic.symbolic_mem_state Symbolic.symbolic_flag_state] in *
                    | progress cbv [Symbolic.ret Option.List.lift Symbolic.bind ErrorT.bind Load64 some_or] in *
                    | discriminate
                    | solve [ eauto 10
                            | exists nil; cbn [List.map]; eauto ]
                    | progress destruct_head'_prod
                    | progress destruct_head'_and
                    | progress destruct_head'_ex
                    | progress specialize_by_assumption
                    | progress specialize_by eauto using lift_eval_idx_Z_impl
                    | match goal with
                      | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; clear H
                      | [ H : compute_array_address _ _ _ = _ |- _ ]
                        => eapply compute_array_address_ok in H; [ | eassumption .. ]
                      | [ IH : forall s s', mapM ?f ?ls s = Success (?v, s') -> _, H : mapM ?f ?ls _ = Success (?v, _) |- _ ]
                        => specialize (IH _ _ H)
                      | [ H : symbolic_flag_state _ = symbolic_flag_state ?x, H' : symbolic_flag_state ?x = _ |- _ ]
                        => is_var x; destruct x
                      | [ H : load _ ?s = Some _ |- context[load _ ?s] ] => rewrite H
                      | [ H : Some _ = fold_right _ _ _ |- _ ] => rewrite <- H
                      | [ |- Forall2 _ (_ :: _) (_ :: _) ] => constructor
                      end
                    | apply conj; eauto; []
                    | break_innermost_match_hyps_step
                    | progress break_match_hyps
                    | eexists (_ :: _)
                    | solve [ eauto using lift_eval_idx_Z_impl ] ].
Qed.

Lemma LoadOutputs_ok G s s' outputaddrs output_types output_vals idxs
      (H : LoadOutputs outputaddrs output_types s = Success (idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hd : gensym_dag_ok G d)
      (Houtputaddrs : Forall2 (fun idx val
                               => match idx with
                                  | Some idx => eval_idx_Z G d idx (Z.land val (Z.ones 64))
                                  | _ => True
                                  end) outputaddrs output_vals)
  : ((exists outputaddrs' : list (idx + list idx),
         Forall2 (fun idxs '((base, len), base_val)
                  => match idxs, base, len with
                     | inr idxs, Some base, Some len
                       => Forall2 (eval_idx_Z G d') idxs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
                     | _, _, _ => False
                     end)
                 outputaddrs'
                 (List.combine (List.combine outputaddrs output_types) output_vals)
         /\ Some idxs
            = Option.List.lift
                (List.map (fun idxs
                           => match idxs with
                              | inr idxs => option_map inr (Option.List.lift (List.map (fun a => load a s') idxs))
                              | inl idx => None (* Some (inl idx) ?? *)
                              end)
                          outputaddrs'))
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  cbv [LoadOutputs Symbolic.bind Symbolic.ret ErrorT.bind] in H.
  break_match_hyps.
  all: repeat first [ progress inversion_ErrorT
                    | progress inversion_prod
                    | progress subst
                    | progress destruct_head'_prod
                    | progress cbn [fst snd] in *
                    | match goal with
                      | [ H := _ |- _ ] => subst H
                      end ].
  match goal with
  | [ H : mapM _ _ _ = Success (?l, ?s) |- _ ]
    => rename l into idxs; rename s into s'
  end.
  revert Houtputaddrs.
  revert Hd.
  revert dependent s'.
  revert outputaddrs output_types output_vals idxs s.
  induction outputaddrs as [|outputaddr outputaddrs IH],
      output_types as [|output_type output_types],
        output_vals as [|output_val output_vals],
          idxs as [|idx idxs];
    try specialize (IH output_types output_vals idxs).
  all: repeat first [ progress cbn [fst snd mapM List.map List.combine option_map fold_right Crypto.Util.Option.bind Symbolic.dag_state Symbolic.symbolic_reg_state Symbolic.symbolic_mem_state Symbolic.symbolic_flag_state] in *
                    | progress cbv [Symbolic.ret] in *
                    | progress intros
                    | progress subst
                    | progress inversion_ErrorT
                    | progress inversion_prod
                    | discriminate
                    | solve [ eauto 10 ]
                    | progress destruct_head'_prod
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress specialize_by_assumption
                    | match goal with
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ [] _ |- _ ] => inversion H; clear H
                      | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; clear H
                      | [ H : option_eq _ (Some _) ?x |- _ ] => cbv [option_eq] in H
                      | [ IH : forall s s', mapM ?f ?ls s = Success (?v, s') -> _, H : mapM ?f ?ls _ = Success (?v, _) |- _ ]
                        => specialize (IH _ _ H)
                      | [ H : symbolic_flag_state _ = symbolic_flag_state ?x, H' : symbolic_flag_state ?x = _ |- _ ]
                        => is_var x; destruct x
                      | [ H : LoadArray _ _ _ = _ |- _ ]
                        => eapply LoadArray_ok in H; [ | eassumption .. ]
                      | [ H : Some _ = _ |- _ ] => rewrite <- H
                      | [ |- Forall2 _ (_ :: _) (_ :: _) ] => constructor
                      | [ H : Forall2 _ ?ls (List.map ?f ?ls') |- Forall2 _ ?ls (List.map ?f' ?ls') ]
                        => erewrite map_ext; [ eapply Forall2_weaken; [ | exact H ] | ];
                           cbv beta;
                           [ solve [ eauto using lift_eval_idx_Z_impl ]
                           | intros; rewrite !Z.land_ones by lia; push_Zmod; try reflexivity ]
                      end
                    | progress cbv [Symbolic.bind ErrorT.bind] in *
                    | break_innermost_match_hyps_step
                    | progress break_match_hyps
                    | progress specialize_by (eapply Forall2_weaken; [ | eassumption ]; cbv beta; intros *; break_innermost_match; eauto using lift_eval_idx_Z_impl)
                    | apply conj; eauto; []
                    | eexists (inr _ :: _)
                    | progress cbv [Option.List.lift] in * ].
Qed.

Lemma mapM_GetReg_ok_bounded G
  : forall regs idxs reg_vals s s'
           (H : mapM GetReg regs s = Success (idxs, s'))
           (d := s.(dag_state))
           (d' := s'.(dag_state))
           (r := s.(symbolic_reg_state))
           (r' := s'.(symbolic_reg_state))
           (f := s.(symbolic_flag_state))
           (f' := s'.(symbolic_flag_state))
           (m := s.(symbolic_mem_state))
           (m' := s'.(symbolic_mem_state))
           (Hd : gensym_dag_ok G d)
           (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
           (Hbounded : Forall (fun v => (0 <= v < 2^64)%Z) reg_vals)
           (Hregval_len : List.length regs = List.length reg_vals)
           (Hregval : Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z G s idx' v) (List.map (get_reg r) (List.map reg_index regs)) reg_vals),
    ((exists reg_idxs,
         List.map (get_reg r) (List.map reg_index regs) = List.map Some reg_idxs
         /\ Forall2 (eval_idx_Z G s') reg_idxs reg_vals)
     /\ Forall2 (eval_idx_Z G s') idxs reg_vals
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n).
Proof.
  induction regs as [|reg regs IH],
      idxs as [|idx idxs],
        reg_vals as [|reg_val reg_vals];
    try specialize (IH idxs reg_vals).
  all: repeat first [ progress cbn [mapM List.map fst snd Symbolic.dag_state Symbolic.symbolic_reg_state Symbolic.symbolic_mem_state Symbolic.symbolic_flag_state List.length] in *
                    | progress cbv [Symbolic.ret Symbolic.bind ErrorT.bind] in *
                    | progress intros
                    | progress destruct_head'_ex
                    | progress destruct_head'_prod
                    | progress destruct_head'_and
                    | progress inversion_option
                    | progress inversion_ErrorT
                    | progress inversion_prod
                    | progress subst
                    | progress inversion_list
                    | progress inversion_nat_eq
                    | progress specialize_by_assumption
                    | progress destruct_head' symbolic_state
                    | progress specialize_by (eapply Forall2_weaken; [ | eassumption ]; cbv [option_eq]; intros *; break_innermost_match; eauto using lift_eval_idx_Z_impl)
                    | exfalso; lia
                    | match goal with
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ [] _ |- _ ] => inversion H; clear H
                      | [ H : Forall _ (_ :: _) |- _ ] => inversion H; clear H
                      | [ |- exists reg_idxs, _ :: _ = List.map Some reg_idxs /\ _ ]
                        => eexists (_ :: _); cbn [List.map]; split; [ apply f_equal2; eassumption | ]
                      | [ IH : forall s s', mapM ?f ?ls s = Success (?v, s') -> _, H : mapM ?f ?ls _ = Success (?v, _) |- _ ]
                        => specialize (IH _ _ H)
                      | [ H : forall ls, nil = List.map _ ls -> _ |- _ ]
                        => specialize (H nil eq_refl)
                      | [ |- exists ls, nil = List.map _ ls /\ _ ] => exists nil
                      | [ H : get_reg ?r ?ri = Some ?i, H' : eval_idx_Z ?G ?d ?i ?v |- _ ]
                        => unique assert (forall i', get_reg r ri = Some i' -> eval_idx_Z G d i' v)
                          by now intro; rewrite H; inversion 1; subst; assumption
                      | [ H : option_eq _ _ (Some _) |- _ ] => cbv [option_eq] in H
                      | [ H : GetReg _ _ = _ |- _ ]
                        => eapply GetReg_ok_bounded in H; [ | solve [ eassumption | reflexivity | lia ] .. ]
                      | [ |- Forall2 _ (_ :: _) (_ :: _) ] => constructor
                      end
                    | solve [ eauto 10 using lift_eval_idx_Z_impl ]
                    | break_innermost_match_hyps_step
                    | apply conj; eauto 10 using lift_eval_idx_Z_impl; [] ].
Qed.

Import Map.Interface Map.Separation. (* for coercions *)
Require Import bedrock2.Array.
Require Import bedrock2.ZnWords.
Import LittleEndianList.
Import coqutil.Word.Interface.
Definition cell64 wa (v : Z) : Semantics.mem_state -> Prop :=
  Lift1Prop.ex1 (fun bs => sep (emp (
      length bs = 8%nat /\ v = le_combine bs))
                               (eq (OfListWord.map.of_list_word_at wa bs))).

Definition R_scalar_or_array {dereference_scalar:bool}
           (val : Z + list Z) (asm_val : Naive.word 64)
  := match val with
     | inr array_vals => array cell64 (word.of_Z 8) asm_val array_vals
     | inl scalar_val => if dereference_scalar
                         then cell64 asm_val scalar_val
                         else emp (word.unsigned asm_val = scalar_val)
     end.
Definition R_list_scalar_or_array {dereference_scalar:bool}
           (Z_vals : list (Z + list Z)) (asm_vals : list (Naive.word 64))
  := List.fold_right
       sep
       (emp True)
       (List.map
          (fun '(val, asm_val) => R_scalar_or_array (dereference_scalar:=dereference_scalar) val asm_val)
          (List.combine Z_vals asm_vals)).

Definition get_asm_reg (m : machine_state) (reg_available : list REG) : list Z
  := List.map (Semantics.get_reg m) reg_available.

Definition R_runtime_input
           (output_scalars_are_pointers := false)
           (frame : Semantics.mem_state -> Prop)
           (output_types : type_spec) (runtime_inputs : list (Z + list Z))
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (reg_available : list REG) (runtime_reg : list Z)
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop
  := exists (stack_placeholder_values : list Z) (output_placeholder_values : list (Z + list Z)),
    Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
    /\ (Nat.min (List.length output_types + List.length runtime_inputs) (List.length reg_available) <= List.length runtime_reg)%nat
    /\ get_asm_reg m reg_available = runtime_reg
    /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
    /\ List.length asm_arguments_out = List.length output_types
    /\ List.map word.unsigned (asm_arguments_out ++ asm_arguments_in)
       = List.firstn (List.length output_types + List.length runtime_inputs) runtime_reg
    /\ Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_placeholder_values
    /\ stack_size = List.length stack_placeholder_values
    /\ (Semantics.get_reg m rsp - 8 * Z.of_nat stack_size)%Z = word.unsigned stack_base
    /\ Forall2 val_or_list_val_matches_spec output_placeholder_values output_types
    /\ Forall (fun v => match v with
                        | inl v => (0 <= v < 2^64)%Z
                        | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                        end) output_placeholder_values
    /\ (* it must be the case that all the scalars in output_placeholder_values match what's in registers / the calling convention *)
      Forall2
        (fun v1 v2 => match v1 with
                      | inl v => if output_scalars_are_pointers
                                 then True
                                 else v = v2
                      | inr _ => True
                      end)
        output_placeholder_values
        (firstn (length output_types) runtime_reg)
    /\ (* it must be the case that all the scalars in the real input values match what's in registers / the calling convention *)
      Forall2
        (fun v1 v2 => match v1 with
                      | inl v => v = v2
                      | inr _ => True
                      end)
        runtime_inputs
        (firstn (length runtime_inputs) (skipn (length output_types) runtime_reg))
    /\ ((frame *
           R_list_scalar_or_array (dereference_scalar:=output_scalars_are_pointers) output_placeholder_values asm_arguments_out *
           R_list_scalar_or_array (dereference_scalar:=false) runtime_inputs asm_arguments_in *
           array cell64 (word.of_Z 8) stack_base stack_placeholder_values)%sep)
         m.

(* TODO : should we preserve inputs? *)
Definition R_runtime_output
           (output_scalars_are_pointers := false)
           (frame : Semantics.mem_state -> Prop)
           (runtime_outputs : list (Z + list Z)) (input_types : type_spec)
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop
  := exists (stack_placeholder_values : list Z) (input_placeholder_values : list (Z + list Z)),
    Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
    /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
    /\ Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_placeholder_values
    /\ stack_size = List.length stack_placeholder_values
    /\ Forall2 val_or_list_val_matches_spec input_placeholder_values input_types
    /\ Forall (fun v => match v with
                        | inl v => (0 <= v < 2^64)%Z
                        | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                        end) input_placeholder_values
    /\ ((frame *
           R_list_scalar_or_array (dereference_scalar:=output_scalars_are_pointers) runtime_outputs asm_arguments_out *
           R_list_scalar_or_array (dereference_scalar:=false) input_placeholder_values asm_arguments_in *
           array cell64 (word.of_Z 8) stack_base stack_placeholder_values)%sep)
         m.

Definition word_args_to_Z_args
  : list (Naive.word 64 + list (Naive.word 64)) -> list (Z + list Z)
  := List.map (fun v => match v with
                        | inl v => inl (word.unsigned v)
                        | inr vs => inr (List.map word.unsigned vs)
                        end).

Lemma word_args_to_Z_args_bounded args
  : Forall (fun v => match v with
                     | inl v => (0 <= v < 2^64)%Z
                     | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                     end) (word_args_to_Z_args args).
Proof.
  cbv [word_args_to_Z_args].
  repeat first [ progress intros
               | rewrite Forall_map_iff, Forall_forall
               | progress break_innermost_match
               | apply Word.Properties.word.unsigned_range ].
Qed.

Lemma word_args_to_Z_args_length args
  : length (word_args_to_Z_args args) = length args.
Proof. apply map_length. Qed.

Definition init_symbolic_state_G (m : machine_state)
  : (symbol -> option Z) * dag -> (symbol -> option Z) * symbolic_state
  := fun st
     => let vals := Tuple.to_list _ (m.(machine_reg_state)) in
        let '(initial_reg_idxs, (G, d)) := dag_gensym_n_G vals st in
        (G,
         {| dag_state := d
            ; symbolic_reg_state := Tuple.from_list_default None 16 (List.map Some initial_reg_idxs)
            ; symbolic_flag_state := Tuple.repeat None 6
            ; symbolic_mem_state := []
         |}).

Lemma init_symbolic_state_eq_G G d m
  : init_symbolic_state d = snd (init_symbolic_state_G m (G, d)).
Proof.
  cbv [init_symbolic_state init_symbolic_state_G].
  pose proof (@dag_gensym_n_eq_G G d (Tuple.to_list 16 m.(machine_reg_state))) as H.
  rewrite Tuple.length_to_list in H; rewrite H; clear H.
  eta_expand; cbn [fst snd].
  reflexivity.
Qed.

Lemma init_symbolic_state_G_ok m G d G' ss
      (frame : Semantics.mem_state -> Prop)
      (Hd : gensym_dag_ok G d)
      (H : init_symbolic_state_G m (G, d) = (G', ss))
      (d' := ss.(dag_state))
      (Hframe : frame m)
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list 16 m.(machine_reg_state)))
  : R frame G' ss m
    /\ (forall reg, Option.is_Some (get_reg ss.(symbolic_reg_state) (reg_index reg)) = true)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  cbv [init_symbolic_state_G] in *.
  eta_expand; cbn [fst snd] in *; inversion_prod; subst.
  pose proof (dag_gensym_n_G_ok _ _ _ _ _ _ ltac:(eassumption) ltac:(repeat rewrite <- surjective_pairing; reflexivity) ltac:(eassumption)).
  destruct_head'_and; cbv [R].
  repeat match goal with |- _ /\ _ => split end; try eassumption; try reflexivity.
  2: { cbv [Tuple.repeat R_flags Tuple.append Tuple.fieldwise Tuple.fieldwise' R_flag]; cbn [fst snd];
       repeat apply conj; congruence. }
  2: { intros; cbn [List.map]; cbv [get_reg symbolic_reg_state].
       unshelve erewrite <- Tuple.nth_default_to_list, Tuple.from_list_default_eq, Tuple.to_list_from_list.
       { rewrite map_length.
         erewrite length_Forall2, Tuple.length_to_list
           by (eapply dag_gensym_n_G_ok; [ | eta_expand; reflexivity | ]; assumption).
         reflexivity. }
       erewrite map_nth_default with (x:=0%N); [ reflexivity | ].
       erewrite length_Forall2, Tuple.length_to_list
         by (eapply dag_gensym_n_G_ok; [ | eta_expand; reflexivity | ]; assumption).
       clear; cbv [reg_index]; break_innermost_match; lia. }
  set (v := dag_gensym_n_G _ _) in *; clearbody v; destruct_head'_prod; cbn [fst snd] in *.
  eassert (H' : Tuple.to_list 16 m.(machine_reg_state) = _).
  { repeat match goal with H : _ |- _ => clear H end.
      cbv [Tuple.to_list Tuple.to_list'].
      set_evars; eta_expand; subst_evars; reflexivity. }
  generalize dependent (Tuple.to_list 16 m.(machine_reg_state)); intros; subst.
  repeat match goal with H : context[?x :: _] |- _ => assert_fails is_var x; set x in * end.
  repeat match goal with H : Forall2 _ ?v (_ :: _) |- _ => is_var v; inversion H; clear H; subst end.
  repeat match goal with H : Forall2 _ ?v nil |- _ => is_var v; inversion H; clear H; subst end.
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst end.
  cbv [List.map Tuple.from_list_default Tuple.from_list_default'].
  cbv [R_regs R_reg Tuple.fieldwise Tuple.fieldwise' eval_idx_Z] in *; cbn [fst snd].
  repeat apply conj; intros; inversion_option; subst; try assumption.
  all: change 64%Z with (Z.of_N 64).
  all: rewrite land_ones_eq_of_bounded; [ reflexivity | ].
  all: assumption.
Qed.

Lemma init_symbolic_state_ok m G d
      (frame : Semantics.mem_state -> Prop)
      (Hd : gensym_dag_ok G d)
      (ss := init_symbolic_state d)
      (d' := ss.(dag_state))
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list 16 m.(machine_reg_state)))
      (Hframe : frame m)
  : exists G',
    R frame G' ss m
    /\ (forall reg, Option.is_Some (get_reg ss.(symbolic_reg_state) (reg_index reg)) = true)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  subst ss d'; erewrite init_symbolic_state_eq_G.
  eexists; eapply init_symbolic_state_G_ok; try eassumption.
  eta_expand; reflexivity.
Qed.

Lemma Forall2_get_reg_of_R G d r mr regs
      (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
      (Hreg : R_regs G d r mr)
  : Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z G d idx' v)
            (List.map (get_reg r) (List.map reg_index regs))
            (List.map (Semantics.get_reg mr) regs).
Proof.
  induction regs as [|reg regs IH]; cbn [List.map] in *;
    inversion Hwide; clear Hwide; subst;
    constructor; auto; clear dependent regs; [].
  assert (reg_offset reg = 0%N) by now destruct reg.
  assert (reg_index reg < length (Tuple.to_list _ r))
    by now rewrite Tuple.length_to_list; destruct reg; cbv [reg_index]; lia.
  cbv [get_reg Semantics.get_reg R_regs] in *.
  rewrite Tuple.fieldwise_to_list_iff in Hreg.
  erewrite @Forall2_forall_iff in Hreg by now rewrite !Tuple.length_to_list.
  specialize (Hreg (reg_index reg) ltac:(assumption)); rewrite !@Tuple.nth_default_to_list in *.
  cbv [index_and_shift_and_bitcount_of_reg] in *.
  generalize dependent (reg_size reg); intros; subst.
  generalize dependent (reg_offset reg); intros; subst.
  change (Z.of_N 0) with 0%Z.
  change (Z.of_N 64) with 64%Z.
  rewrite Z.shiftr_0_r.
  do 2 match goal with
       | [ H : context[Tuple.nth_default ?d ?i ?l], H' : context[Tuple.nth_default ?d' ?i' ?l] |- _ ]
         => is_evar d; unify d d'; unify i i'
       | [ H : context[Tuple.nth_default ?d ?i ?l] |- context[Tuple.nth_default ?d' ?i' ?l] ]
         => is_evar d; unify d d'; unify i i'
       end.
  cbv [R_reg] in Hreg.
  destruct Hreg as [Hreg Hreg'].
  rewrite <- Hreg'.
  now apply Hreg.
Qed.

Lemma get_reg_bounded mr regs
  : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z)
           (List.map (Semantics.get_reg mr) regs).
Proof.
  rewrite Forall_map, Forall_forall; intros reg ?.
  assert ((reg_size reg <= 64)%N)
    by now clear; destruct reg; cbv [reg_index reg_size]; lia.
  cbv [Semantics.get_reg index_and_shift_and_bitcount_of_reg] in *.
  rewrite Z.land_nonneg, Z.shiftr_nonneg.
  split; [ right; apply Z.ones_nonneg; lia | ].
  eapply Z.le_lt_trans;
    [ rewrite Z.land_comm; apply Z.land_le; intros; apply Z.ones_nonneg
    | rewrite Z.ones_equiv, Z.lt_pred_le; Z.peel_le ];
    lia.
Qed.

Lemma reg_all_set_set_reg r regs i v
  : Forall (fun v => Option.is_Some v = true) (List.map (get_reg r) regs)
    -> Forall (fun v => Option.is_Some v = true)
              (List.map (get_reg (set_reg r i v)) regs).
Proof.
  rewrite !Forall_map; apply Forall_impl; intro.
  rewrite get_reg_set_reg_full.
  cbv [Option.is_Some]; break_innermost_match; congruence.
Qed.

Lemma reg_all_set_fold_left {A} r regs f (ls : list A)
      (Hf : forall rst v,
          List.In v ls
          -> Forall (fun v => Option.is_Some v = true) (List.map (get_reg rst) regs)
          -> Forall (fun v => Option.is_Some v = true) (List.map (get_reg (f rst v)) regs))
  : Forall (fun v => Option.is_Some v = true) (List.map (get_reg r) regs)
    -> Forall (fun v => Option.is_Some v = true)
              (List.map (get_reg (fold_left f ls r))
                        regs).
Proof.
  revert r; induction ls as [|x xs IH]; intros; cbn [fold_left]; auto.
  apply IH; break_innermost_match; intros; apply Hf; cbn [List.In] in *; auto.
Qed.

Lemma load_eval_R_mem_eval G d idx idx' mem_st m' frame
      (Hmem : R_mem frame G d mem_st m')
      (Hload : load idx mem_st = Some idx')
  : exists val,
    eval_idx_Z G d idx' val.
Proof.
  cbv [load option_map] in *.
  break_innermost_match_hyps; inversion_option; subst; destruct_head'_prod.
  revert dependent m'; induction mem_st as [|m mem_st IH]; cbn [R_mem find] in *; intros.
  all: repeat first [ progress inversion_option
                    | progress inversion_pair
                    | progress cbn [fst snd] in *
                    | progress reflect_hyps
                    | progress subst
                    | progress specialize_by_assumption
                    | progress break_innermost_match_hyps ].
  all: repeat first [ progress cbv [sep R_cell64 Lift1Prop.ex1 emp eval_idx_Z] in *
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress subst
                    | now eauto ].
Qed.

Lemma load_eval_R_mem_eval_Forall2 G d idxs l n z mem_st m' frame l1
      (Hmem : R_mem frame G d mem_st m')
      (Hl : Forall2 (eval_idx_Z G d) l
                    (List.map (fun i => Z.land (z + 8 * Z.of_nat i) (Z.ones 64))
                              (seq 0 n)))
      (Hmem_all : Option.List.lift (List.map (fun a => load a mem_st) idxs) = Some l1)
  : exists vals,
    Forall2 (eval_idx_Z G d) l1 vals.
Proof.
  revert dependent l1.
  induction idxs as [|idx idxs IH],
      l1 as [|x xs];
    try specialize (IH xs); intros.
  all: repeat first [ progress cbn [List.map fold_right] in *
                    | progress cbv [Crypto.Util.Option.bind Option.List.lift] in *
                    | progress inversion_option
                    | progress inversion_list
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress specialize_by reflexivity
                    | progress subst
                    | progress break_match_hyps
                    | match goal with
                      | [ H : load _ _ = Some _ |- _ ] => eapply load_eval_R_mem_eval in H; [ | eassumption ]
                      end
                    | now eexists nil; eauto
                    | now eexists (_ :: _); eauto ].
Qed.

Definition R_regs_preserved_v rn (m : Semantics.reg_state)
  := Z.land (Tuple.nth_default 0%Z rn m) (Z.ones 64).

Definition R_regs_preserved G d (m : Semantics.reg_state) rs rs'
  := forall rn idx, get_reg rs' rn = Some idx -> exists idx', get_reg rs rn = Some idx' /\ let v := R_regs_preserved_v rn m in eval_idx_Z G d idx' v -> eval_idx_Z G d idx v.

Global Instance R_regs_preserved_Reflexive G d m : Reflexive (R_regs_preserved G d m) | 100.
Proof. intro; cbv [R_regs_preserved]; eauto. Qed.

Lemma R_regs_subsumed_get_reg_same_eval G d rs rs' rm
      (H : R_regs G d rs rm)
      (H_impl : R_regs_preserved G d rm rs rs')
  : R_regs G d rs' rm.
Proof.
  cbv [R_regs get_reg R_regs_preserved R_regs_preserved_v] in *.
  rewrite @Tuple.fieldwise_to_list_iff, @Forall2_forall_iff_nth_error in *.
  intro i; specialize (H i); specialize (H_impl i).
  rewrite <- !@Tuple.nth_default_to_list in *.
  cbv [nth_default option_eq] in *.
  repeat first [ progress destruct_head'_and
               | progress destruct_head'_ex
               | rewrite @Tuple.length_to_list in *
               | progress cbv [R_reg eval_idx_Z] in *
               | progress break_innermost_match
               | progress break_innermost_match_hyps
               | now auto
               | progress intros
               | progress subst
               | match goal with
                 | [ H : nth_error _ _ = None |- _ ] => apply nth_error_error_length in H
                 | [ H : ?i >= ?n, H' : context[nth_error (Tuple.to_list ?n _) ?i] |- _ ]
                   => rewrite nth_error_length_error in H' by now rewrite Tuple.length_to_list; lia
                 | [ H : forall x, Some _ = Some x -> _ |- _ ]
                   => specialize (H _ eq_refl)
                 | [ H : ?x = ?y, H' : context[?y] |- _ ] => is_var x; rewrite <- H in H'
                 end
               | apply conj; auto; [] ].
Qed.

Lemma R_regs_preserved_set_reg G d rs rs' ri rm v
      (H : R_regs_preserved G d rm rs rs')
      (H_same : (ri < 16)%nat -> exists idx, get_reg rs ri = Some idx /\ let v' := R_regs_preserved_v ri rm in eval_idx_Z G d idx v' -> eval_idx_Z G d v v')
  : R_regs_preserved G d rm rs (set_reg rs' ri v).
Proof.
  cbv [R_regs_preserved] in *.
  intros rn idx; specialize (H rn).
  rewrite get_reg_set_reg_full; intro.
  repeat first [ progress break_innermost_match_hyps
               | progress inversion_option
               | progress subst
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress destruct_head'_ex
               | progress specialize_by_assumption
               | progress specialize_by lia
               | rewrite @Bool.andb_true_iff in *
               | rewrite @Bool.andb_false_iff in *
               | solve [ eauto ]
               | progress reflect_hyps
               | match goal with
                 | [ H : forall v, ?k = Some v -> _, H' : ?k = Some _ |- _ ]
                   => specialize (H _ H')
                 end ].
Qed.

Lemma R_regs_preserved_fold_left_set_reg_index {T} G d rs rs' rm (r_idxs : list (_ * (_ + _ * T)))
      (H : R_regs_preserved G d rm rs rs')
      (H_same : Forall (fun '(r, v) => let v := match v with inl v => v | inr (v, _) => v end in exists idx, get_reg rs (reg_index r) = Some idx /\ let v' := R_regs_preserved_v (reg_index r) rm in eval_idx_Z G d idx v' -> eval_idx_Z G d v v') r_idxs)
  : R_regs_preserved
      G d rm
      rs
      (fold_left (fun rst '(r, idx')
                  => set_reg rst (reg_index r)
                             match idx' with
                             | inl idx' => idx'
                             | inr (base_idx', idxs') => base_idx'
                             end)
                 r_idxs rs').
Proof.
  revert dependent rs'; induction r_idxs as [|[r v] r_idxs IH]; cbn [fold_left];
    inversion_one_head Forall; auto; intros; [].
  apply IH; clear IH; auto; [].
  apply R_regs_preserved_set_reg; auto.
Qed.

Lemma Semantics_get_reg_eq_nth_default_of_R_regs G d ss ms r
      (Hsz : reg_size r = 64%N)
      (HR : R_regs G d ss ms)
  : Semantics.get_reg ms r = Tuple.nth_default 0%Z (reg_index r) (ms : Semantics.reg_state).
Proof.
  assert (Hro : reg_offset r = 0%N) by now revert Hsz; clear; cbv; destruct r; lia.
  cbv [R_regs R_reg] in HR.
  rewrite Tuple.fieldwise_to_list_iff, Forall2_forall_iff_nth_error in HR.
  specialize (HR (reg_index r)).
  cbv [Semantics.get_reg index_and_shift_and_bitcount_of_reg].
  rewrite Hro, Hsz; change (Z.of_N 0) with 0%Z; change (Z.of_N 64) with 64%Z.
  rewrite Z.shiftr_0_r, <- Tuple.nth_default_to_list; cbv [nth_default option_eq] in *.
  break_innermost_match_hyps; break_innermost_match; inversion_option; destruct_head'_and; try congruence; try tauto.
Qed.

Lemma Semantics_get_reg_eq_nth_default_of_R frame G ss ms r
      (Hsz : reg_size r = 64%N)
      (HR : R frame G ss ms)
  : Semantics.get_reg ms r = Tuple.nth_default 0%Z (reg_index r) (ms : Semantics.reg_state).
Proof.
  destruct ss, ms; eapply Semantics_get_reg_eq_nth_default_of_R_regs; try eassumption; apply HR.
Qed.

Lemma Forall2_R_regs_preserved_same_helper G d reg_available idxs m rs
      (Hreg_wide_enough
        : Forall
            (fun reg : REG =>
               let
                 '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in
               sz = 64%N) reg_available)
      (H : Forall2 (fun (idx' : idx + idx * list idx) v
                    => match idx' with
                       | inl idx' => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                       | inr (base', _) => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                       end)
                   idxs (firstn (List.length idxs) (get_asm_reg m reg_available)))
      (HR : R_regs G d rs m)
      (Hex : forall n r, (n < List.length idxs)%nat -> nth_error reg_available n = Some r -> exists idx, get_reg rs (reg_index r) = Some idx)
  : Forall (fun '(r, v)
            => let v := match v with inl v => v | inr (v, _) => v end in
               exists idx, get_reg rs (reg_index r) = Some idx
                           /\ let v' := R_regs_preserved_v (reg_index r) m in eval_idx_Z G d idx v' -> eval_idx_Z G d v v')
           (List.combine reg_available idxs).
Proof.
  cbv [get_asm_reg] in *.
  rewrite firstn_map, Forall2_map_r_iff in H.
  apply Forall2_flip in H.
  rewrite Forall2_forall_iff_nth_error in H.
  rewrite @Forall_forall in *.
  intros [r ?] H'; apply In_nth_error_value in H'.
  specialize (Hreg_wide_enough r).
  specialize (fun v pf => Hreg_wide_enough (nth_error_In _ v pf)).
  destruct H' as [n H'].
  specialize (H n).
  rewrite ListUtil.nth_error_firstn in H.
  rewrite nth_error_combine in H'.
  cbv [option_eq] in H.
  cbv [R_regs_preserved_v].
  repeat first [ progress break_innermost_match_hyps
               | progress inversion_option
               | progress subst
               | progress inversion_pair
               | progress cbv [index_and_shift_and_bitcount_of_reg] in *
               | solve [ eauto ]
               | match goal with
                 | [ H : (forall reg, Option.is_Some (get_reg ?s (reg_index reg)) = true)
                     |- context[get_reg ?s (reg_index ?ri)] ]
                   => generalize (H ri); cbv [Option.is_Some]; break_innermost_match;
                      try congruence
                 | [ H : forall v, nth_error ?ls v = Some _ -> _ |- _ ]
                   => specialize (H _ ltac:(eassumption))
                 end ].
  all: specialize (Hex _ _ ltac:(eassumption) ltac:(eassumption)).
  all: destruct_head'_ex.
  all: erewrite <- Semantics_get_reg_eq_nth_default_of_R_regs by eassumption.
  all: eauto.
Qed.

Lemma R_mem_frame_cps_id {P : Prop} (HP : P) frame G d s
  : Lift1Prop.iff1 (R_mem frame G d s) (frame * (R_mem (emp P) G d s))%sep.
Proof.
  induction s as [|[? ?] s IH]; cbn [R_mem]; [ | rewrite IH ];
    SeparationLogic.cancel.
  cbn [seps]; apply SeparationLogic.Proper_emp_iff; tauto.
Qed.

Lemma R_mem_nil_iff G d P
  : Lift1Prop.iff1 (R_mem (emp P) G d nil) (emp P).
Proof. reflexivity. Qed.

Lemma R_mem_cons_iff G d v s P
  : Lift1Prop.iff1 (R_mem (emp P) G d (v :: s))
                   (R_cell64 G d (fst v) (snd v) * R_mem (emp P) G d s)%sep.
Proof. destruct v; reflexivity. Qed.

Lemma R_mem_app_iff G d s1 s2 P
  : Lift1Prop.iff1 (R_mem (emp P) G d (s1 ++ s2))
                   (R_mem (emp P) G d s1 * R_mem (emp P) G d s2)%sep.
Proof.
  induction s1 as [|? ? IH]; cbn [List.app].
  all: rewrite ?R_mem_nil_iff, ?R_mem_cons_iff, ?IH, ?(R_mem_frame_cps_id I (emp P)).
  { intro; rewrite ?SeparationLogic.sep_emp_l; tauto. }
  { SeparationLogic.ecancel. }
Qed.

Lemma R_mem_rev_iff G d s P
  : Lift1Prop.iff1 (R_mem (emp P) G d (List.rev s))
                   (R_mem (emp P) G d s).
Proof.
  induction s as [|? ? IH]; cbn [List.rev].
  all: rewrite ?R_mem_app_iff, ?R_mem_cons_iff, ?R_mem_nil_iff, ?IH, ?(R_mem_frame_cps_id I (emp P)).
  { SeparationLogic.cancel. }
  { assert (H : @Lift1Prop.iff1 Semantics.mem_state (emp P) (emp (P /\ P)))
      by (apply SeparationLogic.Proper_emp_iff; tauto).
    rewrite H at 3.
    SeparationLogic.cancel.
    cbn [seps]; intro.
    rewrite ?SeparationLogic.sep_emp_l; cbv [emp]; tauto. }
Qed.

Lemma R_mem_combine_array_iff_helper frame G d addrs val_idxs base_value base_word_value vals init
      (Haddrs : Forall2 (eval_idx_Z G d) addrs (List.map (fun i => Z.land (base_value + 8 * Z.of_nat i) (Z.ones 64)) (seq init (List.length vals))))
      (Hvals : Forall2 (eval_idx_Z G d) val_idxs vals)
      (Hbase : base_value = word.unsigned base_word_value)
  : Lift1Prop.iff1 (R_mem frame G d (List.combine addrs val_idxs))
                   (frame * array cell64 (word.of_Z 8) (word.add base_word_value (word.of_Z (8 * Z.of_nat init))) vals)%sep.
Proof.
  subst.
  revert dependent vals; intro vals; revert val_idxs vals init.
  induction addrs as [|addr addrs IH],
      val_idxs as [|val_idx val_idxs],
        vals as [|val vals];
    intro init; cbn [List.combine List.length seq List.map R_mem array]; intros;
    try (specialize (IH val_idxs vals (S init)); rewrite IH; clear IH).
  all: repeat first [ progress subst
                    | now inversion_one_head Forall2
                    | progress specialize_by_assumption
                    | match goal with
                      | [ H : Forall2 _ (_ :: _) (_ :: _) |- _ ] => rewrite Forall2_cons_cons_iff in H; destruct H
                      | [ |- Lift1Prop.iff1 (R_cell64 ?G ?d ?addr ?val_idx * ?P)%sep (cell64 ?x ?y * ?Q)%sep ]
                        => cut (Lift1Prop.iff1 P Q);
                           [ intros ->; progress SeparationLogic.cancel | ]
                      | [ |- Lift1Prop.iff1 (array ?cell ?sz ?init ?val) (array ?cell ?sz ?init' ?val) ]
                        => cut (init = init');
                           [ intros ->; reflexivity | try ZnWords ]
                      end
                    | progress (SeparationLogic.cancel; cbn [seps]) ].
  repeat
    repeat
    first [ progress destruct_head'_ex
          | progress destruct_head'_and
          | progress cbv [cell64 R_cell64 Lift1Prop.iff1 Lift1Prop.ex1 sep emp eval_idx_Z] in *
          | progress intros
          | progress subst
          | assumption
          | match goal with
            | [ |- map.split _ _ _ ] => eassumption
            | [ H : ?T, H' : ?T |- _ ] => clear H'
            | [ H : eval ?G ?d ?i ?v1, H' : eval ?G ?d ?i ?v2 |- _ ]
              => unique assert (v1 = v2) by (eapply eval_eval; eassumption);
                 try (subst v1 || subst v2); clear H'
            | [ |- iff _ _ ] => split
            | [ |- _ /\ _ ] => split
            | [ H : eval ?G ?d ?idx ?v1 |- eval ?G ?d ?idx ?v2 ]
              => cut (v2 = v1); [ intros ->; exact H | ]
            | [ H : word.unsigned ?x = ?y |- _ ]
              => is_var x; assert (x = word.of_Z y) by (now rewrite <- H, word.of_Z_unsigned);
                 subst x
            | [ H : ?y = word.unsigned ?x |- _ ]
              => is_var x; assert (x = word.of_Z y) by (now rewrite H, word.of_Z_unsigned);
                 subst x
            | [ H : context[word.unsigned (word.of_Z _)] |- _ ]
              => rewrite word.unsigned_of_Z in H
            | [ |- ?x = ?x ] => reflexivity
            | [ |- le_combine _ = le_combine _ ] => reflexivity
            | [ |- OfListWord.map.of_list_word_at _ ?x = OfListWord.map.of_list_word_at _ ?x ] => apply f_equal2
            | [ |- ?x = _ ] => is_evar x; reflexivity
            | [ |- ?G ] => assert_fails has_evar G; ZnWords
            | [ |- ex _ ] => eexists
            end
          | rewrite Z.land_ones by lia ].
Qed.

Lemma R_mem_combine_array_iff frame G d addrs val_idxs base_value base_word_value vals
      (Haddrs : Forall2 (eval_idx_Z G d) addrs (List.map (fun i => Z.land (base_value + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length vals))))
      (Hvals : Forall2 (eval_idx_Z G d) val_idxs vals)
      (Hbase : base_value = word.unsigned base_word_value)
  : Lift1Prop.iff1 (R_mem frame G d (List.combine addrs val_idxs))
                   (frame * array cell64 (word.of_Z 8) base_word_value vals)%sep.
Proof.
  rewrite R_mem_combine_array_iff_helper by eassumption.
  SeparationLogic.cancel; cbn [seps].
  match goal with
  | [ |- Lift1Prop.iff1 (array ?cell ?sz ?init ?val) (array ?cell ?sz ?init' ?val) ]
    => cut (init = init');
       [ intros ->; reflexivity | ]
  end.
  ZnWords.
Qed.

Lemma R_mem_flat_map_R_list_scalar_or_array_iff_emp {dereference_scalar:bool} G d
  : forall (idxs : list (idx + idx * list idx)) base_vals addr_idxs addr_vals base_vals_words
           (Haddrs : Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals)
           (Hidxs : Forall2 (fun idx' v
                             => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                                match idx' with
                                | inl idx'
                                  => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                                | inr (base', addrs')
                                  => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                     /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                                end)
                            idxs base_vals)
           (Hidxs' : Forall2 (fun idx addr_idx
                              => match idx, addr_idx with
                                 | inl idx, inl addr_idx
                                   => if dereference_scalar
                                      then True
                                      else forall v v', eval_idx_Z G d idx v -> eval_idx_Z G d addr_idx v' -> v = v'
                                 | inr (base, idxs), inr addr_idxs
                                   => List.length idxs = List.length addr_idxs
                                 | inl _, inr _ | inr _, inl _ => False
                                 end)
                             idxs addr_idxs)
           (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals),
    Lift1Prop.iff1
      (R_mem (emp True) G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                    | inl _, _ | _, inl _ => []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    end)
                (List.combine idxs addr_idxs)))
      (R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals base_vals_words)%sep.
Proof.
  pose dereference_scalar as dereference_scalar'.
  induction idxs as [|idx idxs IH],
      base_vals as [|base_val base_vals],
        addr_idxs as [|addr_idx addr_idxs],
          addr_vals as [|addr_val addr_vals],
            base_vals_words as [|base_vals_word base_vals_words];
    try specialize (IH base_vals addr_idxs addr_vals base_vals_words);
    do 3 (intro H; inversion H; clear H); subst.
  all: cbv [R_list_scalar_or_array] in *; cbn [List.map flat_map R_mem fold_right List.combine List.length]; intros; inversion_nat_eq; inversion_list.
  all: SeparationLogic.cancel; cbn [seps].
  all: [ > ].
  rewrite R_mem_app_iff, IH by assumption; clear IH.
  repeat first [ progress subst
               | progress cbn [R_mem] in *
               | progress destruct_head'_and
               | match goal with
                 | [ H : eval_idx_or_list_idx _ _ _ _ |- _ ] => cbv [eval_idx_or_list_idx] in H
                 | [ H : forall v v', ?P v -> ?Q v' -> v = v', H' : ?P _, H'' : ?Q _ |- _ ]
                   => eapply H in H''; [ | exact H' ]; subst
                 | [ |- Lift1Prop.iff1 (emp _) (emp _) ] => apply SeparationLogic.Proper_emp_iff
                 | [ |- True <-> _ ] => split; try tauto; intros _
                 | [ |- word.unsigned _ = _ ] => rewrite ?Z.land_ones; ZnWords
                 | [ |- Lift1Prop.iff1 (R_mem (emp True) _ _ (List.combine _ _)) (array _ _ _ _) ]
                   => rewrite R_mem_combine_array_iff;
                      [ now SeparationLogic.cancel | try eassumption .. ]
                 | [ H : Forall2 ?P ?l (List.map ?f (seq 0 ?n)) |- Forall2 ?P ?l (List.map ?f' (seq 0 ?n')) ]
                   => cut (n = n');
                      [ (intros <-);
                        erewrite map_ext; [ exact H | cbv beta; intro ]
                      | ]
                 | [ H : Forall2 _ _ _ |- List.length _ = List.length _ ]
                   => apply eq_length_Forall2 in H
                 end
               | congruence
               | reflexivity
               | progress break_innermost_match
               | progress break_innermost_match_hyps
               | exfalso; assumption
               | progress (SeparationLogic.cancel; cbn [seps])
               | progress cbv [R_scalar_or_array] ].
  all: [ > lazymatch goal with
           | [ |- Lift1Prop.iff1 (R_cell64 _ _ _ _) (cell64 _ _) ]
             => idtac
           end ].
  all: repeat
         repeat
         first [ progress cbv [R_cell64 cell64 Lift1Prop.iff1 Lift1Prop.ex1 emp sep eval_idx_Z] in *
               | progress intros
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress subst
               | assumption
               | match goal with
                 | [ |- iff _ _ ] => split
                 | [ |- _ /\ _ ] => split
                 | [ H : eval ?G ?d ?i ?v1, H' : eval ?G ?d ?i ?v2 |- _ ]
                   => unique assert (v1 = v2) by (eapply eval_eval; eassumption);
                      try (subst v1 || subst v2); clear H'
                 | [ H : eval ?G ?d ?idx ?v1 |- eval ?G ?d ?idx ?v2 ]
                   => cut (v2 = v1); [ intros ->; exact H | ]
                 | [ H : word.unsigned ?x = ?y |- _ ]
                   => is_var x; assert (x = word.of_Z y) by (now rewrite <- H, word.of_Z_unsigned);
                      subst x
                 | [ H : ?y = word.unsigned ?x |- _ ]
                   => is_var x; assert (x = word.of_Z y) by (now rewrite H, word.of_Z_unsigned);
                      subst x
                 | [ H : context[word.unsigned (word.of_Z _)] |- _ ]
                   => rewrite word.unsigned_of_Z in H
                 | [ |- map.split _ _ _ ] => eassumption
                 | [ H : ?T, H' : ?T |- _ ] => clear H'
                 | [ |- ?x = ?x ] => reflexivity
                 | [ |- le_combine _ = le_combine _ ] => reflexivity
                 | [ |- OfListWord.map.of_list_word_at _ ?x = OfListWord.map.of_list_word_at _ ?x ] => apply f_equal2
                 | [ |- word.unsigned _ = _ ] => rewrite ?Z.land_ones; ZnWords
                 | [ |- _ = word.of_Z _ ] => rewrite ?Z.land_ones; ZnWords
                 | [ |- ex _ ] => eexists
                 end
               | reflexivity ].
Qed.


Lemma R_mem_flat_map_R_list_scalar_or_array_iff {dereference_scalar:bool} frame G d
      (idxs : list (idx + idx * list idx)) base_vals addr_idxs addr_vals base_vals_words
      (Haddrs : Forall2 (eval_idx_or_list_idx G d) addr_idxs addr_vals)
      (Hidxs : Forall2 (fun idx' v
                        => let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
                           match idx' with
                           | inl idx'
                             => eval_idx_Z G d idx' (Z.land v (Z.ones 64))
                           | inr (base', addrs')
                             => eval_idx_Z G d base' (Z.land v (Z.ones 64))
                                /\ Forall2 (eval_idx_Z G d) addrs' (addrs_vals_of v addrs')
                           end)
                       idxs base_vals)
      (Hidxs' : Forall2 (fun idx addr_idx
                         => match idx, addr_idx with
                            | inl idx, inl addr_idx
                              => if dereference_scalar
                                 then True
                                 else forall v v', eval_idx_Z G d idx v -> eval_idx_Z G d addr_idx v' -> v = v'
                            | inr (base, idxs), inr addr_idxs
                              => List.length idxs = List.length addr_idxs
                            | inl _, inr _ | inr _, inl _ => False
                            end)
                        idxs addr_idxs)
      (Hbase_vals_words : List.map word.unsigned base_vals_words = base_vals)
  : Lift1Prop.iff1
      (R_mem frame G d
             (List.flat_map
                (fun '(idx', idx)
                 => match idx', idx with
                    | inl addr_or_val, inl val => if dereference_scalar then [(addr_or_val, val)] else []
                    | inl _, _ | _, inl _ => []
                    | inr (base', addrs'), inr items
                      => List.combine addrs' items
                    end)
                (List.combine idxs addr_idxs)))
      (frame * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals base_vals_words)%sep.
Proof.
  intros.
  rewrite ?(R_mem_frame_cps_id I frame).
  erewrite R_mem_flat_map_R_list_scalar_or_array_iff_emp by eassumption.
  reflexivity.
Qed.

Import Coq.Strings.String.
Import Coq.Lists.List.
Import Crypto.Util.Option.
Axiom TODO : string -> Prop.
Axiom todo : forall s, TODO s.
Lemma Forall2_rets_of_R_mem {A} G frame d mem_st m' idxs base_len_base_vals rets
      (Hbase : Forall2 (fun idxs '((base, len), base_val)
                        => match idxs, (base:option A), len with
                           | inr idxs, Some base, Some len
                             => Forall2 (eval_idx_Z G d) idxs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
                           | _, _, _ => False
                           end)
                       idxs
                       base_len_base_vals)
      (Hmem : R_mem frame G d mem_st m')
      (Hrets : Some rets
               = Option.List.lift
                   (List.map (fun idxs
                              => match idxs : idx + list idx with
                                 | inr idxs => option_map inr (Option.List.lift (List.map (fun a => load a mem_st) idxs))
                                 | inl idx => None (* Some (inl idx) ?? *)
                                 end)
                             idxs))
  : exists runtime_rets,
    TODO "Forall2_rets_of_R_mem runtime_rets R_mem postcondition"%string
    /\ Forall2 (eval_idx_or_list_idx G d) rets runtime_rets.
Proof.
  revert dependent idxs; revert base_len_base_vals.
  induction rets as [|ret rets IH],
      base_len_base_vals as [|base_len_base_val base_len_base_vals],
        idxs as [|idx idxs];
    try specialize (IH base_len_base_vals idxs).
  all: repeat first [ progress cbn [List.map fold_right]
                    | progress cbv [Option.List.lift Crypto.Util.Option.bind option_map] in *
                    | progress intros
                    | progress subst
                    | progress destruct_head'_ex
                    | progress destruct_head'_and
                    | progress inversion_option
                    | progress inversion_list
                    | progress specialize_by_assumption
                    | progress specialize_by reflexivity
                    | match goal with
                      | [ H : Forall2 _ (_ :: _) _ |- _ ] => inversion H; clear H
                      | [ H : Forall2 _ nil _ |- _ ] => inversion H; clear H
                      | [ H : fold_right _ (Some nil) (List.map (fun a => load a _) _) = Some _ |- _ ]
                        => eapply load_eval_R_mem_eval_Forall2 in H; [ | eassumption .. ]
                      end
                    | break_innermost_match_step
                    | break_innermost_match_hyps_step
                    | progress break_match_hyps
                    | now eexists nil; split; auto using todo
                    | now eexists (inr _ :: _); eauto ].
Qed.

Local Ltac saturate_lengths_step :=
  let do_with ls :=
    lazymatch ls with
    | @List.map ?A ?B ?f ?x
      => unique pose proof (@map_length A B f x)
    | @firstn ?A ?n ?x
      => unique pose proof (@firstn_length A n x)
    | @skipn ?A ?n ?x
      => unique pose proof (@skipn_length A n x)
    | @seq ?start ?len
      => unique pose proof (@seq_length start len)
    | @List.app ?A ?l ?l'
      => unique pose proof (@app_length A l l')
    end in
  match goal with
  | [ |- context[length (?x ++ ?y)] ]
    => rewrite (app_length x y)
  | [ H : Forall2 _ ?y ?x |- _ ]
    => unique assert (length y = length x) by eapply eq_length_Forall2, H
  | [ |- context[length ?ls] ]
    => do_with ls
  | [ H : context[length ?ls] |- _ ]
    => do_with ls
  end.
Local Ltac saturate_lengths := repeat saturate_lengths_step.

Local Lemma connect_Forall2_app_connect {A B C R1 R2 R3 R4 ls1 ls1' ls2 ls2' ls3}
      (H1 : @Forall2 A B R1 ls1 ls1')
      (H2 : @Forall2 A B R2 ls2 ls2')
      (H3 : @Forall2 _ C R3 (ls1' ++ ls2') ls3)
      (Ha : forall a1 b1 c, R1 a1 b1 -> R3 b1 c -> R4 a1 c : Prop)
      (Hb : forall a2 b2 c, R2 a2 b2 -> R3 b2 c -> R4 a2 c : Prop)
  : @Forall2 _ C R4 (ls1 ++ ls2) ls3.
Proof.
  saturate_lengths.
  rewrite app_length in *.
  rewrite !@Forall2_forall_iff_nth_error in *; intro i.
  repeat first [ progress rewrite ?@nth_error_app in *
               | match goal with
                 | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                   => specialize (H i); lazymatch type of H with context[nth_error ls i] => idtac end
                 | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                   => specialize (H i); lazymatch type of H with context[nth_error ls i] => idtac end
                 end ].
  all: repeat first [ progress cbv [option_eq] in *
                    | progress cbn [List.length] in *
                    | progress inversion_option
                    | progress subst
                    | lia
                    | solve [ eauto ]
                    | match goal with
                      | [ H : ?x < ?y, H' : context[(?x - ?y)%nat] |- _ ]
                        => rewrite (@not_le_minus_0 x y) in H' by lia
                      | [ H : nth_error ?l 0 = _ |- _ ] => is_var l; destruct l; cbn [nth_error] in H
                      | [ H : nth_error ?ls ?i = Some _, H' : ~?i < length ?ls |- _ ]
                        => rewrite nth_error_length_error in H by lia
                      | [ H : nth_error ?ls ?i = _, H' : nth_error ?ls ?i' = _ |- _ ]
                        => let H'' := fresh in
                           assert (H'' : i = i') by lia; rewrite H'' in *; rewrite H in H'
                      end
                    | break_innermost_match_step
                    | break_innermost_match_hyps_step ].
Qed.

(* turn off once proof is finished *)
Local Ltac debug_run tac := tac ().
Local Ltac handle_R_regs _ :=
  lazymatch goal with
  | [ H : R _ _ (update_dag_with (init_symbolic_state _) _) ?m
      |- R_regs _ _ (set_reg (fold_left _ _ (Symbolic.symbolic_reg_state (init_symbolic_state _))) _ _) ?m' ]
    => debug_run ltac:(fun _ => idtac "R => R_regs set_reg start");
       (*in_evars_do ltac:(destruct_head' symbolic_state; cbn [Symbolic.symbolic_reg_state Symbolic.dag_state] in * );*)
      eapply R_regs_subsumed_get_reg_same_eval;
      [ eapply R_regs_subsumed;
        [ apply H | now eauto ]
      | let finish_some_reg _ :=
          cbv [R_regs_preserved_v];
          match goal with
          | [ H : (forall reg, Option.is_Some (get_reg ?s (reg_index reg)) = true)
              |- context[get_reg ?s (reg_index ?ri)] ]
            => generalize (H ri); cbv [Option.is_Some]; break_innermost_match;
               try congruence
          end;
          eauto using lift_eval_idx_Z_impl in
        let rec do_stuff _
          := lazymatch goal with
             | [ |- R_regs_preserved _ _ _ ?x ?x ] => reflexivity
             | [ |- R_regs_preserved _ _ _ _ (set_reg _ _ _) ]
               => apply R_regs_preserved_set_reg;
                  [ do_stuff ()
                  | solve [ intros; finish_some_reg () ] ]
             | [ |- R_regs_preserved _ _ _ _ (fold_left _ _ _) ]
               => apply R_regs_preserved_fold_left_set_reg_index;
                  [ do_stuff ()
                  | lazymatch goal with
                    | [ H : Forall2 _ ?x (firstn (List.length ?x) (get_asm_reg _ ?reg_available))
                        |- Forall _ (List.combine ?reg_available ?x) ]
                      => eapply Forall2_R_regs_preserved_same_helper;
                         lazymatch goal with
                         | [ |- Forall2 _ x (firstn (List.length x) (get_asm_reg _ reg_available)) ]
                           => eapply Forall2_weaken; [ | exact H ];
                              cbv beta; intros *; break_innermost_match;
                              intros; destruct_head'_and; eauto using lift_eval_idx_Z_impl
                         | [ H : R _ _ _ _ |- R_regs _ _ _ _ ] => eapply R_regs_subsumed; [ apply H | eauto ]
                         | _ => first [ assumption
                                      | intros; finish_some_reg ()
                                      | idtac ]
                         end
                    end ]
             end in
        do_stuff () ];
      [ match goal with |- ?G => idtac "TODO" G end .. ];
      debug_run ltac:(fun _ => idtac "R => R_regs set_reg end")
  end.

Theorem symex_asm_func_M_correct
        d frame asm_args_out asm_args_in (G : symbol -> option Z) (s := init_symbolic_state d)
        (s' : symbolic_state) (m : machine_state) (output_types : type_spec) (stack_size : nat) (stack_base : Naive.word 64)
        (inputs : list (idx + list idx)) (callee_saved_registers : list REG) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (H : symex_asm_func_M callee_saved_registers output_types stack_size inputs reg_available asm s = Success (Success rets, s'))
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (runtime_reg : list Z)
        (*(Hasm_reg : get_asm_reg m reg_available = runtime_reg)*)
        (runtime_callee_saved_registers : list Z)
        (*(Hasm_callee_saved_registers : get_asm_reg m callee_saved_registers = runtime_callee_saved_registers)*)
        (HR : R_runtime_input frame output_types runtime_inputs stack_size stack_base asm_args_out asm_args_in reg_available runtime_reg callee_saved_registers runtime_callee_saved_registers m)
        (Hd_ok : gensym_dag_ok G d)
        (d' := s'.(dag_state))
        (H_enough_reg : (List.length output_types + List.length runtime_inputs <= List.length reg_available)%nat)
        (Hcallee_saved_reg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) callee_saved_registers)
        (Hreg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : exists m' G'
           (runtime_rets : list (Z + list Z)),
    (DenoteLines m asm = Some m'
     /\ R_runtime_output frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size stack_base asm_args_out asm_args_in callee_saved_registers runtime_callee_saved_registers m'
     /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  pose proof (word_args_to_Z_args_bounded word_runtime_inputs).
  cbv [symex_asm_func_M Symbolic.bind ErrorT.bind lift_dag] in H.
  break_match_hyps; destruct_head'_prod; destruct_head'_unit; cbn [fst snd] in *; try discriminate; [].
  repeat first [ progress subst
               | match goal with
                 | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                 | [ x := ?y |- _ ] => subst x
                 end ].
  cbv [R_runtime_input] in HR; repeat (destruct_head'_ex; destruct_head'_and).
  let HR := lazymatch goal with HR : sep _ _ (machine_mem_state m) |- _ => HR end in
  destruct (init_symbolic_state_ok m G _ _ ltac:(eassumption) ltac:(eassumption) HR) as [G1 ?]; destruct_head'_and.
  let in_evars_do tac :=
    let do_with ev :=
      let H := fresh in
      pose ev as H;
      (instantiate (1:=ltac:(progress tac)) in (value of H)); subst H in
    repeat match goal with
           | [ H : context[?ev] |- _ ] => is_evar ev; do_with ev
           | [ H := context[?ev] |- _ ] => is_evar ev; do_with ev
           | [ |- context[?ev] ] => is_evar ev; do_with ev
           end in
  repeat first [ progress destruct_head'_ex
               | progress destruct_head'_and
               | progress cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *
               | solve [ auto ]
               | match reverse goal with
                 | [ H : build_inputs _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_inputs start");
                      move H at bottom; eapply build_inputs_ok in H;
                      [
                      | lazymatch goal with
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | [ |- Forall2 val_or_list_val_matches_spec _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [ | assumption ];
                      debug_run ltac:(fun _ => idtac "build_inputs end")
                 | [ H : R _ _ (init_symbolic_state _) _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "update R start");
                      eapply R_subsumed in H; [ | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "update R end")
                 | [ H : build_merge_base_addresses _ _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_base_addresses start");
                      move H at bottom;
                      eapply build_merge_base_addresses_ok
                        with (runtime_reg := runtime_reg (*get_asm_reg m reg_available*))
                        in H;
                      [
                      | clear H;
                        lazymatch goal with
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [ | try assumption .. ];
                      [ | repeat first [ match goal with
                                         | [ H1 : Forall2 ?R1 ?l1 (firstn ?n1 (get_asm_reg ?m ?reg_available)),
                                               H2 : Forall2 ?R2 ?l2 (firstn ?n2 (skipn ?n1 (get_asm_reg ?m ?reg_available)))
                                             |- Forall2 ?R3 (?l1 ++ ?l2) (firstn ?n3 (get_asm_reg ?m ?reg_available)) ]
                                           => replace n3 with (n1 + n2) by lia;
                                              rewrite <- (firstn_skipn n1 (firstn (n1 + n2) (get_asm_reg m reg_available))), firstn_firstn, skipn_firstn, minus_plus, Nat.min_l by lia;
                                              apply Forall2_app; eapply Forall2_weaken; [ | exact H1 | | exact H2 ];
                                              cbv beta; intros *;
                                              [ refine (fun x => or_introl x)
                                              | refine (fun x => or_intror x) ]
                                         end
                                       | lia
                                       | saturate_lengths_step
                                       | progress intros *
                                       | break_innermost_match_step
                                       | progress subst
                                       | progress destruct_head'_or
                                       | progress intros
                                       | eapply connect_Forall2_app_connect; [ eassumption | eassumption | try eassumption | .. ]
                                       | solve [ eauto using lift_eval_idx_Z_impl ]
                                       | progress cbv [eval_idx_or_list_idx] in * ] .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_base_addresses end")
                 | [ H : build_merge_stack_placeholders _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders start");
                      subst stack_size;
                      move H at bottom; eapply build_merge_stack_placeholders_ok in H;
                      [ destruct H as [G_final H]
                      | lazymatch goal with
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [ | try assumption .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders end")
                 | [ H : mapM _ callee_saved_registers _ = _ |- @ex ?T _ ]
                   => lazymatch T with
                      | (*runtime_rets*) list (Z + list Z) => idtac
                      | (*m'*) machine_state => idtac
                      end;
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers start");
                      eapply (@mapM_GetReg_ok_bounded G_final) in H;
                      [ | clear H; try assumption .. ];
                      [
                      | lazymatch goal with
                        | [ |- Forall2 (fun idx v => forall idx', idx = Some idx' -> eval_idx_Z _ _ idx' v)
                                       (List.map (get_reg _) (List.map reg_index _))
                                       _ ]
                          => destruct_head' symbolic_state; cbn [Symbolic.symbolic_reg_state Symbolic.dag_state] in *; subst;
                             eapply Forall2_get_reg_of_R;
                             [ lazymatch goal with
                               | [ |- R_regs _ _ _ _ ]
                                 => try match goal with H : R _ _ _ _ |- _ => eapply H end
                               | _ => idtac
                               end .. ];
                             repeat first [ assumption
                                          | reflexivity
                                          | rewrite map_length ]
                        | [ |- gensym_dag_ok _ _ ] => eassumption
                        | _ => idtac
                        end .. ];
                      [
                      | lazymatch goal with
                        | [ |- Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z)
                                      (List.map (Semantics.get_reg _) _) ]
                          => apply get_reg_bounded
                        | _ => idtac
                        end;
                        repeat first [ assumption
                                     | reflexivity
                                     | rewrite map_length ] .. ];
                      [
                      | lazymatch goal with
                        | [ |- R_regs _ _ _ _ ] => handle_R_regs ()
                        | _ => idtac
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers end")
                 | [ H : SymexLines _ _ = Success _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "SymexLines start");
                      eapply SymexLines_R in H;
                      [ destruct H as [m' H];
                        exists m', G_final;
                        repeat (destruct_head'_ex; destruct_head'_and);
                        repeat match goal with
                               | [ H : R _ ?G ?s _ |- _ ]
                                 => unique assert (gensym_dag_ok G s) by (destruct s; apply H)
                               end
                      | clear H;
                        lazymatch goal with
                        | [ H : R _ _ _ ?m |- R ?frame' _ _ ?m' ]
                          => move H at bottom; unify frame frame'; unify m m'; cbv [update_dag_with R];
                             destruct_head' symbolic_state;
                             cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *;
                             subst;
                             destruct_head'_and;
                             repeat first [ solve [ auto ]
                                          | progress cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *
                                          | progress subst
                                          | eapply R_flags_subsumed; [ eassumption | now eauto ]
                                          | match goal with
                                            | [ |- _ /\ _ ] => split
                                            | [ |- R_flags _ _ _ _ ]
                                              => progress
                                                   (cbv [R update_dag_with] in *;
                                                    destruct_head'_and)
                                            | [ |- gensym_dag_ok _ _ ]
                                              => progress destruct_head' symbolic_state
                                            end ]
                        | _ => idtac
                        end .. ];
                      [
                      | lazymatch goal with
                        | [ |- R_regs _ _ _ _ ] => handle_R_regs ()
                        | _ => auto
                        end .. ];
                      [ | match goal with |- ?G => idtac "TODO" G end .. ];
                      debug_run ltac:(fun _ => idtac "SymexLines end")
                 | [ H : LoadOutputs _ _ _ = _ |- exists runtime_rets : list (Z + list Z), _ ]
                   => debug_run ltac:(fun _ => idtac "LoadOutputs start");
                      eapply LoadOutputs_ok in H;
                      [ | clear H; try eassumption .. ];
                      [
                      | match goal with
                        | [ |- Forall2 _ (firstn _ _) _ ]
                          => eapply Forall2_firstn;
                             eapply Forall2_weaken; [ | eassumption ]; cbv beta; intros *; break_innermost_match; eauto using lift_eval_idx_Z_impl
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "LoadOutputs end")
                 | [ H : Some ?rets = Option.List.lift (List.map (fun idxs => match idxs with inr idxs' => option_map inr (Option.List.lift (List.map (fun a => load a _) idxs')) | inl _ => _ end) _) |- exists runtime_rets : list (Z + list Z), _ ]
                   => debug_run ltac:(fun _ => idtac "Forall2_rets_of_R_mem start");
                      eapply Forall2_rets_of_R_mem in H;
                      [ destruct H as [runtime_rets H]; exists runtime_rets
                      | clear H;
                        lazymatch goal with
                        | [ |- Forall2 _ _ _ ] => eassumption
                        | [ |- R_mem _ _ _ _ _ ]
                          => eapply R_mem_subsumed;
                             lazymatch goal with
                             | [ H : R ?frame ?G ?ss ?ms |- R_mem ?frame' ?G' ?d ?ss' ?ms' ]
                               => let unif_or_eq x y := first [ unify x y | let H := fresh in assert (H : y = x) by congruence; rewrite H ] in
                                  unif_or_eq frame frame'; unif_or_eq G G';
                                  unif_or_eq (Symbolic.dag_state ss) d;
                                  unif_or_eq (Symbolic.symbolic_mem_state ss) ss';
                                  unif_or_eq (machine_mem_state ms) ms';
                                  cbv [R] in H;
                                  destruct_head' symbolic_state; apply H
                             | _ => eauto
                             end
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "Forall2_rets_of_R_mem end")
                 end
               | progress repeat (apply conj; eauto 10; []) ].
  all: destruct_head' symbolic_state; cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *; subst.
  { cbv [R_runtime_output R update_dag_with] in *; destruct_head'_and.
    do 2 eexists.
    repeat match goal with |- _ /\ _ => split end.
    cbv [Semantics.machine_reg_state] in *.
    all: lazymatch goal with
         | [ H : R_regs _ _ _ ?m' |- Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ ?m') ]
           => cbv [R_regs R_reg] in H;
              rewrite Tuple.fieldwise_to_list_iff, Forall2_forall_iff_nth_error in H;
              rewrite Forall_forall_iff_nth_error_match;
              let i := fresh "i" in
              intro i; specialize (H i); cbv [option_eq] in H;
              revert H; break_innermost_match; try tauto; try discriminate;
              rewrite ?Z.land_ones by lia;
              try now clear; intros [_ ?]; Z.to_euclidean_division_equations; nia
         | [ |- get_asm_reg _ ?callee_saved_registers = get_asm_reg _ ?callee_saved_registers ]
           => cbv [get_asm_reg] in *;
              revert dependent callee_saved_registers;
              intro callee_saved_registers;
              rewrite ?eq_filter_nil_Forall_iff, <- !Forall2_eq, ?Forall2_map_map_iff, ?Forall2_map_r_iff, ?Forall2_map_l_iff, ?Forall2_forall_iff_nth_error, ?Forall_forall_iff_nth_error_match;
              intros;
              repeat match goal with
                     | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                       => specialize (H i)
                     | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                       => specialize (H i)
                     | [ H : context[nth_error (List.combine ?ls _) _] |- context[nth_error ?ls ?i] ]
                       => specialize (H i)
                     end;
              rewrite ?@nth_error_combine in *;
              cbv [option_eq eval_idx_Z] in *;
              repeat first [ exfalso; assumption
                           | reflexivity
                           | assumption
                           | progress inversion_option
                           | progress subst
                           | match goal with
                             | [ H : negb _ = false |- _ ] => rewrite Bool.negb_false_iff in H; reflect_hyps
                             | [ H : eval _ _ ?x ?v, H' : eval _ _ ?x ?v' |- _ ]
                               => unique assert (v = v') by eauto 10 using eval_eval
                             end
                           | break_innermost_match_step
                           | break_innermost_match_hyps_step ]
         | _ => idtac
         end.
    (* what's left:
  Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) ?stack_placeholder_values

goal 2 (ID 17077) is:
 Datatypes.length x = Datatypes.length ?stack_placeholder_values
goal 3 (ID 17080) is:
 Forall2 val_or_list_val_matches_spec ?input_placeholder_values
   (type_spec_of_runtime (word_args_to_Z_args word_runtime_inputs))
goal 4 (ID 17083) is:
 Forall
   (fun v : Z + list Z =>
    match v with
    | inl v0 => (0 <= v0 < 2 ^ 64)%Z
    | inr vs => Forall (fun v0 : Z => (0 <= v0 < 2 ^ 64)%Z) vs
    end) ?input_placeholder_values
goal 5 (ID 17084) is:
 (frame ⋆ R_list_scalar_or_array runtime_rets asm_args_out
  ⋆ R_list_scalar_or_array ?input_placeholder_values asm_args_in
  ⋆ array cell64 (word.of_Z 8) stack_base ?stack_placeholder_values)%sep m'
     *)
    1-5: [ > match goal with |- ?G => idtac "TODO" G end .. ].
    1-5: shelve. }
  { lazymatch goal with
    | [ H : R _ _ (update_dag_with _ _) _ |- R_mem _ _ _ _ ?m ]
      => cbv [R update_dag_with] in H; destruct_head'_and;
         lazymatch goal with
         | [ H : R_mem ?P ?G ?d ?st ?m |- R_mem ?P' ?G' ?d' ?st' ?m ]
           => let H' := fresh in
              assert (H' : R_mem P G' d' st m);
              [ eapply R_mem_subsumed; [ exact H | solve [ eauto ] ]
              | clear H;
                revert H'; generalize m;
                change (Lift1Prop.impl1 (R_mem P G' d' st) (R_mem P' G' d' st'));
                cut (Lift1Prop.iff1 (R_mem P G' d' st) (R_mem P' G' d' st'));
                [ intros ->; reflexivity | ] ]
         end
    end.
    repeat
      first [ match goal with
              | [ |- context[R_mem ?frame _ _ _] ]
                => lazymatch frame with
                   | emp _ => fail
                   | _ => rewrite !(R_mem_frame_cps_id I frame)
                   end
              | [ |- context[R_mem (emp _) _ _ (_ ++ _)] ]
                => rewrite R_mem_app_iff
              | [ |- context[R_mem (emp _) _ _ (List.rev _)] ]
                => rewrite R_mem_rev_iff
              | [ |- context[R_mem (emp _) _ _ (List.combine _ _)] ]
                => erewrite R_mem_combine_array_iff;
                   [
                   | lazymatch goal with
                     | [ |- Forall2 _ _ _ ] => eapply Forall2_weaken; [ | eassumption ]; eauto using lift_eval_idx_Z_impl
                     | [ |- (Tuple.nth_default 0 (reg_index _) _ - 8 * Z.of_nat (Datatypes.length _))%Z = word.unsigned _ ]
                       => erewrite <- Semantics_get_reg_eq_nth_default_of_R_regs by (eassumption + reflexivity); try eassumption
                     | _ => idtac
                     end .. ]
              | [ |- context[List.flat_map _ (_ ++ _)] ]
                => rewrite flat_map_app
              | [ |- context[List.combine ?ls (?l1 ++ ?l2)] ]
                => is_var ls; is_var l1;
                   rewrite <- (firstn_skipn (List.length l1) ls), combine_app_samelength
                     by (saturate_lengths; lia)
              end
            | progress (SeparationLogic.cancel; cbn [seps]) ].
    { saturate_lengths.
      erewrite !(R_mem_flat_map_R_list_scalar_or_array_iff_emp (dereference_scalar:=false)).
      all: [ >
           | saturate_lengths;
             try solve [ rewrite ?firstn_firstn;
                         eapply Forall2_weaken; [ | (idtac + eapply Forall2_firstn + eapply Forall2_skipn); eassumption ];
                         cbv beta zeta; intros *; break_innermost_match; intros;
                         destruct_head'_and;
                         eauto 10 using lift_eval_idx_Z_impl, lift_eval_idx_or_list_idx_impl, Forall2_weaken ];
             let rewrite_rev_on ls :=
               lazymatch ls with
               | firstn ?n ?ls
                 => lazymatch goal with
                    | [ H : _ = firstn ?n' ?ls |- _ ]
                      => cut (n = n');
                         [ intros ->; rewrite <- H | lia ]
                    end
               end in
             lazymatch goal with
             | [ |- List.map word.unsigned ?ls' = firstn ?n' ?zls ]
               => rewrite_rev_on zls
             | [ |- List.map word.unsigned ?ls' = skipn ?n' ?zls ]
               => rewrite_rev_on zls
             | _ => idtac
             end;
             repeat
               first [ rewrite @firstn_firstn in *
                     | rewrite @firstn_app in *
                     | rewrite @firstn_map in *
                     | rewrite @skipn_map in *
                     | rewrite Nat.sub_diag in *
                     | rewrite firstn_O in *
                     | rewrite app_nil_r in *
                     | rewrite firstn_all in *
                     | match goal with
                       | [ H : context[skipn (List.length ?x) (?x ++ _)] |- _ ]
                         => rewrite skipn_app_sharp in H by reflexivity
                       | [ |- List.map word.unsigned _ = List.map word.unsigned _ ] => reflexivity
                       | [ H : Forall2 _ ?ls _ |- Forall2 _ (firstn ?n' ?ls) _ ]
                         => let H' := fresh in
                            pose proof H as H';
                            apply (Forall2_firstn (n:=n')) in H;
                            apply (Forall2_skipn (n:=n')) in H'
                       | [ H : Forall2 _ ?ls _ |- Forall2 _ (skipn ?n' ?ls) _ ]
                         => let H' := fresh in
                            pose proof H as H';
                            apply (Forall2_firstn (n:=n')) in H;
                            apply (Forall2_skipn (n:=n')) in H'
                       | [ H : Forall2 _ ?ls (firstn (Nat.min ?x ?y) _) |- Forall2 _ ?ls _ ]
                         => first [ rewrite Nat.min_l in H by lia
                                  | rewrite Nat.min_r in H by lia ]
                       | [ _ : context[firstn ?n ?x], _ : context[firstn ?n' ?x'] |- _ ]
                         => let H := fresh in
                            constr_eq x x'; (* work around https://github.com/coq/coq/issues/15554 *)
                            assert_fails constr_eq n n';
                            lazymatch n with List.length ?ls => is_var ls end;
                            assert (H : n' = n) by congruence; rewrite H in *
                       end ];
             lazymatch goal with
             | [ |- Forall2 _ _ _ ]
               => repeat match goal with
                         | [ H : Forall2 _ ?ls _ |- context[Forall2 _ ?ls _] ]
                           => revert H
                         | [ H : Forall2 _ ?ls _ |- context[Forall2 _ _ ?ls] ]
                           => revert H
                         | [ H : Forall _ ?ls |- context[Forall2 _ ?ls _] ]
                           => revert H
                         | [ H : Forall _ ?ls |- context[Forall2 _ _ ?ls] ]
                           => revert H
                         | [ H : Forall2 _ _ ?ls |- context[Forall2 _ ?ls _] ]
                           => revert H
                         | [ H : Forall2 _ _ ?ls |- context[Forall2 _ _ ?ls] ]
                           => revert H
                         end;
                  rewrite !@Forall2_forall_iff_nth_error, !@Forall_forall_iff_nth_error_match;
                  cbv [option_eq];
                  intros;
                  repeat match goal with
                         | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                           => specialize (H i)
                         | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                           => specialize (H i)
                         end;
                  repeat first [ exfalso; assumption
                               | assumption
                               | progress cbv [eval_idx_or_list_idx eval_idx_Z] in *
                               | progress rewrite ?@nth_error_firstn, ?@nth_error_map, ?@nth_error_seq, ?@nth_error_skipn in *
                               | progress subst
                               | break_innermost_match_step
                               | break_innermost_match_hyps_step
                               | progress intros
                               | progress destruct_head'_and
                               | progress specialize_by_assumption
                               | progress specialize_by exact (inr nil)
                               | match goal with
                                 | [ H : eval _ _ ?x ?v, H' : eval _ _ ?x ?v' |- _ ]
                                   => unique assert (v = v') by eauto 10 using eval_eval
                                 | [ H : nth_error ?ls ?n = Some _ |- _ ]
                                   => unique assert ((n < List.length ls)%nat) by now eapply nth_error_value_length; eassumption
                                 | [ H : nth_error ?ls (List.length ?l1 + ?i) = Some ?v, H' : nth_error ?ls (List.length ?l2 + ?i) = Some ?v' |- _ ]
                                   => first [ is_var v | is_var v' ];
                                      let H'' := fresh in
                                      assert (H'' : List.length l1 = List.length l2) by congruence;
                                      rewrite H'' in *;
                                      assert (v = v') by congruence;
                                      (subst v || subst v')
                                 | [ H : (?x < 2^?n)%Z |- context[Z.land ?x (Z.ones ?n)] ]
                                   => rewrite Z.land_ones, Z.mod_small by lia
                                 end ]
             | _ => idtac
             end .. ];
        [ > repeat first [ rewrite Nat.sub_diag
                         | rewrite firstn_O
                         | rewrite app_nil_r
                         | rewrite skipn_app_sharp by congruence
                         | match goal with
                           | [ |- context[firstn ?n ?ls] ]
                             => replace n with (List.length ls) by congruence; rewrite firstn_all
                           end
                         | progress (SeparationLogic.cancel; cbn [seps]) ]
        | .. ]. }
Admitted.

Theorem symex_asm_func_correct
        frame asm_args_out asm_args_in (G : symbol -> option Z) (d : dag) (output_types : type_spec) (stack_size : nat) (stack_base : Naive.word 64)
        (inputs : list (idx + list idx)) (callee_saved_registers : list REG) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (s' : symbolic_state)
        (H : symex_asm_func d callee_saved_registers output_types stack_size inputs reg_available asm = Success (rets, s'))
        (d' := s'.(dag_state))
        (m : machine_state)
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (runtime_reg : list Z)
        (runtime_callee_saved_registers : list Z)
        (Hasm_reg : get_asm_reg m reg_available = runtime_reg)
        (HR : R_runtime_input frame output_types runtime_inputs stack_size stack_base asm_args_out asm_args_in reg_available runtime_reg callee_saved_registers runtime_callee_saved_registers m)
        (HG_ok : gensym_dag_ok G d)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : (exists m' G'
            (runtime_rets : list (Z + list Z)),
        DenoteLines m asm = Some m'
        /\ R_runtime_output frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size stack_base asm_args_out asm_args_in callee_saved_registers runtime_callee_saved_registers m'
        /\ (forall e n, eval G d e n -> eval G' d' e n)
        /\ gensym_dag_ok G' d'
        /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets).
Proof.
  cbv [symex_asm_func] in H; break_innermost_match_hyps; inversion_ErrorT; inversion_prod; subst; reflect_hyps.
  cbv [R]; break_innermost_match.
  let H := multimatch goal with H : _ = Success _ |- _ => H end in
  eapply symex_asm_func_M_correct in H; try eassumption; try apply surjective_pairing; try reflexivity.
  { destruct_head'_ex; destruct_head'_and.
    do 3 eexists; repeat match goal with |- _ /\ _ => apply conj end; try eassumption. }
  { subst runtime_inputs; apply eq_length_Forall2 in Hinputs; lia. }
Qed.

Theorem check_equivalence_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {assembly_callee_saved_registers' : assembly_callee_saved_registers_opt}
        {t}
        (frame : Semantics.mem_state -> Prop)
        (asm : Lines)
        (expr : API.Expr t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (Hwf : API.Wf expr)
        (H : check_equivalence asm expr arg_bounds out_bounds = Success tt)
        (st : machine_state)
        (PHOAS_args : type.for_each_lhs_of_arrow API.interp_type t)
        (word_args : list (Naive.word 64 + list (Naive.word 64)))
        (args := word_args_to_Z_args word_args)
        (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
        (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
        (output_types : type_spec := match simplify_base_type (type.final_codomain t) out_bounds with Success output_types => output_types | Error _ => nil end)
        (asm_args_out asm_args_in : list (Naive.word 64))
        (runtime_regs := get_asm_reg st assembly_calling_registers)
        (runtime_callee_saved_registers := get_asm_reg st assembly_callee_saved_registers)
        (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
        (stack_base := word.of_Z (Semantics.get_reg st rsp - 8 * Z.of_nat stack_size))
        (HR : R_runtime_input frame output_types args stack_size stack_base asm_args_out asm_args_in assembly_calling_registers runtime_regs assembly_callee_saved_registers runtime_callee_saved_registers st)
  : exists asm' st' (retvals : list (Z + list Z)),
    strip_ret asm = Success asm'
    /\ DenoteLines st asm' = Some st'
    /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
    /\ R_runtime_output frame retvals (type_spec_of_runtime args) stack_size stack_base asm_args_out asm_args_in assembly_callee_saved_registers runtime_callee_saved_registers st'.
Proof.
  subst stack_size.
  cbv beta delta [check_equivalence ErrorT.bind] in H.
  repeat match type of H with
         | (let n := ?v in _) = _
           => set v as n in H;
                lazymatch type of H with
                | (let n := ?v in ?rest) = ?rhs
                  => change (match v with n => rest end = rhs) in H
                end
         | match ?v with Success n => @?S n | Error e => @?E e end = ?rhs
           => let n := fresh n in
              let e := fresh e in
              destruct v as [n|e] eqn:?; [ change (S n = rhs) in H | change (E e = rhs) in H ];
                cbv beta in H
         | match ?v with pair a b => @?P a b end = ?rhs
           => let a := fresh a in
              let b := fresh b in
              destruct v as [a b] eqn:?; change (P a b = rhs) in H;
                cbv beta in H
         | match ?v with true => ?T | false => ?F end = ?rhs
           => let a := fresh a in
              let b := fresh b in
              destruct v eqn:?; [ change (T = rhs) in H | change (F = rhs) in H ];
                cbv beta in H
         end; try discriminate; [].
  reflect_hyps.
  subst.
  pose proof empty_gensym_dag_ok.
  let H := fresh in pose proof Hargs as H; eapply build_input_runtime_ok_nil in H; [ | eassumption .. ].
  pose proof (word_args_to_Z_args_bounded word_args).
  repeat first [ assumption
               | match goal with
                 | [ H : build_inputs _ _ = _ |- _ ] => move H at bottom; eapply build_inputs_ok in H; [ | eassumption .. ]
                 | [ H : symex_PHOAS ?expr ?inputs ?d = Success _, H' : build_input_runtime _ ?ri = Some _ |- _ ]
                   => move H at bottom; eapply symex_PHOAS_correct with (runtime_inputs:=ri) in H; [ | eassumption .. ]
                 | [ H : symex_asm_func _ _ _ _ _ _ _ = Success _ |- _ ]
                   => move H at bottom; eapply symex_asm_func_correct in H;
                      [ | try (eassumption + apply surjective_pairing + reflexivity) .. ];
                      [ | clear H; eapply Forall2_weaken; [ apply lift_eval_idx_or_list_idx_impl | eassumption ] ]
                 end
               | progress destruct_head'_ex
               | progress destruct_head'_and
               | progress inversion_prod
               | progress inversion_ErrorT
               | progress subst
               | match goal with
                 | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                   => rewrite H in H'; inversion_option
                 | [ H : forall args, Forall2 ?P args ?v -> Forall2 _ _ _, H' : Forall2 ?P _ ?v |- _ ]
                   => specialize (H _ H')
                 | [ Himpl : forall e n, eval ?G1 ?d1 e n -> eval ?G2 ?d2 e n,
                       H1 : Forall2 (eval_idx_or_list_idx ?G1 ?d1) ?PHOAS_output ?r1,
                       H2 : Forall2 (eval_idx_or_list_idx ?G2 ?d2) ?PHOAS_output ?r2
                       |- _ ]
                   => assert_fails constr_eq r1 r2;
                      assert (r1 = r2) by (eapply eval_eval_idx_or_list_idx_Forall2_gen; eassumption);
                      subst
                 | [ H := _ |- _ ] => subst H
                 end ].
  do 3 eexists; repeat apply conj; try eassumption; trivial.
Qed.

Theorem generate_assembly_of_hinted_expr_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {assembly_callee_saved_registers' : assembly_callee_saved_registers_opt}
        {t}
        (asm : Lines)
        (expr : API.Expr t)
        (f : type.interp _ t)
        (arg_bounds : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (out_bounds : ZRange.type.base.option.interp (type.final_codomain t))
        (asm_out : Lines)
        (* Phrased this way to line up with the bounds pipeline exactly *)
        (Hbounded
         : (forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds arg1 = true),
               ZRange.type.base.option.is_bounded_by out_bounds (type.app_curried (API.Interp expr) arg1) = true
               /\ type.app_curried (API.Interp expr) arg1 = type.app_curried f arg2)
           /\ API.Wf expr)
        (H : generate_assembly_of_hinted_expr asm expr arg_bounds out_bounds = Success asm_out)
  : asm = asm_out
    /\ forall (st : machine_state)
              (frame : Semantics.mem_state -> Prop)
              (PHOAS_args : type.for_each_lhs_of_arrow API.interp_type t)
              (word_args : list (Naive.word 64 + list (Naive.word 64)))
              (args := word_args_to_Z_args word_args)
              (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
              (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
              (output_types : type_spec := match simplify_base_type (type.final_codomain t) out_bounds with Success output_types => output_types | Error _ => nil end)
              (asm_args_out asm_args_in : list (Naive.word 64))
              (runtime_regs := get_asm_reg st assembly_calling_registers)
              (runtime_callee_saved_registers := get_asm_reg st assembly_callee_saved_registers)
              (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
              (stack_base := word.of_Z (Semantics.get_reg st rsp - 8 * Z.of_nat stack_size))
              (HR : R_runtime_input frame output_types args stack_size stack_base asm_args_out asm_args_in assembly_calling_registers runtime_regs assembly_callee_saved_registers runtime_callee_saved_registers st),
      (* Should match check_equivalence_correct exactly *)
      exists asm' st' (retvals : list (Z + list Z)),
             strip_ret asm = Success asm'
        /\ DenoteLines st asm' = Some st'
        /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
        /\ R_runtime_output frame retvals (type_spec_of_runtime args) stack_size stack_base asm_args_out asm_args_in assembly_callee_saved_registers runtime_callee_saved_registers st'.
Proof.
  cbv [generate_assembly_of_hinted_expr] in H.
  break_innermost_match_hyps; inversion H; subst; destruct_head'_and; split; [ reflexivity | intros ].
  eapply check_equivalence_correct; eassumption.
Qed.

(* Some theorems about the result of calling generate_assembly_of_hinted_expr_correct on various Pipeline functions *)
