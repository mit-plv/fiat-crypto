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
Require Import Crypto.Util.ListUtil.StdlibCompat.
Require Import Crypto.Util.ListUtil.IndexOf.
Require Import Crypto.Util.ListUtil.Split.
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
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.PrintContext.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.ClearHead.
Import API.Compilers APINotations.Compilers AbstractInterpretation.ZRange.Compilers.
Import ListNotations.
Local Open Scope list_scope.

(* TODO: move to global settings *)
Local Set Keyed Unification.

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
                                    | eapply Forall.Forall2_combine; [ | eassumption .. ]; eauto
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
    exfalso; match goal with H : _ |- _ => apply nth_error_In in H; cbn in H end; assumption.
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
Lemma get_reg_set_reg_full s rn rn' v
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
