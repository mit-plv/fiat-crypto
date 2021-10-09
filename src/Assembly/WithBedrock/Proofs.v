Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
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
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
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
    Modulo.push_Zmod; Modulo.pull_Zmod);
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

Definition merge_fresh_symbol_G (v : Z) : (symbol -> option Z) * dag -> idx * ((symbol -> option Z) * dag)
  := fun '(G, d) => let '(idx, d) := merge_fresh_symbol d in (idx, (ctx_set idx v G, d)).

Definition build_inputarray_G (vals : list Z) : (symbol -> option Z) * dag -> list idx * ((symbol -> option Z) * dag)
  := List.foldmap merge_fresh_symbol_G vals.

Fixpoint build_inputs_G (vals : list (Z + list Z))
  : (symbol -> option Z) * dag -> list (idx + list idx) * ((symbol -> option Z) * dag)
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

Fixpoint dag_gensym_n_G (vals : list Z) : (symbol -> option Z) * dag -> list idx * ((symbol -> option Z) * dag)
  := match vals with
     | nil => fun st => ([], st)
     | v :: vs
       => fun st
          => let '(idx, st) := merge_fresh_symbol_G v st in
             let '(rest, st) := dag_gensym_n_G vs st in
             (idx :: rest, st)
     end.

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

Lemma merge_fresh_symbol_G_ok_bounded G d v G' d' idx
      (Hd : gensym_dag_ok G d)
      (H : merge_fresh_symbol_G v (G, d) = (idx, (G', d')))
      (Hv : (0 <= v < 2^64)%Z)
  : eval_idx_Z G' d' idx v
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  replace v with (Z.land v (Z.ones (Z.of_N 64))); [ now apply merge_fresh_symbol_G_ok | ].
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia.
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

Import Map.Interface Map.Separation. (* for coercions *)
Require Import bedrock2.Array.
Import LittleEndianList.
Import coqutil.Word.Interface.
(* outputs, inputs *)
Definition get_asm_arguments (m : machine_state) (output_types : type_spec) (runtime_inputs : type_spec) (reg_available : list REG) : list (Naive.word 64) * list (Naive.word 64).
  (* TODO *)
Admitted.
Definition R_runtime_input (frame : Semantics.mem_state) (output_types : type_spec) (runtime_inputs : list (Z + list Z)) (stack_size : nat) (asm_arguments_out asm_arguments_in : list (Naive.word 64)) (reg_available : list REG) (m : machine_state) : Prop.
  (* TODO *)
Admitted.
Definition cell64 wa (v : Z) : Semantics.mem_state -> Prop :=
  Lift1Prop.ex1 (fun bs => sep (emp (
      length bs = 8%nat /\ v = le_combine bs))
                               (eq (OfListWord.map.of_list_word_at wa bs))).
Print array.
Check array cell64 (word.of_Z 8).
Definition R_runtime_output (frame : Semantics.mem_state) (runtime_outputs : list (Z + list Z)) (runtime_inputs : type_spec) (stack_size : nat) (asm_arguments_out asm_arguments_in : list (Naive.word 64)) (m : machine_state) : Prop.
  Print array.
  Check array.
  Check R_cell64.
  Locate array.
  (* TODO *)
Admitted.

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

Theorem symex_asm_func_M_correct
        d frame asm_args_out asm_args_in (G : symbol -> option Z) (s := init_symbolic_state d)
        (s' : symbolic_state) (m : machine_state) (output_types : type_spec) (stack_size : nat)
        (inputs : list (idx + list idx)) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (H : symex_asm_func_M output_types stack_size inputs reg_available asm s = Success (Success rets, s'))
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (Hasm : get_asm_arguments m output_types (type_spec_of_runtime runtime_inputs) reg_available = (asm_args_out, asm_args_in))
        (HR : R_runtime_input frame output_types runtime_inputs stack_size asm_args_out asm_args_in reg_available m)
        (Hd_ok : gensym_dag_ok G d)
        (d' := s'.(dag_state))
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : exists m' G'
           (runtime_rets : list (Z + list Z)),
    DenoteLines m asm = Some m'
    /\ R_runtime_output frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size asm_args_out asm_args_in m'
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n)
    /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets.
Proof.
  pose proof (word_args_to_Z_args_bounded word_runtime_inputs).
  cbv [symex_asm_func_M Symbolic.bind ErrorT.bind lift_dag] in H.
  break_innermost_match_hyps; destruct_head'_prod; destruct_head'_unit; cbn [fst snd] in *; try discriminate; [].
  repeat first [ progress subst
               | match goal with
                 | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                 | [ x := ?y |- _ ] => subst x
                 end ].
  (* ... *)
  let H := lazymatch goal with H : SymexLines _ _ = Success _ |- _ => H end in
  eapply SymexLines_R in H;
    [ destruct H as [? H]; do 3 eexists;
      repeat match goal with |- _ /\ _ => split end;
      try apply H
    | .. ].
Admitted.

Theorem symex_asm_func_correct
        frame asm_args_out asm_args_in (G : symbol -> option Z) (d : dag) (output_types : type_spec) (stack_size : nat)
        (inputs : list (idx + list idx)) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (s' : symbolic_state)
        (H : symex_asm_func d output_types stack_size inputs reg_available asm = Success (rets, s'))
        (d' := s'.(dag_state))
        (m : machine_state)
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (Hasm : get_asm_arguments m output_types (type_spec_of_runtime runtime_inputs) reg_available = (asm_args_out, asm_args_in))
        (HR : R_runtime_input frame output_types runtime_inputs stack_size asm_args_out asm_args_in reg_available m)
        (HG_ok : gensym_dag_ok G d)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : (exists m' G'
            (runtime_rets : list (Z + list Z)),
        DenoteLines m asm = Some m'
        /\ R_runtime_output frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size asm_args_out asm_args_in m'
        /\ (forall e n, eval G d e n -> eval G' d' e n)
        /\ gensym_dag_ok G' d'
        /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets).
Proof.
  cbv [symex_asm_func] in H; break_innermost_match_hyps; inversion_ErrorT; inversion_prod; subst.
  cbv [R]; break_innermost_match.
  let H := multimatch goal with H : _ = Success _ |- _ => H end in
  eapply symex_asm_func_M_correct in H; try eassumption; try apply surjective_pairing.
  { destruct_head'_ex; destruct_head'_and.
    do 3 eexists; repeat match goal with |- _ /\ _ => apply conj end; try eassumption. }
Qed.

Theorem check_equivalence_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
        {t}
        (frame : Semantics.mem_state)
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
        (asm_args := get_asm_arguments st output_types (type_spec_of_runtime args) assembly_calling_registers)
        (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
        (HR : R_runtime_input frame output_types args stack_size (fst asm_args) (snd asm_args) assembly_calling_registers st)
  : exists asm' st' (retvals : list (Z + list Z)),
    strip_ret asm = Success asm'
    /\ DenoteLines st asm' = Some st'
    /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
    /\ R_runtime_output frame retvals (type_spec_of_runtime args) stack_size (fst asm_args) (snd asm_args) st'.
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
                 | [ H : symex_asm_func _ _ _ _ _ _ = Success _ |- _ ]
                   => move H at bottom; eapply symex_asm_func_correct in H;
                      [ | try (eassumption + apply surjective_pairing) .. ];
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
                 end ].
  do 3 eexists; repeat apply conj; try eassumption; trivial.
Qed.

Theorem generate_assembly_of_hinted_expr_correct
        {assembly_calling_registers' : assembly_calling_registers_opt}
        {assembly_stack_size' : assembly_stack_size_opt}
        {assembly_output_first : assembly_output_first_opt}
        {assembly_argument_registers_left_to_right : assembly_argument_registers_left_to_right_opt}
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
              (frame : Semantics.mem_state)
              (PHOAS_args : type.for_each_lhs_of_arrow API.interp_type t)
              (word_args : list (Naive.word 64 + list (Naive.word 64)))
              (args := word_args_to_Z_args word_args)
              (Hargs : build_input_runtime t args = Some (PHOAS_args, []))
              (HPHOAS_args : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) arg_bounds PHOAS_args = true)
              (output_types : type_spec := match simplify_base_type (type.final_codomain t) out_bounds with Success output_types => output_types | Error _ => nil end)
              (asm_args := get_asm_arguments st output_types (type_spec_of_runtime args) assembly_calling_registers)
              (stack_size := N.to_nat (assembly_stack_size match strip_ret asm with Success asm => asm | Error _ => asm end))
              (HR : R_runtime_input frame output_types args stack_size (fst asm_args) (snd asm_args) assembly_calling_registers st),
      (* Should match check_equivalence_correct exactly *)
      exists asm' st' (retvals : list (Z + list Z)),
             strip_ret asm = Success asm'
        /\ DenoteLines st asm' = Some st'
        /\ simplify_base_runtime (type.app_curried (API.Interp expr) PHOAS_args) = Some retvals
        /\ R_runtime_output frame retvals (type_spec_of_runtime args) stack_size (fst asm_args) (snd asm_args) st'.
Proof.
  cbv [generate_assembly_of_hinted_expr] in H.
  break_innermost_match_hyps; inversion H; subst; destruct_head'_and; split; [ reflexivity | intros ].
  eapply check_equivalence_correct; eassumption.
Qed.

(* Some theorems about the result of calling generate_assembly_of_hinted_expr_correct on various Pipeline functions *)
