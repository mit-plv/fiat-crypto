Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Relations.Relations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.AbstractInterpretation.
Require Import Crypto.Experiments.NewPipeline.AbstractInterpretationWf.

Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.
  Import AbstractInterpretation.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import AbstractInterpretationWf.Compilers.
  Import AbstractInterpretationWf.Compilers.partial.
  Import invert_expr.

  Module Import partial.
    Import AbstractInterpretation.Compilers.partial.
    Import NewPipeline.UnderLets.Compilers.UnderLets.
    Section with_type.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Let type_base (x : base_type) : type := type.base x.
      Local Coercion type_base : base_type >-> type.
      Context {ident : type -> Type}.
      Local Notation expr := (@expr base_type ident).
      Local Notation Expr := (@expr.Expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident).
      Context (abstract_domain' : base_type -> Type)
              (bottom' : forall A, abstract_domain' A)
              (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
              (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop)
              {abstract_interp_ident_Proper : forall t, Proper (eq ==> abstract_domain'_R t) (abstract_interp_ident t)}
              {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}.
      Local Notation abstract_domain := (@abstract_domain base_type abstract_domain').
      Local Notation bottom := (@bottom base_type abstract_domain' (@bottom')).
      Local Notation bottom_for_each_lhs_of_arrow := (@bottom_for_each_lhs_of_arrow base_type abstract_domain' (@bottom')).
      Local Notation abstract_domain_R := (@abstract_domain_R base_type abstract_domain' abstract_domain'_R).

      Section extract.
        Context (ident_extract : forall t, ident t -> abstract_domain t)
                {ident_extract_Proper : forall {t}, Proper (eq ==> abstract_domain_R) (ident_extract t)}.

        Local Notation extract' := (@extract' base_type ident abstract_domain' ident_extract).
        Local Notation extract_gen := (@extract_gen base_type ident abstract_domain' ident_extract).

        Lemma extract'_Proper G
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @abstract_domain_R t v1 v2)
              {t}
          : Proper (expr.wf G ==> abstract_domain_R) (@extract' t).
        Proof using ident_extract_Proper. apply expr.wf_interp_Proper_gen1, HG. Qed.

        Lemma extract_gen_Proper G
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @abstract_domain_R t v1 v2)
              {t}
          : Proper (expr.wf G ==> type.and_for_each_lhs_of_arrow (@abstract_domain_R) ==> abstract_domain'_R (type.final_codomain t)) (@extract_gen t).
        Proof using ident_extract_Proper.
          intros ?? Hwf; cbv [extract_gen respectful abstract_domain_R].
          rewrite <- type.related_iff_app_curried.
          eapply extract'_Proper; eassumption.
        Qed.
      End extract.
    End with_type.

    Module ident.
      Import defaults.
      Local Notation UnderLets := (@UnderLets base.type ident).
      Section with_type.
        Context (abstract_domain' : base.type -> Type).
        Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
        Context (annotate_ident : forall t, abstract_domain' t -> option (ident (t -> t)))
                (bottom' : forall A, abstract_domain' A)
                (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
                (update_literal_with_state : forall A : base.type.base, abstract_domain' A -> base.interp A -> base.interp A)
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (is_annotation : forall t, ident t -> bool).
        Context (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop).
        Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' abstract_domain'_R).
        Context {annotate_ident_Proper : forall t, Proper (abstract_domain'_R t ==> eq) (annotate_ident t)}
                {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
                {update_literal_with_state_Proper : forall t, Proper (abstract_domain'_R (base.type.type_base t) ==> eq ==> eq) (update_literal_with_state t)}
                (extract_list_state_length : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_map (@length _) (extract_list_state t v1) = option_map (@length _) (extract_list_state t v2))
                (extract_list_state_rel : forall t v1 v2, abstract_domain'_R _ v1 v2 -> forall l1 l2, extract_list_state t v1 = Some l1 -> extract_list_state t v2 = Some l2 -> forall vv1 vv2, List.In (vv1, vv2) (List.combine l1 l2) -> @abstract_domain'_R t vv1 vv2).

        Section extract.
          Local Notation extract := (@ident.extract abstract_domain' abstract_interp_ident).

          Lemma extract_Proper G
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @abstract_domain_R t v1 v2)
                {t}
            : Proper (expr.wf G ==> type.and_for_each_lhs_of_arrow (@abstract_domain_R) ==> abstract_domain'_R (type.final_codomain t)) (@extract t).
          Proof using abstract_interp_ident_Proper.
            apply @extract_gen_Proper; eauto.
          Qed.
        End extract.
      End with_type.
    End ident.

    Section specialized.
      Import defaults.
      Local Notation abstract_domain' := ZRange.type.base.option.interp (only parsing).
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Local Notation abstract_domain'_R t := (@eq (abstract_domain' t)) (only parsing).
      Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' (fun t => abstract_domain'_R t)).

      Definition abstraction_relation' {t} : abstract_domain' t -> base.interp t -> Prop
        := fun st v => @ZRange.type.base.option.is_bounded_by t st v = true.

      Lemma interp_annotate_ident {t} st idc
            (Hst : @annotate_ident t st = Some idc)
        : forall v, abstraction_relation' st v
               -> (forall cast_outside_of_range,
                     ident.gen_interp cast_outside_of_range idc v = v).
      Proof.
        cbv [annotate_ident Option.bind] in Hst; break_innermost_match_hyps; inversion_option; subst;
          cbv [ident.gen_interp ident.cast abstraction_relation' ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by];
          intros; destruct_head'_prod; cbn [fst snd] in *;
            break_innermost_match; Bool.split_andb; try congruence; reflexivity.
      Qed.

      Lemma interp_annotate_ident_Proper {t} st1 st2 (Hst : abstract_domain'_R t st1 st2)
        : @annotate_ident t st1 = @annotate_ident t st2.
      Proof. congruence. Qed.

      Lemma bottom'_bottom {t} : forall v, abstraction_relation' (bottom' t) v.
      Proof.
        cbv [abstraction_relation' bottom']; induction t; cbn; intros; break_innermost_match; cbn; try reflexivity.
        rewrite Bool.andb_true_iff; split; auto.
      Qed.

      Lemma abstract_interp_ident_related {t} (idc : ident t)
        : type.related_hetero (@abstraction_relation') (@abstract_interp_ident t idc) (ident.interp idc).
      Proof.
        destruct idc; cbv [abstract_interp_ident abstraction_relation'].
        all: cbv [type.related_hetero ZRange.ident.option.interp ident.interp ident.gen_interp respectful_hetero type.interp ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp ZRange.type.base.option.Some].
      Admitted.

      Lemma interp_update_literal_with_state {t : base.type.base} st v
        : @abstraction_relation' t st v -> @update_literal_with_state t st v = v.
      Proof.
        cbv [abstraction_relation' update_literal_with_state update_Z_literal_with_state ZRange.type.base.option.is_bounded_by];
          break_innermost_match; try congruence; reflexivity.
      Qed.

      Lemma extract_list_state_related {t} st v ls
        : @abstraction_relation' _ st v
          -> @extract_list_state t st = Some ls
          -> length ls = length v
            /\ forall st' (v' : base.interp t), List.In (st', v') (List.combine ls v) -> @abstraction_relation' t st' v'.
      Proof.
        cbv [abstraction_relation' extract_list_state]; cbn [ZRange.type.base.option.is_bounded_by].
        intros; subst.
        split.
        { eapply FoldBool.fold_andb_map_length; eassumption. }
        { intros *.
          revert dependent v; induction ls, v; cbn; try tauto.
          rewrite Bool.andb_true_iff.
          intros; destruct_head'_and; destruct_head'_or; inversion_prod; subst; eauto. }
      Qed.

      Lemma Extract_FromFlat_ToFlat' {t} (e : Expr t) (Hwf : Wf e) b_in1 b_in2
            (Hb : type.and_for_each_lhs_of_arrow (fun t => type.eqv) b_in1 b_in2)
        : partial.Extract (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e)) b_in1
          = partial.Extract e b_in2.
      Proof.
        cbv [partial.Extract partial.ident.extract partial.extract_gen partial.extract'].
        revert b_in1 b_in2 Hb.
        rewrite <- (@type.related_iff_app_curried base.type ZRange.type.base.option.interp (fun _ => eq)).
        apply GeneralizeVar.Interp_gen1_FromFlat_ToFlat, Hwf.
      Qed.

      Lemma Extract_FromFlat_ToFlat {t} (e : Expr t) (Hwf : Wf e) b_in
            (Hb : Proper (type.and_for_each_lhs_of_arrow (fun t => type.eqv)) b_in)
        : partial.Extract (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e)) b_in
          = partial.Extract e b_in.
      Proof. apply Extract_FromFlat_ToFlat'; assumption. Qed.
    End specialized.
  End partial.
  Import defaults.

  Module RelaxZRange.
    Module ident.
      Section relax.
        Context (relax_zrange : zrange -> option zrange)
                (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                         -> relax_zrange r = Some r'
                                         -> is_tighter_than_bool z r' = true).

        Lemma interp_relax {t} (idc idc' : ident t)
              (Hidc : @RelaxZRange.ident.relax relax_zrange t idc = Some idc')
              v
              (Hinterp : forall cast_outside_of_range, type.app_curried (ident.gen_interp cast_outside_of_range idc) v = type.app_curried (ident.interp idc) v)
          : forall cast_outside_of_range, type.app_curried (ident.gen_interp cast_outside_of_range idc') v = type.app_curried (ident.interp idc) v.
        Proof.
          intro cast_outside_of_range.
          pose proof (Hinterp (fun _ => id)).
          pose proof (fun myrange => Hinterp (fun _ => cast_outside_of_range myrange)).
          destruct idc; cbv [RelaxZRange.ident.relax Option.bind] in *; inversion_option; break_innermost_match_hyps; inversion_option; subst;
            repeat match goal with
                   | [ H : relax_zrange _ = Some _ |- _ ] => unique pose proof (fun zl zu pf => Hrelax _ _ (Build_zrange zl zu) pf H)
                   end;
            repeat first [ reflexivity
                         | discriminate
                         | congruence
                         | progress cbv [RelaxZRange.ident.relax Option.bind id ident.cast is_tighter_than_bool] in *
                         | progress cbn [fst snd] in *
                         | progress subst
                         | progress inversion_option
                         | progress inversion_prod
                         | progress destruct_head'_prod
                         | progress destruct_head'_and
                         | progress cbn in *
                         | progress Bool.split_andb
                         | progress intros
                         | match goal with
                           | [ H : forall x, (_, _) = (_, _) |- _ ]
                             => pose proof (fun x => f_equal (@fst _ _) (H x));
                               pose proof (fun x => f_equal (@snd _ _) (H x));
                               clear H
                           | [ H : context[andb _ _ = true] |- _ ] => rewrite Bool.andb_true_iff in H || setoid_rewrite Bool.andb_true_iff in H
                           | [ H : context[Z.leb _ _ = true] |- _ ] => rewrite Z.leb_le in H || setoid_rewrite Z.leb_le in H
                           | [ H : forall a b, and (Z.le ?x a) (Z.le b ?y) -> _ /\ _, H' : Z.le ?x _, H'' : Z.le _ ?y |- _ ]
                             => unique pose proof (proj1 (H _ _ (conj H' H'')));
                                unique pose proof (proj2 (H _ _ (conj H' H'')))
                           end
                         | progress rewrite ?Bool.andb_false_iff in *
                         | progress destruct_head'_or
                         | progress break_innermost_match_hyps
                         | progress break_innermost_match
                         | progress Z.ltb_to_lt
                         | apply (f_equal2 (@pair _ _))
                         | lia ].
        Qed.
      End relax.
    End ident.

    Module expr.
      Section relax.
        Context (relax_zrange : zrange -> option zrange)
                (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                         -> relax_zrange r = Some r'
                                         -> is_tighter_than_bool z r' = true).
        Lemma interp_relax {t} (e : expr t)
              v
              (Hinterp : forall cast_outside_of_range, type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) e) v
                                                  = type.app_curried (defaults.interp e) v)
          : forall cast_outside_of_range, type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) (RelaxZRange.expr.relax relax_zrange e)) v
                                     = type.app_curried (defaults.interp e) v.
        Proof.
          intro cast_outside_of_range; rewrite <- (Hinterp cast_outside_of_range); pose proof (Hinterp cast_outside_of_range).
          induction e; cbn -[RelaxZRange.ident.relax] in *; interp_safe_t; cbv [option_map] in *;
            break_innermost_match; cbn -[RelaxZRange.ident.relax] in *; interp_safe_t;
              eauto using tt.
          all: repeat first [ reflexivity
                            | progress intros
                            | progress specialize_by_assumption
                            | progress cbn -[RelaxZRange.ident.relax] in *
                            | match goal with
                              | [ H : unit -> ?T |- _ ] => specialize (H tt)
                              | [ H : forall x : _ * _, _ |- _ ] => specialize (fun a b => H (a, b))
                              | [ e : expr (type.base (base.type.type_base base.type.unit)) |- _ ]
                                => match goal with
                                  | [ |- context[expr.interp ?ii e] ] => destruct (expr.interp ii e)
                                  | [ H : context[expr.interp ?ii e] |- _ ] => destruct (expr.interp ii e)
                                  end
                              end
                            | progress cbn [fst snd] in *
                            | match goal with
                              | [ H : _ |- _ ] => rewrite H
                              end ].
          all: specialize_all_ways.
          all: repeat first [ reflexivity
                            | progress intros
                            | progress specialize_by_assumption
                            | progress cbn -[RelaxZRange.ident.relax] in *
                            | match goal with
                              | [ H : unit -> ?T |- _ ] => specialize (H tt)
                              | [ H : forall x : _ * _, _ |- _ ] => specialize (fun a b => H (a, b))
                              | [ e : expr (type.base (base.type.type_base base.type.unit)) |- _ ]
                                => match goal with
                                  | [ |- context[expr.interp ?ii e] ] => destruct (expr.interp ii e)
                                  | [ H : context[expr.interp ?ii e] |- _ ] => destruct (expr.interp ii e)
                                  end
                              end
                            | progress cbn [fst snd] in *
                            | match goal with
                              | [ H : _ |- _ ] => rewrite H
                              end ].
        Admitted.

        Lemma Interp_Relax {t} (e : Expr t)
              v
              (Hinterp : forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) e) v
                                                  = type.app_curried (defaults.Interp e) v)
          : forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (RelaxZRange.expr.Relax relax_zrange e)) v
                                     = type.app_curried (defaults.Interp e) v.
        Proof. eapply @interp_relax; try assumption. Qed.
      End relax.
    End expr.
  End RelaxZRange.
  Hint Resolve RelaxZRange.expr.Wf_Relax : wf.

  Axiom admit_pf : False.
  Local Notation admit := (match admit_pf with end).

  Lemma Interp_PartialEvaluateWithBounds
        cast_outside_of_range
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (PartialEvaluateWithBounds E b_in)) arg1
      = type.app_curried (Interp E) arg2.
  Proof.
  Admitted.

  Lemma Interp_PartialEvaluateWithBounds_bounded
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      ZRange.type.base.option.is_bounded_by
        (partial.Extract (PartialEvaluateWithBounds E b_in) b_in)
        (type.app_curried (expr.Interp (@ident.interp) (PartialEvaluateWithBounds E b_in)) arg1)
      = true.
  Proof.
  Admitted.

  Lemma Interp_PartialEvaluateWithListInfoFromBounds
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds E b_in)) arg1 = type.app_curried (Interp E) arg2.
  Proof.
  Admitted.

  Theorem CheckedPartialEvaluateWithBounds_Correct
          (relax_zrange : zrange -> option zrange)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {t} (E : Expr t)
          (Hwf : Wf E)
          (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
          (b_out : ZRange.type.base.option.interp (type.final_codomain t))
          {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R _ _ (fun _ => eq))) b_in}
          rv (Hrv : CheckedPartialEvaluateWithBounds relax_zrange E b_in b_out = inl rv)
    : (forall arg1 arg2
              (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
              (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          ZRange.type.base.option.is_bounded_by b_out (type.app_curried (Interp rv) arg1) = true
          /\ forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) rv) arg1
                                           = type.app_curried (Interp E) arg2)
      /\ Wf rv.
  Proof.
    cbv [CheckedPartialEvaluateWithBounds CheckPartialEvaluateWithBounds Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    split.
    { intros arg1 arg2 Harg12 Harg1.
      assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
        by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
      split.
      all: repeat first [ rewrite !@GeneralizeVar.Interp_gen1_FromFlat_ToFlat by eauto with wf typeclass_instances
                        | rewrite Extract_FromFlat_ToFlat by auto with wf
                        | eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; [ eassumption | ]
                        | apply Interp_PartialEvaluateWithBounds_bounded; auto
                        | progress cbv [ident.interp]
                        | rewrite RelaxZRange.expr.Interp_Relax; eauto
                        | erewrite !Interp_PartialEvaluateWithBounds
                        | solve [ eauto ]
                        | progress intros ]. }
    { auto with wf. }
  Qed.
End Compilers.
