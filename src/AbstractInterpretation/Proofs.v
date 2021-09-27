Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Relations.Relations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.SplitBounds.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.PER.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.DoWithHyp.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Inversion.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.API.
Require Import Crypto.CastLemmas.
Require Import Rewriter.Language.UnderLetsProofs.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.AbstractInterpretation.Wf.
Require Import Crypto.AbstractInterpretation.ZRangeProofs.

Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.
  Import AbstractInterpretation.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import Language.API.Compilers.
  Import UnderLetsProofs.Compilers.
  Import AbstractInterpretation.Wf.Compilers.
  Import AbstractInterpretation.ZRangeProofs.Compilers.
  Import AbstractInterpretation.Wf.Compilers.partial.
  Import invert_expr.

  Local Notation related_bounded' b v1 v2
    := (ZRange.type.base.option.is_bounded_by b v1 = true
        /\ ZRange.type.base.option.is_bounded_by b v2 = true
        /\ v1 = v2) (only parsing).
  Local Notation related_bounded
    := (@type.related_hetero3 _ _ _ _ (fun t b v1 v2 => related_bounded' b v1 v2)).

  Module ZRange.
    Module type.
      Global Instance is_bounded_by_Proper_related_eq {t}
      : Proper (eq ==> type.eqv ==> eq) (@ZRange.type.is_bounded_by t).
      Proof.
        cbv [Proper respectful]; destruct t; [ cbn | reflexivity ];
          intros; subst; reflexivity.
      Qed.

      Module option.
        Global Instance is_bounded_by_Proper_related_eq {t}
        : Proper (eq ==> type.eqv ==> eq) (@ZRange.type.option.is_bounded_by t).
        Proof.
          cbv [Proper respectful]; destruct t; [ cbn | reflexivity ];
            intros; subst; reflexivity.
        Qed.
      End option.
    End type.
  End ZRange.

  Module Import partial.
    Import AbstractInterpretation.Compilers.partial.
    Import UnderLets.Compilers.UnderLets.
    Section with_type.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Let type_base (x : base_type) : type := type.base x.
      Local Coercion type_base : base_type >-> type.
      Context {ident : type -> Type}.
      Local Notation Expr := (@expr.Expr base_type ident).
      Context (abstract_domain' base_interp : base_type -> Type)
              (ident_interp : forall t, ident t -> type.interp base_interp t)
              (abstraction_relation' : forall t, abstract_domain' t -> base_interp t -> Prop)
              (bottom' : forall A, abstract_domain' A)
              (bottom'_related : forall t v, abstraction_relation' t (bottom' t) v)
              (skip_annotations_under : forall t, ident t -> bool)
              (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
              (ident_interp_Proper : forall t (idc : ident t), type.related_hetero abstraction_relation' (abstract_interp_ident t idc) (ident_interp t idc))
              (ident_interp_Proper' : forall t, Proper (eq ==> type.eqv) (ident_interp t))
              (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop)
              (abstraction_relation'_Proper : forall t, Proper (abstract_domain'_R t ==> eq ==> Basics.impl) (abstraction_relation' t))
              {abstract_domain'_R_transitive : forall t, Transitive (@abstract_domain'_R t)}
              {abstract_domain'_R_symmetric : forall t, Symmetric (@abstract_domain'_R t)}
              {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
              (abstract_domain'_R_of_related : forall t st v, @abstraction_relation' t st v -> @abstract_domain'_R t st st).
      Local Notation abstract_domain := (@abstract_domain base_type abstract_domain').
      Definition abstraction_relation {t} : abstract_domain t -> type.interp base_interp t -> Prop
        := type.related_hetero (@abstraction_relation').
      Local Notation bottom := (@bottom base_type abstract_domain' (@bottom')).
      Local Notation bottom_for_each_lhs_of_arrow := (@bottom_for_each_lhs_of_arrow base_type abstract_domain' (@bottom')).
      Local Notation abstract_domain_R := (@abstract_domain_R base_type abstract_domain' abstract_domain'_R).
      Local Notation var := (type.interp base_interp).
      Local Notation expr := (@expr.expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident).
      Local Notation value := (@value base_type ident var abstract_domain').
      Local Notation value_with_lets := (@value_with_lets base_type ident var abstract_domain').
      Local Notation state_of_value := (@state_of_value base_type ident var abstract_domain' bottom').
      Context (annotate : forall (is_let_bound : bool) t, abstract_domain' t -> @expr var t -> @UnderLets var (@expr var t))
              (interp_ident : bool -> forall t, ident t -> value_with_lets t)
              (ident_extract : forall t, ident t -> abstract_domain t)
              (interp_annotate
               : forall is_let_bound t st e
                   (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e)),
                  expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate is_let_bound t st e))
                  = expr.interp (@ident_interp) e)
              (ident_extract_Proper : forall t, Proper (eq ==> abstract_domain_R) (ident_extract t)).
      Local Notation eta_expand_with_bound' := (@eta_expand_with_bound' base_type ident _ abstract_domain' annotate bottom').
      Local Notation eval_with_bound' := (@partial.eval_with_bound' base_type ident _ abstract_domain' annotate bottom' skip_annotations_under interp_ident).
      Local Notation extract' := (@extract' base_type ident abstract_domain' bottom' ident_extract).
      Local Notation extract_gen := (@extract_gen base_type ident abstract_domain' bottom' ident_extract).
      Local Notation reify := (@reify base_type ident _ abstract_domain' annotate bottom').
      Local Notation reflect := (@reflect base_type ident _ abstract_domain' annotate bottom').
      Local Notation interp := (@interp base_type ident var abstract_domain' annotate bottom' skip_annotations_under interp_ident).
      Local Notation bottomify := (@bottomify base_type ident _ abstract_domain' bottom').

      Lemma bottom_related t v : @abstraction_relation t bottom v.
      Proof using bottom'_related. cbv [abstraction_relation]; induction t; cbn; cbv [respectful_hetero]; eauto. Qed.

      Local Hint Resolve bottom_related : core typeclass_instances.

      Lemma bottom_for_each_lhs_of_arrow_related t v : type.and_for_each_lhs_of_arrow (@abstraction_relation) (@bottom_for_each_lhs_of_arrow t) v.
      Proof using bottom'_related. induction t; cbn; eauto using bottom_related. Qed.

      Local Notation bottom_Proper := (@bottom_Proper base_type abstract_domain' bottom' abstract_domain'_R bottom'_Proper).
      Local Notation bottom_for_each_lhs_of_arrow_Proper := (@bottom_for_each_lhs_of_arrow_Proper base_type abstract_domain' bottom' abstract_domain'_R bottom'_Proper).

      Local Hint Resolve (@bottom_Proper) (@bottom_for_each_lhs_of_arrow_Proper) : core typeclass_instances.

      Fixpoint related_bounded_value {t} : abstract_domain t -> value t -> type.interp base_interp t -> Prop
        := match t return abstract_domain t -> value t -> type.interp base_interp t -> Prop with
           | type.base t
             => fun st '(e_st, e) v
                => abstract_domain'_R t st e_st
                   /\ expr.interp ident_interp e = v
                   /\ abstraction_relation' t st v
           | type.arrow s d
             => fun st e v
               => Proper type.eqv v
                 /\ forall st_s e_s v_s,
                   let st_s := match s with
                               | type.base _ => st_s
                               | type.arrow _ _ => bottom
                               end in
                   @related_bounded_value s st_s e_s v_s
                   -> @related_bounded_value d (st st_s) (UnderLets.interp ident_interp (e e_s)) (v v_s)
           end.
      Definition related_bounded_value_with_lets {t} : abstract_domain t -> value_with_lets t -> type.interp base_interp t -> Prop
        := fun st e v => related_bounded_value st (UnderLets.interp ident_interp e) v.

      Definition related_of_related_bounded_value {t} st e v
        : @related_bounded_value t st e v -> v == v.
      Proof using Type. destruct t; [ reflexivity | intros [? ?]; assumption ]. Qed.

      Lemma abstract_domain'_R_refl_of_rel_l t x y (H : @abstract_domain'_R t x y)
        : @abstract_domain'_R t x x.
      Proof using abstract_domain'_R_symmetric abstract_domain'_R_transitive. eapply PER_valid_l; eassumption. Qed.

      Lemma abstract_domain'_R_refl_of_rel_r t x y (H : @abstract_domain'_R t x y)
        : @abstract_domain'_R t y y.
      Proof using abstract_domain'_R_symmetric abstract_domain'_R_transitive. eapply PER_valid_r; eassumption. Qed.

      Local Hint Immediate abstract_domain'_R_refl_of_rel_l abstract_domain'_R_refl_of_rel_r : core.

      Local Instance abstract_domain_R_Symmetric {t} : Symmetric (@abstract_domain_R t) := _ : Symmetric (type.related _).
      Local Instance abstract_domain_R_Transitive {t} : Transitive (@abstract_domain_R t) := _ : Transitive (type.related _).

      Lemma abstract_domain_R_refl_of_rel_l t x y (H : @abstract_domain_R t x y)
        : @abstract_domain_R t x x.
      Proof using abstract_domain'_R_symmetric abstract_domain'_R_transitive. eapply PER_valid_l; eassumption. Qed.

      Lemma abstract_domain_R_refl_of_rel_r t x y (H : @abstract_domain_R t x y)
        : @abstract_domain_R t y y.
      Proof using abstract_domain'_R_symmetric abstract_domain'_R_transitive. eapply PER_valid_r; eassumption. Qed.

      Local Hint Immediate abstract_domain_R_refl_of_rel_l abstract_domain_R_refl_of_rel_r : core.

      Lemma related_bottom_for_each_lhs_of_arrow {t} v
        : type.and_for_each_lhs_of_arrow (@abstraction_relation) (@bottom_for_each_lhs_of_arrow t) v.
      Proof using bottom'_related. induction t; cbn; eauto. Qed.

      Local Hint Immediate related_bottom_for_each_lhs_of_arrow : core.

      Fixpoint fill_in_bottom_for_arrows {t} : abstract_domain t -> abstract_domain t
        := match t with
           | type.base t => fun x => x
           | type.arrow s d
             => fun f x => let x := match s with
                                | type.base _ => x
                                | type.arrow _ _ => bottom
                                end in
                       @fill_in_bottom_for_arrows d (f x)
           end.

      Lemma abstract_domain_R_bottom_fill_arrows {t}
        : abstract_domain_R (@bottom t) (fill_in_bottom_for_arrows (@bottom t)).
      Proof using bottom'_Proper.
        cbv [abstract_domain_R]; induction t as [t|s IHs d IHd]; cbn [fill_in_bottom_for_arrows bottom type.related];
          cbv [respectful Proper] in *; auto.
      Qed.

      Lemma fill_in_bottom_for_arrows_bottom_related {t} v
        : abstraction_relation (fill_in_bottom_for_arrows (@bottom t)) v.
      Proof using bottom'_related.
        cbv [abstraction_relation]; induction t; cbn; cbv [respectful_hetero]; eauto.
      Qed.

      Hint Resolve fill_in_bottom_for_arrows_bottom_related : core.

      Local Instance fill_in_bottom_for_arrows_Proper {t} : Proper (abstract_domain_R ==> abstract_domain_R) (@fill_in_bottom_for_arrows t).
      Proof using bottom'_Proper.
        pose proof (@bottom_Proper).
        cbv [Proper respectful abstract_domain_R] in *; induction t; cbn in *; cbv [respectful] in *;
          intros; break_innermost_match; eauto.
      Qed.

      Local Instance bottom_eqv_Proper_refl {t} : Proper type.eqv (@bottom t).
      Proof using Type. cbv [Proper]; induction t; cbn in *; cbv [respectful] in *; eauto. Qed.

      Lemma bottom_eqv_refl {t} : @bottom t == @bottom t.
      Proof using Type. apply bottom_eqv_Proper_refl. Qed.
      Local Hint Resolve bottom_eqv_refl : core.

      Local Instance fill_in_bottom_for_arrows_Proper_eqv {t} : Proper (type.eqv ==> type.eqv) (@fill_in_bottom_for_arrows t).
      Proof using Type.
        cbv [Proper respectful] in *; induction t; cbn in *; cbv [respectful] in *;
          intros; break_innermost_match; cbn in *; cbv [respectful] in *; eauto.
      Qed.

      Lemma state_of_value_related_fill {t} v (HP : Proper abstract_domain_R (@state_of_value t v))
        : abstract_domain_R (@state_of_value t v) (fill_in_bottom_for_arrows (@state_of_value t v)).
      Proof using bottom'_Proper. destruct t; [ assumption | apply abstract_domain_R_bottom_fill_arrows ]. Qed.

      Lemma eqv_bottom_fill_bottom {t}
        : @bottom t == fill_in_bottom_for_arrows bottom.
      Proof using Type. induction t; cbn; [ reflexivity | ]; cbv [respectful]; auto. Qed.

      Lemma eqv_fill_bottom_idempotent {t} v1 v2
        : v1 == v2 -> fill_in_bottom_for_arrows (fill_in_bottom_for_arrows v1) == @fill_in_bottom_for_arrows t v2.
      Proof using Type. induction t; cbn; cbv [respectful]; break_innermost_match; auto. Qed.

      Lemma abstract_domain_R_fill_bottom_idempotent {t} v1 v2
        : abstract_domain_R v1 v2
          -> abstract_domain_R (fill_in_bottom_for_arrows (fill_in_bottom_for_arrows v1))
                               (@fill_in_bottom_for_arrows t v2).
      Proof using bottom'_Proper.
        pose proof (@bottom_Proper) as Hb.
        induction t as [|s IHs d IHd]; cbn; cbv [respectful Proper abstract_domain_R] in *; break_innermost_match; auto.
      Qed.

      Lemma app_curried_state_of_value_fill {t} v x y
            (H : type.and_for_each_lhs_of_arrow (@type.eqv) x y)
        : type.app_curried (@state_of_value t v) x = type.app_curried (fill_in_bottom_for_arrows (@state_of_value t v)) y.
      Proof using Type.
        destruct t; [ reflexivity | cbv [state_of_value] ].
        apply type.app_curried_Proper; [ apply eqv_bottom_fill_bottom | assumption ].
      Qed.

      Lemma first_order_app_curried_fill_in_bottom_for_arrows_eq {t} f xs
            (Ht : type.is_not_higher_order t = true)
        : type.app_curried (t:=t) f xs = type.app_curried (fill_in_bottom_for_arrows f) xs.
      Proof using Type.
        clear -Ht.
        induction t as [| [|s' d'] IHs d IHd]; cbn in *; try discriminate; auto.
      Qed.

      Lemma first_order_abstraction_relation_fill_in_bottom_for_arrows_iff
            {t} f v
            (Ht : type.is_not_higher_order t = true)
        : @abstraction_relation t f v
          <-> @abstraction_relation t (fill_in_bottom_for_arrows f) v.
      Proof using Type.
        clear -Ht; cbv [abstraction_relation].
        split; induction t as [| [|s' d'] IHs d IHd];
          cbn in *; cbv [respectful_hetero]; try discriminate; auto.
      Qed.

      Lemma related_state_of_value_of_related_bounded_value {t} st e v
        : @related_bounded_value t st e v -> abstract_domain_R match t with
                                                              | type.base _ => st
                                                              | type.arrow _ _ => bottom
                                                              end (state_of_value e).
      Proof using bottom'_Proper. intro H; destruct t; cbn in *; [ destruct e; apply H | repeat intro; refine bottom_Proper ]. Qed.

      Lemma related_state_of_value_of_related_bounded_value2 {t} st e v (st' := match t with
                                                                                | type.base _ => st
                                                                                | type.arrow _ _ => bottom
                                                                                end)
        : @related_bounded_value t st' e v -> abstract_domain_R st' (state_of_value e).
      Proof using bottom'_Proper. intro H; destruct t; cbn in *; [ destruct e; apply H | repeat intro; refine bottom_Proper ]. Qed.

      Lemma related_bounded_value_Proper {t} st1 st2 (Hst : abstract_domain_R (fill_in_bottom_for_arrows st1) (fill_in_bottom_for_arrows st2))
            a a1 a2
            (Ha' : type.eqv a1 a2)
        : @related_bounded_value t st1 a a1 -> @related_bounded_value t st2 a a2.
      Proof using abstraction_relation'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric bottom'_Proper.
        induction t as [t|s IHs d IHd]; cbn [related_bounded_value type.related] in *; cbv [respectful abstract_domain_R] in *.
        all: cbn [type.andb_each_lhs_of_arrow] in *.
        all: rewrite ?Bool.andb_true_iff in *.
        all: destruct_head'_and.
        { intros; break_innermost_match; subst;
            destruct_head'_and; repeat apply conj; auto.
          { etransitivity; (idtac + symmetry); eassumption. }
          { eapply abstraction_relation'_Proper; (eassumption + reflexivity). } }
        { intros [? Hrel].
          split; [ repeat intro; etransitivity; (idtac + symmetry); eapply Ha'; (eassumption + (etransitivity; (idtac + symmetry); eassumption)) | ].
          pose proof (@bottom_Proper s) as Hsbot.
          intros ?? v_s; destruct s; intros Hx; cbn [type.related] in *;
            cbn [fill_in_bottom_for_arrows] in *; cbv [respectful] in *.
          { specialize_by_assumption; cbn in *.
            eapply IHd; [ cbn in Hst |- *; eapply Hst | apply Ha'; reflexivity | eapply Hrel, Hx ]; cbv [respectful].
            cbn [related_bounded_value] in *.
            break_innermost_match_hyps; destruct_head'_and.
            eauto. }
          { eapply IHd; [ eapply Hst | apply Ha' | eapply Hrel, Hx ];
              [ eexact Hsbot | refine (@related_of_related_bounded_value _ _ _ v_s _); eassumption | refine bottom ]. } }
      Qed.

      Lemma related_bounded_value_fill_bottom_iff {t} st1 st2 (Hst : abstract_domain_R st1 st2)
            a a1 a2
            (Ha' : type.eqv a1 a2)
        : @related_bounded_value t st1 a a1 <-> @related_bounded_value t (fill_in_bottom_for_arrows st2) a a2.
      Proof using abstraction_relation'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric bottom'_Proper.
        split; eapply related_bounded_value_Proper; try solve [ (idtac + symmetry); assumption ].
        all: (idtac + symmetry); apply abstract_domain_R_fill_bottom_idempotent.
        all: (idtac + symmetry); assumption.
      Qed.

      Lemma related_bounded_value_Proper1 {t}
        : Proper (abstract_domain_R ==> eq ==> eq ==> Basics.impl) (@related_bounded_value t).
      Proof using abstraction_relation'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric bottom'_Proper.
        repeat intro; subst; eapply related_bounded_value_Proper.
        { eapply fill_in_bottom_for_arrows_Proper; eassumption. }
        { eapply related_of_related_bounded_value; eassumption. }
        { assumption. }
      Qed.

      Lemma related_bounded_value_Proper_eq {t}
        : Proper (eq ==> eq ==> eq ==> Basics.impl) (@related_bounded_value t).
      Proof using Type.
        repeat intro; subst; assumption.
      Qed.

      Lemma related_bounded_value_Proper_interp_eq_base {t}
        : Proper (eq ==> RelProd eq (fun x y => expr.interp ident_interp x = expr.interp ident_interp y) ==> eq ==> Basics.impl) (@related_bounded_value (type.base t)).
      Proof using Type.
        repeat intro; subst.
        cbv [value RelProd relation_conjunction predicate_intersection pointwise_extension RelCompFun] in *.
        destruct_head'_prod; destruct_head'_and; cbn [fst snd] in *; subst.
        cbv [related_bounded_value] in *; destruct_head'_and; repeat apply conj; subst; (idtac + symmetry); assumption.
      Qed.

      Fixpoint interp_reify
               annotate_with_state is_let_bound {t} st e v b_in
               (Hb : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) b_in)
               (H : related_bounded_value st e v) {struct t}
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
              type.app_curried (expr.interp ident_interp (UnderLets.interp ident_interp (@reify annotate_with_state is_let_bound t e b_in))) arg1
              = type.app_curried v arg2)
          /\ (forall arg1
                     (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1)
                     (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                 abstraction_relation'
                   _
                   (type.app_curried (fill_in_bottom_for_arrows st) b_in)
                   (type.app_curried (expr.interp ident_interp (UnderLets.interp ident_interp (@reify annotate_with_state is_let_bound t e b_in))) arg1))
      with interp_reflect
             annotate_with_state {t} st e v
             (Hst_Proper : Proper abstract_domain_R st)
             (H_val : expr.interp ident_interp e == v)
             (Hst1 : abstraction_relation (fill_in_bottom_for_arrows st) (expr.interp ident_interp e))
             {struct t}
           : related_bounded_value
               st
               (@reflect annotate_with_state t e st)
               v.
      Proof using interp_annotate abstraction_relation'_Proper bottom'_related bottom'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric.
        all: destruct t as [t|s d];
          [ clear interp_reify interp_reflect
          | pose proof (fun is_let_bound => interp_reify annotate_with_state is_let_bound s) as interp_reify_s;
            pose proof (fun is_let_bound => interp_reify annotate_with_state is_let_bound d) as interp_reify_d;
            pose proof (interp_reflect annotate_with_state s) as interp_reflect_s;
            pose proof (interp_reflect annotate_with_state d) as interp_reflect_d;
            clear interp_reify interp_reflect;
            pose proof (@abstract_domain_R_bottom_fill_arrows s);
            pose proof (@abstract_domain_R_bottom_fill_arrows d) ].
        all: cbn [reify reflect] in *; fold (@reify) (@reflect) in *.
        all: cbn [related_bounded_value type.related type.app_curried] in *.
        all: cbn [UnderLets.interp expr.interp type.final_codomain type.andb_each_lhs_of_arrow type.is_base fst snd fill_in_bottom_for_arrows type.map_for_each_lhs_of_arrow type.for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow partial.bottom_for_each_lhs_of_arrow partial.bottom] in *.
        all: destruct annotate_with_state; try destruct is_let_bound.
        all: repeat first [ reflexivity
                          | progress eta_expand
                          | progress cbv [type.is_not_higher_order] in *
                          | progress cbn [UnderLets.interp expr.interp type.final_codomain fst snd] in *
                          | progress subst
                          | progress destruct_head'_and
                          | progress destruct_head'_prod
                          | progress destruct_head_hnf' and
                          | progress destruct_head_hnf' prod
                          | progress destruct_head_hnf' unit
                          | progress split_and
                          | progress subst
                          | discriminate
                          | rewrite UnderLets.interp_splice
                          | rewrite UnderLets.interp_to_expr
                          | rewrite interp_annotate
                          | match goal with
                            | [ H : context[andb _ _ = true] |- _ ] => rewrite !Bool.andb_true_iff in H
                            | [ |- context[andb _ _ = true] ] => rewrite !Bool.andb_true_iff
                            end
                          | match goal with
                            | [ H : fst ?x = _ |- _ ] => is_var x; destruct x
                            | [ H : Proper _ ?st |- ?R (?st _) (?st _) ] => apply H
                            | [ |- ?R (state_of_value _) (state_of_value _) ] => cbv [state_of_value] in *
                            end
                          | solve [ repeat intro; apply bottom_Proper
                                  | auto; cbv [Proper respectful Basics.impl] in *; eauto ]
                          | progress (repeat apply conj; intros * )
                          | progress intros
                          | progress destruct_head'_or
                          | do_with_exactly_one_hyp ltac:(fun H => eapply H; clear H);
                            try assumption; auto; []
                          | match goal with
                            | [ |- Proper ?R _ ] => (eapply PER_valid_l + eapply PER_valid_r); eassumption
                            | [ |- @related_bounded_value ?t ?st1 (reflect _ _ ?st2) _ ]
                              => (tryif first [ constr_eq st1 st2 | has_evar st1 | has_evar st2 ]
                                  then fail
                                  else (eapply (@related_bounded_value_Proper1 t st2 st1);
                                        try reflexivity))
                            | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry; assumption
                            end
                          | break_innermost_match_step
                          | do_with_exactly_one_hyp ltac:(fun H => eapply H; clear H);
                            try assumption; auto
                          | match goal with
                            | [ |- abstraction_relation (fill_in_bottom_for_arrows (?f (state_of_value ?e))) _ ]
                              => replace (state_of_value e) with (match s with
                                                                 | type.base _ => state_of_value e
                                                                 | type.arrow _ _ => bottom
                                                                 end) by (destruct s; reflexivity)
                            end
                          | progress fold (@reify) (@reflect) (@type.interp) (@type.related) (@type.related_hetero) in *
                          | match goal with
                            | [ |- type.related _ (expr.interp _ (UnderLets.interp _ (reify _ _ _ _))) _ ]
                              => rewrite type.related_iff_app_curried
                            | [ |- type.related_hetero _ (@state_of_value ?t _) _ ]
                              => is_var t; destruct t; cbv [state_of_value]; [ cbn | apply bottom_related ]
                            end ].
      Qed.

      Lemma interp_reify_first_order
               annotate_with_state is_let_bound {t} st e v b_in
               (Ht : type.is_not_higher_order t = true)
               (Hb : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) b_in)
               (H : related_bounded_value st e v)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
              type.app_curried (expr.interp ident_interp (UnderLets.interp ident_interp (@reify annotate_with_state is_let_bound t e b_in))) arg1
              = type.app_curried v arg2)
          /\ (forall arg1
                     (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1)
                     (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                 abstraction_relation'
                   _
                   (type.app_curried st b_in)
                   (type.app_curried (expr.interp ident_interp (UnderLets.interp ident_interp (@reify annotate_with_state is_let_bound t e b_in))) arg1)).
      Proof using interp_annotate abstraction_relation'_Proper bottom'_related bottom'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric.
        rewrite first_order_app_curried_fill_in_bottom_for_arrows_eq by assumption.
        apply interp_reify; assumption.
      Qed.

      Lemma interp_reflect_first_order
             annotate_with_state {t} st e v
             (Ht : type.is_not_higher_order t = true)
             (Hst_Proper : Proper abstract_domain_R st)
             (H_val : expr.interp ident_interp e == v)
             (Hst : abstraction_relation st (expr.interp ident_interp e))
        : related_bounded_value
            st
            (@reflect annotate_with_state t e st)
            v.
      Proof using interp_annotate abstraction_relation'_Proper bottom'_related bottom'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric.
        rewrite first_order_abstraction_relation_fill_in_bottom_for_arrows_iff in Hst by assumption.
        apply interp_reflect; assumption.
      Qed.

      Lemma related_bounded_value_annotate_base {t}
            v_st st v
        : @related_bounded_value (type.base t) v_st st v
          -> @related_bounded_value (type.base t) v_st (fst st, UnderLets.interp ident_interp (annotate true t (fst st) (snd st))) v.
      Proof using interp_annotate abstraction_relation'_Proper.
        clear -interp_annotate abstraction_relation'_Proper.
        cbv [Proper respectful Basics.impl] in *.
        cbn; break_innermost_match; cbn; intros.
        destruct_head'_and; subst; repeat apply conj; auto.
        rewrite interp_annotate by eauto; reflexivity.
      Qed.

      Lemma related_bounded_value_bottomify {t} v_st st v
        : @related_bounded_value t v_st st v
          -> @related_bounded_value t bottom (UnderLets.interp ident_interp (bottomify st)) v.
      Proof using bottom'_Proper bottom'_related.
        induction t; cbn in *;
          repeat first [ progress subst
                       | progress cbv [respectful] in *
                       | progress cbn [UnderLets.interp] in *
                       | progress destruct_head'_and
                       | break_innermost_match_step
                       | progress intros
                       | apply conj
                       | reflexivity
                       | apply bottom'_Proper
                       | apply bottom'_related
                       | solve [ eauto ]
                       | rewrite UnderLets.interp_splice ].
      Qed.

      Context (interp_ident_Proper
               : forall annotate_with_state t idc,
                  related_bounded_value (ident_extract t idc) (UnderLets.interp ident_interp (interp_ident annotate_with_state t idc)) (ident_interp t idc)).

      Lemma interp_interp
            annotate_with_state G G' {t} (e_st e1 e2 e3 : expr t)
            (HG : forall t v1 v2 v3, List.In (existT _ t (v1, v2, v3)) G
                                     -> related_bounded_value_with_lets v1 v2 v3)
            (HG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> v1 == v2)
            (Hwf : expr.wf3 G e_st e1 e2)
            (Hwf' : expr.wf G' e2 e3)
        : related_bounded_value_with_lets
            (extract' e_st)
            (interp annotate_with_state e1)
            (expr.interp (@ident_interp) e2).
      Proof using interp_ident_Proper interp_annotate abstraction_relation'_Proper ident_interp_Proper' abstract_domain'_R_transitive abstract_domain'_R_symmetric bottom'_Proper bottom'_related.
        clear -ident_interp_Proper' interp_ident_Proper interp_annotate abstraction_relation'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric bottom'_Proper bottom'_related HG HG' Hwf Hwf'.
        cbv [related_bounded_value_with_lets] in *;
          revert dependent annotate_with_state; revert dependent G'; induction Hwf; intros;
            cbn [extract' interp expr.interp UnderLets.interp List.In related_bounded_value reify reflect] in *; cbv [Let_In] in *.
        all: destruct annotate_with_state eqn:?.
        all: repeat first [ progress intros
                          | progress subst
                          | progress inversion_sigma
                          | progress inversion_prod
                          | progress destruct_head'_and
                          | progress destruct_head'_or
                          | progress destruct_head'_sig
                          | progress destruct_head'_sigT
                          | progress destruct_head'_prod
                          | progress eta_expand
                          | exfalso; assumption
                          | progress cbn [UnderLets.interp List.In eq_rect fst snd projT1 projT2] in *
                          | rewrite UnderLets.interp_splice
                          | rewrite interp_annotate
                          | solve [ cbv [Proper respectful Basics.impl] in *; unshelve eauto using related_of_related_bounded_value, related_bounded_value_bottomify ]
                          | progress specialize_by_assumption
                          | progress cbv [Let_In] in *
                          | progress cbn [state_of_value extract'] in *
                          | progress expr.invert_subst
                          | match goal with
                            | [ |- abstract_domain ?t ] => exact (@bottom t)
                            | [ H : expr.wf _ _ _ |- Proper type.eqv _ ]
                              => apply expr.wf_interp_Proper_gen1 in H;
                                 [ cbv [Proper]; etransitivity; (idtac + symmetry); exact H | auto ]
                            | [ H : _ |- _ ]
                              => (tryif first [ constr_eq H HG | constr_eq H HG' ]
                                   then fail
                                   else (apply H; clear H))
                            | [ |- related_bounded_value _ (fst _, UnderLets.interp _ (annotate _ _ _ _)) _ ]
                              => apply related_bounded_value_annotate_base
                            | [ H : context[match ?v with None => _ | _ => _ end] |- _ ] => destruct v eqn:?
                            | [ H : context[@related_bounded_value (type.base ?t) ?x _ ?y]
                                |- @related_bounded_value (type.base ?t) ?x _ ?y ]
                              => eapply related_bounded_value_Proper_interp_eq_base; [ reflexivity | split; hnf | reflexivity | eapply H ];
                                 cbn [fst snd expr.interp];
                                 [ reflexivity | reflexivity | .. ]
                            end
                          | apply conj
                          | match goal with
                            | [ H : _ = _ |- _ ] => rewrite H
                            end
                          | break_innermost_match_step
                          | progress expr.inversion_wf_one_constr
                          | match goal with
                            | [ H : _ |- _ ]
                              => (tryif first [ constr_eq H HG | constr_eq H HG' ]
                                   then fail
                                   else (eapply H; clear H;
                                         [ lazymatch goal with
                                           | [ |- expr.wf _ _ _ ]
                                             => solve [ eassumption
                                                      | match goal with
                                                        | [ H : forall v1 v2, expr.wf _ _ _ |- expr.wf _ (?f ?x) _ ]
                                                          => apply (H x x)
                                                        end ]
                                           | [ |- bool ] (* unused [annotate_with_state] argument to a [Proper ... /\ ...] lemma which is used for its [Proper] part *)
                                             => constructor
                                           | _ => idtac
                                           end .. ];
                                         match goal with
                                           [ |- ?G ] => assert_fails has_evar G
                                         end))
                            end
                          | reflexivity ].
      Qed.

      Lemma interp_eval_with_bound'
            annotate_with_state {t} (e_st e1 e2 : expr t)
            (Hwf : expr.wf3 nil e_st e1 e2)
            (Hwf' : expr.wf nil e2 e2)
            (Ht : type.is_not_higher_order t = true)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
            (Hst : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) st)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
              type.app_curried (expr.interp ident_interp (eval_with_bound' annotate_with_state e1 st)) arg1
              = type.app_curried (expr.interp ident_interp e2) arg2)
          /\ (forall arg1
                     (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1)
                     (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                 abstraction_relation'
                   _
                   (extract_gen e_st st)
                   (type.app_curried (expr.interp ident_interp (eval_with_bound' annotate_with_state e1 st)) arg1)).
      Proof using interp_annotate abstraction_relation'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric bottom'_related interp_ident_Proper bottom'_Proper ident_interp_Proper'.
        cbv [extract_gen extract' eval_with_bound'].
        split; intros; rewrite UnderLets.interp_to_expr, UnderLets.interp_splice.
        all: eapply interp_reify_first_order; eauto.
        all: eapply interp_interp; eauto; wf_t.
      Qed.

      Lemma interp_eta_expand_with_bound'
            {t} (e1 e2 : expr t)
            (Hwf : expr.wf nil e1 e2)
            (b_in : type.for_each_lhs_of_arrow abstract_domain t)
            (Hb_in : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) b_in)
        : forall arg1 arg2
            (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
            (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
          type.app_curried (expr.interp ident_interp (eta_expand_with_bound' e1 b_in)) arg1 = type.app_curried (expr.interp ident_interp e2) arg2.
      Proof using interp_annotate ident_interp_Proper' bottom'_related abstraction_relation'_Proper bottom'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric.
        cbv [eta_expand_with_bound'].
        intros; rewrite UnderLets.interp_to_expr.
        eapply interp_reify; eauto.
        eapply interp_reflect; eauto using bottom_related.
        eapply @expr.wf_interp_Proper_gen; auto using Hwf.
      Qed.

      Lemma interp_extract'_from_wf_gen G
            (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> abstract_domain_R v1 v2)
            {t} (e1 e2 : expr t)
            (Hwf : expr.wf G e1 e2)
        : abstract_domain_R (extract' e1) (extract' e2).
      Proof using ident_extract_Proper bottom'_Proper.
        cbv [abstract_domain_R] in *; induction Hwf; cbn [extract']; break_innermost_match.
        all: repeat first [ progress subst
                          | progress inversion_sigma
                          | progress inversion_prod
                          | solve [ cbv [Proper respectful] in *; eauto ]
                          | progress cbv [respectful Let_In] in *
                          | progress cbn [type.related List.In eq_rect partial.bottom] in *
                          | progress intros
                          | progress destruct_head'_or
                          | apply bottom_Proper
                          | match goal with H : _ |- type.related _ _ _ => apply H; clear H end ].
      Qed.

      Lemma interp_extract'_from_wf {t} (e1 e2 : expr t)
            (Hwf : expr.wf nil e1 e2)
        : abstract_domain_R (extract' e1) (extract' e2).
      Proof using ident_extract_Proper bottom'_Proper.
        eapply interp_extract'_from_wf_gen; revgoals; wf_t.
      Qed.
    End with_type.

    Module ident.
      Import API.
      Local Notation UnderLets := (@UnderLets base.type ident).
      Section with_type.
        Context (abstract_domain' : base.type -> Type).
        Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
        Local Notation var := interp_type.
        Context (annotate_expr : forall t, abstract_domain' t -> option (@expr var (t -> t)))
                (bottom' : forall A, abstract_domain' A)
                (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
                (update_literal_with_state : forall A : base.type.base, abstract_domain' A -> base.interp A -> base.interp A)
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (extract_option_state : forall A, abstract_domain' (base.type.option A) -> option (option (abstract_domain' A)))
                (is_annotated_for : forall t t', @expr var t -> abstract_domain' t' -> bool)
                (skip_annotations_under : forall t, ident t -> bool)
                (strip_annotation : forall t, ident t -> option (@value base.type ident var abstract_domain' t))
                (abstraction_relation' : forall t, abstract_domain' t -> base.interp t -> Prop)
                (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop)
                (abstraction_relation'_Proper : forall t, Proper (abstract_domain'_R t ==> eq ==> Basics.impl) (abstraction_relation' t))
                (bottom'_related : forall t v, abstraction_relation' t (bottom' t) v)
                {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
                {abstract_domain'_R_transitive : forall t, Transitive (@abstract_domain'_R t)}
                {abstract_domain'_R_symmetric : forall t, Symmetric (@abstract_domain'_R t)}.
        Local Notation abstraction_relation := (@abstraction_relation base.type abstract_domain' base.interp abstraction_relation').
        Local Notation ident_interp := ident.interp (only parsing).
        Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' abstract_domain'_R).
        Local Notation fill_in_bottom_for_arrows := (@fill_in_bottom_for_arrows base.type abstract_domain' bottom').
        Local Notation related_bounded_value := (@related_bounded_value base.type ident abstract_domain' base.interp (@ident_interp) abstraction_relation' bottom' abstract_domain'_R).
        Context {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                (interp_annotate_expr
                 : forall t st idc,
                    annotate_expr t st = Some idc
                    -> forall v, abstraction_relation' _ st v
                           -> expr.interp (@ident_interp) idc v = v)
                (abstract_interp_ident_Proper'
                 : forall t idc, type.related_hetero (@abstraction_relation') (abstract_interp_ident t idc) (ident_interp idc))
                (extract_list_state_related
                 : forall t st ls v st' v',
                    extract_list_state t st = Some ls
                    -> abstraction_relation' _ st v
                    -> List.In (st', v') (List.combine ls v)
                    -> abstraction_relation' t st' v')
                (extract_list_state_length_good
                 : forall t st ls v,
                    extract_list_state t st = Some ls
                    -> abstraction_relation' _ st v
                    -> length ls = length v)
                (extract_option_state_related
                 : forall t st a v,
                    extract_option_state t st = Some a
                    -> abstraction_relation' _ st v
                    -> option_eq (abstraction_relation' t) a v)
                (strip_annotation_related
                 : forall t idc v,
                    strip_annotation t idc = Some v
                    -> related_bounded_value (abstract_interp_ident t idc) v (ident_interp idc)).

        Local Notation update_annotation := (@ident.update_annotation _ abstract_domain' annotate_expr is_annotated_for).
        Local Notation annotate_with_expr := (@ident.annotate_with_expr _ abstract_domain' annotate_expr is_annotated_for).
        Local Notation annotate_base := (@ident.annotate_base _ abstract_domain' annotate_expr is_annotated_for).
        Local Notation annotate := (@ident.annotate _ abstract_domain' annotate_expr abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
        Local Notation reify := (@reify base.type ident _ abstract_domain' annotate bottom').
        Local Notation reflect := (@reflect base.type ident _ abstract_domain' annotate bottom').

        Lemma abstract_interp_ident_Proper'' t idc
          : type.related_hetero (@abstraction_relation') (fill_in_bottom_for_arrows (abstract_interp_ident t idc)) (ident_interp idc).
        Proof using abstract_interp_ident_Proper' bottom'_related.
          generalize (abstract_interp_ident_Proper' t idc); clear -bottom'_related.
          generalize (ident_interp idc), (abstract_interp_ident t idc); clear idc.
          intros v st H.
          induction t as [| [|s' d'] IHs d IHd]; cbn in *; cbv [respectful_hetero] in *;
            auto.
          intros; apply IHd, H; clear IHd H.
          intros; apply bottom_related; assumption.
        Qed.

        Lemma interp_update_annotation t st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e))
          : expr.interp (@ident_interp) (@update_annotation t st e)
            = expr.interp (@ident_interp) e.
        Proof using interp_annotate_expr.
          cbv [update_annotation];
            repeat first [ reflexivity
                         | progress subst
                         | progress eliminate_hprop_eq
                         | progress cbn [expr.interp eq_rect] in *
                         | match goal with
                           | [ H : annotate_expr _ _ = Some _ |- _ ] => rewrite (interp_annotate_expr _ _ _ H) by eassumption
                           end
                         | progress expr.invert_match
                         | progress type_beq_to_eq
                         | progress rewrite_type_transport_correct
                         | progress break_innermost_match_step ].
        Qed.

        Lemma interp_annotate_with_expr is_let_bound t st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e))
          : expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate_with_expr is_let_bound t st e))
            = expr.interp (@ident_interp) e.
        Proof using interp_annotate_expr.
          cbv [annotate_with_expr]; break_innermost_match; cbn [expr.interp UnderLets.interp];
            apply interp_update_annotation; assumption.
        Qed.

        Lemma interp_annotate_base is_let_bound (t : base.type.base) st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base (base.type.type_base t)) (@ident_interp) e))
          : expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate_base is_let_bound t st e))
            = expr.interp (@ident_interp) e.
        Proof using interp_annotate_expr.
          cbv [annotate_base]; break_innermost_match; expr.invert_subst; cbv beta iota in *; subst.
          { apply interp_annotate_with_expr; assumption. }
        Qed.

        Lemma interp_annotate is_let_bound (t : base.type) st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e))
          : expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate is_let_bound t st e))
            = expr.interp (@ident_interp) e.
        Proof using interp_annotate_expr abstract_interp_ident_Proper' extract_list_state_related extract_list_state_length_good extract_option_state_related bottom'_related.
          induction t; cbn [annotate]; auto using interp_annotate_base.
          all: repeat first [ reflexivity
                            | progress subst
                            | progress inversion_option
                            | progress inversion_prod
                            | progress destruct_head'_ex
                            | progress destruct_head'_and
                            | progress break_innermost_match
                            | progress break_innermost_match_hyps
                            | progress expr.invert_subst
                            | progress cbn [fst snd UnderLets.interp expr.interp ident_interp Nat.add] in *
                            | progress cbv [ident.literal] in *
                            | match goal with
                              | [ H : context[ident_interp (ident.ident_Literal _)] |- _ ] => rewrite ident.interp_ident_Literal in H
                              | [ H : context[ident_interp ident.ident_Some] |- _ ] => rewrite ident.interp_ident_Some in H
                              | [ H : context[ident_interp ident.ident_pair] |- _ ] => rewrite ident.interp_ident_pair in H
                              end
                            | rewrite !UnderLets.interp_splice
                            | rewrite !UnderLets.interp_splice_list
                            | rewrite !List.map_map
                            | rewrite expr.interp_reify_list
                            | rewrite nth_error_combine
                            | apply interp_annotate_with_expr; assumption
                            | progress fold (@base.interp) in *
                            | progress intros
                            | pose proof (@extract_list_state_length_good _ _ _ _ ltac:(eassumption) ltac:(eassumption)); clear extract_list_state_length_good
                            | match goal with
                              | [ H : context[expr.interp _ (reify_list _)] |- _ ] => rewrite expr.interp_reify_list in H
                              | [ H : abstraction_relation' (_ * _) _ (_, _) |- _ ]
                                => pose proof (abstract_interp_ident_Proper'' _ ident.fst _ _ H);
                                  pose proof (abstract_interp_ident_Proper'' _ ident.snd _ _ H);
                                  clear H
                              | [ H : context[_ = _] |- _ = _ ] => rewrite H by assumption
                              | [ |- List.map ?f (List.combine ?l1 ?l2) = List.map ?g ?l2 ]
                                => transitivity (List.map g (List.map (@snd _ _) (List.combine l1 l2)));
                                  [ rewrite List.map_map; apply List.map_ext_in
                                  | rewrite map_snd_combine, List.firstn_all2; [ reflexivity | ] ]
                              | [ Hls : extract_list_state ?t ?st = Some ?ls, He : abstraction_relation' _ ?st ?v |- abstraction_relation' _ _ _ ]
                                => apply (fun st' v' => extract_list_state_related t st ls v st' v' Hls He)
                              | [ H : context[List.nth_error (List.combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                              | [ H : List.In _ (List.combine _ _) |- _ ] => apply List.In_nth_error in H
                              | [ |- List.In _ (List.combine _ _) ] => eapply nth_error_In
                              | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                              | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map_ex in H
                              | [ H : List.nth_error _ _ = None |- _ ] => rewrite List.nth_error_None in H
                              | [ H : context[length ?ls] |- _ ] => tryif is_var ls then fail else (progress autorewrite with distr_length in H)
                              | [ |- context[length ?ls] ] => tryif is_var ls then fail else (progress autorewrite with distr_length)
                              | [ H : List.nth_error ?ls ?n = Some _, H' : length ?ls <= ?n |- _ ]
                                => apply nth_error_value_length in H; exfalso; clear -H H'; lia
                              | [ H : List.nth_error ?l ?n = _, H' : List.nth_error ?l ?n' = _ |- _ ]
                                => unify n n'; rewrite H in H'
                              | [ Hls : extract_list_state ?t ?st = Some ?ls, He : abstraction_relation' _ ?st ?v |- _ ]
                                => pose proof (fun st' v' => extract_list_state_related t st ls v st' v' Hls He); clear extract_list_state_related
                              | [ IH : forall st e, _ -> expr.interp _ (UnderLets.interp _ (annotate _ _ _)) = _ |- List.map (fun x => expr.interp _ _) (List.combine _ _) = expr.interp _ _ ]
                                => erewrite List.map_ext_in;
                                   [
                                   | intros; eta_expand; rewrite IH; cbn [expr.interp ident_interp ident.smart_Literal]; [ reflexivity | ] ]
                              | [ H : abstraction_relation' _ ?st (List.map (expr.interp _) ?ls), H' : forall st' v', List.In _ (List.combine _ _) -> abstraction_relation' _ _ _, H'' : List.nth_error ?ls _ = Some ?e |- abstraction_relation' _ _ (expr.interp _ ?e) ]
                                => apply H'
                              | [ H : context[List.nth_error (List.seq _ _) _] |- _ ] => rewrite nth_error_seq in H
                              end
                            | apply Nat.eq_le_incl
                            | rewrite <- List.map_map with (f:=fst), map_fst_combine
                            | match goal with
                              | [ |- context[List.map (fun a : ?A * ?B => @?body a) (List.combine _ _)] ]
                                => let aa := fresh in
                                   let bb := fresh in
                                   let g' := match (eval cbn [fst] in (fun (bb : B) (aa : A) => body (aa, bb))) with
                                             | fun _ => ?g => g
                                             end in
                                   erewrite <- List.map_map with (f:=fst) (g:=g'), map_fst_combine
                              end
                            | rewrite Lists.List.firstn_all2 by distr_length
                            | apply map_nth_default_seq
                            | progress destruct_head' option
                            | progress cbn [Option.combine option_map reify_option option_rect UnderLets.splice_option] in *
                            | apply (f_equal Some)
                            | match goal with
                              | [ H : abstraction_relation' _ ?st _, H' : extract_option_state _ ?st = _ |- _ ]
                                => eapply extract_option_state_related in H; [ clear H' | eexact H' ];
                                   cbv [option_eq] in H
                              | [ H : context[expr.interp _ _ = expr.interp _ _] |- expr.interp _ _ = expr.interp _ _ ] => apply H; clear H
                              | [ H : forall st' v', List.In _ (List.combine _ _) -> abstraction_relation' _ _ _ |- abstraction_relation' _ _ _ ]
                                => apply H; clear H; cbv [List.nth_default]
                              | [ |- None = Some _ ] => exfalso; lia
                              end ].
        Qed.

        Local Notation interp_ident := (@ident.interp_ident _ abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for strip_annotation).

        Lemma interp_ident_Proper_not_nth_default_nostrip annotate_with_state t idc
          : related_bounded_value (abstract_interp_ident t idc) (UnderLets.interp (@ident_interp) (Base (reflect annotate_with_state (expr.Ident idc) (abstract_interp_ident _ idc)))) (ident_interp idc).
        Proof using abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr abstract_interp_ident_Proper bottom'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric.
          cbn [UnderLets.interp].
          eapply interp_reflect;
            try first [ apply ident.interp_Proper
                      | apply abstract_interp_ident_Proper''
                      | eapply abstract_interp_ident_Proper; reflexivity
                      | apply interp_annotate ];
            eauto.
        Qed.

        Lemma interp_ident_Proper_not_nth_default annotate_with_state t idc
          : related_bounded_value
              (abstract_interp_ident t idc)
              ((UnderLets.interp (@ident_interp))
                 (Base match strip_annotation _ idc with
                       | Some v => v
                       | None => reflect annotate_with_state (expr.Ident idc) (abstract_interp_ident _ idc)
                       end))
              (ident_interp idc).
        Proof using abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr abstract_interp_ident_Proper bottom'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric strip_annotation_related.
          pose proof (strip_annotation_related t idc) as H.
          break_innermost_match; eauto using eq_refl, interp_ident_Proper_not_nth_default_nostrip.
        Qed.

        Lemma interp_ident_Proper_nth_default annotate_with_state T (idc:=@ident.List_nth_default T)
          : related_bounded_value (abstract_interp_ident _ idc) (UnderLets.interp (@ident_interp) (interp_ident annotate_with_state idc)) (ident_interp idc).
        Proof using abstract_interp_ident_Proper abstract_interp_ident_Proper' abstraction_relation'_Proper extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr bottom'_related.
          subst idc; cbn [interp_ident reify reflect fst snd UnderLets.interp ident_interp related_bounded_value abstract_domain value].
          cbv [abstract_domain]; cbn [type.interp bottom_for_each_lhs_of_arrow state_of_value fst snd].
          repeat first [ progress intros
                       | progress cbn [UnderLets.interp fst snd expr.interp ident_interp] in *
                       | progress destruct_head'_prod
                       | progress destruct_head'_and
                       | progress subst
                       | progress eta_expand
                       | rewrite UnderLets.interp_splice
                       | progress expr.invert_subst
                       | break_innermost_match_step
                       | progress cbn [type.interp base.interp base.base_interp] in *
                       | rewrite interp_annotate
                       | solve [ cbv [Proper respectful Basics.impl] in *; eauto ]
                       | split; [ apply (@abstract_interp_ident_Proper _ (@ident.List_nth_default T) _ eq_refl) | ]
                       | split; [ reflexivity | ]
                       | apply (@abstract_interp_ident_Proper'' _ (@ident.List_nth_default T))
                       | apply conj
                       | rewrite map_nth_default_always
                       | rewrite expr.interp_reify_list
                       | match goal with
                         | [ H : context[expr.interp _ (UnderLets.interp _ (annotate _ _ _))] |- _ ]
                           => rewrite interp_annotate in H
                         | [ H : context[expr.interp _ (reify_list _)] |- _ ]
                           => rewrite expr.interp_reify_list in H
                         | [ H : _ = reify_list _ |- _ ] => apply (f_equal (expr.interp (@ident_interp))) in H
                         | [ H : expr.interp _ ?x = _ |- context[expr.interp _ ?x] ] => rewrite H
                         | [ |- Proper _ _ ] => cbv [Proper type.related respectful]
                         end ].
        Qed.

        Lemma interp_ident_Proper annotate_with_state t idc
          : related_bounded_value (abstract_interp_ident t idc) (UnderLets.interp (@ident_interp) (interp_ident annotate_with_state idc)) (ident_interp idc).
        Proof using abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr strip_annotation_related.
          pose idc as idc'.
          destruct idc; first [ refine (@interp_ident_Proper_not_nth_default _ _ idc')
                              | refine (@interp_ident_Proper_nth_default _ _) ].
        Qed.

        Local Notation eval_with_bound := (@partial.ident.eval_with_bound _ abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for strip_annotation).
        Local Notation eta_expand_with_bound := (@partial.ident.eta_expand_with_bound _ abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
        Local Notation extract := (@ident.extract abstract_domain' bottom' abstract_interp_ident).

        Lemma interp_eval_with_bound
              annotate_with_state {t} (e_st e1 e2 : expr t)
              (Hwf : expr.wf3 nil e_st e1 e2)
              (Hwf' : expr.wf nil e2 e2)
              (Ht : type.is_not_higher_order t = true)
              (st : type.for_each_lhs_of_arrow abstract_domain t)
              (Hst : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) st)
          : (forall arg1 arg2
                    (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                    (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
                type.app_curried (expr.interp (@ident_interp) (eval_with_bound skip_annotations_under annotate_with_state e1 st)) arg1
                = type.app_curried (expr.interp (@ident_interp) e2) arg2)
            /\ (forall arg1
                       (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1)
                       (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                   abstraction_relation'
                     _
                     (extract e_st st)
                     (type.app_curried (expr.interp (@ident_interp) (eval_with_bound skip_annotations_under annotate_with_state e1 st)) arg1)).
        Proof using abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr strip_annotation_related. cbv [extract eval_with_bound]; apply @interp_eval_with_bound' with (abstract_domain'_R:=abstract_domain'_R); auto using interp_annotate, interp_ident_Proper, ident.interp_Proper. Qed.

        Lemma interp_eta_expand_with_bound
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
              (Ht : type.is_not_higher_order t = true)
              (b_in : type.for_each_lhs_of_arrow abstract_domain t)
              (Hb_in : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) b_in)
          : forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
            type.app_curried (expr.interp (@ident_interp) (eta_expand_with_bound e1 b_in)) arg1 = type.app_curried (expr.interp (@ident_interp) e2) arg2.
        Proof using abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr. cbv [partial.ident.eta_expand_with_bound]; eapply interp_eta_expand_with_bound'; eauto using interp_annotate, ident.interp_Proper. Qed.
      End with_type.
    End ident.

    Lemma default_relax_zrange_good
      : forall r r' z, is_tighter_than_bool z r = true
                       -> default_relax_zrange r = Some r'
                       -> is_tighter_than_bool z r' = true.
    Proof.
      cbv [default_relax_zrange]; intros; inversion_option; subst; assumption.
    Qed.

    Section specialized.
      Import API.
      Local Notation abstract_domain' := ZRange.type.base.option.interp (only parsing).
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Local Notation abstract_domain'_R t := (@eq (abstract_domain' t)) (only parsing).
      Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' (fun t => abstract_domain'_R t)).
      Local Notation fill_in_bottom_for_arrows := (@fill_in_bottom_for_arrows base.type abstract_domain' bottom').

      Definition abstraction_relation' {t} : abstract_domain' t -> base.interp t -> Prop
        := fun st v => @ZRange.type.base.option.is_bounded_by t st v = true.

      Lemma bottom'_bottom {t} : forall v, abstraction_relation' (bottom' t) v.
      Proof using Type.
        cbv [abstraction_relation' bottom']; induction t; cbn; intros; break_innermost_match; cbn; try reflexivity.
        rewrite Bool.andb_true_iff; split; auto.
      Qed.

      Lemma abstract_interp_ident_related {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t} (idc : ident t)
        : type.related_hetero (@abstraction_relation') (abstract_interp_ident assume_cast_truncates t idc) (ident.interp idc).
      Proof using Type. apply ZRange.ident.option.interp_related. Qed.

      Local Ltac zrange_interp_idempotent_t :=
        repeat first [ progress destruct_head'_ex
                     | progress subst
                     | progress cbn in *
                     | progress cbv [ZRange.goodb ZRange.ident.option.interp_Z_cast_truncate ZRange.ident.option.interp_Z_cast] in *
                     | reflexivity
                     | lia
                     | progress Z.ltb_to_lt
                     | progress destruct_head'_and
                     | break_innermost_match_step
                     | break_innermost_match_hyps_step
                     | rewrite (proj1 ZRange.normalize_id_iff_goodb)
                     | progress Bool.split_andb
                     | match goal with
                       | [ H : ?x = ?x |- _ ] => clear H
                       | [ H : (?x <= ?y)%Z, H' : (?y <= ?x)%Z |- _ ]
                         => assert (x = y) by lia; clear H H'
                       end
                     | progress unshelve Reflect.reflect_hyps; []
                     | progress destruct_head'_or
                     | progress destruct_head' zrange
                     | rewrite Bool.andb_true_iff
                     | match goal with
                       | [ |- and _ _ ] => split
                       end
                     | progress cbv [is_bounded_by_bool] ].

      Lemma zrange_interp_tighter_bounded_Z_cast {opts : AbstractInterpretation.Options} {assume_cast_truncates r1 r2 v}
            (H1 : ZRange.type.base.option.is_bounded_by (t:=base.type.Z) r1 v = true)
            (H2 : ZRange.type.base.option.is_bounded_by (t:=base.type.Z) r2 v = true)
        : ZRange.type.base.option.is_bounded_by (t:=base.type.Z) (ZRange.ident.option.interp assume_cast_truncates ident.Z_cast r1 r2) v = true.
      Proof using Type. destruct r1, r2, assume_cast_truncates; zrange_interp_idempotent_t. Qed.

      Lemma zrange_interp_tighter_bounded_Z_cast2 {opts : AbstractInterpretation.Options} {assume_cast_truncates r1 r2 v}
            (H1 : ZRange.type.base.option.is_bounded_by (t:=base.type.Z*base.type.Z) r1 v = true)
            (H2 : ZRange.type.base.option.is_bounded_by (t:=base.type.Z*base.type.Z) r2 v = true)
        : ZRange.type.base.option.is_bounded_by (t:=base.type.Z*base.type.Z) (ZRange.ident.option.interp assume_cast_truncates ident.Z_cast2 r1 r2) v = true.
      Proof using Type. destruct r1, r2, assume_cast_truncates; zrange_interp_idempotent_t. Qed.

      Local Notation related_bounded_value := (@related_bounded_value base.type ident abstract_domain' base.interp (@ident.interp) (@abstraction_relation') bottom' (fun t => abstract_domain'_R t)).
      Lemma always_strip_annotation_related {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t} (idc : ident t)
            v (Hv : always_strip_annotation assume_cast_truncates t idc = Some v)
        : related_bounded_value (abstract_interp_ident assume_cast_truncates t idc) v (ident.interp idc).
      Proof using Type.
        pose proof (@abstract_interp_ident_related _ assume_cast_truncates _ ident.Z_cast).
        pose proof (fun x1 x2 y1 y2 H x01 x02 y01 y02 H' => @abstract_interp_ident_related _ assume_cast_truncates _ ident.Z_cast2 (x1, x2) (y1, y2) H (x01, x02) (y01, y02) H').
        cbv [always_strip_annotation] in *; break_innermost_match_hyps; inversion_option; subst.
        all: repeat first [ reflexivity
                          | progress cbn [related_bounded_value UnderLets.interp fst snd type.related_hetero] in *
                          | progress cbv [respectful_hetero] in *
                          | progress intros
                          | progress destruct_head'_and
                          | progress subst
                          | progress inversion_prod
                          | progress inversion_option
                          | match goal with
                            | [ |- Proper _ _ ] => exact _
                            | [ |- _ /\ _ ] => split
                            | [ H1 : (?x <=? ?y)%zrange = true, H2 : is_bounded_by_bool _ ?x = true |- _ ]
                              => unique pose proof (ZRange.is_bounded_by_of_is_tighter_than _ _ H1 _ H2)
                            | [ |- andb _ _ = true ] => rewrite Bool.andb_true_iff
                            | [ H : andb _ _ = true |- _ ] => rewrite Bool.andb_true_iff in H
                            | [ H : ZRange.type.base.option.is_bounded_by (Some _) _ = _ |- _ ]
                              => progress cbn -[zrange_beq prod_beq] in H
                            | [ H : ZRange.type.base.option.is_bounded_by (Some _, Some _) _ = _ |- _ ]
                              => progress cbn -[zrange_beq prod_beq] in H
                            | [ H : ZRange.type.base.is_tighter_than _ _ = _ |- _ ]
                              => progress cbn -[zrange_beq prod_beq] in H
                            | [ H : bind _ _ = Some _ |- _ ] => progress cbv [bind] in H
                            end
                          | progress break_innermost_match
                          | progress break_innermost_match_hyps
                          | progress Reflect.reflect_beq_to_eq zrange_beq
                          | progress cbv [abstraction_relation' ZRange.type.base.option.lift_Some] in *
                          | cbn [Compilers.ident_interp]; progress cbv [ident.cast2]
                          | rewrite ident.cast_in_bounds by assumption
                          | now destruct assume_cast_truncates
                          | rewrite zrange_interp_idempotent_Z_cast by (cbn; eexists; eassumption)
                          | rewrite zrange_interp_idempotent_Z_cast2 by (cbn; eexists (_, _); rewrite Bool.andb_true_iff; split; eassumption)
                          | progress cbv [abstract_interp_ident] in *
                          | match goal with
                            | [ H : _ |- _ ] => apply H; cbn; cbn [ZRange.type.base.option.is_bounded_by] in *; Prod.eta_expand; rewrite ?Bool.andb_true_iff in *; destruct_head'_and; try apply conj; try apply zrange_lb; now auto
                            end
                          | progress cbn [ZRange.type.base.option.is_bounded_by]
                          | match goal with
                            | [ H : ZRange.ident.option.interp ?act ident.Z_cast ?r1 ?r2 = Some ?r3 |- ZRange.type.base.is_bounded_by ?r3 ?v = true ]
                              => let H' := fresh in
                                 pose proof (@zrange_interp_tighter_bounded_Z_cast _ act r1 r2 v) as H';
                                 rewrite H in H'; now apply H'
                            | [ H : context G[ZRange.ident.option.interp ?act ident.Z_cast2 ?r1 ?r2] |- _ ]
                              => let G' := context G[(ZRange.ident.option.interp act ident.Z_cast (fst r1) (fst r2),
                                                      ZRange.ident.option.interp act ident.Z_cast (snd r1) (snd r2))] in
                                 change G' in H
                            end ].
      Qed.

      Lemma strip_annotation_related {opts : AbstractInterpretation.Options} {assume_cast_truncates strip_annotations : bool} {t} (idc : ident t)
            v (Hv : strip_annotation assume_cast_truncates strip_annotations t idc = Some v)
        : related_bounded_value (abstract_interp_ident assume_cast_truncates t idc) v (ident.interp idc).
      Proof using Type.
        destruct strip_annotations; cbv [strip_annotation] in *; try congruence;
          now apply always_strip_annotation_related.
      Qed.

      Lemma extract_list_state_related {t} st v ls
        : @abstraction_relation' _ st v
          -> @extract_list_state t st = Some ls
          -> length ls = length v
             /\ forall st' (v' : base.interp t), List.In (st', v') (List.combine ls v) -> @abstraction_relation' t st' v'.
      Proof using Type.
        cbv [abstraction_relation' extract_list_state]; cbn [ZRange.type.base.option.is_bounded_by].
        intros; subst.
        split.
        { eapply FoldBool.fold_andb_map_length; eassumption. }
        { intros *.
          revert dependent v; induction ls, v; cbn; try tauto.
          rewrite Bool.andb_true_iff.
          intros; destruct_head'_and; destruct_head'_or; inversion_prod; subst; eauto. }
      Qed.

      Lemma extract_option_state_related {t} st a v
        : extract_option_state t st = Some a
          -> @abstraction_relation' _ st v
          -> option_eq (@abstraction_relation' t) a v.
      Proof using Type.
        cbv [abstraction_relation' extract_option_state option_eq]; intros; subst; cbn in *; cbv [option_beq_hetero] in *; break_match; break_match_hyps; auto; congruence.
      Qed.

      Lemma Extract_FromFlat_ToFlat' {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t} (e : Expr t) (Hwf : Wf e) b_in1 b_in2
            (Hb : type.and_for_each_lhs_of_arrow (fun t => type.eqv) b_in1 b_in2)
        : partial.Extract assume_cast_truncates (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e)) b_in1
          = partial.Extract assume_cast_truncates e b_in2.
      Proof using Type.
        cbv [partial.Extract partial.ident.extract partial.extract_gen].
        revert b_in1 b_in2 Hb.
        rewrite <- (@type.related_iff_app_curried base.type ZRange.type.base.option.interp (fun _ => eq)).
        apply interp_extract'_from_wf; auto with wf typeclass_instances.
        apply GeneralizeVar.wf_from_flat_to_flat, Hwf.
      Qed.

      Lemma Extract_FromFlat_ToFlat {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t} (e : Expr t) (Hwf : Wf e) b_in
            (Hb : Proper (type.and_for_each_lhs_of_arrow (fun t => type.eqv)) b_in)
        : partial.Extract assume_cast_truncates (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e)) b_in
          = partial.Extract assume_cast_truncates e b_in.
      Proof using Type. apply Extract_FromFlat_ToFlat'; assumption. Qed.

      Lemma Extract_GeneralizeVar {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t} (e : Expr t) (Hwf : Wf e) b_in
            (Hb : Proper (type.and_for_each_lhs_of_arrow (fun t => type.eqv)) b_in)
        : partial.Extract assume_cast_truncates (GeneralizeVar.GeneralizeVar (e _)) b_in
          = partial.Extract assume_cast_truncates e b_in.
      Proof using Type. apply Extract_FromFlat_ToFlat; assumption. Qed.

      Section with_relax.
        Context {relax_zrange : zrange -> option zrange}
                (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                         -> relax_zrange r = Some r'
                                         -> is_tighter_than_bool z r' = true).

        Local Lemma Hrelax' r r' z
          : is_bounded_by_bool z r = true
            -> relax_zrange (ZRange.normalize r) = Some r'
            -> is_bounded_by_bool z r' = true.
        Proof using Hrelax.
          intros H Hr.
          eapply ZRange.is_bounded_by_of_is_tighter_than; [ eapply Hrelax; [ | eassumption ] | eassumption ].
          eapply ZRange.is_tighter_than_bool_normalize_of_goodb, ZRange.goodb_of_is_bounded_by_bool; eassumption.
        Qed.

        Lemma interp_annotate_expr {t} st idc
              (Hst : @annotate_expr relax_zrange _ t st = Some idc)
          : forall v, abstraction_relation' st v
                      -> expr.interp (@ident.interp) idc v = v.
        Proof using Hrelax.
          repeat first [ progress cbv [annotate_expr Crypto.Util.Option.bind annotation_of_state option_map abstraction_relation' ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by] in *
                       | reflexivity
                       | progress inversion_option
                       | progress subst
                       | break_innermost_match_hyps_step
                       | break_innermost_match_step
                       | progress cbn [ident.interp base.interp base.base_interp expr.interp] in *
                       | progress cbv [ident.cast2] in *
                       | progress intros
                       | progress Bool.split_andb
                       | rewrite ident.cast_in_bounds by assumption
                       | match goal with
                         | [ H : is_bounded_by_bool ?v ?r = true, H' : relax_zrange (ZRange.normalize ?r) = Some ?r' |- _ ]
                           => unique assert (is_bounded_by_bool v r' = true) by (eapply Hrelax'; eassumption)
                         end ].
        Qed.

        Lemma interp_annotate_expr_Proper {t} st1 st2 (Hst : abstract_domain'_R t st1 st2)
          : @annotate_expr relax_zrange interp_type t st1 = @annotate_expr relax_zrange interp_type t st2.
        Proof using Type. congruence. Qed.

        Local Hint Resolve interp_annotate_expr abstract_interp_ident_related : core.

        Lemma interp_eval_with_bound
              {opts : AbstractInterpretation.Options}
              {assume_cast_truncates : bool}
              {skip_annotations_under : forall t, ident t -> bool}
              {strip_preexisting_annotations : bool}
              {t} (e_st e1 e2 : expr t)
              (Hwf : expr.wf3 nil e_st e1 e2)
              (Hwf' : expr.wf nil e2 e2)
              (Ht : type.is_not_higher_order t = true)
              (st : type.for_each_lhs_of_arrow abstract_domain t)
          : (forall arg1 arg2
                    (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                    (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                type.app_curried (expr.interp (@ident.interp) (eval_with_bound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e1 st)) arg1
                = type.app_curried (expr.interp (@ident.interp) e2) arg2)
            /\ (forall arg1
                       (Harg11 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg1)
                       (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                   abstraction_relation'
                     (extract assume_cast_truncates e_st st)
                     (type.app_curried (expr.interp (@ident.interp) (eval_with_bound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e1 st)) arg1)).
        Proof using Hrelax.
          cbv [eval_with_bound]; split;
            [ intros arg1 arg2 Harg12 Harg1
            | intros arg1 Harg11 Harg1 ].
          all: eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1; [ | apply ZRange.type.option.is_bounded_by_impl_related_hetero ].
          all: eapply ident.interp_eval_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom, interp_annotate_expr with typeclass_instances.
          all: intros; (eapply extract_list_state_related + eapply extract_option_state_related + eapply strip_annotation_related); eassumption.
        Qed.

        Lemma interp_eta_expand_with_bound
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
              (Ht : type.is_not_higher_order t = true)
              (b_in : type.for_each_lhs_of_arrow abstract_domain t)
          : forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
            type.app_curried (interp (partial.eta_expand_with_bound relax_zrange e1 b_in)) arg1 = type.app_curried (interp e2) arg2.
        Proof using Hrelax.
          cbv [partial.eta_expand_with_bound]; intros arg1 arg2 Harg12 Harg1.
          eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1.
          { apply ident.interp_eta_expand_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom, interp_annotate_expr with typeclass_instances.
            all: intros; (eapply extract_list_state_related + eapply extract_option_state_related); eassumption. }
          { apply ZRange.type.option.is_bounded_by_impl_related_hetero. }
        Qed.

        Lemma Interp_EvalWithBound
              {opts : AbstractInterpretation.Options}
              {assume_cast_truncates : bool}
              {skip_annotations_under : forall t, ident t -> bool}
              {strip_preexisting_annotations : bool}
              {t} (e : Expr t)
              (Hwf : expr.Wf e)
              (Ht : type.is_not_higher_order t = true)
              (st : type.for_each_lhs_of_arrow abstract_domain t)
              (Hst : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) st)
          : (forall arg1 arg2
                    (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                    (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                type.app_curried (expr.Interp (@ident.interp) (EvalWithBound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e st)) arg1
                = type.app_curried (expr.Interp (@ident.interp) e) arg2)
            /\ (forall arg1
                       (Harg11 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg1)
                       (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                   abstraction_relation'
                     (Extract assume_cast_truncates e st)
                     (type.app_curried (expr.Interp (@ident.interp) (EvalWithBound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e st)) arg1)).
        Proof using Hrelax. cbv [Extract EvalWithBound]; apply interp_eval_with_bound; try apply expr.Wf3_of_Wf; auto. Qed.

        Lemma Interp_EtaExpandWithBound
              {t} (E : Expr t)
              (Hwf : Wf E)
              (Ht : type.is_not_higher_order t = true)
              (b_in : type.for_each_lhs_of_arrow abstract_domain t)
          : forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
            type.app_curried (Interp (partial.EtaExpandWithBound relax_zrange E b_in)) arg1 = type.app_curried (Interp E) arg2.
        Proof using Hrelax. cbv [partial.EtaExpandWithBound]; apply interp_eta_expand_with_bound; eauto with typeclass_instances. Qed.
      End with_relax.

      Lemma strip_ranges_is_looser t b v
        : @ZRange.type.option.is_bounded_by t b v = true
          -> ZRange.type.option.is_bounded_by (ZRange.type.option.strip_ranges b) v = true.
      Proof using Type.
        induction t as [t|s IHs d IHd]; cbn in *; [ | tauto ].
        induction t; cbn in *; break_innermost_match; cbn in *; rewrite ?Bool.andb_true_iff; try solve [ intuition ].
        { repeat match goal with ls : list _ |- _ => revert ls end.
          intros ls1 ls2; revert ls2.
          induction ls1, ls2; cbn in *; rewrite ?Bool.andb_true_iff; solve [ intuition ]. }
        { destruct_head' option; cbn; eauto; congruence. }
      Qed.

      Lemma andb_strip_ranges_Proper t (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t) arg1
        : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true ->
          type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by)
                                               (type.map_for_each_lhs_of_arrow (@ZRange.type.option.strip_ranges) b_in) arg1 = true.
      Proof using Type.
        induction t as [t|s IHs d IHd]; cbn [type.andb_bool_for_each_lhs_of_arrow type.map_for_each_lhs_of_arrow type.for_each_lhs_of_arrow] in *;
          rewrite ?Bool.andb_true_iff; [ tauto | ].
        destruct_head'_prod; cbn [fst snd]; intros [? ?].
        erewrite IHd by eauto.
        split; [ | reflexivity ].
        apply strip_ranges_is_looser; assumption.
      Qed.

      Lemma strip_ranges_Proper t
        : Proper (abstract_domain_R ==> abstract_domain_R) (@ZRange.type.option.strip_ranges t).
      Proof using Type.
        induction t as [t|s IHs d IHd]; cbn in *.
        all: cbv [Proper respectful abstract_domain_R] in *; intros; subst; eauto.
      Qed.

      Lemma and_strip_ranges_Proper' t
        : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R) ==> type.and_for_each_lhs_of_arrow (@abstract_domain_R))
                 (type.map_for_each_lhs_of_arrow (@ZRange.type.option.strip_ranges) (t:=t)).
      Proof using Type.
        induction t as [t|s IHs d IHd]; cbn [type.and_for_each_lhs_of_arrow type.map_for_each_lhs_of_arrow abstract_domain_R type.for_each_lhs_of_arrow] in *;
          cbv [Proper respectful] in *; [ tauto | ].
        intros; destruct_head'_prod; cbn [fst snd] in *; destruct_head'_and.
        split; [ | solve [ auto ] ].
        apply strip_ranges_Proper; auto.
      Qed.

      Lemma interp_strip_annotations
            {opts : AbstractInterpretation.Options}
            {assume_cast_truncates : bool}
            {t} (e_st e1 e2 : expr t)
            (Hwf : expr.wf3 nil e_st e1 e2)
            (Hwf' : expr.wf nil e2 e2)
            (Ht : type.is_not_higher_order t = true)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
              type.app_curried (expr.interp (@ident.interp) (strip_annotations assume_cast_truncates e1 st)) arg1
              = type.app_curried (expr.interp (@ident.interp) e2) arg2)
          /\ (forall arg1
                     (Harg11 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg1)
                     (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                 abstraction_relation'
                   (extract assume_cast_truncates e_st st)
                   (type.app_curried (expr.interp (@ident.interp) (strip_annotations assume_cast_truncates e1 st)) arg1)).
      Proof using Type.
        cbv [strip_annotations]; split;
          [ intros arg1 arg2 Harg12 Harg1
          | intros arg1 Harg11 Harg1 ].
        all: eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1; [ | apply ZRange.type.option.is_bounded_by_impl_related_hetero ].
        all: eapply ident.interp_eval_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom, interp_annotate_expr, default_relax_zrange_good, abstract_interp_ident_related with typeclass_instances.
        all: intros; (eapply extract_list_state_related + eapply extract_option_state_related + eapply strip_annotation_related); eassumption.
      Qed.

      Lemma Interp_StripAnnotations
            {opts : AbstractInterpretation.Options}
            {assume_cast_truncates : bool}
            {t} (E : Expr t)
            (Hwf : Wf E)
            (Ht : type.is_not_higher_order t = true)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (expr.Interp (@ident.interp) (StripAnnotations assume_cast_truncates E b_in)) arg1
          = type.app_curried (expr.Interp (@ident.interp) E) arg2.
      Proof using Type.
        apply (@interp_strip_annotations _ assume_cast_truncates t (E _) (E _) (E _)); try apply expr.Wf3_of_Wf; auto.
      Qed.

      Lemma Interp_StripAnnotations_bounded
            {opts : AbstractInterpretation.Options}
            {assume_cast_truncates : bool}
            {t} (E : Expr t)
            (Hwf : expr.Wf E)
            (Ht : type.is_not_higher_order t = true)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1
                 (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          ZRange.type.base.option.is_bounded_by
            (partial.Extract assume_cast_truncates E b_in)
            (type.app_curried (expr.Interp (@ident.interp) (StripAnnotations assume_cast_truncates E b_in)) arg1)
          = true.
      Proof using Type.
        apply (@interp_strip_annotations _ assume_cast_truncates t (E _) (E _) (E _)); try apply expr.Wf3_of_Wf; auto.
      Qed.

      Lemma Interp_EtaExpandWithListInfoFromBound
            {t} (E : Expr t)
            (Hwf : Wf E)
            (Ht : type.is_not_higher_order t = true)
            (b_in : type.for_each_lhs_of_arrow abstract_domain t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (Interp (partial.EtaExpandWithListInfoFromBound E b_in)) arg1 = type.app_curried (Interp E) arg2.
      Proof using Type.
        cbv [partial.EtaExpandWithListInfoFromBound].
        intros; apply Interp_EtaExpandWithBound; trivial.
        { exact default_relax_zrange_good. }
        { apply andb_strip_ranges_Proper; assumption. }
      Qed.
    End specialized.
  End partial.
  Import API.

  Lemma Interp_PartialEvaluateWithBounds
        {opts : AbstractInterpretation.Options}
        relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations
        (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                 -> relax_zrange r = Some r'
                                 -> is_tighter_than_bool z r' = true)
        {t} (E : Expr t)
        (Hwf : Wf E)
        (Ht : type.is_not_higher_order t = true)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (expr.Interp (@ident.interp) (PartialEvaluateWithBounds relax_zrange skip_annotations_under strip_preexisting_annotations assume_cast_truncates E b_in)) arg1
      = type.app_curried (expr.Interp (@ident.interp) E) arg2.
  Proof.
    cbv [PartialEvaluateWithBounds].
    intros arg1 arg2 Harg12 Harg1.
    assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
      by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
    assert (arg2_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg2)
      by (hnf; etransitivity; [ symmetry; eassumption | eassumption ]).
    rewrite <- (GeneralizeVar.Interp_gen1_GeneralizeVar E) by auto with wf.
    eapply Interp_EvalWithBound; eauto with wf typeclass_instances.
  Qed.

  Lemma Interp_PartialEvaluateWithBounds_bounded
        {opts : AbstractInterpretation.Options}
        relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations
        (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                 -> relax_zrange r = Some r'
                                 -> is_tighter_than_bool z r' = true)
        {t} (E : Expr t)
        (Hwf : Wf E)
        (Ht : type.is_not_higher_order t = true)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1
             (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1)
             (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      ZRange.type.base.option.is_bounded_by
        (partial.Extract assume_cast_truncates E b_in)
        (type.app_curried (expr.Interp (@ident.interp) (PartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in)) arg1)
      = true.
  Proof.
    cbv [PartialEvaluateWithBounds].
    intros arg1 Harg11 Harg1.
    rewrite <- Extract_GeneralizeVar by auto with wf typeclass_instances.
    eapply @Interp_EvalWithBound; eauto with wf typeclass_instances.
  Qed.

  Lemma Interp_PartialEvaluateWithListInfoFromBounds
        {opts : AbstractInterpretation.Options}
        {t} (E : Expr t)
        (Hwf : Wf E)
        (Ht : type.is_not_higher_order t = true)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds E b_in)) arg1 = type.app_curried (Interp E) arg2.
  Proof.
    cbv [PartialEvaluateWithListInfoFromBounds]; intros arg1 arg2 Harg12 Harg1.
    assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
        by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
    assert (arg2_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg2)
      by (hnf; etransitivity; [ symmetry; eassumption | eassumption ]).
    rewrite <- (GeneralizeVar.Interp_gen1_GeneralizeVar E) by auto.
    apply Interp_EtaExpandWithListInfoFromBound; eauto with wf.
  Qed.

  Theorem CheckedPartialEvaluateWithBounds_Correct
          {opts : AbstractInterpretation.Options}
          (relax_zrange : zrange -> option zrange)
          (assume_cast_truncates : bool)
          (skip_annotations_under : forall t, ident t -> bool)
          (strip_preexisting_annotations : bool)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {t} (E : Expr t)
          (Hwf : Wf E)
          (Ht : type.is_not_higher_order t = true)
          (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
          (b_out : ZRange.type.base.option.interp (type.final_codomain t))
          rv (Hrv : CheckedPartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in b_out = inl rv)
    : (forall arg1 arg2
              (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
              (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          ZRange.type.base.option.is_bounded_by b_out (type.app_curried (Interp rv) arg1) = true
          /\ type.app_curried (Interp rv) arg1 = type.app_curried (Interp E) arg2)
      /\ Wf rv.
  Proof.
    cbv [CheckedPartialEvaluateWithBounds Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    all: split;
      [ intros arg1 arg2 Harg12 Harg1;
        assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
          by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]);
        split;
          repeat first [ rewrite !@GeneralizeVar.Interp_gen1_FromFlat_ToFlat by eauto with wf typeclass_instances
                       | rewrite <- Extract_FromFlat_ToFlat by auto with typeclass_instances; apply Interp_PartialEvaluateWithBounds_bounded; auto
                       | rewrite Extract_FromFlat_ToFlat by auto with wf typeclass_instances
                       | progress intros
                       | eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; [ eassumption | ]
                       | solve [ eauto with wf typeclass_instances ]
                       | erewrite !Interp_PartialEvaluateWithBounds
                       | apply type.app_curried_Proper
                       | apply expr.Wf_Interp_Proper_gen
                       | progress intros ]
        | eauto with wf typeclass_instances ].
  Qed.
End Compilers.
