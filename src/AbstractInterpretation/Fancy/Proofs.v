Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Relations.Relations.
Require Import Crypto.Util.Bool.Reflect.
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
Require Import Crypto.AbstractInterpretation.Fancy.AbstractInterpretation.
Require Import Crypto.AbstractInterpretation.Fancy.Wf.
Require Import Crypto.AbstractInterpretation.ZRangeProofs.

Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.
  Import AbstractInterpretation.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import Language.API.Compilers.
  Import UnderLetsProofs.Compilers.
  Import AbstractInterpretation.Fancy.Wf.Compilers.
  Import AbstractInterpretation.ZRangeProofs.Compilers.
  Import AbstractInterpretation.Fancy.Wf.Compilers.partial.
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
              (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop).
      Local Notation abstract_domain := (@abstract_domain base_type abstract_domain').
      Local Notation abstract_domain_R := (@abstract_domain_R base_type abstract_domain' abstract_domain'_R).
      (* we only care about inputs that are extensional, so we restrict this here *)
      (* skip_base:=true because abstract_domain'_R refl and eqv refl follows from abstraction_relation' *)
      Definition abstraction_relation {t} : abstract_domain t -> type.interp base_interp t -> Prop
        := type.related_hetero_and_Proper (skip_base:=true) (@abstract_domain'_R) (fun _ => eq) (@abstraction_relation').
      (*Definition abstraction_relation {t} : abstract_domain t -> type.interp base_interp t -> Prop
        := type.related_hetero (@abstraction_relation').*)
      Context (ident_interp_Proper : forall t (idc : ident t), abstraction_relation (abstract_interp_ident t idc) (ident_interp t idc))
              (ident_interp_Proper' : forall t, Proper (eq ==> type.eqv) (ident_interp t))
              (abstraction_relation'_Proper : forall t, Proper (abstract_domain'_R t ==> eq ==> Basics.impl) (abstraction_relation' t))
              {abstract_domain'_R_transitive : forall t, Transitive (@abstract_domain'_R t)}
              {abstract_domain'_R_symmetric : forall t, Symmetric (@abstract_domain'_R t)}
              {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
              (base_type_beq : base_type -> base_type -> bool)
              {reflect_base_type_beq : reflect_rel eq base_type_beq}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
              {try_make_transport_base_type_cps_correct : type.try_make_transport_cps_correctT base_type}
              (abstract_domain'_R_of_related : forall t st v, @abstraction_relation' t st v -> @abstract_domain'_R t st st).
      Local Notation bottom := (@bottom base_type abstract_domain' (@bottom')).
      Local Notation bottom_for_each_lhs_of_arrow := (@bottom_for_each_lhs_of_arrow base_type abstract_domain' (@bottom')).
      Local Notation var := (type.interp base_interp).
      Local Notation expr := (@expr.expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident).
      Local Notation value' := (@value' base_type ident var abstract_domain').
      Local Notation value := (@value base_type ident var abstract_domain').
      Local Notation state_of_value := (@state_of_value base_type ident var abstract_domain').
      Local Notation project_value' := (@project_value' base_type ident var abstract_domain').
      Local Notation extract_gen := (@extract_gen base_type ident abstract_domain' abstract_interp_ident).
      Context {default_expr : @DefaultValue.type.base.DefaultT _ (@expr abstract_domain)}. (* needed for impossible cases *)
      Context (annotate : forall (is_let_bound : bool) t, abstract_domain' t -> @expr var t -> @UnderLets var (@expr var t))
              (interp_ident' : bool -> forall t, ident t -> @UnderLets var (value' t))
              (interp_annotate
               : forall is_let_bound t st e
                   (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e)),
                  expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate is_let_bound t st e))
                  = expr.interp (@ident_interp) e)
              (abstract_interp_ident_Proper : forall t, Proper (eq ==> abstract_domain_R) (abstract_interp_ident t)).
      Local Notation eta_expand_with_bound' := (@eta_expand_with_bound' base_type ident _ abstract_domain' annotate bottom').
      Local Notation eval_with_bound' := (@partial.eval_with_bound' base_type ident _ try_make_transport_base_type_cps abstract_domain' annotate bottom' skip_annotations_under default_expr abstract_interp_ident interp_ident').
      Local Notation reify := (@reify base_type ident _ abstract_domain' annotate bottom').
      Local Notation reflect := (@reflect base_type ident _ abstract_domain' annotate bottom').
      Local Notation interp := (@interp base_type ident var try_make_transport_base_type_cps abstract_domain' annotate bottom' skip_annotations_under default_expr abstract_interp_ident interp_ident').
      Local Notation invert_default := (@invert_default base_type ident try_make_transport_base_type_cps abstract_domain' default_expr).
      Local Notation invert_default' := (@invert_default' base_type ident try_make_transport_base_type_cps abstract_domain' default_expr).
      Local Notation interp_ident := (@interp_ident base_type ident var abstract_domain' abstract_interp_ident interp_ident').

      Lemma abstract_domain_R_refl_of_abstraction_relation {t st v}
        : @abstraction_relation t st v -> Proper abstract_domain_R st.
      Proof using abstract_domain'_R_of_related. apply type.related_hetero_and_Proper_proj1, abstract_domain'_R_of_related. Qed.
      Local Hint Immediate abstract_domain_R_refl_of_abstraction_relation : core typeclass_instances.
      Lemma eqv_refl_of_abstraction_relation {t st v}
        : @abstraction_relation t st v -> v == v.
      Proof using Type. apply type.related_hetero_and_Proper_proj2; repeat intro; hnf; auto. Qed.
      Local Hint Immediate eqv_refl_of_abstraction_relation : core typeclass_instances.

      Lemma eqv_refl_of_abstraction_relation_for_each_lhs_of_arrow {t st v}
        : type.and_for_each_lhs_of_arrow (t:=t) (@abstraction_relation) st v -> type.and_for_each_lhs_of_arrow (t:=t) (@type.eqv) v v.
      Proof using Type.
        apply type.and_for_each_lhs_of_arrow_Proper_impl_hetero2, @eqv_refl_of_abstraction_relation.
      Qed.
      Local Hint Immediate eqv_refl_of_abstraction_relation_for_each_lhs_of_arrow : core typeclass_instances.

      Lemma abstract_domain_R_refl_of_abstraction_relation_for_each_lhs_of_arrow {t st v}
        : type.and_for_each_lhs_of_arrow (t:=t) (@abstraction_relation) st v -> type.and_for_each_lhs_of_arrow (t:=t) (@abstract_domain_R) st st.
      Proof using abstract_domain'_R_of_related.
        apply type.and_for_each_lhs_of_arrow_Proper_impl_hetero1, @abstract_domain_R_refl_of_abstraction_relation.
      Qed.
      Local Hint Immediate abstract_domain_R_refl_of_abstraction_relation_for_each_lhs_of_arrow : core typeclass_instances.

      Lemma abstraction_relation_iff_app_curried {t st v}
        : @abstraction_relation t st v
          <-> (Proper (@abstract_domain_R t) st
               /\ v == v
               /\ forall x y,
                  type.and_for_each_lhs_of_arrow (@abstraction_relation) x y
                  -> abstraction_relation' _ (type.app_curried st x) (type.app_curried v y)).
      Proof using abstract_domain'_R_of_related.
        apply type.related_hetero_and_Proper_iff_app_curried; eauto; repeat intro; hnf; eauto.
      Qed.

      Local Notation bottom_Proper := (@bottom_Proper base_type abstract_domain' bottom' abstract_domain'_R bottom'_Proper).
      Local Notation bottom_for_each_lhs_of_arrow_Proper := (@bottom_for_each_lhs_of_arrow_Proper base_type abstract_domain' bottom' abstract_domain'_R bottom'_Proper).

      Local Hint Resolve (@bottom_Proper) (@bottom_for_each_lhs_of_arrow_Proper) : core typeclass_instances.

      Lemma bottom_related t v : v == v -> @abstraction_relation t bottom v.
      Proof using bottom'_Proper bottom'_related.
        induction t; cbv [abstraction_relation]; cbn [type.related_hetero_and_Proper]; cbv [respectful_hetero]; repeat split; eauto.
        repeat intro; cbn.
        repeat first [ do_with_exactly_one_hyp ltac:(fun H => apply H)
                     | eassumption
                     | eapply eqv_refl_of_abstraction_relation ].
      Qed.

      Local Hint Immediate bottom_related : core typeclass_instances.

      Lemma related_bottom_for_each_lhs_of_arrow t v : type.and_for_each_lhs_of_arrow (@type.eqv) v v -> type.and_for_each_lhs_of_arrow (@abstraction_relation) (@bottom_for_each_lhs_of_arrow t) v.
      Proof using bottom'_Proper bottom'_related. induction t; cbn; split; split_and; eauto using bottom_related. Qed.
      Local Hint Immediate related_bottom_for_each_lhs_of_arrow : core.

      Lemma related_bottom_for_each_lhs_of_arrow_hetero_eqv_l t v v' : type.and_for_each_lhs_of_arrow (@type.eqv) v v' -> type.and_for_each_lhs_of_arrow (@abstraction_relation) (@bottom_for_each_lhs_of_arrow t) v.
      Proof using bottom'_Proper bottom'_related. intro; apply related_bottom_for_each_lhs_of_arrow; etransitivity; (idtac + symmetry); eassumption. Qed.
      Lemma related_bottom_for_each_lhs_of_arrow_hetero_eqv_r t v v' : type.and_for_each_lhs_of_arrow (@type.eqv) v' v -> type.and_for_each_lhs_of_arrow (@abstraction_relation) (@bottom_for_each_lhs_of_arrow t) v.
      Proof using bottom'_Proper bottom'_related. intro; apply related_bottom_for_each_lhs_of_arrow; etransitivity; (idtac + symmetry); eassumption. Qed.
      Local Hint Immediate related_bottom_for_each_lhs_of_arrow_hetero_eqv_l related_bottom_for_each_lhs_of_arrow_hetero_eqv_r : core.

      Fixpoint related_bounded_value' {t} : abstract_domain t -> value' t -> type.interp base_interp t -> Prop
        := match t return abstract_domain t -> value' t -> type.interp base_interp t -> Prop with
           | type.base t
             => fun st e v
                => expr.interp ident_interp e = v
                   /\ abstraction_relation' t st v
           | type.arrow s d
             => fun st e v
               => Proper type.eqv v
                  /\ Proper abstract_domain_R st
                  /\ forall st_s e_s v_s,
                   @related_bounded_value' s st_s e_s v_s
                   -> @related_bounded_value' d (st st_s) (UnderLets.interp ident_interp (e (st_s, e_s))) (v v_s)
           end.
      Definition related_bounded_value {t} : value t -> type.interp base_interp t -> Prop
        := fun st_e v => related_bounded_value' (state_of_value st_e) (UnderLets.interp ident_interp (project_value' st_e)) v.

      Definition related_of_related_bounded_value' {t} st e v
        : @related_bounded_value' t st e v -> v == v.
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

      Definition abstract_domain_R_of_related_bounded_value' {t} st e v
        : @related_bounded_value' t st e v -> abstract_domain_R st st.
      Proof using abstract_domain'_R_of_related.
        destruct t; [ cbn; intros [? ?]; subst; eapply abstract_domain'_R_of_related; eassumption | intros [? ?]; destruct_head'_and; assumption ].
      Qed.

      Lemma abstraction_relation_Proper_iff {t} : Proper (abstract_domain_R ==> type.eqv ==> iff) (@abstraction_relation t).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper.
        apply @type.related_hetero_and_Proper_Proper_iff; try exact _.
        all: try now repeat intro; split; subst; eapply abstraction_relation'_Proper; (idtac + symmetry); auto; eassumption.
        all: try now apply abstract_domain'_R_of_related.
      Qed.

      Lemma abstraction_relation_Proper_iff_abstract_domain_R {t} : Proper (abstract_domain_R ==> eq ==> iff) (@abstraction_relation t).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper.
        repeat intro; subst.
        match goal with |- ?A <-> ?B => cut (A \/ B -> (A <-> B)); [ tauto | ] end.
        intro H'.
        apply abstraction_relation_Proper_iff; try assumption.
        destruct_head'_or; eapply eqv_refl_of_abstraction_relation; eassumption.
      Qed.

      Lemma abstraction_relation_Proper_iff_eqv {t} : Proper (eq ==> type.eqv ==> iff) (@abstraction_relation t).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper.
        repeat intro; subst.
        match goal with |- ?A <-> ?B => cut (A \/ B -> (A <-> B)); [ tauto | ] end.
        intro H'.
        apply abstraction_relation_Proper_iff; try assumption.
        destruct_head'_or; eapply abstract_domain_R_refl_of_abstraction_relation; eassumption.
      Qed.

      Local Instance bottom_eqv_Proper_refl {t} : Proper type.eqv (@bottom t).
      Proof using Type. cbv [Proper]; induction t; cbn in *; cbv [respectful] in *; eauto. Qed.

      Lemma bottom_eqv_refl {t} : @bottom t == @bottom t.
      Proof using Type. apply bottom_eqv_Proper_refl. Qed.
      Local Hint Resolve bottom_eqv_refl : core.

      Lemma related_refl_of_related_bounded_value' {t} st e v
        : @related_bounded_value' t st e v -> abstract_domain_R st st.
      Proof using abstract_domain'_R_of_related.
        destruct t; cbn; break_innermost_match; intros; destruct_head'_and; try assumption.
        eapply abstract_domain'_R_of_related; eassumption.
      Qed.

      Lemma related_bounded_value'_Proper {t} st1 st2 (Hst : abstract_domain_R st1 st2)
            a a1 a2
            (Ha' : type.eqv a1 a2)
        : @related_bounded_value' t st1 a a1 -> @related_bounded_value' t st2 a a2.
      Proof using abstraction_relation'_Proper abstract_domain'_R_transitive abstract_domain'_R_symmetric abstract_domain'_R_of_related.
        induction t as [t|s IHs d IHd]; cbn [related_bounded_value' type.related] in *; cbv [respectful abstract_domain_R] in *.
        all: subst.
        { intros; destruct_head'_and; subst; repeat apply conj; try reflexivity.
          eapply abstraction_relation'_Proper; (eassumption + reflexivity). }
        { intros [? Hrel].
          split; [ | split ];
            [ repeat intro; etransitivity; (idtac + symmetry); (eapply Ha' + eapply Hst); (eassumption + (etransitivity; (idtac + symmetry); eassumption)) ..
            | ].
          { intros ?? v_s Hx; cbn [type.related] in *; cbv [respectful] in *.
            eapply IHd; [ cbn in Hst |- *; eapply Hst | apply Ha' | eapply Hrel, Hx ].
            all: try now eapply related_refl_of_related_bounded_value'; eassumption.
            all: try now eapply related_of_related_bounded_value'; eassumption. } }
      Qed.

      Lemma related_bounded_value'_Proper1 {t}
        : Proper (abstract_domain_R ==> eq ==> eq ==> Basics.impl) (@related_bounded_value' t).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper.
        repeat intro; subst; eapply related_bounded_value'_Proper; try eassumption.
        eapply related_of_related_bounded_value'; eassumption.
      Qed.

      Lemma related_bounded_value'_Proper3 {t}
        : Proper (eq ==> eq ==> type.eqv ==> Basics.impl) (@related_bounded_value' t).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper.
        repeat intro; subst; eapply related_bounded_value'_Proper; try eassumption.
        eapply abstract_domain_R_of_related_bounded_value'; eassumption.
      Qed.

      Lemma related_bounded_value'_Proper_eq {t}
        : Proper (eq ==> eq ==> eq ==> Basics.impl) (@related_bounded_value' t).
      Proof using Type.
        repeat intro; subst; assumption.
      Qed.

      Lemma related_bounded_value'_Proper_interp_eq_base {t}
        : Proper (eq ==> (fun x y => expr.interp ident_interp x = expr.interp ident_interp y) ==> eq ==> Basics.impl) (@related_bounded_value' (type.base t)).
      Proof using Type.
        repeat intro; subst.
        cbv [related_bounded_value'] in *; destruct_head'_and; repeat apply conj; subst; (idtac + symmetry); assumption.
      Qed.

      Lemma state_of_value_reflect is_let_bound {t} e st
        : state_of_value (@reflect is_let_bound t e st) = st.
      Proof using Type. destruct t; reflexivity. Qed.

      Lemma related_bounded_value'_of_abstraction_relation_of_reflect
        {t} {annotate_with_state}
        (interp_reflect
           : forall st e v
                    (H_val : expr.interp ident_interp e == v)
                    (Hst1 : abstraction_relation st (expr.interp ident_interp e)),
            related_bounded_value
              (@reflect annotate_with_state t e st)
              v)
        st v
        (H : abstraction_relation st v)
        : @related_bounded_value' t st (UnderLets.interp ident_interp (project_value' (@reflect annotate_with_state t (expr.Var v) st))) v.
      Proof using Type.
        specialize (interp_reflect st (expr.Var v) v).
        cbv [related_bounded_value] in interp_reflect.
        rewrite state_of_value_reflect in interp_reflect.
        apply interp_reflect; try assumption.
        eapply eqv_refl_of_abstraction_relation; eassumption.
      Qed.

      Fixpoint interp_reify
        annotate_with_state is_let_bound {t} e v b_in
        (H : related_bounded_value e v)
        {struct t}
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
          type.app_curried (expr.interp ident_interp (UnderLets.interp ident_interp (@reify annotate_with_state is_let_bound t e b_in))) arg1
          = type.app_curried v arg2
      with interp_reflect
             annotate_with_state {t} st e v
             (*(Hst_Proper : Proper abstract_domain_R st)*) (* follows from abstraction relation *)
             (H_val : expr.interp ident_interp e == v)
             (Hst1 : abstraction_relation st (expr.interp ident_interp e))
             {struct t}
           : related_bounded_value
               (@reflect annotate_with_state t e st)
               v
      with abstraction_relation_of_related_bounded_value'
             {t} st e v
             {struct t}
        : @related_bounded_value' t st e v
          -> abstraction_relation st v.
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper bottom'_Proper bottom'_related interp_annotate.
        all: destruct t as [t|s d];
          [ clear interp_reify interp_reflect abstraction_relation_of_related_bounded_value'
          | pose proof (fun annotate_with_state is_let_bound => interp_reify annotate_with_state is_let_bound s) as interp_reify_s;
            pose proof (fun annotate_with_state is_let_bound => interp_reify annotate_with_state is_let_bound d) as interp_reify_d;
            pose proof (fun annotate_with_state => interp_reflect annotate_with_state s) as interp_reflect_s;
            pose proof (fun annotate_with_state => interp_reflect annotate_with_state d) as interp_reflect_d;
            pose proof (abstraction_relation_of_related_bounded_value' s) as abstraction_relation_of_related_bounded_value'_s;
            pose proof (abstraction_relation_of_related_bounded_value' d) as abstraction_relation_of_related_bounded_value'_d;
            pose proof (@related_bounded_value'_of_abstraction_relation_of_reflect s false (interp_reflect_s false)) as related_bounded_value'_of_abstraction_relation_s;
            pose proof (@related_bounded_value'_of_abstraction_relation_of_reflect d false (interp_reflect_d false)) as related_bounded_value'_of_abstraction_relation_d;
            try specialize (interp_reify_s annotate_with_state);
            try specialize (interp_reify_d annotate_with_state);
            try specialize (interp_reflect_s annotate_with_state);
            try specialize (interp_reflect_d annotate_with_state);
            clear interp_reify interp_reflect abstraction_relation_of_related_bounded_value' ].
        all: cbv [abstraction_relation] in *; cbn [type.related_hetero_and_Proper] in *; cbv [respectful_hetero] in *.
        all: cbn [reify reflect] in *; fold (@reify) (@reflect) in *.
        all: cbn [related_bounded_value' type.related type.app_curried] in *.
        all: cbn [UnderLets.interp expr.interp type.final_codomain type.andb_each_lhs_of_arrow type.is_base fst snd type.map_for_each_lhs_of_arrow type.for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow partial.bottom_for_each_lhs_of_arrow partial.bottom] in *.
        all: try destruct annotate_with_state; try destruct is_let_bound.
        all: change (type.related_hetero_and_Proper abstract_domain'_R (fun t : base_type => eq) abstraction_relation' (t:=?t)) with (@abstraction_relation t) in *.
        all: repeat first [ reflexivity
                          | assumption
                          | progress eta_expand
                          | progress cbn [UnderLets.interp expr.interp type.final_codomain fst snd] in *
                          | progress cbn [state_of_value project_value' fst snd Base_value' UnderLets.interp] in *
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
                            | [ |- type.related _ ?x ?x ]
                              => eapply related_refl_of_related_bounded_value'; eassumption
                            end
                          | match goal with
                            | [ H' : ?R ?i, H : forall a b, ?R a /\ @?A b -> @?B b |- _ ]
                              => specialize (fun b H'' => H i b (conj H' H''))
                            | [ H' : ?R ?i, H : forall a b, @?A a /\ ?R b -> @?B a |- _ ]
                              => specialize (fun a H'' => H a i (conj H'' H'))
                            end
                          | solve [ repeat intro; apply bottom_Proper
                                  | auto; cbv [Proper respectful Basics.impl] in *; eauto
                                  | eapply related_refl_of_related_bounded_value'; eassumption
                                  | eapply related_bottom_for_each_lhs_of_arrow, eqv_refl_of_abstraction_relation_for_each_lhs_of_arrow; eassumption
                                  | eapply abstract_domain_R_refl_of_abstraction_relation; eassumption ]
                          | progress (repeat apply conj; intros * )
                          | progress intros
                          | progress destruct_head'_or
                          | match goal with
                            | [ |- Proper ?R _ ] => (eapply PER_valid_l + eapply PER_valid_r); eassumption
                            | [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry; assumption
                            end
                          | match goal with
                            | [ H : related_bounded_value' ?st ?e ?v |- related_bounded_value' ?st ?e' ?v' ]
                              => is_evar e'; unify e e';
                                 eapply related_bounded_value'_Proper3; [ reflexivity .. | symmetry | exact H ]
                            | [ H' : abstraction_relation ?stv ?vv, H : forall annotate_with_state st e v, _ == v -> abstraction_relation st (expr.interp _ e) -> related_bounded_value (reflect annotate_with_state e st) v |- related_bounded_value' ?stv ?ee ?vv ]
                              => is_evar ee;
                                 specialize (H false stv (expr.Var vv) vv);
                                 cbv [related_bounded_value] in H;
                                 rewrite state_of_value_reflect in H; eapply H; clear H
                            end
                          | break_innermost_match_step
                          | progress fold (@reify) (@reflect) (@type.interp) (@type.related) (@type.related_hetero) (@related_bounded_value') (@abstraction_relation) in *
                          | match goal with
                            | [ H : forall a b c d e (f : bool), _ |- _ ]
                              => unique pose proof (fun a b c d e => H a b c d e true);
                                 unique pose proof (fun a b c d e => H a b c d e false);
                                 clear H
                            | [ |- type.related _ (expr.interp _ (UnderLets.interp _ (reify _ _ _ _))) _ ]
                              => rewrite type.related_iff_app_curried
                            | [ interp_reflect_d : context[_ -> related_bounded_value (reflect _ _ _) _] |- related_bounded_value' ?st (UnderLets.interp _ (project_value' (reflect _ ?e ?st))) ?v ]
                              => specialize (interp_reflect_d st e v);
                                 cbv [related_bounded_value] in interp_reflect_d;
                                 rewrite state_of_value_reflect in interp_reflect_d
                            | [ H : context[_ -> type.app_curried (expr.interp _ (UnderLets.interp _ (reify ?b _ _ _))) _ = _] |- type.app_curried (expr.interp _ (UnderLets.interp _ (reify ?b ?is_let_bound ?e ?b_in))) ?arg = _ ]
                              => apply H; clear H
                            | [ H : context[_ -> abstraction_relation' _ (type.app_curried _ _) (type.app_curried (expr.interp _ (UnderLets.interp _ (reify ?b _ _ _))) _)]
                                |- abstraction_relation' _ (type.app_curried _ ?x) (type.app_curried (expr.interp _ (UnderLets.interp _ (reify ?b ?is_let_bound ?e ?b_in))) ?arg) ]
                              => specialize (H is_let_bound e); cbn [state_of_value Base_value' fst] in H;
                                 eapply H; clear H
                            | [ |- related_bounded_value (_, Base _) _ ] => hnf; cbn [state_of_value project_value' Base_value' UnderLets.interp fst snd]
                            | [ H : forall st e v, _ -> related_bounded_value' _ (UnderLets.interp _ (?u _)) _ |- related_bounded_value' _ (UnderLets.interp _ (?u _)) _ ]
                              => apply H; clear H
                            | [ H : context[_ -> related_bounded_value' _ _ _ -> abstraction_relation _ _] |- abstraction_relation _ _ ]
                              => eapply H; clear H
                            end
                          | match goal with
                            | [ H : forall x : _ * _, _ |- _ ] => specialize (fun a b => H (a, b))
                            end
                          | rewrite state_of_value_reflect
                          | rewrite type.related_hetero_iff_app_curried
                          | do_with_exactly_one_hyp ltac:(fun H => apply H; clear H) ].
      Qed.

      Lemma related_bounded_value'_of_abstraction_relation_annotate_with_state
        {t} {annotate_with_state} st v
        (H : abstraction_relation st v)
        : @related_bounded_value' t st (UnderLets.interp ident_interp (project_value' (@reflect annotate_with_state t (expr.Var v) st))) v.
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper bottom'_Proper bottom'_related interp_annotate.
        apply related_bounded_value'_of_abstraction_relation_of_reflect; try assumption.
        apply @interp_reflect.
      Qed.

      Lemma related_bounded_value'_of_abstraction_relation
        {t} st v
        (H : abstraction_relation st v)
        : @related_bounded_value' t st (UnderLets.interp ident_interp (project_value' (@reflect false t (expr.Var v) st))) v.
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper bottom'_Proper bottom'_related interp_annotate.
        apply related_bounded_value'_of_abstraction_relation_annotate_with_state; assumption.
      Qed.

      Lemma abstraction_relation_of_related_bounded_value'_app_curried
        {t} st e v b_in arg
        (H : @related_bounded_value' t st e v)
        (Harg : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg)
        : abstraction_relation' _ (type.app_curried st b_in) (type.app_curried v arg).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper bottom'_Proper bottom'_related interp_annotate.
        pose proof (@abstraction_relation_of_related_bounded_value' t st e v H) as H'.
        rewrite abstraction_relation_iff_app_curried in H'.
        apply H'; assumption.
      Qed.

      Lemma related_bounded_value_annotate_base {t}
            v_st st v
        : @related_bounded_value' (type.base t) v_st st v
          -> @related_bounded_value' (type.base t) v_st (UnderLets.interp ident_interp (annotate true t v_st st)) v.
      Proof using interp_annotate abstraction_relation'_Proper.
        clear -interp_annotate abstraction_relation'_Proper.
        cbv [Proper respectful Basics.impl] in *.
        cbn; break_innermost_match; cbn; intros.
        destruct_head'_and; subst; repeat apply conj; auto.
        rewrite interp_annotate by eauto; reflexivity.
      Qed.

      Lemma interp_extract_gen_from_wf_gen G
        (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> abstract_domain_R v1 v2)
        {t} (e1 e2 : expr t) b_in1 b_in2
        (Hwf : expr.wf G e1 e2)
        (Hb_in : type.and_for_each_lhs_of_arrow (@abstract_domain_R) b_in1 b_in2)
        : abstract_domain'_R _ (extract_gen e1 b_in1) (extract_gen e2 b_in2).
      Proof using abstract_interp_ident_Proper.
        cbv [extract_gen].
        eapply type.related_iff_app_curried; try assumption.
        unshelve eapply expr.wf_interp_Proper_gen1; try eassumption.

      Qed.

      Lemma interp_extract_gen_from_wf
        {t} (e1 e2 : expr t) b_in1 b_in2
        (Hwf : expr.wf nil e1 e2)
        (Hb_in : type.and_for_each_lhs_of_arrow (@abstract_domain_R) b_in1 b_in2)
        : abstract_domain'_R _ (extract_gen e1 b_in1) (extract_gen e2 b_in2).
      Proof using abstract_interp_ident_Proper.
        eapply interp_extract_gen_from_wf_gen; try eassumption; wf_t.
      Qed.

      Context (interp_ident_Proper
               : forall annotate_with_state t idc,
                  related_bounded_value (interp_ident annotate_with_state idc) (ident_interp t idc)).

      Lemma interp_interp
        annotate_with_state G G' G'' G''' {t} (e e_st e_v : expr t)
        (HG : forall t v1 v2 v3, List.In (existT _ t (v1, v2, v3)) G
                                 -> related_bounded_value v2 v3
                                    /\ abstract_domain_R v1 (state_of_value v2))
        (HG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> abstract_domain_R (state_of_value v1) v2)
        (HG'' : forall t v1 v2, List.In (existT _ t (v1, v2)) G'' -> v1 == v2)
        (HG''' : forall t v1 v2, List.In (existT _ t (v1, v2)) G''' -> abstract_domain_R v1 v2)
        (Hwf : expr.wf3 G e_st e e_v)
        (Hwf' : expr.wf G' e e_st)
        (Hwf'' : expr.wf G'' e_v e_v)
        (Hwf''' : expr.wf G''' e_st e_st)
        : related_bounded_value
            (interp annotate_with_state e e_st)
            (expr.interp (@ident_interp) e_v)
          /\ abstract_domain_R (expr.interp (@abstract_interp_ident) e_st) (state_of_value (interp annotate_with_state e e_st)).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstraction_relation'_Proper ident_interp_Proper' interp_annotate interp_ident_Proper try_make_transport_base_type_cps_correct.
        clear -abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstraction_relation'_Proper ident_interp_Proper' interp_annotate interp_ident_Proper try_make_transport_base_type_cps_correct HG HG' HG'' HG''' Hwf Hwf' Hwf'' Hwf'''.
        cbv [related_bounded_value] in *;
          revert dependent annotate_with_state; revert dependent G'; revert dependent G''; revert dependent G'''; induction Hwf; intros.
        all: destruct annotate_with_state eqn:?.
        all: cbn [interp expr.interp UnderLets.interp List.In related_bounded_value' reify reflect abstract_domain_R type.related] in *; cbv [Let_In Proper respectful] in *; cbn [state_of_value Base_value' fst snd] in *.
        all: repeat apply conj; intros.
        all: repeat first [ progress intros
                          | progress subst
                          | progress inversion_sigma
                          | progress inversion_pair
                          | progress destruct_head'_sig
                          | progress destruct_head'_and
                          | progress eta_expand
                          | progress cbv [interp_ident] in *
                          | progress cbn [eq_rect UnderLets.interp project_value' state_of_value fst snd Base_value' List.In apply_value] in *
                          | progress eliminate_hprop_eq
                          | apply related_bounded_value_annotate_base
                          | eapply abstract_domain_R_of_related_bounded_value'; eassumption
                          | eapply related_of_related_bounded_value'; eassumption
                          | solve [ cbv [abstract_domain_R] in *; (idtac + symmetry); eauto ]
                          | progress split_and
                          | erewrite invert_default_Some by first [ eassumption | reflexivity ]
                          | erewrite invert_default'_Some by first [ eassumption | reflexivity ]
                          | rewrite UnderLets.interp_splice
                          | progress destruct_head'_or
                          | eapply expr.wf_interp_Proper_gen1; [ | now eauto ]
                          | match goal with
                            | [ |- _ /\ _ ] => split
                            end
                          | progress expr.inversion_wf_constr
                          | do_with_hyp' ltac:(fun H => now apply H; first [ eapply related_of_related_bounded_value' | eapply related_refl_of_related_bounded_value' ]; eauto)
                          | match goal with
                            | [ H : context[related_bounded_value' _ (UnderLets.interp _ (project_value' (interp _ (?f2 _) (?f1 _)))) (expr.interp _ (?f3 _))]
                                |- related_bounded_value' _ (UnderLets.interp _ (project_value' (interp _ (?f2 _) (?f1 _)))) (expr.interp _ (?f3 _)) ]
                              => first [ eapply H
                                       | eapply related_bounded_value'_Proper1; [ | reflexivity .. | eapply H ] ];
                                 lazymatch goal with
                                 | [ |- expr.wf _ _ _ ] => solve [ eauto ]
                                 | _ => idtac
                                 end;
                                 clear H
                            | [ H : context[related_bounded_value' _ (UnderLets.interp _ (UnderLets.interp _ (project_value' (interp _ ?f2 ?f1)) _)) (expr.interp _ ?f3 _)]
                                |- related_bounded_value' _ (UnderLets.interp _ (UnderLets.interp _ (project_value' (interp _ ?f2 ?f1)) _)) (expr.interp _ ?f3 _) ]
                              => first [ eapply H
                                       | eapply related_bounded_value'_Proper1; [ | reflexivity .. | eapply H ] ];
                                 lazymatch goal with
                                 | [ |- expr.wf _ _ _ ] => solve [ eauto ]
                                 | _ => idtac
                                 end;
                                 clear H
                            | [ H : context[abstract_domain_R (expr.interp _ (?f1 _)) (state_of_value (interp _ (?f2 _) (?f1 _)))]
                                |- abstract_domain_R (expr.interp _ (?f1 _)) (state_of_value (interp _ (?f2 _) (?f1 _))) ]
                              => first [ eapply H; clear H
                                       | etransitivity; [ | eapply H; clear H ] ];
                                 lazymatch goal with
                                 | [ |- expr.wf _ _ _ ] => solve [ eauto ]
                                 | _ => idtac
                                 end
                            | [ H : context[type.related abstract_domain'_R (expr.interp _ ?f1 _) (state_of_value (interp _ ?f2 ?f1) _)]
                                |- abstract_domain_R (expr.interp _ ?f1 _) (state_of_value (interp _ ?f2 ?f1) _) ]
                              => eapply H; clear H;
                                 lazymatch goal with
                                 | [ |- expr.wf _ _ _ ] => solve [ eauto ]
                                 | _ => idtac
                                 end
                            | [ H : context[_ -> abstract_domain_R _ (state_of_value (interp _ ?f _))]
                                |- abstract_domain_R (state_of_value (interp _ ?f ?x)) (state_of_value (interp _ ?f ?x)) ]
                              => etransitivity; [ symmetry | ]; eapply H; clear H;
                                 lazymatch goal with
                                 | [ |- expr.wf _ _ _ ] => solve [ eauto ]
                                 | _ => idtac
                                 end
                            | [ |- abstract_domain_R (state_of_value _) (expr.interp _ _) ] => symmetry
                            end
                          | progress repeat first [ progress eta_expand | break_innermost_match_step ] ].
      Qed.

      Lemma interp_eval_with_bound'
            annotate_with_state {t} (e e_st e_v : expr t)
            (Hwf : expr.wf3 nil e_st e e_v)
            (Hwf' : expr.wf nil e e_st)
            (Hwf'' : expr.wf nil e_v e_v)
            (Hwf''' : expr.wf nil e_st e_st)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
              type.app_curried (expr.interp ident_interp (eval_with_bound' annotate_with_state e e_st st)) arg1
              = type.app_curried (expr.interp ident_interp e_v) arg2)
          /\ (forall arg1
                     (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1)
                     (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                 abstraction_relation'
                   _
                   (extract_gen e_st st)
                   (type.app_curried (expr.interp ident_interp (eval_with_bound' annotate_with_state e e_st st)) arg1)).
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstraction_relation'_Proper bottom'_Proper bottom'_related ident_interp_Proper' interp_annotate interp_ident_Proper try_make_transport_base_type_cps_correct.
        cbv [extract_gen eval_with_bound'].
        split; intros; rewrite UnderLets.interp_to_expr.
        { apply interp_reify; eauto; [].
          eapply interp_interp; eauto; wf_t. }
        { erewrite interp_reify; try eassumption.
          { eapply abstraction_relation_of_related_bounded_value'_app_curried; try assumption; [].
            eapply related_bounded_value'_Proper1; [ .. | eapply interp_interp ]; try reflexivity; try eassumption; eauto; wf_t; [].
            symmetry; eapply interp_interp; try eassumption; wf_t. }
          { now eapply interp_interp; eauto; wf_t. } }
        Unshelve.
        all: exact true.
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
      Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstraction_relation'_Proper bottom'_Proper bottom'_related ident_interp_Proper' interp_annotate.
        cbv [eta_expand_with_bound'].
        intros; rewrite UnderLets.interp_to_expr.
        eapply interp_reify; eauto.
        eapply interp_reflect; try (apply bottom_related; etransitivity; [ | symmetry ]).
        all: eapply @expr.wf_interp_Proper_gen; [ | exact Hwf ]; auto.
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
                (strip_annotation : forall t, ident t -> option (@value' base.type ident var abstract_domain' t))
                (abstraction_relation' : forall t, abstract_domain' t -> base.interp t -> Prop)
                (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop)
                (abstraction_relation'_Proper : forall t, Proper (abstract_domain'_R t ==> eq ==> Basics.impl) (abstraction_relation' t))
                (bottom'_related : forall t v, abstraction_relation' t (bottom' t) v)
                {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
                {abstract_domain'_R_transitive : forall t, Transitive (@abstract_domain'_R t)}
                {abstract_domain'_R_symmetric : forall t, Symmetric (@abstract_domain'_R t)}
                (abstract_domain'_R_of_related : forall t st v, @abstraction_relation' t st v -> @abstract_domain'_R t st st).
        Local Notation abstraction_relation := (@abstraction_relation base.type abstract_domain' base.interp abstraction_relation' abstract_domain'_R).
        Local Notation ident_interp := ident.interp (only parsing).
        Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' abstract_domain'_R).
        Local Notation related_bounded_value' := (@related_bounded_value' base.type ident abstract_domain' base.interp (@ident_interp) abstraction_relation' abstract_domain'_R).
        Local Notation related_bounded_value := (@related_bounded_value base.type ident abstract_domain' base.interp (@ident_interp) abstraction_relation' abstract_domain'_R).
        Context {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                (interp_annotate_expr
                 : forall t st idc,
                    annotate_expr t st = Some idc
                    -> forall v, abstraction_relation' _ st v
                           -> expr.interp (@ident_interp) idc v = v)
                (abstract_interp_ident_Proper'
                 : forall t idc, abstraction_relation (abstract_interp_ident t idc) (ident_interp idc))
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
                    -> related_bounded_value' (abstract_interp_ident t idc) v (ident_interp idc)).

        Local Notation update_annotation := (@ident.update_annotation _ abstract_domain' annotate_expr is_annotated_for).
        Local Notation annotate_with_expr := (@ident.annotate_with_expr _ abstract_domain' annotate_expr is_annotated_for).
        Local Notation annotate_base := (@ident.annotate_base _ abstract_domain' annotate_expr is_annotated_for).
        Local Notation annotate := (@ident.annotate _ abstract_domain' annotate_expr abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
        Local Notation reify := (@reify base.type ident _ abstract_domain' annotate bottom').
        Local Notation reflect := (@reflect base.type ident _ abstract_domain' annotate bottom').

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
                            | progress cbn [fst snd UnderLets.interp expr.interp ident.interp Nat.add] in *
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
                                => let H' := fresh in
                                   let H'' := fresh in
                                   pose proof H as H';
                                   pose proof H as H'';
                                   apply (abstract_interp_ident_Proper' _ ident.fst) in H';
                                   apply (abstract_interp_ident_Proper' _ ident.snd) in H'';
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

        Local Notation interp_ident' := (@ident.interp_ident' _ abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for strip_annotation).

        Lemma interp_ident_Proper_not_nth_default_nostrip annotate_with_state t idc
          : related_bounded_value (reflect annotate_with_state (expr.Ident idc) (abstract_interp_ident _ idc)) (@ident_interp t idc).
        Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr.
          eapply interp_reflect;
            try first [ apply ident.interp_Proper
                      | eapply abstract_interp_ident_Proper; reflexivity
                      | apply interp_annotate ];
            eauto.
        Qed.

        Lemma interp_ident_Proper_not_nth_default annotate_with_state t idc
          : related_bounded_value'
              (abstract_interp_ident t idc)
              (UnderLets.interp
                 (@ident.interp)
                 match strip_annotation _ idc with
                 | Some v => Base v
                 | None => project_value' _ (reflect annotate_with_state (expr.Ident idc) (abstract_interp_ident _ idc))
                 end)
              (ident_interp idc).
        Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr strip_annotation_related.
          pose proof (strip_annotation_related t idc) as H.
          cbv [related_bounded_value].
          break_innermost_match; eauto using eq_refl, interp_ident_Proper_not_nth_default_nostrip.
          eapply related_bounded_value'_Proper1; [ try exact eq_refl; try exact _ .. | eapply interp_reflect; eauto using interp_annotate ].
          all: eauto.
          all: rewrite ?state_of_value_reflect.
          all: try now apply abstract_interp_ident_Proper.
          all: try now apply Compilers.eqv_Reflexive_Proper.
        Qed.

        Lemma interp_ident_Proper_nth_default annotate_with_state T (idc:=@ident.List_nth_default T)
          : related_bounded_value' (abstract_interp_ident _ idc) (UnderLets.interp (@ident.interp) (interp_ident' annotate_with_state idc)) (ident_interp idc).
        Proof using abstract_domain'_R_of_related abstract_interp_ident_Proper abstract_interp_ident_Proper' bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr.
          subst idc; cbn [interp_ident reify reflect fst snd UnderLets.interp ident_interp related_bounded_value' abstract_domain value].
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
                       | apply (@abstract_interp_ident_Proper' _ (@ident.List_nth_default T))
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
                         end
                       | progress cbn [interp_ident' reify snd fst Base_value' reflect project_value']; eta_expand ].
        Qed.

        Lemma interp_ident_Proper annotate_with_state t idc
          : related_bounded_value' (abstract_interp_ident _ idc) (UnderLets.interp (@ident.interp) (@interp_ident' t annotate_with_state idc)) (ident_interp idc).
        Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr strip_annotation_related.
          pose idc as idc'.
          destruct idc;
            first [ refine (@interp_ident_Proper_not_nth_default _ _ idc')
                  | refine (@interp_ident_Proper_nth_default _ _) ].
        Qed.

        Local Notation eval_with_bound := (@partial.ident.eval_with_bound _ abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for strip_annotation).
        Local Notation eta_expand_with_bound := (@partial.ident.eta_expand_with_bound _ abstract_domain' annotate_expr bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
        Local Notation extract := (@ident.extract abstract_domain' abstract_interp_ident).

        Lemma interp_eval_with_bound
          annotate_with_state {t} (e e_st e_v : expr t)
          (Hwf : expr.wf3 nil e_st e e_v)
          (Hwf' : expr.wf nil e e_st)
          (Hwf'' : expr.wf nil e_v e_v)
          (Hwf''' : expr.wf nil e_st e_st)
          (st : type.for_each_lhs_of_arrow abstract_domain t)
          : (forall arg1 arg2
                    (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                    (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
                type.app_curried (expr.interp (@ident_interp) (eval_with_bound skip_annotations_under annotate_with_state e e_st st)) arg1
                = type.app_curried (expr.interp (@ident_interp) e_v) arg2)
            /\ (forall arg1
                       (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1)
                       (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                   abstraction_relation'
                     _
                     (extract e_st st)
                     (type.app_curried (expr.interp (@ident_interp) (eval_with_bound skip_annotations_under annotate_with_state e e_st st)) arg1)).
        Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr strip_annotation_related.
          cbv [extract eval_with_bound]; eapply @interp_eval_with_bound' with (abstract_domain'_R:=abstract_domain'_R); auto using interp_annotate, interp_ident_Proper, ident.interp_Proper; try exact _; intros; apply interp_ident_Proper.
        Qed.

        Lemma interp_eta_expand_with_bound
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
              (b_in : type.for_each_lhs_of_arrow abstract_domain t)
              (Hb_in : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) b_in)
          : forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
            type.app_curried (expr.interp (@ident_interp) (eta_expand_with_bound e1 b_in)) arg1 = type.app_curried (expr.interp (@ident_interp) e2) arg2.
        Proof using abstract_domain'_R_of_related abstract_domain'_R_symmetric abstract_domain'_R_transitive abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_Proper bottom'_related extract_list_state_length_good extract_list_state_related extract_option_state_related interp_annotate_expr.
          cbv [partial.ident.eta_expand_with_bound]; eapply interp_eta_expand_with_bound'; eauto using (@interp_ident), interp_annotate, ident.interp_Proper; try typeclasses eauto.
        Qed.
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

      Definition abstraction_relation' {t} : abstract_domain' t -> base.interp t -> Prop
        := fun st v => @ZRange.type.base.option.is_bounded_by t st v = true.

      Local Notation abstraction_relation := (@abstraction_relation _ abstract_domain' _ (@abstraction_relation') (fun t => abstract_domain'_R t)).

      Lemma bottom'_bottom {t} : forall v, abstraction_relation' (bottom' t) v.
      Proof using Type.
        cbv [abstraction_relation' bottom']; induction t; cbn; intros; break_innermost_match; cbn; try reflexivity.
        rewrite Bool.andb_true_iff; split; auto.
      Qed.

      Lemma abstract_interp_ident_related {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t} (idc : ident t)
        : abstraction_relation (abstract_interp_ident assume_cast_truncates t idc) (ident.interp idc).
      Proof using Type. apply ZRange.ident.option.interp_related_and_Proper. Qed.

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

      Local Notation related_bounded_value' := (@related_bounded_value' base.type ident abstract_domain' base.interp (@ident.interp) (@abstraction_relation') (fun t => abstract_domain'_R t)).
      Lemma always_strip_annotation_related {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t} (idc : ident t)
            v (Hv : always_strip_annotation assume_cast_truncates t idc = Some v)
        : related_bounded_value' (abstract_interp_ident assume_cast_truncates t idc) v (ident.interp idc).
      Proof using Type.
        pose proof (@abstract_interp_ident_related _ assume_cast_truncates _ ident.Z_cast).
        pose proof (fun x1 x2 y1 y2 H x01 x02 y01 y02 H' => proj2 (proj2 (proj2 (proj2 (@abstract_interp_ident_related _ assume_cast_truncates _ ident.Z_cast2)) (x1, x2) (y1, y2) H)) (x01, x02) (y01, y02) H').
        cbn [abstraction_relation] in *.
        cbv [always_strip_annotation] in *; break_innermost_match_hyps; inversion_option; subst.
        all: repeat first [ reflexivity
                          | progress cbn [related_bounded_value' UnderLets.interp fst snd type.related_hetero] in *
                          | progress cbv [respectful_hetero] in *
                          | progress intros
                          | progress destruct_head'_and
                          | progress subst
                          | progress inversion_prod
                          | progress inversion_option
                          | progress destruct_head_hnf' prod
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
                          | cbn [ident.interp]; progress cbv [ident.cast2]
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
        : related_bounded_value' (abstract_interp_ident assume_cast_truncates t idc) v (ident.interp idc).
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
        eapply expr.wf_interp_Proper_gen1; [ | apply GeneralizeVar.wf_from_flat_to_flat, Hwf ].
        wf_t.
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
              {t} (e_st e e_v : expr t)
              (Hwf : expr.wf3 nil e_st e e_v)
              (Hwf' : expr.wf nil e e_st)
              (Hwf'' : expr.wf nil e_v e_v)
              (Hwf''' : expr.wf nil e_st e_st)
              (st : type.for_each_lhs_of_arrow abstract_domain t)
          : (forall arg1 arg2
                    (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                    (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                type.app_curried (expr.interp (@ident.interp) (eval_with_bound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e e_st st)) arg1
                = type.app_curried (expr.interp (@ident.interp) e_v) arg2)
            /\ (forall arg1
                       (Harg11 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg1)
                       (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                   abstraction_relation'
                     (extract assume_cast_truncates e_st st)
                     (type.app_curried (expr.interp (@ident.interp) (eval_with_bound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e e_st st)) arg1)).
        Proof using Hrelax.
          cbv [eval_with_bound]; split;
            [ intros arg1 arg2 Harg12 Harg1
            | intros arg1 Harg11 Harg1 ].
          all: eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1; [ | apply @ZRange.type.option.is_bounded_by_impl_related_hetero_and_Proper with (skip_base:=true) ].
          all: eapply ident.interp_eval_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom, interp_annotate_expr with typeclass_instances.
          all: try (intros; (eapply extract_list_state_related + eapply extract_option_state_related + eapply strip_annotation_related); eassumption).
        Qed.

        Lemma interp_eta_expand_with_bound
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
              (b_in : type.for_each_lhs_of_arrow abstract_domain t)
          : forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
            type.app_curried (interp (partial.eta_expand_with_bound relax_zrange e1 b_in)) arg1 = type.app_curried (interp e2) arg2.
        Proof using Hrelax.
          cbv [partial.eta_expand_with_bound]; intros arg1 arg2 Harg12 Harg1.
          eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1.
          { apply ident.interp_eta_expand_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom, interp_annotate_expr with typeclass_instances.
            all: try (intros; (eapply extract_list_state_related + eapply extract_option_state_related); eassumption).
            all: try (cbv [Proper]; eapply abstract_domain_R_refl_of_abstraction_relation_for_each_lhs_of_arrow; try eassumption; reflexivity). }
          { apply ZRange.type.option.is_bounded_by_impl_related_hetero_and_Proper. }
        Qed.

        Lemma Interp_EvalWithBound
              {opts : AbstractInterpretation.Options}
              {assume_cast_truncates : bool}
              {skip_annotations_under : forall t, ident t -> bool}
              {strip_preexisting_annotations : bool}
              {t} (e : Expr t)
              (Hwf : expr.Wf e)
              (st : type.for_each_lhs_of_arrow abstract_domain t)
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
        Proof using Hrelax.
          cbv [EvalWithBound Let_In].
          epose proof (interp_eval_with_bound
                         (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e) _)
                         (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e) _)
                         (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e) _)) as H.
          edestruct H as [H0 H1]; [ shelve .. | ].
          split; intros.
          { cbv [expr.Interp]; erewrite H0 by eassumption.
            eapply (@type.related_iff_app_curried _ _ (fun _ => eq) t).
            { apply GeneralizeVar.Interp_gen1_FromFlat_ToFlat; eauto. }
            { etransitivity; (idtac + symmetry); eassumption. } }
          { lazymatch goal with
            | [ H : context[abstraction_relation' ?e _] |- abstraction_relation' ?e' _ ]
              => replace e' with e; [ now eapply H | ]
            end.
            apply Extract_FromFlat_ToFlat'; eauto; [].
            eapply type.and_for_each_lhs_of_arrow_Proper_impl_hetero1;
              [ | eapply type.andb_bool_impl_and_for_each_lhs_of_arrow; [ | eassumption ] ];
              [ | refine (fun t x y H => H) ];
              cbv beta.
            intros *; eapply ZRange.type.option.is_bounded_by_impl_eqv_refl. }
          Unshelve.
          all: try apply expr.Wf3_of_Wf.
          all: apply GeneralizeVar.Wf_FromFlat_to_flat.
          all: apply Hwf.
        Qed.

        Lemma Interp_EtaExpandWithBound
              {t} (E : Expr t)
              (Hwf : Wf E)
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
            {t} (e_st e e_v : expr t)
            (Hwf : expr.wf3 nil e_st e e_v)
            (Hwf' : expr.wf nil e e_st)
            (Hwf'' : expr.wf nil e_v e_v)
            (Hwf''' : expr.wf nil e_st e_st)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
              type.app_curried (expr.interp (@ident.interp) (strip_annotations assume_cast_truncates e e_st st)) arg1
              = type.app_curried (expr.interp (@ident.interp) e_v) arg2)
          /\ (forall arg1
                     (Harg11 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg1)
                     (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                 abstraction_relation'
                   (extract assume_cast_truncates e_st st)
                   (type.app_curried (expr.interp (@ident.interp) (strip_annotations assume_cast_truncates e e_st st)) arg1)).
      Proof using Type.
        cbv [strip_annotations]; split;
          [ intros arg1 arg2 Harg12 Harg1
          | intros arg1 Harg11 Harg1 ].
        all: eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1; [ | apply @ZRange.type.option.is_bounded_by_impl_related_hetero_and_Proper with (skip_base:=true) ].
        all: eapply ident.interp_eval_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom, interp_annotate_expr, default_relax_zrange_good, abstract_interp_ident_related with typeclass_instances.
        all: try (intros; (eapply extract_list_state_related + eapply extract_option_state_related + eapply strip_annotation_related); eassumption).
      Qed.

      Lemma Interp_StripAnnotations
            {opts : AbstractInterpretation.Options}
            {assume_cast_truncates : bool}
            {t} (E : Expr t)
            (Hwf : Wf E)
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
    eapply @Interp_EvalWithBound; eauto with wf typeclass_instances.
  Qed.

  Lemma Interp_PartialEvaluateWithListInfoFromBounds
        {opts : AbstractInterpretation.Options}
        {t} (E : Expr t)
        (Hwf : Wf E)
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
          (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
          (b_out : ZRange.type.base.option.interp (type.final_codomain t))
          rv (Hrv : CheckedPartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in b_out = inl rv)
          {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
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
        (*assert (b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related _ _ (fun _ => eq))) b_in)
          by (cbv [Proper] in *;
              eapply type.and_for_each_lhs_of_arrow_Proper_impl_hetero1;
              [ | eapply type.andb_bool_impl_and_for_each_lhs_of_arrow; [ | eassumption ] ];
              [ | refine (fun t x y H => H) ];
              cbv beta;
              intros *; eapply ZRange.type.option.is_bounded_by_impl_eqv_refl);*)
        split;
        repeat first [ rewrite !@GeneralizeVar.Interp_gen1_FromFlat_ToFlat by eauto with wf typeclass_instances
                     | rewrite <- Extract_FromFlat_ToFlat by eauto with typeclass_instances; apply Interp_PartialEvaluateWithBounds_bounded; auto
                     | rewrite Extract_FromFlat_ToFlat by eauto with wf typeclass_instances
                     | progress intros
                     | eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; [ eassumption | ]
                     | solve [ eauto with wf typeclass_instances ]
                     | erewrite !Interp_PartialEvaluateWithBounds
                     | apply type.app_curried_Proper
                     | apply expr.Wf_Interp_Proper_gen
                     | progress intros ]
      | eauto with wf typeclass_instances ].
  Qed.

  Theorem CheckedPartialEvaluateWithBounds_Correct_first_order
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
    eapply CheckedPartialEvaluateWithBounds_Correct; eauto with core typeclass_instances.
  Qed.
End Compilers.
