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
Require Import Crypto.Util.Tactics.Head.
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

  Local Notation related_bounded' b v1 v2
    := (ZRange.type.base.option.is_bounded_by b v1 = true
        /\ ZRange.type.base.option.is_bounded_by b v2 = true
        /\ v1 = v2) (only parsing).
  Local Notation related_bounded
    := (@type.related_hetero3 _ _ _ _ (fun t b v1 v2 => related_bounded' b v1 v2)).

  Module ZRange.
    Module type.
      Module option.
        Lemma is_bounded_by_impl_related_hetero t
              (x : ZRange.type.option.interp t) (v : type.interp base.interp t)
        : ZRange.type.option.is_bounded_by x v = true
          -> type.related_hetero (fun t x v => ZRange.type.base.option.is_bounded_by x v = true) x v.
        Proof. induction t; cbn in *; intuition congruence. Qed.
      End option.
    End type.
  End ZRange.

  Module Import partial.
    Import AbstractInterpretation.Compilers.partial.
    Import NewPipeline.UnderLets.Compilers.UnderLets.
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
              (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
              (ident_interp_Proper : forall t (idc : ident t), type.related_hetero abstraction_relation' (abstract_interp_ident t idc) (ident_interp t idc)).
      Local Notation abstract_domain := (@abstract_domain base_type abstract_domain').
      Definition abstraction_relation {t} : abstract_domain t -> type.interp base_interp t -> Prop
        := type.related_hetero (@abstraction_relation').
      Local Notation bottom := (@bottom base_type abstract_domain' (@bottom')).
      Local Notation bottom_for_each_lhs_of_arrow := (@bottom_for_each_lhs_of_arrow base_type abstract_domain' (@bottom')).
      Local Notation var := (type.interp base_interp).
      Local Notation expr := (@expr.expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident).
      Local Notation value := (@value base_type ident var abstract_domain').
      Local Notation value_with_lets := (@value_with_lets base_type ident var abstract_domain').
      Local Notation state_of_value := (@state_of_value base_type ident var abstract_domain').
      Context (annotate : forall (is_let_bound : bool) t, abstract_domain' t -> @expr var t -> @UnderLets var (@expr var t))
              (interp_ident : forall t, ident t -> value_with_lets t)
              (ident_extract : forall t, ident t -> abstract_domain t).
      Local Notation eta_expand_with_bound' := (@eta_expand_with_bound' base_type ident _ abstract_domain' annotate bottom').
      Local Notation eval_with_bound' := (@partial.eval_with_bound' base_type ident _ abstract_domain' annotate bottom' interp_ident).
      Local Notation extract' := (@extract' base_type ident abstract_domain' ident_extract).
      Local Notation extract_gen := (@extract_gen base_type ident abstract_domain' ident_extract).
      (*
      Local Notation reify1 := (@reify base_type ident var1 abstract_domain' annotate1 bottom').
      Local Notation reify2 := (@reify base_type ident var2 abstract_domain' annotate2 bottom').
      Local Notation reflect1 := (@reflect base_type ident var1 abstract_domain' annotate1 bottom').
      Local Notation reflect2 := (@reflect base_type ident var2 abstract_domain' annotate2 bottom').
      Local Notation interp1 := (@interp base_type ident var1 abstract_domain' annotate1 bottom' interp_ident1).
      Local Notation interp2 := (@interp base_type ident var2 abstract_domain' annotate2 bottom' interp_ident2).
      Local Notation eval_with_bound'1 := (@eval_with_bound' base_type ident var1 abstract_domain' annotate1 bottom' interp_ident1).
      Local Notation eval_with_bound'2 := (@eval_with_bound' base_type ident var2 abstract_domain' annotate2 bottom' interp_ident2).
      Local Notation eval'1 := (@eval' base_type ident var1 abstract_domain' annotate1 bottom' interp_ident1).
      Local Notation eval'2 := (@eval' base_type ident var2 abstract_domain' annotate2 bottom' interp_ident2).
      Local Notation eta_expand_with_bound'1 := (@eta_expand_with_bound' base_type ident var1 abstract_domain' annotate1 bottom').
      Local Notation eta_expand_with_bound'2 := (@eta_expand_with_bound' base_type ident var2 abstract_domain' annotate2 bottom').
*)
(*

      Fixpoint value (t : type)
        := (abstract_domain t
            * match t return Type (* COQBUG(https://github.com/coq/coq/issues/7727) *) with
              | type.base t
                => @expr var t
              | type.arrow s d
                => value s -> UnderLets (value d)
              end)%type.

      Definition value_with_lets (t : type)
        := UnderLets (value t).


      Fixpoint bottom {t} : abstract_domain t
        := match t with
           | type.base t => bottom' t
           | type.arrow s d => fun _ => @bottom d
           end.

      Fixpoint bottom_for_each_lhs_of_arrow {t} : type.for_each_lhs_of_arrow abstract_domain t
        := match t return type.for_each_lhs_of_arrow abstract_domain t with
           | type.base t => tt
           | type.arrow s d => (bottom, @bottom_for_each_lhs_of_arrow d)
           end.

      Definition state_of_value {t} : value t -> abstract_domain t
        := match t return value t -> abstract_domain t with
           | type.base t => fun '(st, v) => st
           | type.arrow s d => fun '(st, v) => st
           end.

      Fixpoint reify (is_let_bound : bool) {t} : value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t)
        := match t return value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t) with
           | type.base t
             => fun '(st, v) 'tt
                => annotate is_let_bound t st v
           | type.arrow s d
             => fun '(f_st, f_e) '(sv, dv)
                => Base
                     (λ x , (UnderLets.to_expr
                               (fx <-- f_e (@reflect _ (expr.Var x) sv);
                                  @reify false _ fx dv)))
           end%core%expr
      with reflect {t} : @expr var t -> abstract_domain t -> value t
           := match t return @expr var t -> abstract_domain t -> value t with
              | type.base t
                => fun e st => (st, e)
              | type.arrow s d
                => fun e absf
                   => (absf,
                       (fun v
                        => let stv := state_of_value v in
                           (rv <-- (@reify false s v bottom_for_each_lhs_of_arrow);
                              Base (@reflect d (e @ rv) (absf stv))%expr)))
              end%under_lets.

      (* N.B. Because the [App] case only looks at the second argument
              of arrow-values, we are free to set the state of [Abs]
              nodes to [bottom], because for any [Abs] nodes which are
              actually applied (here and in places where we don't
              rewrite), we just drop it. *)
      Fixpoint interp {t} (e : @expr value_with_lets t) : value_with_lets t
        := match e in expr.expr t return value_with_lets t with
           | expr.Ident t idc => interp_ident _ idc (* Base (reflect (###idc) (abstract_interp_ident _ idc))*)
           | expr.Var t v => v
           | expr.Abs s d f => Base (bottom, fun x => @interp d (f (Base x)))
           | expr.App s d f x
             => (x' <-- @interp s x;
                   f' <-- @interp (s -> d)%etype f;
                   snd f' x')
           | expr.LetIn (type.arrow _ _) B x f
             => (x' <-- @interp _ x;
                   @interp _ (f (Base x')))
           | expr.LetIn (type.base A) B x f
             => (x' <-- @interp _ x;
                   x'' <-- reify true (* this forces a let-binder here *) x' tt;
                   @interp _ (f (Base (reflect x'' (state_of_value x')))))
           end%under_lets.

      Definition eval_with_bound' {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (e' <-- interp e; reify false e' st).

      Definition eval' {t} (e : @expr value_with_lets t) : expr t
        := eval_with_bound' e bottom_for_each_lhs_of_arrow.

      Definition eta_expand_with_bound' {t} (e : @expr var t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (reify false (reflect e bottom) st).

      Section extract.
        Context (ident_extract : forall t, ident t -> abstract_domain t).

        Definition extract' {t} (e : @expr abstract_domain t) : abstract_domain t
          := expr.interp (@ident_extract) e.

        Definition extract_gen {t} (e : @expr abstract_domain t) (bound : type.for_each_lhs_of_arrow abstract_domain t)
          : abstract_domain' (type.final_codomain t)
          := type.app_curried (extract' e) bound.
      End extract.
    End with_var.



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
 *)
      Lemma interp_eval_with_bound'
            {t} (e_st e1 e2 : expr t)
            (Hwf : expr.wf3 nil e_st e1 e2)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
              type.app_curried (expr.interp ident_interp (eval_with_bound' e1 st)) arg1
              = type.app_curried (expr.interp ident_interp e2) arg2)
          /\ (forall arg1
                     (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
                 abstraction_relation'
                   _
                   (extract_gen e_st st)
                   (type.app_curried (expr.interp ident_interp (eval_with_bound' e1 st)) arg1)).
      Proof using Type.
        cbv [extract_gen extract'].
        cbv [eval_with_bound'].
      Admitted.

      Lemma interp_eta_expand_with_bound'
            {t} (e1 e2 : expr t)
            (Hwf : expr.wf nil e1 e2)
            (b_in : type.for_each_lhs_of_arrow abstract_domain t)
        : forall arg1 arg2
            (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
            (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
          type.app_curried (expr.interp ident_interp (eta_expand_with_bound' e1 b_in)) arg1 = type.app_curried (expr.interp ident_interp e2) arg2.
      Proof using Type.
        cbv [eta_expand_with_bound'].
      Admitted.



  (*
      Definition eval_with_bound' {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (e' <-- interp e; reify false e' st).

      Definition eval' {t} (e : @expr value_with_lets t) : expr t
        := eval_with_bound' e bottom_for_each_lhs_of_arrow.

      Definition eta_expand_with_bound' {t} (e : @expr var t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (reify false (reflect e bottom) st).
*)
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
        Context (abstraction_relation' : forall t, abstract_domain' t -> base.interp t -> Prop).
        Context (cast_outside_of_range : zrange -> Z -> Z).
        Local Notation abstraction_relation := (@abstraction_relation base.type abstract_domain' base.interp abstraction_relation').
        (*Context {annotate_ident_Proper : forall t, Proper (abstract_domain'_R t ==> eq) (annotate_ident t)}
                {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
                {update_literal_with_state_Proper : forall t, Proper (abstract_domain'_R (base.type.type_base t) ==> eq ==> eq) (update_literal_with_state t)}
                (extract_list_state_length : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_map (@length _) (extract_list_state t v1) = option_map (@length _) (extract_list_state t v2))
                (extract_list_state_rel : forall t v1 v2, abstract_domain'_R _ v1 v2 -> forall l1 l2, extract_list_state t v1 = Some l1 -> extract_list_state t v2 = Some l2 -> forall vv1 vv2, List.In (vv1, vv2) (List.combine l1 l2) -> @abstract_domain'_R t vv1 vv2).
         *)
        Local Notation eval_with_bound := (@partial.ident.eval_with_bound _ abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
        Local Notation eta_expand_with_bound := (@partial.ident.eta_expand_with_bound _ abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
        Local Notation extract := (@ident.extract abstract_domain' abstract_interp_ident).

        Lemma interp_eval_with_bound
              {t} (e_st e1 e2 : expr t)
              (Hwf : expr.wf3 nil e_st e1 e2)
              (st : type.for_each_lhs_of_arrow abstract_domain t)
          : (forall arg1 arg2
                    (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                    (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
                type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) (eval_with_bound e1 st)) arg1
                = type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) e2) arg2)
            /\ (forall arg1
                       (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
                   abstraction_relation'
                     _
                     (extract e_st st)
                     (type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) (eval_with_bound e1 st)) arg1)).
        Proof using Type. cbv [extract eval_with_bound]; apply interp_eval_with_bound'; assumption. Qed.

        Lemma interp_eta_expand_with_bound
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
              (b_in : type.for_each_lhs_of_arrow abstract_domain t)
          : forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
            type.app_curried (interp (eta_expand_with_bound e1 b_in)) arg1 = type.app_curried (interp e2) arg2.
        Proof. cbv [partial.ident.eta_expand_with_bound]; eapply interp_eta_expand_with_bound'; eauto. Qed.

(*
        Definition eval {t} (e : @expr value_with_lets t) : @expr var t
          := @eval' base.type ident var abstract_domain' annotate bottom' (@interp_ident) t e.


*)
        (*
        Section extract.
          Local Notation extract := (@ident.extract abstract_domain' abstract_interp_ident).

          Lemma extract_Proper G
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @abstract_domain_R t v1 v2)
                {t}
            : Proper (expr.wf G ==> type.and_for_each_lhs_of_arrow (@abstract_domain_R) ==> abstract_domain'_R (type.final_codomain t)) (@extract t).
          Proof using abstract_interp_ident_Proper.
            apply @extract_gen_Proper; eauto.
          Qed.
        End extract.*)
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

      (*    Definition eval {var} {t} (e : @expr _ t) : expr t
        := (@partial.ident.eval)
             var abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation t e.
      Definition Eval {t} (e : Expr t) : Expr t
        := fun var => eval (e _).
      Definition Extract {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' abstract_interp_ident t (e _) bound.
       *)


      Lemma interp_eval_with_bound
            cast_outside_of_range
            {t} (e_st e1 e2 : expr t)
            (Hwf : expr.wf3 nil e_st e1 e2)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
              type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) (eval_with_bound e1 st)) arg1
              = type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) e2) arg2)
          /\ (forall arg1
                  (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                 abstraction_relation'
                   (extract e_st st)
                   (type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) (eval_with_bound e1 st)) arg1)).
      Proof using Type.
        cbv [eval_with_bound]; split;
          [ intros arg1 arg2 Harg12 Harg1
          | intros arg1 Harg1 ].
        all: eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1; [ | apply ZRange.type.option.is_bounded_by_impl_related_hetero ].
        all: eapply ident.interp_eval_with_bound with (abstraction_relation':=@abstraction_relation'); eauto.
      Qed.

      Lemma interp_eta_expand_with_bound
            {t} (e1 e2 : expr t)
            (Hwf : expr.wf nil e1 e2)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (interp (partial.eta_expand_with_bound e1 b_in)) arg1 = type.app_curried (interp e2) arg2.
      Proof.
        cbv [partial.eta_expand_with_bound]; intros arg1 arg2 Harg12 Harg1.
        eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1.
        { apply ident.interp_eta_expand_with_bound with (abstraction_relation':=@abstraction_relation'); eauto. }
        { apply ZRange.type.option.is_bounded_by_impl_related_hetero. }
      Qed.

      Lemma Interp_EvalWithBound
            cast_outside_of_range
            {t} (e : Expr t)
            (Hwf : expr.Wf3 e)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
              type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (EvalWithBound e st)) arg1
              = type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) e) arg2)
          /\ (forall arg1
                     (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                 abstraction_relation'
                   (Extract e st)
                   (type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (EvalWithBound e st)) arg1)).
      Proof using Type. cbv [Extract EvalWithBound]; apply interp_eval_with_bound, Hwf. Qed.

      Lemma Interp_EtaExpandWithBound
            {t} (E : Expr t)
            (Hwf : Wf E)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (Interp (partial.EtaExpandWithBound E b_in)) arg1 = type.app_curried (Interp E) arg2.
      Proof. cbv [partial.EtaExpandWithBound]; apply interp_eta_expand_with_bound, Hwf. Qed.

      Lemma strip_ranges_is_looser t b v
        : @ZRange.type.option.is_bounded_by t b v = true
          -> ZRange.type.option.is_bounded_by (ZRange.type.option.strip_ranges b) v = true.
      Proof.
        induction t as [t|s IHs d IHd]; cbn in *; [ | tauto ].
        induction t; cbn in *; break_innermost_match; cbn in *; rewrite ?Bool.andb_true_iff; try solve [ intuition ]; [].
        repeat match goal with ls : list _ |- _ => revert ls end.
        intros ls1 ls2; revert ls2.
        induction ls1, ls2; cbn in *; rewrite ?Bool.andb_true_iff; solve [ intuition ].
      Qed.

      Lemma andb_strip_ranges_Proper t (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t) arg1
        : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true ->
          type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by)
                                               (type.map_for_each_lhs_of_arrow (@ZRange.type.option.strip_ranges) b_in) arg1 = true.
      Proof.
        induction t as [t|s IHs d IHd]; cbn [type.andb_bool_for_each_lhs_of_arrow type.map_for_each_lhs_of_arrow type.for_each_lhs_of_arrow] in *;
          rewrite ?Bool.andb_true_iff; [ tauto | ].
        destruct_head'_prod; cbn [fst snd]; intros [? ?].
        erewrite IHd by eauto.
        split; [ | reflexivity ].
        apply strip_ranges_is_looser; assumption.
      Qed.

      Lemma Interp_EtaExpandWithListInfoFromBound
            {t} (E : Expr t)
            (Hwf : Wf E)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (Interp (partial.EtaExpandWithListInfoFromBound E b_in)) arg1 = type.app_curried (Interp E) arg2.
      Proof.
        cbv [partial.EtaExpandWithListInfoFromBound].
        intros; apply Interp_EtaExpandWithBound; trivial.
        apply andb_strip_ranges_Proper; assumption.
      Qed.
    End specialized.
  End partial.
  Import defaults.

  Module Import CheckCasts.
    Module ident.
      Lemma interp_eqv_without_casts t idc
            cast_outside_of_range1 cast_outside_of_range2
            (Hc : partial.is_annotation t idc = false)
      : ident.gen_interp cast_outside_of_range1 idc
        == ident.gen_interp cast_outside_of_range2 idc.
      Proof.
        generalize (@ident.gen_interp_Proper cast_outside_of_range1 t idc idc eq_refl);
          destruct idc; try exact id; cbn in Hc; discriminate.
      Qed.
    End ident.

    Lemma interp_eqv_without_casts
          cast_outside_of_range1 cast_outside_of_range2
          G {t} e1 e2 e3
          (HG : forall t v1 v2 v3, List.In (existT _ t (v1, v2, v3)) G -> v2 == v3)
          (Hwf : expr.wf3 G e1 e2 e3)
          (Hc : @CheckCasts.get_casts t e1 = nil)
    : expr.interp (@ident.gen_interp cast_outside_of_range1) e2
      == expr.interp (@ident.gen_interp cast_outside_of_range2) e3.
    Proof.
      induction Hwf;
        repeat first [ progress cbn [CheckCasts.get_casts] in *
                     | discriminate
                     | match goal with
                       | [ H : (_ ++ _)%list = nil |- _ ] => apply List.app_eq_nil in H
                       end
                     | progress destruct_head'_and
                     | progress break_innermost_match_hyps
                     | progress interp_safe_t
                     | solve [ eauto using ident.interp_eqv_without_casts ] ].
    Qed.

    Lemma Interp_WithoutUnsupportedCasts {t} (e : Expr t)
          (Hc : CheckCasts.GetUnsupportedCasts e = nil)
          (Hwf : expr.Wf3 e)
          cast_outside_of_range1 cast_outside_of_range2
      : expr.Interp (@ident.gen_interp cast_outside_of_range1) e
        == expr.Interp (@ident.gen_interp cast_outside_of_range2) e.
    Proof. eapply interp_eqv_without_casts with (G:=nil); wf_safe_t. Qed.
  End CheckCasts.

  Module RelaxZRange.
    Definition relaxed_cast_outside_of_range
               (relax_zrange : zrange -> option zrange)
               (cast_outside_of_range : zrange -> Z -> Z)
    : zrange -> Z -> Z
      := fun r v
         => match relax_zrange r with
            | Some r' => ident.cast cast_outside_of_range r' v
            | None => cast_outside_of_range r v
            end.

    Module ident.
      Section relax.
        Context (relax_zrange : zrange -> option zrange)
                (cast_outside_of_range : zrange -> Z -> Z)
                (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                         -> relax_zrange r = Some r'
                                         -> is_tighter_than_bool z r' = true).

        Local Notation relaxed_cast_outside_of_range := (@relaxed_cast_outside_of_range relax_zrange cast_outside_of_range).

        Lemma interp_relax {t} (idc : ident t)
          : ident.gen_interp cast_outside_of_range (@RelaxZRange.ident.relax relax_zrange t idc)
            == ident.gen_interp relaxed_cast_outside_of_range idc.
        Proof.
          pose proof (@ident.gen_interp_Proper cast_outside_of_range t idc idc eq_refl) as Hp.
          destruct idc; cbn [type.related] in *; repeat (let x := fresh "x" in intro x; specialize (Hp x));
            repeat first [ assumption
                         | reflexivity
                         | discriminate
                         | congruence
                         | progress subst
                         | progress cbv [relaxed_cast_outside_of_range RelaxZRange.ident.relax Option.bind ident.cast respectful is_tighter_than_bool id] in *
                         | progress cbn [ident.gen_interp type.related type.interp base.interp upper lower] in *
                         | progress destruct_head'_prod
                         | progress specialize_by (exact eq_refl)
                         | break_match_step ltac:(fun x => let h := head x in constr_eq h relax_zrange)
                         | match goal with
                           | [ H : relax_zrange ?r = Some ?r' |- context[Z.leb (lower ?r) ?v] ]
                             => pose proof (fun pf => Hrelax _ _ (Build_zrange v v) pf H); clear H
                           end
                         | break_innermost_match_step ].
        Qed.
      End relax.
    End ident.

    Module expr.
      Section relax.
        Context (relax_zrange : zrange -> option zrange)
                (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                         -> relax_zrange r = Some r'
                                         -> is_tighter_than_bool z r' = true)
                (cast_outside_of_range : zrange -> Z -> Z).

        Local Notation relaxed_cast_outside_of_range := (@relaxed_cast_outside_of_range relax_zrange cast_outside_of_range).

        Lemma interp_relax G {t} (e1 e2 : expr t)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
              (Hwf : expr.wf G e1 e2)
          : expr.interp (@ident.gen_interp cast_outside_of_range) (RelaxZRange.expr.relax relax_zrange e1)
            == expr.interp (@ident.gen_interp relaxed_cast_outside_of_range) e2.
        Proof.
          induction Hwf; cbn -[RelaxZRange.ident.relax] in *; interp_safe_t; cbv [option_map] in *;
            break_innermost_match; cbn -[RelaxZRange.ident.relax] in *; interp_safe_t;
              eauto using tt, @ident.interp_relax.
        Qed.

        Lemma Interp_Relax {t} (e : Expr t)
              (Hwf : Wf e)
          : expr.Interp (@ident.gen_interp cast_outside_of_range) (RelaxZRange.expr.Relax relax_zrange e)
            == expr.Interp (@ident.gen_interp relaxed_cast_outside_of_range) e.
        Proof. apply interp_relax with (G:=nil); wf_safe_t. Qed.
      End relax.
    End expr.
  End RelaxZRange.
  Hint Resolve RelaxZRange.expr.Wf_Relax : wf.

  Lemma Interp_PartialEvaluateWithBounds
        cast_outside_of_range
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (PartialEvaluateWithBounds E b_in)) arg1
      = type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) E) arg2.
  Proof.
    cbv [PartialEvaluateWithBounds].
    intros arg1 arg2 Harg12 Harg1.
    assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
      by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
    assert (arg2_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg2)
      by (hnf; etransitivity; [ symmetry; eassumption | eassumption ]).
    rewrite <- (@GeneralizeVar.Interp_gen1_GeneralizeVar _ _ _ _ _ E) by auto with wf.
    eapply Interp_EvalWithBound; eauto with wf.
  Qed.

  Lemma Interp_PartialEvaluateWithBounds_bounded
        cast_outside_of_range
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R _ _ (fun _ => eq))) b_in}
    : forall arg1
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      ZRange.type.base.option.is_bounded_by
        (partial.Extract E b_in)
        (type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (PartialEvaluateWithBounds E b_in)) arg1)
      = true.
  Proof.
    cbv [PartialEvaluateWithBounds].
    intros arg1 Harg1.
    rewrite <- Extract_FromFlat_ToFlat by auto with wf.
    eapply Interp_EvalWithBound; eauto with wf.
  Qed.

  Lemma Interp_PartialEvaluateWithListInfoFromBounds
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
    rewrite <- (@GeneralizeVar.Interp_GeneralizeVar _ E) by auto.
    apply Interp_EtaExpandWithListInfoFromBound; auto with wf.
  Qed.

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
    cbv [CheckedPartialEvaluateWithBounds Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    let H := lazymatch goal with H : _ = nil |- _ => H end in
    pose proof (@Interp_WithoutUnsupportedCasts _ _ H ltac:(solve [ auto with wf ])) as H'; clear H;
      assert (forall cast_outside_of_range1 cast_outside_of_range2,
                 expr.Interp (@ident.gen_interp cast_outside_of_range1) E == expr.Interp (@ident.gen_interp cast_outside_of_range2) E)
      by (intros c1 c2; specialize (H' c1 c2);
          rewrite !@GeneralizeVar.Interp_gen1_FromFlat_ToFlat in H' by eauto with wf typeclass_instances;
          assumption).
    clear H'.
    split.
    { intros arg1 arg2 Harg12 Harg1.
      assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
        by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
      split.
      all: repeat first [ rewrite !@GeneralizeVar.Interp_gen1_FromFlat_ToFlat by eauto with wf typeclass_instances
                        | rewrite <- Extract_FromFlat_ToFlat by auto; apply Interp_PartialEvaluateWithBounds_bounded; auto
                        | rewrite Extract_FromFlat_ToFlat by auto with wf
                        | progress intros
                        | progress cbv [ident.interp]
                        | rewrite RelaxZRange.expr.Interp_Relax; eauto
                        | eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; [ eassumption | ]
                        | solve [ eauto with wf ]
                        | erewrite !Interp_PartialEvaluateWithBounds
                        | apply type.app_curried_Proper
                        | apply expr.Wf_Interp_Proper_gen
                        | progress intros ]. }
    { auto with wf. }
  Qed.
End Compilers.
