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

Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.
  Import AbstractInterpretation.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
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

      Section with_var2.
        Context {var1 var2 : type -> Type}.
        Local Notation UnderLets1 := (@UnderLets.UnderLets base_type ident var1).
        Local Notation UnderLets2 := (@UnderLets.UnderLets base_type ident var2).
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation value1 := (@value base_type ident var1 abstract_domain').
        Local Notation value2 := (@value base_type ident var2 abstract_domain').
        Local Notation value_with_lets1 := (@value_with_lets base_type ident var1 abstract_domain').
        Local Notation value_with_lets2 := (@value_with_lets base_type ident var2 abstract_domain').
        Local Notation state_of_value1 := (@state_of_value base_type ident var1 abstract_domain').
        Local Notation state_of_value2 := (@state_of_value base_type ident var2 abstract_domain').
        Context (annotate1 : forall (is_let_bound : bool) t, abstract_domain' t -> @expr1 t -> UnderLets1 (@expr1 t))
                (annotate2 : forall (is_let_bound : bool) t, abstract_domain' t -> @expr2 t -> UnderLets2 (@expr2 t))
                (annotate_Proper
                 : forall is_let_bound t G
                     v1 v2 (Hv : abstract_domain'_R t v1 v2)
                     e1 e2 (He : expr.wf G e1 e2),
                    UnderLets.wf (fun G' => expr.wf G') G (annotate1 is_let_bound t v1 e1) (annotate2 is_let_bound t v2 e2))
                (interp_ident1 : forall t, ident t -> value_with_lets1 t)
                (interp_ident2 : forall t, ident t -> value_with_lets2 t).
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

        Definition abstract_domain_R {t} : relation (abstract_domain t)
          := type.related abstract_domain'_R.

        (** This one is tricky.  Because we need to be stable under
            weakening and reordering of the context, we permit any
            context for well-formedness of the input in the arrow
            case, and simply tack on that context at the beginning of
            the output.  This is sort-of wasteful on the output
            context, but it's sufficient to prove
            [wf_value_Proper_list] below, which is what we really
            need. *)
        Fixpoint wf_value G {t} : value1 t -> value2 t -> Prop
          := match t return value1 t -> value2 t -> Prop with
             | type.base t
               => fun v1 v2
                 => abstract_domain_R (fst v1) (fst v2)
                   /\ expr.wf G (snd v1) (snd v2)
             | type.arrow s d
               => fun v1 v2
                 => abstract_domain_R (fst v1) (fst v2)
                   /\ (forall seg G' sv1 sv2,
                         G' = (seg ++ G)%list
                         -> @wf_value seg s sv1 sv2
                         -> UnderLets.wf
                             (fun G' => @wf_value G' d) G'
                             (snd v1 sv1) (snd v2 sv2))
             end.

        Definition wf_value_with_lets G {t} : value_with_lets1 t -> value_with_lets2 t -> Prop
          := UnderLets.wf (fun G' => wf_value G') G.

        Context (interp_ident_Proper
                 : forall G t idc1 idc2 (Hidc : idc1 = idc2),
                    wf_value_with_lets G (interp_ident1 t idc1) (interp_ident2 t idc2)).

        Global Instance bottom_Proper {t} : Proper abstract_domain_R (@bottom t) | 10.
        Proof using bottom'_Proper.
          clear -bottom'_Proper type_base.
          cbv [Proper] in *; induction t; cbn; cbv [respectful]; eauto.
        Qed.

        Global Instance bottom_for_each_lhs_of_arrow_Proper {t}
          : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) (@bottom_for_each_lhs_of_arrow t) | 10.
        Proof using bottom'_Proper.
          clear -bottom'_Proper type_base.
          pose proof (@bottom_Proper).
          cbv [Proper] in *; induction t; cbn; cbv [respectful]; eauto.
        Qed.

        Lemma state_of_value_Proper G {t} v1 v2 (Hv : @wf_value G t v1 v2)
          : abstract_domain_R (state_of_value1 v1) (state_of_value2 v2).
        Proof using Type.
          clear -Hv type_base.
          destruct t, v1, v2, Hv; cbn in *; cbv [respectful]; eauto.
        Qed.

        Local Hint Resolve (ex_intro _ nil) (ex_intro _ (cons _ nil)).
        Local Hint Constructors expr.wf ex.
        Local Hint Unfold List.In.

        Lemma wf_value_Proper_list G1 G2
              (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
              t e1 e2
              (Hwf : @wf_value G1 t e1 e2)
          : @wf_value G2 t e1 e2.
        Proof using Type.
          clear -type_base HG1G2 Hwf.
          revert dependent G1; revert dependent G2; induction t; intros;
            repeat first [ progress cbn in *
                         | progress intros
                         | solve [ eauto ]
                         | progress subst
                         | progress destruct_head'_and
                         | progress destruct_head'_or
                         | apply conj
                         | rewrite List.in_app_iff in *
                         | match goal with H : _ |- _ => apply H; clear H end
                         | wf_unsafe_t_step
                         | eapply UnderLets.wf_Proper_list; [ | | solve [ eauto ] ] ].
        Qed.

        Fixpoint wf_reify (is_let_bound : bool) G {t}
          : forall v1 v2 (Hv : @wf_value G t v1 v2)
              s1 s2 (Hs : type.and_for_each_lhs_of_arrow (@abstract_domain_R) s1 s2),
            UnderLets.wf (fun G' => expr.wf G') G (@reify1 is_let_bound t v1 s1) (@reify2 is_let_bound t v2 s2)
        with wf_reflect G {t}
             : forall e1 e2 (He : expr.wf G e1 e2)
                 s1 s2 (Hs : abstract_domain_R s1 s2),
            @wf_value G t (@reflect1 t e1 s1) (@reflect2 t e2 s2).
        Proof using annotate_Proper bottom'_Proper.
          all: clear -wf_reflect wf_reify annotate_Proper type_base bottom'_Proper.
          all: pose proof (@bottom_for_each_lhs_of_arrow_Proper); cbv [Proper] in *.
          { destruct t as [t|s d];
              [ clear wf_reify wf_reflect
              | specialize (fun G => wf_reflect G s);
                specialize (fun G => wf_reify false G d) ].
            { cbn; intros [? ?] [? ?] [Hv0 Hv1] [] [] [];
                cbn [fst snd] in *.
              apply annotate_Proper; assumption. }
            { cbn; cbv [respectful]; intros [? ?] [? ?] [He0 He1] [? ?] [? ?] [Hs0 Hs1];
                cbn [fst snd] in *.
              do 2 constructor; intros v1 v2.
              eapply UnderLets.wf_to_expr, UnderLets.wf_splice.
              { eapply He1 with (seg:=cons _ nil); eauto using eq_refl. }
              { intros; apply wf_reify; destruct_head'_ex; subst; auto. } } }
          { destruct t as [t|s d];
              [ clear wf_reify wf_reflect
              | specialize (fun G => wf_reflect G d);
                specialize (fun G => wf_reify false G s) ].
            { cbn; auto. }
            { cbn; cbv [respectful]; intros e1 e2 He s1 s2 Hs;
                split; [ solve [ auto ] | ];
                  intros G' seg sv1 sv2 HG1G2 Hsv; subst.
              eapply UnderLets.wf_splice.
              { apply wf_reify; auto; eapply wf_value_Proper_list; [ .. | solve [ eauto ] ];
                  wf_safe_t. }
              { intros G'' a1 a2 [seg' ?] Ha; subst G''.
                constructor.
                apply wf_reflect.
                { constructor; auto; wf_unsafe_t_step; [].
                  destruct_head'_ex; subst.
                  intros *.
                  rewrite !List.in_app_iff; auto. }
                { eapply Hs, state_of_value_Proper; eassumption. } } } }
        Qed.

        Local Ltac wf_interp_t :=
          repeat first [ progress cbv [wf_value_with_lets abstract_domain_R respectful] in *
                       | progress cbn [wf_value fst snd partial.bottom type.related eq_rect List.In] in *
                       | wf_safe_t_step
                       | exact I
                       | apply wf_reify
                       | apply bottom_Proper
                       | progress destruct_head'_ex
                       | progress destruct_head'_or
                       | eapply UnderLets.wf_splice
                       | match goal with
                         | [ |- UnderLets.wf _ _ _ _ ] => constructor
                         | [ |- and _ _ ] => apply conj
                         end
                       | eapply wf_value_Proper_list; [ | solve [ eauto ] ]
                       | eapply UnderLets.wf_Proper_list; [ | | solve [ eauto ] ]
                       | match goal with
                         | [ H : _ |- _ ] => eapply H; clear H; solve [ wf_interp_t ]
                         end
                       | break_innermost_match_step ].

        Lemma wf_interp G G' {t} (e1 : @expr (@value_with_lets1) t) (e2 : @expr (@value_with_lets2) t)
              (Hwf : expr.wf G e1 e2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : wf_value_with_lets G' (interp1 e1) (interp2 e2).
        Proof using annotate_Proper bottom'_Proper interp_ident_Proper.
          revert dependent G'; induction Hwf; intros; cbn [interp];
            try solve [ apply interp_ident_Proper; auto
                      | eauto ];
            wf_interp_t.
        Qed.

        Lemma wf_eval_with_bound' G G' {t} e1 e2 (He : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (@eval_with_bound'1 t e1 st1) (@eval_with_bound'2 t e2 st2).
        Proof using annotate_Proper bottom'_Proper interp_ident_Proper.
          eapply UnderLets.wf_to_expr, UnderLets.wf_splice.
          { eapply wf_interp; solve [ eauto ]. }
          { intros; destruct_head'_ex; subst; eapply wf_reify; eauto. }
        Qed.

        Lemma wf_eval' G G' {t} e1 e2 (He : expr.wf G e1 e2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (@eval'1 t e1) (@eval'2 t e2).
        Proof using annotate_Proper bottom'_Proper interp_ident_Proper.
          eapply wf_eval_with_bound'; eauto; apply bottom_for_each_lhs_of_arrow_Proper.
        Qed.

        Lemma wf_eta_expand_with_bound' G {t} e1 e2 (He : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
          : expr.wf G (@eta_expand_with_bound'1 t e1 st1) (@eta_expand_with_bound'2 t e2 st2).
        Proof using annotate_Proper bottom'_Proper.
          eapply UnderLets.wf_to_expr, wf_reify; [ eapply wf_reflect | ]; eauto; apply bottom_Proper.
        Qed.

        Local Notation lazy_abstract_domain := (@lazy_abstract_domain base_type abstract_domain').
        Local Notation force_abstract_domain := (@force_abstract_domain base_type abstract_domain').
        Local Notation thunk_abstract_domain := (@thunk_abstract_domain base_type abstract_domain').

        Definition lazy_abstract_domain'_R {t} : relation (lazy_abstract_domain (type.base t))
          := fun v1 v2 => abstract_domain'_R t (force_abstract_domain v1) (force_abstract_domain v2).
        Definition lazy_abstract_domain_R {t} : relation (lazy_abstract_domain t)
          := fun v1 v2 => abstract_domain_R (force_abstract_domain v1) (force_abstract_domain v2).

        Local Ltac red_thunk_force' s d :=
          change (@force_abstract_domain (s -> d)) with (fun f x => @force_abstract_domain d (f (@thunk_abstract_domain s x))) in *;
          change (@thunk_abstract_domain (s -> d)) with (fun f x => @thunk_abstract_domain d (f (@force_abstract_domain s x))) in *.
        Local Ltac red_thunk_force :=
          repeat match goal with
                 | [ |- context[@force_abstract_domain (type.arrow ?s ?d)] ] => progress red_thunk_force' s d
                 | [ |- context[@thunk_abstract_domain (type.arrow ?s ?d)] ] => progress red_thunk_force' s d
                 | [ H : context[@force_abstract_domain (type.arrow ?s ?d)] |- _ ] => progress red_thunk_force' s d
                 | [ H : context[@thunk_abstract_domain (type.arrow ?s ?d)] |- _ ] => progress red_thunk_force' s d
                 end;
          cbv beta in *.

        Lemma force_thunk_abstract_domain {t} : (fun v => @force_abstract_domain t (thunk_abstract_domain v)) = (fun v => v).
        Proof.
          induction t as [t|s IHs d IHd]; [ reflexivity | ].
          change
            ((fun (v : abstract_domain (s -> d)) (x : abstract_domain s)
              => id (fun v => force_abstract_domain (thunk_abstract_domain v)) (v (id (fun v => force_abstract_domain (thunk_abstract_domain v)) x)))
             = (fun v => v)).
          rewrite IHs, IHd; cbv [id]; reflexivity.
        Qed.
        Lemma force_thunk_abstract_domain_ext {t} v : @force_abstract_domain t (thunk_abstract_domain v) = v.
        Proof. exact (f_equal (fun f => f v) force_thunk_abstract_domain). Qed.
        (*
        Lemma related_force {t} x y
          : @lazy_abstract_domain_R t x y <-> @abstract_domain_R t (force_abstract_domain x) (force_abstract_domain y).
        Proof.
          induction t as [t|s IHs d IHd]; [ reflexivity | ].
          cbv [lazy_abstract_domain_R abstract_domain_R] in *; cbn [type.related] in *; cbv [respectful] in *.
          setoid_rewrite IHs; setoid_rewrite IHd.
          progress change (@force_abstract_domain (s -> d)) with (fun f x => @force_abstract_domain d (f (@thunk_abstract_domain s x))).
          cbv beta iota.
          (*progress change (@thunk_abstract_domain (s -> d)) with (fun f x => @thunk_abstract_domain d (f (@force_abstract_domain s x))).*)
          intuition.
          { match goal with
            | [ H : _ |- _ ] => apply H; rewrite !force_thunk_abstract_domain_ext; assumption
            end. }
          { match goal with
            | [ |- ?R (force_abstract_domain (?f ?x)) (force_abstract_domain (?g ?y)) ]
              => rewrite <- (force_thunk_abstract_domain_ext x),  <- (force_thunk_abstract_domain_ext y)
            end.
          eauto.
          intuition (rewrite ?force_thunk_abstract_domain_ext; eauto).
          apply H.
         *)
        (*
        Section extract.
          Context (ident_extract : forall t, ident t -> lazy_abstract_domain t)
                  {ident_extract_Proper : forall {t}, Proper (eq ==> lazy_abstract_domain_R) (ident_extract t)}.

          Local Notation extract' := (@extract' base_type ident abstract_domain' ident_extract).
          Local Notation extract_gen := (@extract_gen base_type ident abstract_domain' ident_extract).

          Lemma extract'_Proper G
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @lazy_abstract_domain_R t v1 v2)
                {t}
            : Proper (expr.wf G ==> lazy_abstract_domain_R) (@extract' t).
          Proof using ident_extract_Proper.
            clear -ident_extract_Proper HG type_base; cbv [lazy_abstract_domain_R].
            intros ? ? Hwf.
            induction Hwf; red_thunk_force; cbn -[thunk_abstract_domain force_abstract_domain] in *; red_thunk_force;
              cbv [respectful] in *; try apply ident_extract_Proper; intros; eauto;
                try solve [ repeat first [ progress intros
                             | progress cbn [List.In fst snd] in *
                           | progress cbv [lazy_abstract_domain_R] in *
                           | rewrite force_thunk_abstract_domain_ext
                             | progress wf_safe_t
                             | match goal with
                               | [ H : _ |- _ ] => eapply H; clear H
                               end ] ].
            repeat first [ progress intros
                             | progress cbn [List.In fst snd] in *
                           | progress cbv [lazy_abstract_domain_R] in *
                           | rewrite force_thunk_abstract_domain_ext
                           | progress wf_safe_t ].
            eapply IHHwf1.
            match goal with
            | [ H : _ |- _ ] => eapply H; clear H
            end.
            { repeat first [ progress intros
                           | progress cbn [List.In fst snd] in *
                           | progress cbv [lazy_abstract_domain_R] in *
                           | rewrite force_thunk_abstract_domain_ext
                           | progress wf_safe_t ].
              .

          Qed.

          Local Lemma pull_prod_forall A A' B B' (Q : A * A' -> B * B' -> Prop)
            : (forall x y, Q x y) <-> (forall x0 y0 x1 y1, Q (x0, x1) (y0, y1)).
          Proof. intuition. Qed.

          Lemma abstract_domain_R_app_curried_iff t F G
            : (@abstract_domain_R t F G)
              <-> (forall x y, type.and_for_each_lhs_of_arrow (@abstract_domain_R) x y -> abstract_domain'_R (type.final_codomain t) (type.app_curried F x) (type.app_curried G y)).
          Proof using Type.
            clear -type_base.
            induction t as [t|s IHs d IHd]; cbn; [ tauto | ].
            cbv [respectful].
            rewrite pull_prod_forall.
            lazymatch goal with
            | [ |- (forall x y, @?P x y) <-> (forall z w, @?Q z w) ]
              => cut (forall x y, (P x y <-> Q x y)); [ intro H'; setoid_rewrite H'; reflexivity | intros ??; cbn [fst snd] ]
            end.
            lazymatch goal with
            | [ |- (?P -> ?Q) <-> (forall z w, ?P' /\ @?R z w -> @?S z w) ]
              => unify P P'; cut (P' -> (Q <-> (forall z w, R z w -> S z w))); [ change P with P'; solve [ intuition ] | intro; cbn [fst snd] ]
            end.
            eauto.
          Qed.

          Lemma lazy_abstract_domain_R_app_curried_iff t F G
            : (@lazy_abstract_domain_R t F G)
              <-> (forall x y, type.and_for_each_lhs_of_arrow (@abstract_domain_R) x y -> abstract_domain'_R (type.final_codomain t) (type.app_curried F (type.map_for_each_lhs_of_arrow (@thunk_abstract_domain) x) tt) (type.app_curried G (type.map_for_each_lhs_of_arrow (@thunk_abstract_domain) y) tt)).
          Proof using Type.
            clear -type_base.
            induction t as [t|s IHs d IHd]; cbn; [ tauto | ].
            cbv [respectful].
            rewrite pull_prod_forall; cbn.
            lazymatch goal with
            | [ |- (forall x y, @?P x y) <-> (forall z w, @?Q z w) ]
              => cut (forall x y, (P x y <-> Q (force_abstract_domain x) (force_abstract_domain y))); [ intro H'; setoid_rewrite H' | intros ??; cbn [fst snd] ]
            end.
            { cbn; intuition.
              match goal with
              | [ H : _ |- ?R (type.app_curried (?F ?x) _ _) (type.app_curried (?G ?y) _ _) ]
                => specialize (H x y); rewrite !force_thunk_abstract_domain_ext in H; apply H; auto
              end. }
            lazymatch goal with
            | [ |- (?P -> ?Q) <-> (forall z w, ?P' /\ @?R z w -> @?S z w) ]
              => unify P P'; cut (P' -> (Q <-> (forall z w, R z w -> S z w))); [ change P with P'; solve [ intuition ] | intro; cbn [fst snd] ]
            end.
            eauto.
          Qed.

          Lemma extract_gen_Proper G
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @lazy_abstract_domain_R t v1 v2)
                {t}
            : Proper (expr.wf G ==> type.and_for_each_lhs_of_arrow (@abstract_domain_R) ==> abstract_domain'_R (type.final_codomain t)) (@extract_gen t).
          Proof.
            intros ?? Hwf ?? Hv; cbv [extract_gen].
            generalize (@extract'_Proper G HG t _ _ Hwf).
            generalize (extract' x) (extract' y); clear x y G HG Hwf; intros x y Hwf.
            generalize (conj Hv Hwf).
            clear Hv Hwf.

            setoid_rewrite abstract_domain_R_app_curried_iff.
            lazymatch goal with
            | [ |- ?X -> ?Y ] => cut (X <-> Y); [ tauto | ]
            end.
            induction t; [ solve [ intuition eauto; constructor ] | ];
              cbn [type.final_codomain type.app_curried type.for_each_lhs_of_arrow type.and_for_each_lhs_of_arrow type.map_for_each_lhs_of_arrow fst snd] in *.
            destruct_head'_prod; destruct_head'_and; cbn [fst snd] in *.
            rewrite <- IHt2.
            rewrite !and_assoc, !(and_comm (type.and_for_each_lhs_of_arrow _ _ _)), <- !and_assoc.
            lazymatch goal with
            | [ |- (?A /\ ?B) <-> (?C /\ ?B) ] => cut (A <-> C); [ tauto | ]
            end.
          Definition extract_gen {t} (e : @expr lazy_abstract_domain t) (bound : type.for_each_lhs_of_arrow abstract_domain t)
            : abstract_domain' (type.final_codomain t)
            := type.app_curried (extract' e) (type.map_for_each_lhs_of_arrow (@thunk_abstract_domain) bound) tt.
        End extract.*)

      End with_var2.
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

        Local Instance abstract_interp_ident_Proper_arrow s d
          : Proper (eq ==> abstract_domain'_R s ==> abstract_domain'_R d) (abstract_interp_ident (type.arrow s d))
          := abstract_interp_ident_Proper (type.arrow s d).

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Local Notation update_annotation1 := (@ident.update_annotation var1 abstract_domain' annotate_ident abstract_interp_ident is_annotation).
          Local Notation update_annotation2 := (@ident.update_annotation var2 abstract_domain' annotate_ident abstract_interp_ident is_annotation).
          Local Notation annotate1 := (@ident.annotate var1 abstract_domain' annotate_ident abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Local Notation annotate2 := (@ident.annotate var2 abstract_domain' annotate_ident abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Local Notation annotate_base1 := (@ident.annotate_base var1 abstract_domain' annotate_ident abstract_interp_ident update_literal_with_state is_annotation).
          Local Notation annotate_base2 := (@ident.annotate_base var2 abstract_domain' annotate_ident abstract_interp_ident update_literal_with_state is_annotation).
          Print ident.annotate_with_ident.
          Local Notation annotate_with_ident1 := (@ident.annotate_with_ident var1 abstract_domain' annotate_ident abstract_interp_ident is_annotation).
          Local Notation annotate_with_ident2 := (@ident.annotate_with_ident var2 abstract_domain' annotate_ident abstract_interp_ident is_annotation).
          Local Notation interp_ident1 := (@ident.interp_ident var1 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Local Notation interp_ident2 := (@ident.interp_ident var2 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Local Notation reflect1 := (@reflect base.type ident var1 abstract_domain' annotate1 bottom').
          Local Notation reflect2 := (@reflect base.type ident var2 abstract_domain' annotate2 bottom').

          Lemma wf_update_annotation G {t} st1 st2 (Hst : abstract_domain'_R t st1 st2) e1 e2 (He : expr.wf G e1 e2)
            : expr.wf G (@update_annotation1 t st1 e1) (@update_annotation2 t st2 e2).
          Proof.
            cbv [ident.update_annotation];
              repeat first [ progress subst
                           | progress expr.invert_subst
                           | progress cbn [fst snd projT1 projT2 eq_rect] in *
                           | progress cbn [invert_AppIdent Option.bind invert_App invert_Ident] in *
                           | progress destruct_head'_sig
                           | progress destruct_head'_sigT
                           | progress destruct_head'_and
                           | progress destruct_head'_prod
                           | progress destruct_head' False
                           | progress inversion_option
                           | progress expr.inversion_wf_constr
                           | progress expr.inversion_wf_one_constr
                           | break_innermost_match_hyps_step
                           | expr.invert_match_step
                           | progress expr.inversion_expr
                           | progress rewrite_type_transport_correct
                           | progress type_beq_to_eq
                           | progress type.inversion_type
                           | progress base.type.inversion_type
                           | match goal with
                             | [ H : abstract_domain'_R _ ?x _ |- _ ] => rewrite !H; clear dependent x
                             end
                           | progress wf_safe_t
                           | break_innermost_match_step ].
          Qed.

          Lemma wf_annotate_with_ident
                is_let_bound t G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate_with_ident1 is_let_bound t v1 e1) (@annotate_with_ident2 is_let_bound t v2 e2).
          Proof.
            cbv [ident.annotate_with_ident]; break_innermost_match; repeat constructor; apply wf_update_annotation; assumption.
          Qed.

          Lemma wf_annotate_base
                is_let_bound (t : base.type.base) G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate_base1 is_let_bound t v1 e1) (@annotate_base2 is_let_bound t v2 e2).
          Proof.
            cbv [ident.annotate_base];
              repeat first [ apply wf_annotate_with_ident
                           | break_innermost_match_step
                           | progress subst
                           | progress cbv [type_base ident.smart_Literal] in *
                           | progress cbn [invert_Literal ident.invert_Literal] in *
                           | discriminate
                           | progress destruct_head' False
                           | progress expr.invert_subst
                           | progress expr.inversion_wf
                           | wf_safe_t_step
                           | break_innermost_match_hyps_step
                           | match goal with
                             | [ H : _ = _ :> ident _ |- _ ] => inversion H; clear H
                             | [ |- UnderLets.wf _ _ _ _ ] => constructor
                             | [ H : abstract_domain'_R _ _ _ |- _ ] => rewrite !H
                             end
                           | progress expr.invert_match_step
                           | progress expr.inversion_expr ].
          Qed.

          Lemma wf_annotate
                is_let_bound t G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate1 is_let_bound t v1 e1) (@annotate2 is_let_bound t v2 e2).
          Proof.
            revert dependent G; induction t; intros;
              cbn [ident.annotate]; try apply wf_annotate_base; trivial.
            all: repeat first [ lazymatch goal with
                                | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e1 = Some _, H'' : reflect_list ?e2 = None |- _ ]
                                  => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                                | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e2 = Some _, H'' : reflect_list ?e1 = None |- _ ]
                                  => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                                | [ H : expr.wf _ (reify_list _) (reify_list _) |- _ ] => apply expr.wf_reify_list in H
                                | [ |- expr.wf _ (reify_list _) (reify_list _) ] => apply expr.wf_reify_list
                                | [ |- UnderLets.wf _ _ (UnderLets.splice_list _ _) (UnderLets.splice_list _ _) ]
                                  => eapply @UnderLets.wf_splice_list_no_order with (P:=fun G => expr.wf G); autorewrite with distr_length
                                | [ H : expr.wf _ (reify_list _) ?e, H' : reflect_list ?e = None |- _ ]
                                  => apply expr.wf_reflect_list in H; rewrite H', expr.reflect_reify_list in H; exfalso; clear -H; intuition congruence
                                | [ H : expr.wf _ ?e (reify_list _), H' : reflect_list ?e = None |- _ ]
                                  => apply expr.wf_reflect_list in H; rewrite H', expr.reflect_reify_list in H; exfalso; clear -H; intuition congruence
                                | [ H : extract_list_state ?t ?v1 = ?x1, H' : extract_list_state ?t ?v2 = ?x2, Hv : abstract_domain'_R _ ?v1 ?v2 |- _ ]
                                  => let Hl := fresh in
                                     let Hl' := fresh in
                                     pose proof (extract_list_state_length _ v1 v2 Hv) as Hl;
                                     pose proof (extract_list_state_rel _ v1 v2 Hv) as Hl';
                                     rewrite H, H' in Hl, Hl'; cbv [option_eq option_map] in Hl, Hl'; clear H H'
                                | [ H : ?x = ?x |- _ ] => clear H
                                | [ H : length ?l1 = length ?l2, H' : context[length ?l1] |- _ ] => rewrite H in H'
                                end
                              | apply wf_annotate_with_ident
                              | apply DefaultValue.expr.base.wf_default
                              | apply DefaultValue.expr.wf_default
                              | progress expr.invert_subst
                              | progress cbn [ident.annotate ident.smart_Literal invert_Literal ident.invert_Literal invert_pair invert_AppIdent2 invert_App2 fst snd projT2 projT1 eq_rect Option.bind] in *
                              | progress destruct_head' False
                              | progress inversion_option
                              | progress destruct_head'_ex
                              | discriminate
                              | wf_safe_t_step
                              | progress expr.inversion_wf_constr
                              | progress expr.inversion_expr
                              | progress type_beq_to_eq
                              | progress type.inversion_type
                              | progress base.type.inversion_type
                              | match goal with
                                | [ |- expr.wf _ (update_annotation1 _ _) (update_annotation2 _ _) ] => apply wf_update_annotation
                                | [ H : _ = _ :> ident _ |- _ ] => inversion H; clear H
                                | [ |- UnderLets.wf _ _ _ _ ] => constructor
                                | [ H : abstract_domain'_R _ ?x _ |- _ ] => rewrite !H
                                | [ |- UnderLets.wf _ _ (UnderLets.splice _ _) (UnderLets.splice _ _) ] => eapply UnderLets.wf_splice
                                | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map in H
                                | [ H : context[List.nth_error (List.combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                                | [ |- context[List.nth_error (List.combine _ _) _] ] => rewrite nth_error_combine
                                | [ H : forall x y, Some _ = Some _ -> Some _ = Some _ -> _ |- _ ]
                                  => specialize (H _ _ eq_refl eq_refl)
                                | [ H : forall v1 v2, List.In (v1, v2) (List.combine ?l1 ?l2) -> ?R v1 v2, H' : List.nth_error ?l1 ?n = Some ?a1, H'' : List.nth_error ?l2 ?n = Some ?a2
                                                                                                                                                  |- ?R ?a1 ?a2 ]
                                  => apply H
                                | [ H : List.nth_error ?l ?n' = Some ?v |- List.In (?v, _) (List.combine ?l _) ] => apply nth_error_In with (n:=n')
                                end
                              | break_innermost_match_step
                              | break_innermost_match_hyps_step
                              | progress expr.invert_match
                              | progress expr.inversion_wf_one_constr
                              | match goal with
                                | [ H : context[UnderLets.wf _ _ (annotate1 _ _ _) (annotate2 _ _ _)]
                                    |- UnderLets.wf _ _ (annotate1 _ _ _) (annotate2 _ _ _) ] => eapply H
                                end
                              | apply abstract_interp_ident_Proper_arrow
                              | progress rewrite_type_transport_correct
                              | apply conj
                              | congruence
                              | solve [ wf_t ] ].
          Qed.

          Local Notation wf_value_with_lets := (@wf_value_with_lets base.type ident abstract_domain' abstract_domain'_R var1 var2).
          Local Notation wf_value := (@wf_value base.type ident abstract_domain' abstract_domain'_R var1 var2).

          Lemma wf_interp_ident_nth_default G T
            : wf_value_with_lets G (@interp_ident1 _ (@ident.List_nth_default T)) (@interp_ident2 _ (@ident.List_nth_default T)).
          Proof.
            cbv [wf_value_with_lets wf_value ident.interp_ident]; constructor; cbn -[abstract_domain_R abstract_domain].
            split.
            { exact (abstract_interp_ident_Proper _ (@ident.List_nth_default T) _ eq_refl). }
            { intros; subst.
              destruct_head'_prod; destruct_head'_and; cbn [fst snd] in *.
              repeat first [ progress subst
                           | progress cbn [invert_Literal ident.invert_Literal] in *
                           | lazymatch goal with
                             | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e1 = Some _, H'' : reflect_list ?e2 = None |- _ ]
                               => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                             | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e2 = Some _, H'' : reflect_list ?e1 = None |- _ ]
                               => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                             | [ H : expr.wf _ (reify_list _) (reify_list _) |- _ ] => apply expr.wf_reify_list in H
                             | [ |- expr.wf _ (reify_list _) (reify_list _) ] => apply expr.wf_reify_list
                             | [ |- UnderLets.wf _ _ (UnderLets.splice_list _ _) (UnderLets.splice_list _ _) ]
                               => eapply @UnderLets.wf_splice_list_no_order with (P:=fun G => expr.wf G); autorewrite with distr_length
                             | [ H : expr.wf _ (reify_list _) ?e, H' : reflect_list ?e = None |- _ ]
                               => apply expr.wf_reflect_list in H; rewrite H', expr.reflect_reify_list in H; exfalso; clear -H; intuition congruence
                             | [ H : expr.wf _ ?e (reify_list _), H' : reflect_list ?e = None |- _ ]
                               => apply expr.wf_reflect_list in H; rewrite H', expr.reflect_reify_list in H; exfalso; clear -H; intuition congruence
                             | [ H : extract_list_state ?t ?v1 = ?x1, H' : extract_list_state ?t ?v2 = ?x2, Hv : abstract_domain_R ?v1 ?v2 |- _ ]
                               => let Hl := fresh in
                                  let Hl' := fresh in
                                  pose proof (extract_list_state_length _ v1 v2 Hv) as Hl;
                                  pose proof (extract_list_state_rel _ v1 v2 Hv) as Hl';
                                  rewrite H, H' in Hl, Hl'; cbv [option_eq option_map] in Hl, Hl'; clear H H'
                             | [ H : ?x = ?x |- _ ] => clear H
                             | [ H : length ?l1 = length ?l2, H' : context[length ?l1] |- _ ] => rewrite H in H'
                             end
                           | match goal with
                             | [ |- UnderLets.wf ?Q ?G (UnderLets.splice ?x1 ?e1) (UnderLets.splice ?x2 ?e2) ]
                               => simple refine (@UnderLets.wf_splice _ _ _ _ _ _ _ _ _ Q G x1 x2 _ e1 e2 _);
                                  [ let G := fresh "G" in
                                    intro G;
                                    lazymatch goal with
                                    | [ |- (abstract_domain ?t * _) -> _ -> _ ]
                                      => refine (@wf_value G t)
                                    | [ |- expr _ -> _ -> _ ]
                                      => refine (expr.wf G)
                                    end
                                  | | ]
                             | [ |- UnderLets.wf ?Q ?G (UnderLets.Base _) (UnderLets.Base _) ]
                               => constructor
                             | [ H : _ = _ :> ident _ |- _ ] => inversion H; clear H
                             | [ H : List.nth_error _ _ = None |- _ ] => apply List.nth_error_None in H
                             | [ H : List.nth_error _ _ = Some _ |- _ ]
                               => unique pose proof (@ListUtil.nth_error_value_length _ _ _ _ H);
                                  unique pose proof (@ListUtil.nth_error_value_In _ _ _ _ H)
                             | [ H : context[List.In _ (List.map _ _)] |- _ ] => rewrite List.in_map_iff in H
                             | [ H : (?x <= ?y)%nat, H' : (?y < ?x)%nat |- _ ] => exfalso; clear -H H'; lia
                             | [ H : (?x <= ?y)%nat, H' : (?y < ?x')%nat, H'' : ?x' = ?x |- _ ] => exfalso; clear -H H' H''; lia
                             | [ H : length ?x = length ?y |- context[length ?x] ] => rewrite H
                             | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map in H
                             | [ H : context[List.nth_error (List.combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                             | [ |- context[List.nth_error (List.combine _ _) _] ] => rewrite nth_error_combine
                             | [ H : forall x y, Some _ = Some _ -> Some _ = Some _ -> _ |- _ ]
                               => specialize (H _ _ eq_refl eq_refl)
                             | [ H : forall v1 v2, List.In (v1, v2) (List.combine ?l1 ?l2) -> ?R v1 v2, H' : List.nth_error ?l1 ?n' = Some ?a1, H'' : List.nth_error ?l2 ?n' = Some ?a2
                                                                                                                                                |- _ ]
                               => unique pose proof (H a1 a2 ltac:(apply nth_error_In with (n:=n'); rewrite nth_error_combine, H', H''; reflexivity))
                             | [ H : List.nth_error ?l ?n' = Some ?v |- List.In (?v, _) (List.combine ?l _) ] => apply nth_error_In with (n:=n')
                             | [ H : context[length ?ls] |- _ ] => tryif is_var ls then fail else (progress autorewrite with distr_length in H)
                             | [ H : context[List.nth_error (List.seq _ _) _] |- _ ] => rewrite nth_error_seq in H
                             end
                           | progress inversion_option
                           | progress intros
                           | progress cbn [fst snd value] in *
                           | progress destruct_head'_prod
                           | progress destruct_head'_ex
                           | progress destruct_head'_and
                           | progress destruct_head' False
                           | progress specialize_by_assumption
                           | apply conj
                           | progress expr.invert_subst
                           | progress expr.inversion_wf_constr
                           | progress expr.inversion_expr
                           | wf_safe_t_step
                           | progress destruct_head' (@partial.wf_value)
                           | solve [ eapply wf_annotate; wf_t; try apply DefaultValue.expr.base.wf_default
                                   | eapply wf_annotate_base; wf_t
                                   | eapply (abstract_interp_ident_Proper _ (@ident.List_nth_default T) _ eq_refl); assumption
                                   | eapply wf_update_annotation; wf_t
                                   | wf_t
                                   | match goal with
                                     | [ H : context[UnderLets.wf _ _ _ _] |- UnderLets.wf _ _ _ _ ] => eapply H; solve [ repeat esplit; eauto ]
                                     end
                                   | eauto using List.nth_error_In
                                   | eapply expr.wf_Proper_list; [ | eassumption ]; wf_safe_t; eauto 10 ]
                           | break_innermost_match_step
                           | match goal with
                             | [ H : context[List.In] |- expr.wf _ ?x ?y ]
                               => specialize (H x y); rewrite !List.nth_default_eq, <- List.combine_nth, <- !List.nth_default_eq in H; cbv [List.nth_default] in H |- *
                             | [ H : List.In _ _ -> ?P |- ?P ] => apply H
                             end
                           | break_innermost_match_hyps_step
                           | congruence
                           | rewrite List.combine_length in *
                           | rewrite NPeano.Nat.min_r in * by lia
                           | rewrite NPeano.Nat.min_l in * by lia
                           | progress expr.inversion_wf_one_constr
                           | progress expr.invert_match ]. }
          Qed.

          Lemma wf_interp_ident_not_nth_default G {t} (idc : ident t)
            : wf_value_with_lets G (Base (reflect1 (###idc)%expr (abstract_interp_ident _ idc))) (Base (reflect2 (###idc)%expr (abstract_interp_ident _ idc))).
          Proof.
            constructor; eapply wf_reflect;
              solve [ apply bottom'_Proper
                    | apply wf_annotate
                    | repeat constructor
                    | apply abstract_interp_ident_Proper; reflexivity ].
          Qed.

          Lemma wf_interp_ident G {t} idc1 idc2 (Hidc : idc1 = idc2)
            : wf_value_with_lets G (@interp_ident1 t idc1) (@interp_ident2 t idc2).
          Proof.
            cbv [wf_value_with_lets ident.interp_ident]; subst idc2; destruct idc1;
              first [ apply wf_interp_ident_nth_default
                    | apply wf_interp_ident_not_nth_default ].
          Qed.

          Local Notation eval_with_bound1 := (@partial.ident.eval_with_bound var1 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Local Notation eval_with_bound2 := (@partial.ident.eval_with_bound var2 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Lemma wf_eval_with_bound {t} G G' e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
                (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
            : expr.wf G' (@eval_with_bound1 t e1 st1) (@eval_with_bound2 t e2 st2).
          Proof.
            eapply wf_eval_with_bound';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.

          Local Notation eval1 := (@partial.ident.eval var1 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Local Notation eval2 := (@partial.ident.eval var2 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Lemma wf_eval {t} G G' e1 e2 (Hwf : expr.wf G e1 e2)
                (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
            : expr.wf G' (@eval1 t e1) (@eval2 t e2).
          Proof.
            eapply wf_eval';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.

          Local Notation eta_expand_with_bound1 := (@partial.ident.eta_expand_with_bound var1 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Local Notation eta_expand_with_bound2 := (@partial.ident.eta_expand_with_bound var2 abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation).
          Lemma wf_eta_expand_with_bound {t} G e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
            : expr.wf G (@eta_expand_with_bound1 t e1 st1) (@eta_expand_with_bound2 t e2 st2).
          Proof.
            eapply wf_eta_expand_with_bound';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.

          Section extract.
            Local Notation ident_extract := (@ident.ident_extract abstract_domain' bottom' abstract_interp_ident).
            Local Notation lazy_abstract_domain_R := (@lazy_abstract_domain_R base.type abstract_domain' abstract_domain'_R).
            Global Instance ident_extract_Proper {t}
              : Proper (eq ==> lazy_abstract_domain_R) (@ident_extract t).
            Proof.
              intros idc idc' ?; subst idc'.
              destruct idc; cbn [ident.ident_extract]; cbv [lazy_abstract_domain_R];
                repeat first [ match goal with
                               | [ |- context G[force_abstract_domain _ (thunk_abstract_domain _ ?x)] ]
                                 => let G' := context G [x] in
                                   change G'
                               | [ |- context G[force_abstract_domain _ (fun _ 'tt => ?x)] ]
                                 => cbv [force_abstract_domain abstract_domain_R]
                               end
                             | refine (abstract_interp_ident_Proper _ _ _ eq_refl)
                             | eapply bottom_Proper
                             | eapply bottom'_Proper
                             | progress cbn [type.related]
                             | progress cbv [respectful]
                             | progress intros
                             | refine (abstract_interp_ident_Proper (type.arrow (type.base _) (type.base _)) _ _ eq_refl _ _ _) ].
            Qed.

          (*
            Definition extract {t} (e : @expr _ t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
              := @extract_gen base.type ident abstract_domain' (@ident_extract) t e bound.
           *)
          End extract.
        End with_var2.
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

      Global Instance annotate_ident_Proper {t} : Proper (abstract_domain'_R t ==> eq) (annotate_ident t).
      Proof.
        intros st st' ?; subst st'.
        cbv [annotate_ident]; break_innermost_match; reflexivity.
      Qed.

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

      Global Instance bottom'_Proper {t} : Proper (abstract_domain'_R t) (bottom' t).
      Proof. reflexivity. Qed.

      Lemma bottom'_bottom {t} : forall v, abstraction_relation' (bottom' t) v.
      Proof.
        cbv [abstraction_relation' bottom']; induction t; cbn; intros; break_innermost_match; cbn; try reflexivity.
        rewrite Bool.andb_true_iff; split; auto.
      Qed.

      Global Instance abstract_interp_ident_Proper {t}
        : Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t).
      Proof.
        cbv [abstract_interp_ident abstract_domain_R type.related respectful type.interp]; intros idc idc' ?; subst idc'; destruct idc;
          repeat first [ reflexivity
                       | progress subst
                       | progress cbn [ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp Option.bind] in *
                       | progress cbv [Option.bind]
                       | intro
                       | progress destruct_head'_prod
                       | progress destruct_head'_bool
                       | progress destruct_head' option
                       | solve [ eauto ]
                       | apply NatUtil.nat_rect_Proper_nondep
                       | apply ListUtil.list_rect_Proper
                       | apply ListUtil.list_case_Proper
                       | apply ListUtil.pointwise_map
                       | apply ListUtil.fold_right_Proper
                       | apply ListUtil.update_nth_Proper
                       | apply (@nat_rect_Proper_nondep_gen (_ -> _) (eq ==> eq)%signature)
                       | cbn; apply (f_equal (@Some _))
                       | match goal with
                         | [ H : _ |- _ ] => erewrite H by (eauto; (eassumption || reflexivity))
                         end ].
      Qed.

      Lemma abstract_interp_ident_related {t} (idc : ident t)
        : type.related_hetero (@abstraction_relation') (@abstract_interp_ident t idc) (ident.interp idc).
      Proof.
        destruct idc; cbv [abstract_interp_ident abstraction_relation'].
        all: cbv [type.related_hetero ZRange.ident.option.interp ident.interp ident.gen_interp respectful_hetero type.interp ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp ZRange.type.base.option.Some].
      Admitted.

      Global Instance update_literal_with_state_Proper {t}
        : Proper (abstract_domain'_R (base.type.type_base t) ==> eq ==> eq) (update_literal_with_state t).
      Proof. repeat intro; congruence. Qed.

      Lemma interp_update_literal_with_state {t : base.type.base} st v
        : @abstraction_relation' t st v -> @update_literal_with_state t st v = v.
      Proof.
        cbv [abstraction_relation' update_literal_with_state update_Z_literal_with_state ZRange.type.base.option.is_bounded_by];
          break_innermost_match; try congruence; reflexivity.
      Qed.

      Global Instance extract_list_state_Proper {t}
        : Proper (abstract_domain'_R _ ==> option_eq (SetoidList.eqlistA (@abstract_domain'_R t)))
                 (extract_list_state t).
      Proof.
        intros st st' ?; subst st'; cbv [option_eq extract_list_state]; break_innermost_match; reflexivity.
      Qed.

      Lemma extract_list_state_length
        : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_map (@length _) (extract_list_state t v1) = option_map (@length _) (extract_list_state t v2).
      Proof.
        intros; subst; cbv [option_map extract_list_state]; break_innermost_match; reflexivity.
      Qed.
      Lemma extract_list_state_rel
        : forall t v1 v2, abstract_domain'_R _ v1 v2 -> forall l1 l2, extract_list_state t v1 = Some l1 -> extract_list_state t v2 = Some l2 -> forall vv1 vv2, List.In (vv1, vv2) (List.combine l1 l2) -> @abstract_domain'_R t vv1 vv2.
      Proof.
        intros; cbv [extract_list_state] in *; subst; inversion_option; subst.
        rewrite combine_same, List.in_map_iff in *.
        destruct_head'_ex; destruct_head'_and; inversion_prod; subst; reflexivity.
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

      Section with_var2.
        Context {var1 var2 : type -> Type}.
        Local Notation wf_value_with_lets := (@wf_value_with_lets base.type ident abstract_domain' (fun t => abstract_domain'_R t) var1 var2).

        Lemma wf_eval {t} G G' e1 e2 (Hwf : expr.wf G e1 e2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (@eval var1 t e1) (@eval var2 t e2).
        Proof.
          eapply ident.wf_eval;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel ].
        Qed.

        Lemma wf_eval_with_bound {t} G G' e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (@eval_with_bound var1 t e1 st1) (@eval_with_bound var2 t e2 st2).
        Proof.
          eapply ident.wf_eval_with_bound;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel ].
        Qed.


        Lemma wf_eta_expand_with_bound {t} G e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
          : expr.wf G (@eta_expand_with_bound var1 t e1 st1) (@eta_expand_with_bound var2 t e2 st2).
        Proof.
          eapply ident.wf_eta_expand_with_bound;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel ].
        Qed.
      End with_var2.

      Lemma Wf_Eval {t} (e : Expr t) (Hwf : Wf e) : Wf (Eval e).
      Proof.
        intros ??; eapply wf_eval with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Lemma Wf_EvalWithBound {t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EvalWithBound e bound).
      Proof.
        intros ??; eapply wf_eval_with_bound with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Lemma Wf_EtaExpandWithBound {t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EtaExpandWithBound e bound).
      Proof.
        intros ??; eapply wf_eta_expand_with_bound with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Local Instance Proper_strip_ranges {t}
        : Proper (@abstract_domain_R t ==> @abstract_domain_R t) (@ZRange.type.option.strip_ranges t).
      Proof.
        cbv [Proper abstract_domain_R respectful].
        induction t as [t|s IHs d IHd]; cbn in *; destruct_head'_prod; destruct_head'_and; cbn in *; intros; subst; cbv [respectful] in *;
          eauto.
      Qed.

      Lemma Wf_EtaExpandWithListInfoFromBound {t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EtaExpandWithListInfoFromBound e bound).
      Proof.
        eapply Wf_EtaExpandWithBound; [ assumption | ].
        clear dependent e.
        cbv [Proper] in *; induction t as [t|s IHs d IHd]; cbn in *; destruct_head'_prod; destruct_head'_and; cbn in *; eauto.
        split; auto; apply Proper_strip_ranges; auto.
      Qed.
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
        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Lemma wf_relax G {t} (e1 : @expr var1 t) (e2 : @expr var2 t)
                (Hwf : expr.wf G e1 e2)
            : expr.wf G (@RelaxZRange.expr.relax relax_zrange var1 t e1) (@RelaxZRange.expr.relax relax_zrange var2 t e2).
          Proof using Type.
            clear -Hwf.
            induction Hwf; wf_safe_t.
            cbn [RelaxZRange.expr.relax]; cbv [option_map] in *.
            break_innermost_match;
              repeat first [ progress wf_safe_t
                           | progress expr.invert_subst
                           | progress expr.inversion_wf_constr
                           | progress destruct_head' False
                           | progress inversion_option
                           | progress cbn [invert_Ident invert_Var invert_Abs invert_App invert_LetIn] in *
                           | match goal with
                             | [ H : context[RelaxZRange.expr.relax ?r ?x], H' : RelaxZRange.expr.relax ?r ?x = _ |- _ ]
                               => rewrite H' in H
                             | [ H : context[match RelaxZRange.expr.relax ?r ?x with _ => _ end] |- _ ]
                               => remember (RelaxZRange.expr.relax r x) in *; progress expr.invert_match
                             | [ H : ?x = Some ?a, H' : context[?x] |- _ ] => rewrite H in H'
                             | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                             end
                           | progress expr.inversion_wf_one_constr ].
          Qed.
        End with_var2.

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

        Lemma Wf_Relax {t} (e : Expr t) (Hwf : Wf e) : Wf (@RelaxZRange.expr.Relax relax_zrange t e).
        Proof. intros ??; eapply wf_relax, Hwf. Qed.
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

  Lemma Wf_PartialEvaluateWithListInfoFromBounds
        {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithListInfoFromBounds E b_in).
  Proof. apply Wf_EtaExpandWithListInfoFromBound; assumption. Qed.
  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf.

  Lemma Wf_PartialEvaluateWithBounds
        {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithBounds E b_in).
  Proof. eapply partial.Wf_EvalWithBound; assumption. Qed.
  Hint Resolve Wf_PartialEvaluateWithBounds : wf.

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

  Hint Resolve Wf_EtaExpandWithBound Wf_PartialEvaluateWithListInfoFromBounds : wf.

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
      split.
      { eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; [ eassumption | ].
        clear dependent arg2.
        cbv [ident.interp]; rewrite RelaxZRange.expr.Interp_Relax; eauto.
        all: revert Harg1.
        all: exact admit. (* boundedness *) }
      { intro cast_outside_of_range; revert cast_outside_of_range Harg12.
        intros ? Harg; rewrite RelaxZRange.expr.Interp_Relax; eauto.
        all: revert Harg.
        all: exact admit. (* correctness of interp *) } }
    { auto with wf. }
  Qed.
End Compilers.
