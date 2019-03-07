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
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.LanguageWf.
Require Import Crypto.UnderLetsProofs.
Require Import Crypto.AbstractInterpretation.
Import Coq.Lists.List.

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
    Import UnderLets.Compilers.UnderLets.
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
        Local Notation state_of_value1 := (@state_of_value base_type ident var1 abstract_domain' bottom').
        Local Notation state_of_value2 := (@state_of_value base_type ident var2 abstract_domain' bottom').
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
        Local Notation bottomify1 := (@bottomify base_type ident var1 abstract_domain' bottom').
        Local Notation bottomify2 := (@bottomify base_type ident var2 abstract_domain' bottom').
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
                 => forall seg G' sv1 sv2,
                     G' = (seg ++ G)%list
                     -> @wf_value seg s sv1 sv2
                     -> UnderLets.wf
                         (fun G' => @wf_value G' d) G'
                         (v1 sv1) (v2 sv2)
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
        Proof using bottom'_Proper.
          clear -Hv type_base bottom'_Proper.
          destruct t; [ destruct v1, v2, Hv | ]; cbn in *; cbv [respectful]; eauto; intros; apply bottom_Proper.
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

        Fixpoint wf_reify (annotate_with_state : bool) (is_let_bound : bool) G {t}
          : forall v1 v2 (Hv : @wf_value G t v1 v2)
              s1 s2 (Hs : type.and_for_each_lhs_of_arrow (@abstract_domain_R) s1 s2),
            UnderLets.wf (fun G' => expr.wf G') G (@reify1 annotate_with_state is_let_bound t v1 s1) (@reify2 annotate_with_state is_let_bound t v2 s2)
        with wf_reflect (annotate_with_state : bool) G {t}
             : forall e1 e2 (He : expr.wf G e1 e2)
                 s1 s2 (Hs : abstract_domain_R s1 s2),
            @wf_value G t (@reflect1 annotate_with_state t e1 s1) (@reflect2 annotate_with_state t e2 s2).
        Proof using annotate_Proper bottom'_Proper.
          all: clear -wf_reflect wf_reify annotate_Proper type_base bottom'_Proper.
          all: pose proof (@bottom_for_each_lhs_of_arrow_Proper); cbv [Proper abstract_domain_R] in *.
          all: destruct t as [t|s d];
            [ clear wf_reify wf_reflect
            | pose proof (fun G => wf_reflect annotate_with_state G s) as wf_reflect_s;
              pose proof (fun G => wf_reflect annotate_with_state G d) as wf_reflect_d;
              pose proof (fun G => wf_reify annotate_with_state false G s) as wf_reify_s;
              pose proof (fun G => wf_reify annotate_with_state false G d) as wf_reify_d;
              pose proof (@bottom_Proper s);
              clear wf_reify wf_reflect ].
          all: cbn [reify reflect] in *.
          all: fold (@reify2) (@reflect2) (@reify1) (@reflect1).
          all: cbn in *.
          all: repeat first [ progress cbn [fst snd] in *
                            | progress cbv [respectful] in *
                            | progress intros
                            | progress subst
                            | progress destruct_head'_and
                            | progress destruct_head'_ex
                            | solve [ eauto | wf_t ]
                            | apply annotate_Proper
                            | apply UnderLets.wf_to_expr
                            | break_innermost_match_step
                            | match goal with
                              | [ |- UnderLets.wf _ _ _ _ ] => constructor
                              | [ |- expr.wf _ _ _ ] => constructor
                              | [ He : forall seg G' sv1 sv2, G' = (seg ++ ?G)%list -> _ |- UnderLets.wf _ (?v :: ?G) (UnderLets.splice _ _) (UnderLets.splice _ _) ]
                                => eapply UnderLets.wf_splice; [ apply (He (cons v nil)) | ]
                              | [ |- UnderLets.wf _ _ (UnderLets.splice (reify1 _ _ _ _) _) (UnderLets.splice (reify2 _ _ _ _) _) ]
                                => eapply UnderLets.wf_splice; [ apply wf_reify_s || apply wf_reify_d | ]
                              | [ |- wf_value _ (reflect1 _ _ _) (reflect2 _ _ _) ] => apply wf_reflect_s || apply wf_reflect_d
                              | [ H : wf_value _ ?x ?y |- wf_value _ ?x ?y ]
                                => eapply wf_value_Proper_list; [ | eassumption ]
                              | [ H : forall x y, ?R x y -> ?R' (?f x) (?g y) |- ?R' (?f _) (?g _) ]
                                => apply H
                              | [ |- ?R (state_of_value1 _) (state_of_value2 _) ] => eapply state_of_value_Proper
                              end ].
        Qed.

        Lemma wf_bottomify {t} G v1 v2
              (Hwf : @wf_value G t v1 v2)
          : wf_value_with_lets G (bottomify1 v1) (bottomify2 v2).
        Proof using bottom'_Proper.
          cbv [wf_value_with_lets] in *.
          revert dependent G; induction t as [|s IHs d IHd]; intros;
            cbn [bottomify wf_value]; fold (@value1) (@value2) in *; break_innermost_match;
              constructor.
          all: repeat first [ progress cbn [fst snd wf_value] in *
                            | progress destruct_head'_and
                            | assumption
                            | apply bottom'_Proper
                            | apply conj
                            | progress intros
                            | progress subst
                            | solve [ eapply UnderLets.wf_splice; eauto ] ].
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
                         | [ |- UnderLets.wf _ _ (bottomify1 _) (bottomify2 _) ] => apply wf_bottomify
                         | [ |- UnderLets.wf _ _ _ _ ] => constructor
                         | [ |- and _ _ ] => apply conj
                         end
                       | eapply wf_value_Proper_list; [ | solve [ eauto ] ]
                       | eapply UnderLets.wf_Proper_list; [ | | solve [ eauto ] ]
                       | match goal with
                         | [ H : _ |- _ ] => eapply H; clear H; solve [ wf_interp_t ]
                         end
                       | break_innermost_match_step ].

        Lemma wf_interp (annotate_with_state : bool) G G' {t} (e1 : @expr (@value_with_lets1) t) (e2 : @expr (@value_with_lets2) t)
              (Hwf : expr.wf G e1 e2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : wf_value_with_lets G' (interp1 annotate_with_state e1) (interp2 annotate_with_state e2).
        Proof using annotate_Proper bottom'_Proper interp_ident_Proper.
          revert dependent G'; induction Hwf; intros; cbn [interp];
            try solve [ apply interp_ident_Proper; auto
                      | eauto ];
            wf_interp_t.
        Qed.

        Lemma wf_eval_with_bound' (annotate_with_state : bool) G G' {t} e1 e2 (He : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (@eval_with_bound'1 annotate_with_state t e1 st1) (@eval_with_bound'2 annotate_with_state t e2 st2).
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
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (extract_option_state : forall A, abstract_domain' (base.type.option A) -> option (option (abstract_domain' A)))
                (is_annotated_for : forall t t', ident t -> abstract_domain' t' -> bool).
        Context (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop).
        Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' abstract_domain'_R).
        Context {annotate_ident_Proper : forall t, Proper (abstract_domain'_R t ==> eq) (annotate_ident t)}
                {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
                {is_annotated_for_Proper : forall t t', Proper (eq ==> abstract_domain'_R _ ==> eq) (@is_annotated_for t t')}
                (extract_list_state_length : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_map (@length _) (extract_list_state t v1) = option_map (@length _) (extract_list_state t v2))
                (extract_list_state_rel : forall t v1 v2, abstract_domain'_R _ v1 v2 -> forall l1 l2, extract_list_state t v1 = Some l1 -> extract_list_state t v2 = Some l2 -> forall vv1 vv2, List.In (vv1, vv2) (List.combine l1 l2) -> @abstract_domain'_R t vv1 vv2)
                (extract_option_state_rel : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_eq (option_eq (abstract_domain'_R _)) (extract_option_state t v1) (extract_option_state t v2)).

        Local Instance abstract_interp_ident_Proper_arrow s d
          : Proper (eq ==> abstract_domain'_R s ==> abstract_domain'_R d) (abstract_interp_ident (type.arrow s d))
          := abstract_interp_ident_Proper (type.arrow s d).

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Local Notation update_annotation1 := (@ident.update_annotation var1 abstract_domain' annotate_ident is_annotated_for).
          Local Notation update_annotation2 := (@ident.update_annotation var2 abstract_domain' annotate_ident is_annotated_for).
          Local Notation annotate1 := (@ident.annotate var1 abstract_domain' annotate_ident abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Local Notation annotate2 := (@ident.annotate var2 abstract_domain' annotate_ident abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Local Notation annotate_base1 := (@ident.annotate_base var1 abstract_domain' annotate_ident is_annotated_for).
          Local Notation annotate_base2 := (@ident.annotate_base var2 abstract_domain' annotate_ident is_annotated_for).
          Local Notation annotate_with_ident1 := (@ident.annotate_with_ident var1 abstract_domain' annotate_ident is_annotated_for).
          Local Notation annotate_with_ident2 := (@ident.annotate_with_ident var2 abstract_domain' annotate_ident is_annotated_for).
          Local Notation interp_ident1 := (@ident.interp_ident var1 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Local Notation interp_ident2 := (@ident.interp_ident var2 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Local Notation reflect1 := (@reflect base.type ident var1 abstract_domain' annotate1 bottom').
          Local Notation reflect2 := (@reflect base.type ident var2 abstract_domain' annotate2 bottom').

          Lemma wf_update_annotation G {t} st1 st2 (Hst : abstract_domain'_R t st1 st2) e1 e2 (He : expr.wf G e1 e2)
            : expr.wf G (@update_annotation1 t st1 e1) (@update_annotation2 t st2 e2).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper is_annotated_for_Proper.
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
                           | discriminate
                           | match goal with
                             | [ H : abstract_domain'_R _ ?x _ |- _ ] => rewrite !H
                             | [ H : abstract_domain'_R _ ?x _, H' : context[?x] |- _ ] => rewrite !H in H'
                             end
                           | progress wf_safe_t
                           | break_innermost_match_step ].
          Qed.

          Lemma wf_annotate_with_ident
                is_let_bound t G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate_with_ident1 is_let_bound t v1 e1) (@annotate_with_ident2 is_let_bound t v2 e2).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper is_annotated_for_Proper.
            cbv [ident.annotate_with_ident]; break_innermost_match; repeat constructor; apply wf_update_annotation; assumption.
          Qed.

          Lemma wf_annotate_base
                is_let_bound (t : base.type.base) G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate_base1 is_let_bound t v1 e1) (@annotate_base2 is_let_bound t v2 e2).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper is_annotated_for_Proper.
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
          Proof using abstract_interp_ident_Proper annotate_ident_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
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
                                | [ H : abstract_domain'_R _ ?v1 ?v2, H1 : extract_option_state _ ?v1 = _, H2 : extract_option_state _ ?v2 = _ |- _ ]
                                  => let H' := fresh in
                                     pose proof H as H';
                                     apply extract_option_state_rel in H';
                                     rewrite H1, H2 in H';
                                     cbv [option_eq] in H';
                                     clear H1 H2
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
                              | progress destruct_head' option
                              | progress cbn [Option.combine option_map UnderLets.splice_option reify_option option_rect] in *
                              | progress cbn [type.decode f_equal eq_rect fst snd] in *
                              | solve [ wf_t ] ].
          Qed.

          Local Notation wf_value_with_lets := (@wf_value_with_lets base.type ident abstract_domain' abstract_domain'_R var1 var2).
          Local Notation wf_value := (@wf_value base.type ident abstract_domain' abstract_domain'_R var1 var2).

          Local Ltac type_of_value v :=
            lazymatch v with
            | (abstract_domain ?t * _)%type => t
            | (?a -> UnderLets _ ?b)
              => let a' := type_of_value a in
                let b' := type_of_value b in
                constr:(type.arrow a' b')
            end.
          Lemma wf_interp_ident_nth_default (annotate_with_state : bool) G T
            : wf_value_with_lets G (@interp_ident1 annotate_with_state _ (@ident.List_nth_default T)) (@interp_ident2 annotate_with_state _ (@ident.List_nth_default T)).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            cbv [wf_value_with_lets wf_value ident.interp_ident]; constructor; cbn -[abstract_domain_R abstract_domain].
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
                                   | [ |- expr _ -> _ -> _ ]
                                     => refine (expr.wf G)
                                   | [ |- ?T -> _ -> _ ]
                                     => let t := type_of_value T in
                                       refine (@wf_value G t)
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
                           | progress expr.invert_match
                           | match goal with
                             | [ |- wf_value _ _ _ ] => progress hnf
                             end ]. }
          Qed.

          Lemma wf_interp_ident_not_nth_default (annotate_with_state : bool) G {t} (idc : ident t)
            : wf_value_with_lets G (Base (reflect1 annotate_with_state (###idc)%expr (abstract_interp_ident _ idc))) (Base (reflect2 annotate_with_state (###idc)%expr (abstract_interp_ident _ idc))).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            constructor; eapply wf_reflect;
              solve [ apply bottom'_Proper
                    | apply wf_annotate
                    | repeat constructor
                    | apply abstract_interp_ident_Proper; reflexivity ].
          Qed.

          Lemma wf_interp_ident (annotate_with_state : bool) G {t} idc1 idc2 (Hidc : idc1 = idc2)
            : wf_value_with_lets G (@interp_ident1 annotate_with_state t idc1) (@interp_ident2 annotate_with_state t idc2).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            cbv [wf_value_with_lets ident.interp_ident]; subst idc2; destruct idc1;
              first [ apply wf_interp_ident_nth_default
                    | apply wf_interp_ident_not_nth_default ].
          Qed.

          Local Notation eval_with_bound1 := (@partial.ident.eval_with_bound var1 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Local Notation eval_with_bound2 := (@partial.ident.eval_with_bound var2 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Lemma wf_eval_with_bound (annotate_with_state : bool) {t} G G' e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
                (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
            : expr.wf G' (@eval_with_bound1 annotate_with_state t e1 st1) (@eval_with_bound2 annotate_with_state t e2 st2).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            eapply wf_eval_with_bound';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.

          Local Notation eval1 := (@partial.ident.eval var1 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Local Notation eval2 := (@partial.ident.eval var2 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Lemma wf_eval {t} G G' e1 e2 (Hwf : expr.wf G e1 e2)
                (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
            : expr.wf G' (@eval1 t e1) (@eval2 t e2).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            eapply wf_eval';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.

          Local Notation eta_expand_with_bound1 := (@partial.ident.eta_expand_with_bound var1 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Local Notation eta_expand_with_bound2 := (@partial.ident.eta_expand_with_bound var2 abstract_domain' annotate_ident bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for).
          Lemma wf_eta_expand_with_bound {t} G e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
            : expr.wf G (@eta_expand_with_bound1 t e1 st1) (@eta_expand_with_bound2 t e2 st2).
          Proof using abstract_interp_ident_Proper annotate_ident_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            eapply wf_eta_expand_with_bound';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.
        End with_var2.
      End with_type.
    End ident.

    Section specialized.
      Import defaults.
      Local Notation abstract_domain' := ZRange.type.base.option.interp (only parsing).
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Local Notation abstract_domain'_R t := (@eq (abstract_domain' t)) (only parsing).
      Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' (fun t => abstract_domain'_R t)).

      Global Instance annotate_ident_Proper {relax_zrange} {t} : Proper (abstract_domain'_R t ==> eq) (annotate_ident relax_zrange t).
      Proof.
        intros st st' ?; subst st'.
        cbv [annotate_ident]; break_innermost_match; reflexivity.
      Qed.

      Global Instance bottom'_Proper {t} : Proper (abstract_domain'_R t) (bottom' t).
      Proof. reflexivity. Qed.

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
                       | progress inversion_option
                       | discriminate
                       | solve [ eauto ]
                       | apply NatUtil.nat_rect_Proper_nondep
                       | apply ListUtil.list_rect_Proper
                       | apply ListUtil.list_rect_arrow_Proper
                       | apply ListUtil.list_case_Proper
                       | apply ListUtil.pointwise_map
                       | apply ListUtil.fold_right_Proper
                       | apply ListUtil.update_nth_Proper
                       | apply (@nat_rect_Proper_nondep_gen (_ -> _) (eq ==> eq)%signature)
                       | cbn; apply (f_equal (@Some _))
                       | progress cbn [ZRange.ident.option.interp]
                       | progress cbv [zrange_rect]
                       | apply (f_equal2 pair)
                       | break_innermost_match_step
                       | match goal with
                         | [ H : _ |- _ ] => erewrite H by (eauto; (eassumption || reflexivity))
                         | [ H : forall x y, x = y -> _ |- _ ] => specialize (fun x => H x x eq_refl)
                         | [ H : forall x, ?f x = ?g x, H1 : ?f ?y = _, H2 : ?g ?y = _ |- _ ]
                           => specialize (H y); rewrite H1, H2 in H
                         end ].
      Qed.

      Global Instance extract_list_state_Proper {t}
        : Proper (abstract_domain'_R _ ==> option_eq (SetoidList.eqlistA (@abstract_domain'_R t)))
                 (extract_list_state t).
      Proof.
        intros st st' ?; subst st'; cbv [option_eq extract_list_state]; break_innermost_match; reflexivity.
      Qed.

      Global Instance is_annotated_for_Proper {relax_zrange t t'} : Proper (eq ==> abstract_domain'_R _ ==> eq) (@is_annotated_for relax_zrange t t') | 10.
      Proof. repeat intro; subst; reflexivity. Qed.

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

      Lemma extract_option_state_rel
        : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_eq (option_eq (abstract_domain'_R _)) (extract_option_state t v1) (extract_option_state t v2).
      Proof.
        cbv [extract_option_state option_eq]; intros; subst; break_match; reflexivity.
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
                  | apply extract_list_state_rel
                  | apply extract_option_state_rel ].
        Qed.

        Lemma wf_eval_with_bound {relax_zrange t} G G' e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (@eval_with_bound relax_zrange var1 t e1 st1) (@eval_with_bound relax_zrange var2 t e2 st2).
        Proof.
          eapply ident.wf_eval_with_bound;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel
                  | apply extract_option_state_rel ].
        Qed.


        Lemma wf_eta_expand_with_bound {relax_zrange t} G e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
          : expr.wf G (@eta_expand_with_bound relax_zrange var1 t e1 st1) (@eta_expand_with_bound relax_zrange var2 t e2 st2).
        Proof.
          eapply ident.wf_eta_expand_with_bound;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel
                  | apply extract_option_state_rel ].
        Qed.
      End with_var2.

      Lemma Wf_Eval {t} (e : Expr t) (Hwf : Wf e) : Wf (Eval e).
      Proof.
        intros ??; eapply wf_eval with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Lemma Wf_EvalWithBound {relax_zrange t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EvalWithBound relax_zrange e bound).
      Proof.
        intros ??; eapply wf_eval_with_bound with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Lemma Wf_EtaExpandWithBound {relax_zrange t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EtaExpandWithBound relax_zrange e bound).
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
  Hint Resolve Wf_Eval Wf_EvalWithBound Wf_EtaExpandWithBound Wf_EtaExpandWithListInfoFromBound : wf.
  Import defaults.

  Lemma Wf_PartialEvaluateWithListInfoFromBounds
        {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithListInfoFromBounds E b_in).
  Proof. cbv [PartialEvaluateWithListInfoFromBounds]; auto with wf. Qed.
  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf.

  Lemma Wf_PartialEvaluateWithBounds
        {relax_zrange} {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithBounds relax_zrange E b_in).
  Proof. cbv [PartialEvaluateWithBounds]; auto with wf. Qed.
  Hint Resolve Wf_PartialEvaluateWithBounds : wf.
End Compilers.
