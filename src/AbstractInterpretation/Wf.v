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
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Inversion.
Require Import Crypto.Language.InversionExtra.
Require Import Rewriter.Language.Wf.
Require Import Rewriter.Language.UnderLetsProofs.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Import Coq.Lists.List.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.
  Import AbstractInterpretation.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.InversionExtra.Compilers.
  Import Language.Wf.Compilers.
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
      Local Notation value var := (@value base_type ident var abstract_domain').
      Local Notation abstract_domain := (@abstract_domain base_type abstract_domain').
      Local Notation bottom := (@bottom base_type abstract_domain' (@bottom')).
      Local Notation bottom_for_each_lhs_of_arrow := (@bottom_for_each_lhs_of_arrow base_type abstract_domain' (@bottom')).

      Section with_var2.
        Context {var1 var2 : type -> Type}.
        Local Notation UnderLets1 := (@UnderLets.UnderLets base_type ident var1).
        Local Notation UnderLets2 := (@UnderLets.UnderLets base_type ident var2).
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation value1 := (@value var1).
        Local Notation value2 := (@value var2).
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
                (interp_ident1 : bool -> forall t, ident t -> value_with_lets1 t)
                (interp_ident2 : bool -> forall t, ident t -> value_with_lets2 t)
                (skip_annotations_under : forall t, ident t -> bool).
        Local Notation reify1 := (@reify base_type ident var1 abstract_domain' annotate1 bottom').
        Local Notation reify2 := (@reify base_type ident var2 abstract_domain' annotate2 bottom').
        Local Notation reflect1 := (@reflect base_type ident var1 abstract_domain' annotate1 bottom').
        Local Notation reflect2 := (@reflect base_type ident var2 abstract_domain' annotate2 bottom').
        Local Notation bottomify1 := (@bottomify base_type ident var1 abstract_domain' bottom').
        Local Notation bottomify2 := (@bottomify base_type ident var2 abstract_domain' bottom').
        Local Notation interp1 := (@interp base_type ident var1 abstract_domain' annotate1 bottom' skip_annotations_under interp_ident1).
        Local Notation interp2 := (@interp base_type ident var2 abstract_domain' annotate2 bottom' skip_annotations_under interp_ident2).
        Local Notation eval_with_bound'1 := (@eval_with_bound' base_type ident var1 abstract_domain' annotate1 bottom' skip_annotations_under interp_ident1).
        Local Notation eval_with_bound'2 := (@eval_with_bound' base_type ident var2 abstract_domain' annotate2 bottom' skip_annotations_under interp_ident2).
        Local Notation eval'1 := (@eval' base_type ident var1 abstract_domain' annotate1 bottom' skip_annotations_under interp_ident1).
        Local Notation eval'2 := (@eval' base_type ident var2 abstract_domain' annotate2 bottom' skip_annotations_under interp_ident2).
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
                 : forall G t idc1 idc2 (Hidc : idc1 = idc2) annotate_with_state,
                    wf_value_with_lets G (interp_ident1 annotate_with_state t idc1) (interp_ident2 annotate_with_state t idc2)).

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

        Local Hint Resolve (fun A (P : list A -> Prop) => ex_intro P nil) (fun A (x : A) (P : list A -> Prop) => ex_intro P (cons x nil)) : core.
        Local Hint Constructors expr.wf ex : core.
        Local Hint Unfold List.In : core.

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

        Local Notation skip_annotations_for_App := (@skip_annotations_for_App base_type ident skip_annotations_under).

        Lemma wf_skip_annotations_for_App {var1' var2' G t e1 e2} (Hwf : expr.wf G (t:=t) e1 e2)
          : @skip_annotations_for_App var1' t e1 = @skip_annotations_for_App var2' t e2.
        Proof using Type.
          cbv [skip_annotations_for_App]; break_innermost_match;
            expr.invert_subst;
            repeat first [ progress cbn [projT1 projT2 fst snd eq_rect invert_App_curried invert_Ident Option.bind] in *
                         | reflexivity
                         | exfalso; assumption
                         | progress inversion_option
                         | progress destruct_head'_sig
                         | progress destruct_head'_and
                         | progress expr.inversion_wf_constr
                         | progress subst
                         | match goal with
                           | [ H : expr.wf _ (App_curried _ _) _ |- _ ]
                             => apply expr.invert_wf_App_curried_or_eq_base in H;
                                [ | clear H .. ]
                           | [ |- _ \/ _ ] => right; split; intros; congruence
                           | [ Hwf : expr.wf _ (App_curried _ _) ?e, H' : invert_AppIdent_curried _ = None |- _ ]
                             => apply expr.wf_invert_AppIdent_curried in Hwf; rewrite H' in Hwf; cbv [invert_AppIdent_curried Option.option_eq] in Hwf
                           | [ Hwf : expr.wf _ ?e (App_curried _ _), H' : invert_AppIdent_curried _ = None |- _ ]
                             => apply expr.wf_invert_AppIdent_curried in Hwf; rewrite H' in Hwf; cbv [Option.option_eq invert_AppIdent_curried] in Hwf
                           | [ H : context[invert_App_curried (App_curried _ _)] |- _ ]
                             => rewrite expr.invert_App_curried_App_curried in Hwf
                           end ].
        Qed.

        Lemma wf_interp (annotate_with_state : bool) G G' {t} (e1 : @expr (@value_with_lets1) t) (e2 : @expr (@value_with_lets2) t)
              (Hwf : expr.wf G e1 e2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : wf_value_with_lets G' (interp1 annotate_with_state e1) (interp2 annotate_with_state e2).
        Proof using annotate_Proper bottom'_Proper interp_ident_Proper.
          revert dependent G'; revert annotate_with_state; induction Hwf; intros; cbn [interp];
            try solve [ apply interp_ident_Proper; auto
                      | eauto ];
            match goal with
            | [ G' : list _ |- context[skip_annotations_for_App ?e1v] ]
              => match goal with
                 | [ |- context[skip_annotations_for_App ?e2v] ]
                   => epose proof (wf_skip_annotations_for_App (e1:=e1v) (e2:=e2v) (G:=G') ltac:(solve [ wf_t ]));
                        generalize dependent (skip_annotations_for_App e1v);
                        generalize dependent (skip_annotations_for_App e2v); intros;
                          subst
                 end
            end;
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
      Import API.
      Local Notation UnderLets := (@UnderLets base.type ident).
      Section with_type.
        Context (abstract_domain' : base.type -> Type).
        Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
        Context (bottom' : forall A, abstract_domain' A)
                (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (extract_option_state : forall A, abstract_domain' (base.type.option A) -> option (option (abstract_domain' A))).
        Context (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop).
        Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' abstract_domain'_R).
        Context {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
                (extract_list_state_length : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_map (@length _) (extract_list_state t v1) = option_map (@length _) (extract_list_state t v2))
                (extract_list_state_rel : forall t v1 v2, abstract_domain'_R _ v1 v2 -> forall l1 l2, extract_list_state t v1 = Some l1 -> extract_list_state t v2 = Some l2 -> List.Forall2 (@abstract_domain'_R t) l1 l2)
                (extract_option_state_rel : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_eq (option_eq (abstract_domain'_R _)) (extract_option_state t v1) (extract_option_state t v2)).

        Local Instance abstract_interp_ident_Proper_arrow s d
          : Proper (eq ==> abstract_domain'_R s ==> abstract_domain'_R d) (abstract_interp_ident (type.arrow s d))
          := abstract_interp_ident_Proper (type.arrow s d).

        Local Ltac handle_Forall2_step :=
          first [ match goal with
                  | [ |- List.Forall2 _ ?x ?x ] => rewrite Forall2_Forall; cbv [Proper]
                  | [ |- List.Forall2 _ (List.map _ _) (List.map _ _) ] => rewrite Forall2_map_map_iff
                  | [ |- List.Forall2 _ (List.combine _ _) (List.combine _ _) ]
                    => eapply Forall2_combine; [ intros | eassumption | eassumption ]
                  | [ |- List.Forall2 _ (List.combine ?x _) (List.combine ?x _) ]
                    => eapply Forall2_combine;
                       [ intros
                       | instantiate (1:=fun a b => a = b /\ List.In a x);
                         rewrite Forall2_Forall, Forall_forall; cbv [Proper]; auto
                       | eassumption ]
                  | [ H : expr.wf _ ?d1 ?d2, H' : List.Forall2 (expr.wf _) ?xs ?ys
                      |- expr.wf ?G (nth_default ?d1 ?xs ?n) (nth_default ?d2 ?ys ?n) ]
                    => cut (List.Forall2 (expr.wf G) xs ys /\ expr.wf G d1 d2);
                       [ rewrite Forall2_forall_iff'';
                         let H := fresh in intros [? H]; apply H
                       | ]
                  end ].


        Section with_var2.
          Context {var1 var2 : type -> Type}.
          Local Notation wf_value_with_lets := (@wf_value_with_lets base.type ident abstract_domain' abstract_domain'_R var1 var2).
          Local Notation wf_value := (@wf_value base.type ident abstract_domain' abstract_domain'_R var1 var2).
          Context (annotate_expr1 : forall t, abstract_domain' t -> option (@expr var1 (t -> t)))
                  (annotate_expr2 : forall t, abstract_domain' t -> option (@expr var2 (t -> t)))
                  (is_annotated_for1 : forall t t', @expr var1 t -> abstract_domain' t' -> bool)
                  (is_annotated_for2 : forall t t', @expr var2 t -> abstract_domain' t' -> bool)
                  (strip_annotation1 : forall t, ident t -> option (value _ t))
                  (strip_annotation2 : forall t, ident t -> option (value _ t))
                  (annotation_to_cast1 : forall s d, @expr var1 (s -> d) -> option (@expr var1 s -> @expr var1 d))
                  (annotation_to_cast2 : forall s d, @expr var2 (s -> d) -> option (@expr var2 s -> @expr var2 d))
                  (skip_annotations_under : forall t, ident t -> bool)
                  {wf_annotation_to_cast
                   : forall s d G e1 e2,
                      expr.wf G e1 e2
                      -> option_eq (fun f g => forall e1 e2, expr.wf G e1 e2 -> expr.wf G (f e1) (g e2))
                                   (annotation_to_cast1 s d e1)
                                   (annotation_to_cast2 s d e2)}
                  {annotate_expr_Proper : forall t s1 s2,
                      abstract_domain'_R t s1 s2
                      -> option_eq (expr.wf nil) (annotate_expr1 t s1) (annotate_expr2 t s2)}
                  {is_annotated_for_Proper : forall G t t' e1 e2,
                      expr.wf G e1 e2
                      -> ((abstract_domain'_R _ ==> eq)%signature)
                           (@is_annotated_for1 t t' e1)
                           (@is_annotated_for2 t t' e2)}
                  {wf_strip_annotation
                   : forall G t idc,
                      option_eq (wf_value G)
                                (@strip_annotation1 t idc)
                                (@strip_annotation2 t idc)}.

          Local Notation update_annotation1 := (@ident.update_annotation var1 abstract_domain' annotate_expr1 is_annotated_for1).
          Local Notation update_annotation2 := (@ident.update_annotation var2 abstract_domain' annotate_expr2 is_annotated_for2).
          Local Notation annotate1 := (@ident.annotate var1 abstract_domain' annotate_expr1 abstract_interp_ident extract_list_state extract_option_state is_annotated_for1).
          Local Notation annotate2 := (@ident.annotate var2 abstract_domain' annotate_expr2 abstract_interp_ident extract_list_state extract_option_state is_annotated_for2).
          Local Notation annotate_base1 := (@ident.annotate_base var1 abstract_domain' annotate_expr1 is_annotated_for1).
          Local Notation annotate_base2 := (@ident.annotate_base var2 abstract_domain' annotate_expr2 is_annotated_for2).
          Local Notation annotate_with_expr1 := (@ident.annotate_with_expr var1 abstract_domain' annotate_expr1 is_annotated_for1).
          Local Notation annotate_with_expr2 := (@ident.annotate_with_expr var2 abstract_domain' annotate_expr2 is_annotated_for2).
          Local Notation interp_ident1 := (@ident.interp_ident var1 abstract_domain' annotate_expr1 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for1 strip_annotation1).
          Local Notation interp_ident2 := (@ident.interp_ident var2 abstract_domain' annotate_expr2 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for2 strip_annotation2).
          Local Notation reflect1 := (@reflect base.type ident var1 abstract_domain' annotate1 bottom').
          Local Notation reflect2 := (@reflect base.type ident var2 abstract_domain' annotate2 bottom').

          Lemma wf_update_annotation G {t} st1 st2 (Hst : abstract_domain'_R t st1 st2) e1 e2 (He : expr.wf G e1 e2)
            : expr.wf G (@update_annotation1 t st1 e1) (@update_annotation2 t st2 e2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper is_annotated_for_Proper.
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
                           | break_innermost_match_step
                           | solve [ wf_t ]
                           | match goal with
                             | [ H : abstract_domain'_R _ ?x ?y, H1 : annotate_expr1 _ ?x = _, H2 : annotate_expr2 _ ?y = _ |- _ ]
                               => let H' := fresh in
                                  pose proof (annotate_expr_Proper _ _ _ H) as H';
                                  rewrite H1, H2 in H'; clear H1 H2; cbv [option_eq] in H'
                             | [ H1 : is_annotated_for1 _ _ ?e1 ?s1 = _,
                                      H2 : is_annotated_for2 _ _ ?e2 ?s2 = _ ,
                                           Hwf : expr.wf _ ?e1 ?e2,
                                                 Hrel : abstract_domain'_R _ ?s1 ?s2 |- _ ]
                               => let H' := fresh in
                                  pose proof (is_annotated_for_Proper _ _ _ _ _ Hwf _ _ Hrel) as H';
                                  rewrite H1, H2 in H'; clear H1 H2
                             end ].
          Qed.

          Lemma wf_annotate_with_expr
                is_let_bound t G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate_with_expr1 is_let_bound t v1 e1) (@annotate_with_expr2 is_let_bound t v2 e2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper is_annotated_for_Proper.
            cbv [ident.annotate_with_expr]; break_innermost_match; repeat constructor; apply wf_update_annotation; assumption.
          Qed.

          Lemma wf_annotate_base
                is_let_bound (t : base.type.base) G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate_base1 is_let_bound t v1 e1) (@annotate_base2 is_let_bound t v2 e2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper is_annotated_for_Proper.
            cbv [ident.annotate_base];
              repeat first [ apply wf_annotate_with_expr
                           | break_innermost_match_step
                           | progress subst
                           | progress cbv [type_base ident.smart_Literal] in *
                           | progress cbn [invert_Literal] in *
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

          Local Opaque ident.ident_Some ident.ident_None.
          Lemma wf_annotate
                is_let_bound t G
                v1 v2 (Hv : abstract_domain'_R t v1 v2)
                e1 e2 (He : expr.wf G e1 e2)
            : UnderLets.wf (fun G' => expr.wf G') G (@annotate1 is_let_bound t v1 e1) (@annotate2 is_let_bound t v2 e2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            revert dependent G; induction t; intros;
              cbn [ident.annotate]; try apply wf_annotate_base; trivial.
            all: try solve [ repeat first [ lazymatch goal with
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
                                | [ H : context[invert_pair ?e] |- _ ]
                                  => let lem := lazymatch e with
                                                | (?x, ?y)%expr => constr:(expr.invert_pair_ident_pair(v1:=x) (v2:=y) : invert_pair e = _)
                                                end in
                                     rewrite lem in H
                                end
                              | apply wf_annotate_with_expr
                              | apply DefaultValue.expr.base.wf_default
                              | apply DefaultValue.expr.wf_default
                              | progress expr.invert_subst
                              | progress cbn [ident.annotate ident.smart_Literal invert_Literal invert_pair invert_AppIdent2 invert_App2 fst snd projT2 projT1 eq_rect Option.bind] in *
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
                                | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map_ex in H
                                | [ H : context[List.nth_error (List.combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                                | [ |- context[List.nth_error (List.combine _ _) _] ] => rewrite nth_error_combine
                                | [ H : forall x y, Some _ = Some _ -> Some _ = Some _ -> _ |- _ ]
                                  => specialize (H _ _ eq_refl eq_refl)
                                | [ H : forall v1 v2, List.In (v1, v2) (List.combine ?l1 ?l2) -> ?R v1 v2, H' : List.nth_error ?l1 ?n = Some ?a1, H'' : List.nth_error ?l2 ?n = Some ?a2
                                                                                                                                                  |- ?R ?a1 ?a2 ]
                                  => apply H
                                | [ H : List.nth_error ?l ?n' = Some ?v |- List.In (?v, _) (List.combine ?l _) ] => apply nth_error_In with (n:=n')
                                | [ H : length ?x = length ?y |- context[length ?x] ] => rewrite H
                                end
                              | handle_Forall2_step
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
                              | solve [ wf_t ] ] ].
          Qed.
          Local Ltac type_of_value v :=
            lazymatch v with
            | (abstract_domain ?t * _)%type => t
            | (?a -> UnderLets _ ?b)
              => let a' := type_of_value a in
                let b' := type_of_value b in
                constr:(type.arrow a' b')
            end.
          Local Opaque ident.ident_Literal.
          Lemma wf_interp_ident_nth_default (annotate_with_state : bool) G T
            : wf_value_with_lets G (@interp_ident1 annotate_with_state _ (@ident.List_nth_default T)) (@interp_ident2 annotate_with_state _ (@ident.List_nth_default T)).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            cbv [wf_value_with_lets wf_value ident.interp_ident]; constructor; cbn -[abstract_domain_R abstract_domain].
            { intros; subst.
              destruct_head'_prod; destruct_head'_and; cbn [fst snd] in *.
              repeat first [ progress subst
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
                             | [ H : ident.ident_Literal _ = ident.ident_Literal _ |- _ ]
                               => apply (f_equal (fun idc => invert_Literal (var:=var1) (#idc))) in H; rewrite !expr.invert_Literal_ident_Literal in H
                             | [ H : _ = _ :> ident _ |- _ ] => inversion H; clear H
                             | [ H : List.nth_error _ _ = None |- _ ] => apply List.nth_error_None in H
                             | [ H : List.nth_error _ _ = Some _ |- _ ]
                               => unique pose proof (@ListUtil.nth_error_value_length _ _ _ _ H);
                                  unique pose proof (@ListUtil.nth_error_value_In _ _ _ _ H)
                             | [ H : context[List.In _ (List.map _ _)] |- _ ] => rewrite List.in_map_iff in H
                             | [ H : (?x <= ?y)%nat, H' : (?y < ?x)%nat |- _ ] => exfalso; clear -H H'; lia
                             | [ H : (?x <= ?y)%nat, H' : (?y < ?x')%nat, H'' : ?x' = ?x |- _ ] => exfalso; clear -H H' H''; lia
                             | [ H : length ?x = length ?y |- context[length ?x] ] => rewrite H
                             | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map_ex in H
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
                           | handle_Forall2_step
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

          Lemma wf_interp_ident_not_nth_default_nostrip (annotate_with_state : bool) G {t} (idc : ident t)
            : wf_value_with_lets G (Base (reflect1 annotate_with_state (###idc)%expr (abstract_interp_ident _ idc))) (Base (reflect2 annotate_with_state (###idc)%expr (abstract_interp_ident _ idc))).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            constructor; eapply wf_reflect;
              solve [ apply bottom'_Proper
                    | apply wf_annotate
                    | repeat constructor
                    | apply abstract_interp_ident_Proper; reflexivity ].
          Qed.

          Lemma wf_interp_ident_not_nth_default (annotate_with_state : bool) G {t} (idc : ident t)
            : (wf_value_with_lets G)
                (Base match strip_annotation1 _ idc with
                      | Some v => v
                      | None => reflect1 annotate_with_state (###idc)%expr (abstract_interp_ident _ idc)
                      end)
                (Base match strip_annotation2 _ idc with
                      | Some v => v
                      | None => reflect2 annotate_with_state (###idc)%expr (abstract_interp_ident _ idc)
                      end).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper wf_strip_annotation.
            pose proof (wf_strip_annotation G _ idc).
            break_innermost_match; cbn [option_eq] in *;
              solve [ exfalso; assumption
                    | congruence
                    | apply wf_interp_ident_not_nth_default_nostrip
                    | constructor; assumption ].
          Qed.

          Lemma wf_interp_ident G {t} idc1 idc2 (Hidc : idc1 = idc2) (annotate_with_state : bool)
            : wf_value_with_lets G (@interp_ident1 annotate_with_state t idc1) (@interp_ident2 annotate_with_state t idc2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper wf_strip_annotation.
            cbv [wf_value_with_lets ident.interp_ident]; subst idc2; destruct idc1;
              first [ apply wf_interp_ident_nth_default
                    | apply wf_interp_ident_not_nth_default ].
          Qed.

          Local Notation strip_all_annotations'1 := (@partial.ident.strip_all_annotations' var1 annotation_to_cast1 skip_annotations_under).
          Local Notation strip_all_annotations'2 := (@partial.ident.strip_all_annotations' var2 annotation_to_cast2 skip_annotations_under).
          Local Notation strip_all_annotations1 := (@partial.ident.strip_all_annotations var1 annotation_to_cast1 skip_annotations_under).
          Local Notation strip_all_annotations2 := (@partial.ident.strip_all_annotations var2 annotation_to_cast2 skip_annotations_under).
          Lemma wf_strip_all_annotations' G t e1 e2 (Hwf : expr.wf G e1 e2)
            : forall should_strip, expr.wf G (@strip_all_annotations'1 should_strip t e1) (@strip_all_annotations'2 should_strip t e2).
          Proof using wf_annotation_to_cast.
            induction Hwf; cbn [partial.ident.strip_all_annotations'];
              repeat first [ progress cbn [projT1 projT2 fst snd] in *
                           | progress type.inversion_type
                           | progress wf_safe_t
                           | progress break_innermost_match
                           | progress expr.invert_subst
                           | discriminate
                           | solve [ exfalso; eauto
                                   | eassert (Some _ = None) by eauto; congruence ]
                           | match goal with
                             | [ H1 : annotation_to_cast1 ?s ?d ?e1 = _, H2 : annotation_to_cast2 ?s ?d ?e2 = _ |- _ ]
                               => let H := fresh in
                                  pose proof (fun G => wf_annotation_to_cast s d G e1 e2) as H;
                                  rewrite H1, H2 in H; cbv [option_eq] in H;
                                  clear H1 H2
                             end ].
          Qed.

          Lemma wf_strip_all_annotations G t e1 e2 (Hwf : expr.wf G e1 e2)
            : expr.wf G (@strip_all_annotations1 t e1) (@strip_all_annotations2 t e2).
          Proof using wf_annotation_to_cast. now apply wf_strip_all_annotations'. Qed.

          Local Notation eval_with_bound1 := (@partial.ident.eval_with_bound var1 abstract_domain' annotate_expr1 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for1 strip_annotation1 skip_annotations_under).
          Local Notation eval_with_bound2 := (@partial.ident.eval_with_bound var2 abstract_domain' annotate_expr2 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for2 strip_annotation2 skip_annotations_under).
          Lemma wf_eval_with_bound (annotate_with_state : bool) {t} G G' e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
                (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
            : expr.wf G' (@eval_with_bound1 annotate_with_state t e1 st1) (@eval_with_bound2 annotate_with_state t e2 st2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper wf_strip_annotation.
            eapply wf_eval_with_bound';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.

          Local Notation eval1 := (@partial.ident.eval var1 abstract_domain' annotate_expr1 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for1 strip_annotation1).
          Local Notation eval2 := (@partial.ident.eval var2 abstract_domain' annotate_expr2 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for2 strip_annotation2).
          Lemma wf_eval {t} G G' e1 e2 (Hwf : expr.wf G e1 e2)
                (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
            : expr.wf G' (@eval1 t e1) (@eval2 t e2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper wf_strip_annotation.
            eapply wf_eval';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.

          Local Notation eta_expand_with_bound1 := (@partial.ident.eta_expand_with_bound var1 abstract_domain' annotate_expr1 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for1).
          Local Notation eta_expand_with_bound2 := (@partial.ident.eta_expand_with_bound var2 abstract_domain' annotate_expr2 bottom' abstract_interp_ident extract_list_state extract_option_state is_annotated_for2).
          Lemma wf_eta_expand_with_bound {t} G e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
            : expr.wf G (@eta_expand_with_bound1 t e1 st1) (@eta_expand_with_bound2 t e2 st2).
          Proof using abstract_interp_ident_Proper annotate_expr_Proper bottom'_Proper extract_list_state_length extract_list_state_rel extract_option_state_rel is_annotated_for_Proper.
            eapply wf_eta_expand_with_bound';
              solve [ eassumption
                    | eapply wf_annotate
                    | eapply wf_interp_ident ].
          Qed.
        End with_var2.
      End with_type.
    End ident.

    Section specialized.
      Import API.
      Local Notation abstract_domain' := ZRange.type.base.option.interp (only parsing).
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Local Notation abstract_domain'_R t := (@eq (abstract_domain' t)) (only parsing).
      Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' (fun t => abstract_domain'_R t)).
      Local Notation wf_value := (@wf_value base.type ident abstract_domain' (fun t => abstract_domain'_R t)).

      Lemma annotate_expr_Proper {relax_zrange var1 var2} {t} s1 s2
        : abstract_domain'_R t s1 s2
          -> option_eq (expr.wf nil)
                       (@annotate_expr relax_zrange var1 t s1)
                       (@annotate_expr relax_zrange var2 t s2).
      Proof using Type.
        intros ?; subst s2.
        cbv [annotate_expr Crypto.Util.Option.bind option_eq]; break_innermost_match;
          repeat constructor.
      Qed.

      Global Instance bottom'_Proper {t} : Proper (abstract_domain'_R t) (bottom' t).
      Proof using Type. reflexivity. Qed.

      Global Instance abstract_interp_ident_Proper {opts : AbstractInterpretation.Options} {assume_cast_truncates : bool} {t}
        : Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident assume_cast_truncates t).
      Proof using Type.
        cbv [abstract_interp_ident abstract_domain_R type.related respectful type.interp]; intros idc idc' ?; subst idc'; destruct idc;
          repeat first [ reflexivity
                       | progress subst
                       | progress cbn [ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp Crypto.Util.Option.bind] in *
                       | progress cbv [Crypto.Util.Option.bind]
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
      Proof using Type.
        intros st st' ?; subst st'; cbv [option_eq extract_list_state]; break_innermost_match; reflexivity.
      Qed.

      Local Notation tZ := (base.type.type_base base.type.Z).
      Local Notation cstZ r
        := (expr.App
              (d:=type.arrow (type.base tZ) (type.base tZ))
              (expr.Ident ident.Z_cast)
              (expr.Ident (@ident.Literal base.type.zrange r%zrange))).
      Local Notation cstZZ r1 r2
        := (expr.App
              (d:=type.arrow (type.base (tZ * tZ)) (type.base (tZ * tZ)))
              (expr.Ident ident.Z_cast2)
              (#(@ident.Literal base.type.zrange r1%zrange), #(@ident.Literal base.type.zrange r2%zrange))%expr_pat).

      Lemma wf_always_strip_annotation {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) {var1 var2} G {t} idc
        : option_eq (wf_value G)
                    (always_strip_annotation assume_cast_truncates (var:=var1) t idc)
                    (always_strip_annotation assume_cast_truncates (var:=var2) t idc).
      Proof using Type.
        cbv [always_strip_annotation]; break_innermost_match; try reflexivity;
          cbn [option_eq wf_value].
        all: repeat first [ progress intros
                          | assumption
                          | progress subst
                          | exfalso; congruence
                          | progress cbn [fst snd] in *
                          | progress break_innermost_match
                          | progress destruct_head'_and
                          | match goal with
                            | [ |- UnderLets.wf _ _ (Base _) (Base _) ] => constructor
                            | [ |- _ /\ _ ] => split
                            end
                          | solve [ wf_t ]
                          | progress cbn [abstract_domain_R type.related] in * ].
      Qed.

      Lemma wf_strip_annotation {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) (strip_annotations : bool) {var1 var2} G {t} idc
        : option_eq (wf_value G)
                    (strip_annotation assume_cast_truncates strip_annotations (var:=var1) t idc)
                    (strip_annotation assume_cast_truncates strip_annotations (var:=var2) t idc).
      Proof using Type.
        cbv [strip_annotation]; break_innermost_match; now try apply wf_always_strip_annotation.
      Qed.

      Local Arguments base.try_make_transport_cps / _ _ _.
      Local Arguments type.try_make_transport_cps / _ _ _ _ _.
      Lemma is_annotated_for_spec {relax_zrange var} t t' e st
        : @is_annotated_for relax_zrange var t t' e st = true
          <-> ((exists (pf : t' = tZ) r,
                   (annotation_of_state relax_zrange (rew pf in st) = Some r)
                   /\ existT (@expr var) t e = existT (@expr var) _ (cstZ r))
               \/ (exists (pf : t' = (tZ * tZ)%etype) r1 r2,
                      ((fun '(r1, r2) => (annotation_of_state relax_zrange r1, annotation_of_state relax_zrange r2))
                         (rew pf in st) = (Some r1, Some r2))
                      /\ existT (@expr var) t e = existT (@expr var) _ (cstZZ r1 r2))).
      Proof using Type.
        split.
        { cbv [is_annotated_for]; break_innermost_match; try discriminate.
          all: rewrite ?Bool.andb_true_iff.
          all: intro; destruct_head'_and; reflect_beq_to_eq (option_beq zrange_beq).
          all: constructor; exists eq_refl; cbn [eq_rect].
          all: repeat esplit; try apply (f_equal2 (@pair _ _)); try (symmetry; eassumption).
          all: multimatch goal with
               | [ H : invert_Z_cast _ = Some _ |- _ ]
                 => apply expr.invert_Z_cast_Some in H
               | [ H : invert_Z_cast2 _ = Some _ |- _ ]
                 => apply expr.invert_Z_cast2_Some in H
               end;
            solve [ repeat first [ progress inversion_sigma
                                 | progress subst
                                 | progress cbn [eq_rect] in *
                                 | reflexivity ] ]. }
        { repeat first [ progress intros
                       | progress subst
                       | progress cbn [eq_rect fst snd] in *
                       | progress inversion_option
                       | progress inversion_sigma
                       | progress inversion_prod
                       | progress destruct_head'_ex
                       | progress destruct_head'_and
                       | progress destruct_head'_or
                       | progress cbn
                       | break_innermost_match_step
                       | rewrite Bool.andb_true_iff
                       | apply conj
                       | apply zrange_lb
                       | reflexivity ]. }
      Qed.

      Lemma is_annotated_for_Proper {relax_zrange var1 var2} G t t' e1 e2
        : expr.wf G e1 e2
          -> ((abstract_domain'_R _ ==> eq)%signature)
               (@is_annotated_for relax_zrange var1 t t' e1)
               (@is_annotated_for relax_zrange var2 t t' e2).
      Proof using Type.
        repeat intro; subst;
          match goal with |- ?x = ?y => destruct x eqn:?, y eqn:? end.
        all: repeat first [ match goal with
                            | [ H : is_annotated_for _ _ _ _ _ = true |- _ ]
                              => rewrite is_annotated_for_spec in H
                            | [ H : ?x <> ?x |- _ ] => congruence
                            end
                          | reflexivity
                          | exfalso; assumption
                          | progress cbn [eq_rect fst snd projT1 projT2 andb] in *
                          | progress subst
                          | progress inversion_prod
                          | progress destruct_head'_ex
                          | progress destruct_head'_sig
                          | progress destruct_head'_sigT
                          | progress destruct_head'_prod
                          | progress destruct_head'_and
                          | progress reflect_beq_to_eq zrange_beq
                          | progress inversion_sigma
                          | progress inversion_option
                          | progress destruct_head'_or
                          | progress inversion_type
                          | progress expr.inversion_wf_one_constr
                          | progress expr.invert_subst
                          | progress expr.invert_match
                          | progress expr.inversion_expr
                          | break_innermost_match_hyps_step
                          | match goal with
                            | [ H : is_annotated_for _ _ _ _ _ = false |- _ ]
                              => progress cbn in H
                            end ].
      Qed.

      Lemma wf_annotation_to_cast_helper {var1 var2 t G idc1 idc2}
            (Hidc : idc1 = idc2)
        : option_eq (fun f g => forall e1 e2, expr.wf G e1 e2 -> expr.wf G (f e1) (g e2))
                    (@annotation_to_cast_helper var1 t idc1)
                    (@annotation_to_cast_helper var2 t idc2).
      Proof using Type.
        subst idc2; destruct idc1; cbv; try reflexivity; intros; assumption.
      Qed.

      Lemma wf_annotation_to_cast {var1 var2 s d G e1 e2}
            (Hwf : expr.wf G e1 e2)
        : option_eq (fun f g => forall e1 e2, expr.wf G e1 e2 -> expr.wf G (f e1) (g e2))
                    (@annotation_to_cast var1 s d e1)
                    (@annotation_to_cast var2 s d e2).
      Proof using Type.
        cbv [annotation_to_cast];
          repeat first [ progress wf_safe_t
                       | congruence
                       | progress inversion_option
                       | progress cbn [fst snd projT1 projT2] in *
                       | progress cbv [Option.bind] in *
                       | progress break_innermost_match
                       | progress break_innermost_match_hyps
                       | progress expr.invert_subst
                       | progress expr.inversion_wf_one_constr
                       | progress cbn [invert_AppIdent invert_App invert_Ident invert_App_cps invert_AppIdent_cps Option.bind] in *
                       | progress expr.invert_match
                       | progress expr.inversion_expr
                       | now refine (wf_annotation_to_cast_helper eq_refl) ].
      Qed.

      Lemma extract_list_state_length
        : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_map (@length _) (extract_list_state t v1) = option_map (@length _) (extract_list_state t v2).
      Proof using Type.
        intros; subst; cbv [option_map extract_list_state]; break_innermost_match; reflexivity.
      Qed.
      Lemma extract_list_state_rel
        : forall t v1 v2, abstract_domain'_R _ v1 v2 -> forall l1 l2, extract_list_state t v1 = Some l1 -> extract_list_state t v2 = Some l2 -> List.Forall2 (@abstract_domain'_R t) l1 l2.
      Proof using Type.
        intros; cbv [extract_list_state] in *; subst; inversion_option; subst.
        now rewrite Forall2_Forall, Forall_forall; cbv [Proper].
      Qed.

      Lemma extract_option_state_rel
        : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_eq (option_eq (abstract_domain'_R _)) (extract_option_state t v1) (extract_option_state t v2).
      Proof using Type.
        cbv [extract_option_state option_eq]; intros; subst; break_match; reflexivity.
      Qed.

      Section with_var2.
        Context {var1 var2 : type -> Type}.
        Local Notation wf_value_with_lets := (@wf_value_with_lets base.type ident abstract_domain' (fun t => abstract_domain'_R t) var1 var2).

        Lemma wf_eval {opts : AbstractInterpretation.Options} {t} G G' e1 e2 (Hwf : expr.wf G e1 e2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (t:=t) (eval (var:=var1) e1) (eval (var:=var2) e2).
        Proof using Type.
          eapply ident.wf_eval;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel
                  | apply extract_option_state_rel
                  | apply wf_strip_annotation
                  | intros; now apply annotate_expr_Proper
                  | apply is_annotated_for_Proper ].
        Qed.

        Lemma wf_strip_all_annotations strip_annotations_under G t e1 e2 (Hwf : expr.wf G e1 e2)
          : expr.wf G (@strip_all_annotations strip_annotations_under var1 t e1) (@strip_all_annotations strip_annotations_under var2 t e2).
        Proof using Type. revert Hwf; apply ident.wf_strip_all_annotations, @wf_annotation_to_cast. Qed.

        Lemma wf_eval_with_bound {opts : AbstractInterpretation.Options} {relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations t} G G' e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (var1:=var1) (var2:=var2) (t:=t)
                    (eval_with_bound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e1 st1)
                    (eval_with_bound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e2 st2).
        Proof using Type.
          eapply ident.wf_eval_with_bound;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel
                  | apply extract_option_state_rel
                  | apply wf_strip_annotation
                  | intros; now apply annotate_expr_Proper
                  | apply is_annotated_for_Proper ].
        Qed.

        Lemma wf_strip_annotations {opts : AbstractInterpretation.Options} {assume_cast_truncates} {t} G G' e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
              (HGG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value_with_lets G' v1 v2)
          : expr.wf G' (t:=t) (strip_annotations assume_cast_truncates (var:=var1) e1 st1) (strip_annotations assume_cast_truncates (var:=var2) e2 st2).
        Proof using Type.
          eapply ident.wf_eval_with_bound;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel
                  | apply extract_option_state_rel
                  | apply wf_strip_annotation
                  | intros; now apply annotate_expr_Proper
                  | apply is_annotated_for_Proper ].
        Qed.

        Lemma wf_eta_expand_with_bound {relax_zrange t} G e1 e2 (Hwf : expr.wf G e1 e2) st1 st2 (Hst : type.and_for_each_lhs_of_arrow (@abstract_domain_R) st1 st2)
          : expr.wf G (t:=t) (eta_expand_with_bound relax_zrange (var:=var1) e1 st1) (eta_expand_with_bound relax_zrange (var:=var2) e2 st2).
        Proof using Type.
          eapply ident.wf_eta_expand_with_bound;
            solve [ eassumption
                  | exact _
                  | apply extract_list_state_length
                  | apply extract_list_state_rel
                  | apply extract_option_state_rel
                  | intros; now apply annotate_expr_Proper
                  | apply is_annotated_for_Proper ].
        Qed.
      End with_var2.

      Lemma Wf_StripAllAnnotations strip_annotations_under {t} (e : Expr t) (Hwf : Wf e) : Wf (StripAllAnnotations strip_annotations_under e).
      Proof using Type.
        intros ??; now apply wf_strip_all_annotations.
      Qed.

      Lemma Wf_Eval {opts : AbstractInterpretation.Options} {t} (e : Expr t) (Hwf : Wf e) : Wf (Eval e).
      Proof using Type.
        intros ??; eapply wf_eval with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Lemma Wf_EvalWithBound {opts : AbstractInterpretation.Options} {relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EvalWithBound relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e bound).
      Proof using Type.
        intros ??; eapply wf_eval_with_bound with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Lemma Wf_StripAnnotations {opts : AbstractInterpretation.Options} {assume_cast_truncates} {t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (StripAnnotations assume_cast_truncates e bound).
      Proof using Type.
        intros ??; eapply wf_strip_annotations with (G:=nil); cbn [List.In]; try tauto; apply Hwf.
      Qed.

      Lemma Wf_EtaExpandWithBound {relax_zrange t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EtaExpandWithBound relax_zrange e bound).
      Proof using Type.
        intros ??; eapply wf_eta_expand_with_bound with (G:=nil); cbn [List.In]; try apply Hwf; tauto.
      Qed.

      Local Instance Proper_strip_ranges {t}
        : Proper (@abstract_domain_R t ==> @abstract_domain_R t) (@ZRange.type.option.strip_ranges t).
      Proof using Type.
        cbv [Proper abstract_domain_R respectful].
        induction t as [t|s IHs d IHd]; cbn in *; destruct_head'_prod; destruct_head'_and; cbn in *; intros; subst; cbv [respectful] in *;
          eauto.
      Qed.

      Lemma Wf_EtaExpandWithListInfoFromBound {t} (e : Expr t) bound (Hwf : Wf e) (bound_valid : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R)) bound)
        : Wf (EtaExpandWithListInfoFromBound e bound).
      Proof using Type.
        eapply Wf_EtaExpandWithBound; [ assumption | ].
        clear dependent e.
        cbv [Proper] in *; induction t as [t|s IHs d IHd]; cbn in *; destruct_head'_prod; destruct_head'_and; cbn in *; eauto.
        split; auto; apply Proper_strip_ranges; auto.
      Qed.
    End specialized.
  End partial.
  Hint Resolve Wf_Eval Wf_EvalWithBound Wf_EtaExpandWithBound Wf_EtaExpandWithListInfoFromBound Wf_StripAllAnnotations Wf_StripAnnotations : wf.
  Hint Opaque partial.Eval partial.EvalWithBound partial.EtaExpandWithBound partial.EtaExpandWithListInfoFromBound partial.StripAnnotations partial.StripAllAnnotations : wf interp rewrite.
  Import API.

  Lemma Wf_PartialEvaluateWithListInfoFromBounds
        {opts : AbstractInterpretation.Options}
        {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithListInfoFromBounds E b_in).
  Proof. cbv [PartialEvaluateWithListInfoFromBounds]; eauto with wf. Qed.
  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf.
  Hint Opaque PartialEvaluateWithListInfoFromBounds : wf interp rewrite.

  Lemma Wf_PartialEvaluateWithBounds
        {opts : AbstractInterpretation.Options}
        {relax_zrange} {assume_cast_truncates : bool} {skip_annotations_under : forall t, ident t -> bool} {strip_preexisting_annotations : bool} {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in).
  Proof. cbv [PartialEvaluateWithBounds]; eauto with wf. Qed.
  Hint Resolve Wf_PartialEvaluateWithBounds : wf.
  Hint Opaque PartialEvaluateWithBounds : wf interp rewrite.
End Compilers.
