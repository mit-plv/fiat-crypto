Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.ContextProperties.SmartMap.
Require Import Crypto.Compilers.Named.InterpretToPHOAS.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {base_type_code_dec : DecidableRel (@eq base_type_code)}
          {Name_dec : DecidableRel (@eq Name)}.
  Section with_var.
    Context {var1 var2 : base_type_code -> Type}
            {Context1 : Context Name var1}
            {Context2 : Context Name var2}
            {Context1Ok : ContextOk Context1}
            {Context2Ok : ContextOk Context2}
            (failb1 : forall t, @Syntax.exprf base_type_code op var1 (Tbase t))
            (failb2 : forall t, @Syntax.exprf base_type_code op var2 (Tbase t)).

    Local Ltac t_step :=
      first [ progress intros
            | progress unfold dec in *
            | reflexivity
            | progress subst
            | progress inversion_option
            | erewrite lookupb_extend by assumption
            | rewrite <- !find_Name_and_val_None_iff
            | progress break_innermost_match_step
            | progress break_match_hyps
            | solve [ eauto using find_Name_and_val_flatten_binding_list ]
            | congruence
            | tauto
            | match goal with
              | [ H : lookupb (extend _ _ _) _ = _ |- _ ]
                => erewrite (lookupb_extend _ _ _) in H by assumption
              | [ H : context[List.In _ (_ ++ _)] |- _ ]
                => setoid_rewrite List.in_app_iff in H
              | [ |- context[List.In _ (_ ++ _)] ]
                => rewrite List.in_app_iff
              | [ |- context[find_Name_and_val ?tdec ?ndec ?a ?b ?c ?d ?default] ]
                => lazymatch default with None => fail | _ => idtac end;
                   rewrite (find_Name_and_val_split tdec ndec (default:=default))
              | [ H : context[find_Name_and_val ?tdec ?ndec ?a ?b ?c ?d ?default] |- _ ]
                => lazymatch default with None => fail | _ => idtac end;
                   rewrite (find_Name_and_val_split tdec ndec (default:=default)) in H
              | [ H : forall n t, lookupb _ n = None <-> lookupb _ n = None |- context[lookupb _ _ = None] ]
                => rewrite H
              | [ H : forall n t, lookupb _ n = None |- context[lookupb _ _ = None] ]
                => rewrite H
              end ].
    Local Ltac t := repeat t_step.

    Lemma wff_interpf_to_phoas
          (ctx1 : Context1) (ctx2 : Context2)
          {t} (e : @Named.exprf base_type_code op Name t)
          (Hwf1 : prop_of_option (Named.wff ctx1 e))
          (Hwf2 : prop_of_option (Named.wff ctx2 e))
          G
          (HG : forall n t v1 v2,
              lookupb t ctx1 n = Some v1
              -> lookupb t ctx2 n = Some v2
              -> List.In (existT _ t (v1, v2)%core) G)
          (Hctx1_ctx2 : forall n t,
              lookupb t ctx1 n = None <-> lookupb t ctx2 n = None)
      : wff G (interpf_to_phoas failb1 ctx1 e) (interpf_to_phoas failb2 ctx2 e).
    Proof using Context1Ok Context2Ok Name_dec base_type_code_dec.
      revert dependent G; revert dependent ctx1; revert dependent ctx2; induction e;
        repeat first [ progress intros
                     | progress destruct_head' and
                     | progress break_innermost_match_step
                     | progress simpl in *
                     | progress autorewrite with push_prop_of_option in *
                     | solve [ eauto | tauto ]
                     | match goal with
                       | [ |- wff _ _ _ ] => constructor
                       end ].
      match goal with H : _ |- _ => eapply H end; t.
    Qed.

    Lemma wf_interp_to_phoas_gen
          (ctx1 : Context1) (ctx2 : Context2)
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf1 : Named.wf ctx1 e)
          (Hwf2 : Named.wf ctx2 e)
          (Hctx1 : forall n t, lookupb t ctx1 n = None)
          (Hctx2 : forall n t, lookupb t ctx2 n = None)
      : wf (interp_to_phoas failb1 ctx1 e) (interp_to_phoas failb2 ctx2 e).
    Proof using Context1Ok Context2Ok Name_dec base_type_code_dec.
      constructor; intros.
      apply wff_interpf_to_phoas; t.
    Qed.

    Lemma wf_interp_to_phoas
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf1 : Named.wf (Context:=Context1) empty e)
          (Hwf2 : Named.wf (Context:=Context2) empty e)
      : wf (interp_to_phoas (Context:=Context1) failb1 empty e) (interp_to_phoas (Context:=Context2) failb2 empty e).
    Proof using Context1Ok Context2Ok Name_dec base_type_code_dec.
      apply wf_interp_to_phoas_gen; auto using lookupb_empty.
    Qed.
  End with_var.

  Section all.
    Context {Context : forall var, @Context base_type_code Name var}
            {ContextOk : forall var, ContextOk (Context var)}
            (failb : forall var t, @Syntax.exprf base_type_code op var (Tbase t)).

    Lemma Wf_InterpToPHOAS_gen
          {ctx : forall var, Context var}
          {t} (e : @Named.expr base_type_code op Name t)
          (Hctx : forall var n t, lookupb t (ctx var) n = None)
          (Hwf : forall var, Named.wf (ctx var) e)
      : Wf (InterpToPHOAS_gen failb ctx e).
    Proof using ContextOk Name_dec base_type_code_dec.
      intros ??; apply wf_interp_to_phoas_gen; auto.
    Qed.

    Lemma Wf_InterpToPHOAS
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf : Named.Wf Context e)
      : Wf (InterpToPHOAS (Context:=Context) failb e).
    Proof using ContextOk Name_dec base_type_code_dec.
      intros ??; apply wf_interp_to_phoas; auto.
    Qed.
  End all.
End language.

Hint Resolve Wf_InterpToPHOAS : wf.
