Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
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
          {Name_dec : DecidableRel (@eq Name)}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}.
  Section with_context.
    Context {Context : Context Name interp_base_type}
            {ContextOk : ContextOk Context}
            (failb : forall t, @Syntax.exprf base_type_code op interp_base_type (Tbase t)).

    Lemma interpf_interpf_to_phoas
          (ctx : Context)
          {t} (e : @Named.exprf base_type_code op Name t)
          (Hwf : prop_of_option (Named.wff ctx e))
      : Named.interpf (interp_op:=interp_op) (ctx:=ctx) e
        = Some (Syntax.interpf interp_op (interpf_to_phoas failb ctx e)).
    Proof using Type.
      revert dependent ctx; induction e;
        repeat first [ progress intros
                     | progress subst
                     | progress inversion_option
                     | progress destruct_head' and
                     | progress break_innermost_match_step
                     | progress unfold option_map, LetIn.Let_In in *
                     | apply (f_equal (@Some _))
                     | apply (f_equal (@interp_op _ _ _))
                     | progress simpl in *
                     | progress autorewrite with push_prop_of_option in *
                     | solve [ eauto | congruence | tauto ]
                     | match goal with
                       | [ H : forall ctx Hwf', Named.interpf ?e = Some _, Hwf : prop_of_option (Named.wff _ ?e) |- _ ]
                         => specialize (H _ Hwf)
                       | [ H : forall ctx Hwf, Named.interpf ?e = Some _ |- Named.interpf ?e = Some _ ]
                         => rewrite H by auto
                       end ].
    Qed.

    Lemma interp_interp_to_phoas
          (ctx : Context)
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf : Named.wf ctx e)
          v
      : Named.interp (interp_op:=interp_op) (ctx:=ctx) e v
        = Some (Syntax.interp interp_op (interp_to_phoas failb ctx e) v).
    Proof using Type.
      unfold interp, interp_to_phoas, Named.interp; apply interpf_interpf_to_phoas; auto.
    Qed.
  End with_context.

  Section all.
    Context {Context : forall var, @Context base_type_code Name var}
            {ContextOk : forall var, ContextOk (Context var)}
            (failb : forall var t, @Syntax.exprf base_type_code op var (Tbase t)).

    Lemma Interp_InterpToPHOAS_gen
          {ctx : forall var, Context var}
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf : forall var, Named.wf (ctx var) e)
          v
      : Named.interp (interp_op:=interp_op) (ctx:=ctx _) e v
        = Some (Interp interp_op (InterpToPHOAS_gen failb ctx e) v).
    Proof using Type. apply interp_interp_to_phoas; auto. Qed.

    Lemma Interp_InterpToPHOAS
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf : Named.Wf Context e)
          v
      : Named.Interp (Context:=Context _) (interp_op:=interp_op) e v
        = Some (Interp interp_op (InterpToPHOAS (Context:=Context) failb e) v).
    Proof using Type. apply interp_interp_to_phoas; auto. Qed.
  End all.
End language.
