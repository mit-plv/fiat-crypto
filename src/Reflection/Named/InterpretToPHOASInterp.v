Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Wf.
Require Import Crypto.Reflection.Named.ContextDefinitions.
Require Import Crypto.Reflection.Named.ContextProperties.
Require Import Crypto.Reflection.Named.InterpretToPHOAS.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.

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
            {ContextOk : ContextOk Context}.

    Lemma interpf_interpf_to_phoas
          (ctx : Context)
          {t} (e : @Named.exprf base_type_code op Name t)
          (Hwf : prop_of_option (Named.wff ctx e))
      : Named.interpf (interp_op:=interp_op) (ctx:=ctx) e
        = Some (Syntax.interpf interp_op (interpf_to_phoas ctx e Hwf)).
    Proof.
      revert dependent ctx; induction e;
        repeat first [ progress intros
                     | progress subst
                     | progress inversion_option
                     | progress break_innermost_match_step
                     | progress unfold option_map, LetIn.Let_In in *
                     | apply (f_equal (@Some _))
                     | apply (f_equal (@interp_op _ _ _))
                     | progress simpl in *
                     | solve [ eauto | congruence ]
                     | match goal with
                       | [ H : forall ctx Hwf', Named.interpf ?e = Some _, Hwf : prop_of_option (Named.wff _ ?e) |- _ ]
                         => specialize (H _ Hwf)
                       end ].
    Qed.

    Lemma interp_interp_to_phoas
          (ctx : Context)
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf : Named.wf ctx e)
          v
      : Named.interp (interp_op:=interp_op) (ctx:=ctx) e v
        = Some (Syntax.interp interp_op (interp_to_phoas ctx e Hwf) v).
    Proof.
      unfold interp, interp_to_phoas, Named.interp; apply interpf_interpf_to_phoas.
    Qed.
  End with_context.

  Section all.
    Context {Context : forall var, @Context base_type_code Name var}
            {ContextOk : forall var, ContextOk (Context var)}.

    Lemma Interp_InterpToPHOAS_gen
          {ctx : forall var, Context var}
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf : forall var, Named.wf (ctx var) e)
          v
      : Named.interp (interp_op:=interp_op) (ctx:=ctx _) e v
        = Some (Interp interp_op (InterpToPHOAS_gen ctx e Hwf) v).
    Proof. apply interp_interp_to_phoas. Qed.

    Lemma Interp_InterpToPHOAS
          {t} (e : @Named.expr base_type_code op Name t)
          (Hwf : Named.Wf Context e)
          v
      : Named.interp (Context:=Context _) (interp_op:=interp_op) (ctx:=empty) e v
        = Some (Interp interp_op (InterpToPHOAS e Hwf) v).
    Proof. apply interp_interp_to_phoas. Qed.
  End all.
End language.
