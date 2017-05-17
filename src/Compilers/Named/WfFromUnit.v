Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.

Section language.
  Context {base_type_code Name : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {base_type_code_dec : DecidableRel (@eq base_type_code)}
          {Name_dec : DecidableRel (@eq Name)}.

  Section with_var.
    Context {var}
            (uContext : @Context base_type_code Name (fun _ => unit))
            (uContextOk : ContextOk uContext)
            (vContext : @Context base_type_code Name var)
            (vContextOk : ContextOk vContext).

    Local Ltac t :=
      repeat first [ progress simpl in *
                   | progress intros
                   | progress subst
                   | progress inversion_option
                   | congruence
                   | tauto
                   | solve [ eauto ]
                   | break_innermost_match_step
                   | break_innermost_match_hyps_step
                   | progress destruct_head'_and
                   | progress autorewrite with push_prop_of_option push_eq_Some_trivial in *
                   | rewrite !(@lookupb_extend base_type_code _ Name _) by auto
                   | rewrite (@find_Name_and_val_split base_type_code _ Name _) with (default := lookupb _ _)
                   | match goal with
                     | [ H : ?x = Some _ |- _ ]
                       => assert (x = None) by (split_iff; eauto); congruence
                     | [ |- _ /\ _ ] => split
                     | [ H : _ |- prop_of_option _ ] => eapply H; [ | eassumption ]; clear H
                     | [ |- context[find_Name_and_val ?tdec ?ndec ?b _ _ _ _ = None] ]
                       => rewrite <- !(@find_Name_and_val_None_iff _ tdec _ ndec _ b)
                     end ].

    Lemma wff_from_unit
          (vctx : vContext)
          (uctx : uContext)
          (Hctx : forall t n, lookupb t vctx n = None <-> lookupb t uctx n = None)
          {t} (e : @exprf base_type_code op Name t)
      : wff_unit uctx e = Some trivial -> prop_of_option (wff vctx e).
    Proof using Name_dec base_type_code_dec uContextOk vContextOk.
      revert uctx vctx Hctx; induction e; t.
    Qed.

    Lemma wf_from_unit
          (vctx : vContext)
          (uctx : uContext)
          (Hctx : forall t n, lookupb t vctx n = None <-> lookupb t uctx n = None)
          {t} (e : @expr base_type_code op Name t)
      : wf_unit uctx e = Some trivial -> wf vctx e.
    Proof using Name_dec base_type_code_dec uContextOk vContextOk.
      intros H ?; revert H; apply wff_from_unit; t.
    Qed.
  End with_var.

  Lemma Wf_from_unit
        (Context : forall var, @Context base_type_code Name var)
        (ContextOk : forall var, ContextOk (Context var))
        {t} (e : @expr base_type_code op Name t)
    : wf_unit (Context:=Context _) empty e = Some trivial -> Wf Context e.
  Proof using Name_dec base_type_code_dec.
    intros H ?; revert H; apply wf_from_unit; auto; intros.
    rewrite !lookupb_empty by auto; tauto.
  Qed.
End language.

Hint Resolve wf_from_unit Wf_from_unit wff_from_unit : wf.
