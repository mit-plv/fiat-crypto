Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import Rewriter.Compilers.
  Import expr.Notations.
  Import defaults.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    (*
    Module Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.

      Section with_var0.
        Context {base_type} {ident var : type.type base_type -> Type}.
        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Let type_base (t : base_type) : type := type.base t.
        Coercion type_base : base_type >-> type.
      End with_var0.

      Section full.
        Context {var : type.type base.type -> Type}.
        Local Notation expr := (@expr base.type ident).
        Local Notation value := (@Compile.value base.type ident var).
        Local Notation value_with_lets := (@Compile.value_with_lets base.type ident var).
        Local Notation UnderLets := (UnderLets.UnderLets base.type ident var).
        Local Notation reify_and_let_binds_cps := (@Compile.reify_and_let_binds_cps ident var (@UnderLets.reify_and_let_binds_base_cps var)).
        Local Notation reflect := (@Compile.reflect ident var).
        (*
        Section with_rewrite_head.
          Context (rewrite_head : forall t (idc : ident t), value_with_lets t).

        End with_rewrite_head.

        Notation nbe := (@rewrite_bottomup (fun t idc => reflect (expr.Ident idc))).

        Fixpoint repeat_rewrite
                 (rewrite_head : forall (do_again : forall t : base.type, @expr value (type.base t) -> UnderLets (@expr var (type.base t)))
                                            t (idc : ident t), value_with_lets t)
                 (fuel : nat) {t} e : value_with_lets t
          := @rewrite_bottomup
               (rewrite_head
                  (fun t' e'
                   => match fuel with
                      | Datatypes.O => nbe e'
                      | Datatypes.S fuel' => @repeat_rewrite rewrite_head fuel' (type.base t') e'
                      end%under_lets))
               t e.

        Definition rewrite rewrite_head fuel {t} e : expr t
          := reify (@repeat_rewrite rewrite_head fuel t e).*)

      End full.


      About Rewrite.

      Section all.
        Import defaults.
        Local Notation UnderLets := (UnderLets.UnderLets base.type ident).

        Context (rewrite_head : forall var (do_again : forall t, @expr (@value _ ident var) (type.base t) -> UnderLets var (@expr var (type.base t))) t,
                    ident t -> @value_with_lets _ ident var t).


        (*
        Lemma Wf_Rewrite fuel {t} (e : Expr t) (Hwf : Wf e) : Wf (Rewrite rewrite_head fuel e).
        Proof.
          cbv [Rewrite]; intros ? ?.*)
      End all.
    End Compile.
    *)

    Lemma nbe_rewrite_head_eq : @nbe_rewrite_head = @nbe_rewrite_head0.
    Proof. reflexivity. Qed.

    Lemma fancy_rewrite_head_eq invert_low invert_high
      : (fun var do_again => @fancy_rewrite_head invert_low invert_high var)
        = (fun var => @fancy_rewrite_head0 var invert_low invert_high).
    Proof. reflexivity. Qed.

    Lemma arith_rewrite_head_eq max_const_val : @arith_rewrite_head max_const_val = (fun var => @arith_rewrite_head0 var max_const_val).
    Proof. reflexivity. Qed.

    Lemma nbe_all_rewrite_rules_eq : @nbe_all_rewrite_rules = @nbe_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma fancy_all_rewrite_rules_eq : @fancy_all_rewrite_rules = @fancy_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma arith_all_rewrite_rules_eq : @arith_all_rewrite_rules = @arith_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma Wf_RewriteNBE {t} e (Hwf : Wf e) : Wf (@RewriteNBE t e).
    Proof.
      cbv [RewriteNBE]; rewrite nbe_rewrite_head_eq; cbv [nbe_rewrite_head0]; rewrite nbe_all_rewrite_rules_eq.
    Admitted.
    Lemma Wf_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e) : Wf (@RewriteArith max_const_val t e).
    Proof.
      cbv [RewriteArith]; rewrite arith_rewrite_head_eq; cbv [arith_rewrite_head0]; rewrite arith_all_rewrite_rules_eq.
    Admitted.
    Lemma Wf_RewriteToFancy (invert_low invert_high : Z -> Z -> option Z) {t} e (Hwf : Wf e) : Wf (@RewriteToFancy invert_low invert_high t e).
    Proof.
      cbv [RewriteToFancy]; rewrite fancy_rewrite_head_eq; cbv [fancy_rewrite_head0]; rewrite fancy_all_rewrite_rules_eq.
    Admitted.

    Lemma Interp_RewriteNBE {t} e (Hwf : Wf e) : Interp (@RewriteNBE t e) == Interp e.
    Proof.
      cbv [RewriteNBE]; rewrite nbe_rewrite_head_eq; cbv [nbe_rewrite_head0]; rewrite nbe_all_rewrite_rules_eq.
    Admitted.
    Lemma Interp_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e) : Interp (@RewriteArith max_const_val t e) == Interp e.
    Proof.
      cbv [RewriteArith]; rewrite arith_rewrite_head_eq; cbv [arith_rewrite_head0]; rewrite arith_all_rewrite_rules_eq.
    Admitted.

    Lemma Interp_RewriteToFancy (invert_low invert_high : Z -> Z -> option Z)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : Interp (@RewriteToFancy invert_low invert_high t e) == Interp e.
    Proof.
      cbv [RewriteToFancy]; rewrite fancy_rewrite_head_eq; cbv [fancy_rewrite_head0]; rewrite fancy_all_rewrite_rules_eq.
    Admitted.
  End RewriteRules.

  Lemma Wf_PartialEvaluate {t} e (Hwf : Wf e) : Wf (@PartialEvaluate t e).
  Proof. apply Wf_RewriteNBE, Hwf. Qed.

  Lemma Interp_PartialEvaluate {t} e (Hwf : Wf e) : Interp (@PartialEvaluate t e) == Interp e.
  Proof. apply Interp_RewriteNBE, Hwf. Qed.


  Hint Resolve Wf_PartialEvaluate Wf_RewriteArith Wf_RewriteNBE Wf_RewriteToFancy : wf.
  Hint Rewrite @Interp_PartialEvaluate @Interp_RewriteArith @Interp_RewriteNBE @Interp_RewriteToFancy : interp.
End Compilers.
