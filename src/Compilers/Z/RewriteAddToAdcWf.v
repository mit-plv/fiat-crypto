Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.InterpretToPHOASWf.
Require Import Crypto.Compilers.Named.CompileWf.
Require Import Crypto.Compilers.Named.WfFromUnit.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.RewriteAddToAdc.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.

Section language.
  Local Hint Resolve internal_base_type_dec_lb internal_base_type_dec_lb dec_rel_of_bool_dec_rel : typeclass_instances.

  Lemma Wf_RewriteAdc {t} (e : Expr base_type op t) (Hwf : Wf e)
  : Wf (RewriteAdc e).
  Proof.
    unfold RewriteAdc, option_map; break_innermost_match;
      [ .. | solve [ intros var1 var2; destruct (Hwf var1 var2); auto with wf ] ];
      repeat first [ eapply @Wf_InterpToPHOAS with (t:=Arrow _ _)
                   | progress split_andb
                   | congruence
                   | intros;
                     match goal with
                     | [ |- ContextDefinitions.ContextOk _ ]
                       => eapply @PositiveContextOk
                     end
                   | solve [ auto | eapply @BinPos.Pos.eqb_eq ]
                   | eapply @Wf_from_unit
                   | eapply @dec_rel_of_bool_dec_rel
                   | eapply @internal_base_type_dec_lb
                   | eapply @internal_base_type_dec_bl
                   | intros var1 var2; specialize (Hwf var1 var2); destruct Hwf;
                     constructor; assumption ].
  Qed.
End language.

Hint Resolve Wf_RewriteAdc : wf.
