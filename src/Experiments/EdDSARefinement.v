Require Import Crypto.Spec.EdDSA Bedrock.Word.
Require Import Coq.Classes.Morphisms.
Require Import Util.Decidable Util.Option Util.Tactics.

Module Import NotationsFor8485.
  Import NPeano Nat.
  Notation modulo := modulo.
End NotationsFor8485.

Section EdDSA.
  Context `{prm:EdDSA}.
  Context {eq_dec:DecidableRel Eeq}.
  Local Infix "==" := Eeq (at level 69, no associativity).
  Local Notation valid := (@valid E Eeq Eadd EscalarMult b H l B Eenc Senc).
  Local Infix "*" := EscalarMult. Local Infix "+" := Eadd. Local Infix "++" := combine.
  Local Notation "P - Q" := (P + Eopp Q).

  Context {Proper_Eenc : Proper (Eeq==>Logic.eq) Eenc}.
  Context {Proper_Eopp : Proper (Eeq==>Eeq) Eopp}.
  Context {Proper_Eadd : Proper (Eeq==>Eeq==>Eeq) Eadd}.
  Context {Proper_EscalarMult : Proper (Logic.eq==>Eeq==>Eeq) EscalarMult}.

  Context {decE:word b-> option E}.
  Context {decS:word b-> option nat}.

  Context {decE_canonical: forall x s, decE x = Some s -> x = Eenc s }.
  Context {decS_canonical: forall x s, decS x = Some s -> x = Senc s }.

  Context {decS_Senc: forall x, decS (Senc x) = Some x}.
  Context {decE_Eenc: forall x, decE (Eenc x) = Some x}. (* FIXME: equivalence relation *)

  Lemma solve_for_R : forall s B R n A, s * B == R + n * A <-> R == s*B - n*A.
  Proof.
    intros; split;
      intro Heq; rewrite Heq; clear Heq.
  Admitted.

  Definition verify {mlen} (message:word mlen) (pk:word b) (sig:word (b+b)) : bool :=
    option_rect (fun _ => bool) (fun S : nat =>
    option_rect (fun _ => bool) (fun A : E =>
       weqb
         (split1 b b sig)
         (Eenc (S * B - modulo (wordToNat (H (b + (b + mlen)) (split1 b b sig ++ pk ++ message))) l * A))
    ) false (decE pk)
    ) false (decS (split2 b b sig))
  .

  Lemma verify_correct mlen (message:word mlen) (pk:word b) (sig:word (b+b)) :
      verify message pk sig = true <-> valid message pk sig.
  Proof.
    cbv [verify option_rect option_map].
    split.
    {
      repeat match goal with
             | |- false = true -> _ => let H:=fresh "H" in intro H; discriminate H
             | [H: _ |- _ ] => apply decS_canonical in H
             | [H: _ |- _ ] => apply decE_canonical in H
             | _ => rewrite weqb_true_iff
             | _ => break_match
             end.
      intro.
      subst.
      rewrite <-combine_split.
      rewrite Heqo.
      rewrite H0.
      constructor.
      rewrite <-H0.
      rewrite solve_for_R.
      reflexivity.
    }
    {
      intros [? ? ? ? Hvalid].
      rewrite solve_for_R in Hvalid.
      rewrite split1_combine.
      rewrite split2_combine.
      rewrite decS_Senc.
      rewrite decE_Eenc.
      rewrite weqb_true_iff.
      f_equiv. exact Hvalid.
    }
  Qed.

  Lemma scalarMult_mod_order : forall l x B, l * B == Ezero -> (modulo x l) * B == x * B. Admitted.

  Lemma sign_valid : forall A_ sk {n} (M:word n), A_ = public sk -> valid M A_ (sign A_ sk M).
  Proof.
    cbv [sign public].
    intros. subst. constructor.
    Local Arguments H {_} _.
    Local Notation "'$' x" := (wordToNat x) (at level 1).
    Local Infix "mod" := modulo (at level 50).
    set (HRAM := H (Eenc ($ (H (prngKey sk ++ M)) * B) ++ Eenc (curveKey sk * B) ++ M)).
    set (r := H (prngKey sk ++ M)).
    repeat rewrite scalarMult_mod_order by eapply EdDSA_l_order_B.
  Admitted.
End EdDSA.
