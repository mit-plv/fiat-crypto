Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Tactics.VerdiTactics.
Require Import BinNat BinInt NArith Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.CompleteEdwardsCurve.ExtendedCoordinates.

Local Infix "++" := Word.combine.
Local Notation " a '[:' i ']' " := (Word.split1 i _ a) (at level 40).
Local Notation " a '[' i ':]' " := (Word.split2 i _ a) (at level 40).

Lemma sharper_verify : { verify | forall pk l msg sig, verify pk l msg sig = ed25519_verify pk l msg sig}.
Proof.
  eexists; intros.
  cbv [ed25519_verify EdDSA.verify Encoding.dec EdDSA.PointEncoding PointEncoding
                      PointEncoding.point_encoding EdDSA.FlEncoding FlEncoding
                      Encoding.modular_word_encoding ed25519params].
  break_match.
  break_match.
  break_match.
  repeat match goal with
  | |- context [(?n * ?P)%E] =>
    rewrite <-(unExtendedPoint_mkExtendedPoint P);
    erewrite <-scalarMultM1_rep
  | |- context [(?P + unExtendedPoint _)%E] =>
    rewrite <-(unExtendedPoint_mkExtendedPoint P);
    erewrite unifiedAddM1_rep
  end.
  rewrite !Znat.Z_nat_N, <-!Word.wordToN_nat.
  
  (* unfold scalarMultM1 at 1. *)
Admitted.