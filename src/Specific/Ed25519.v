Require Import Bedrock.Word.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Tactics.VerdiTactics.
Require Import BinNat BinInt NArith Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.Encoding Crypto.Spec.PointEncoding.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.Util.IterAssocOp.

Local Infix "++" := Word.combine.
Local Notation " a '[:' i ']' " := (Word.split1 i _ a) (at level 40).
Local Notation " a '[' i ':]' " := (Word.split2 i _ a) (at level 40).
Local Arguments H {_} _.
Local Arguments scalarMultM1 {_} {_} _ _.
Local Arguments unifiedAddM1 {_} {_} _ _.

Lemma sharper_verify : { verify | forall pk l msg sig, verify pk l msg sig = ed25519_verify pk l msg sig}.
Proof.
  eexists; intros.
  cbv [ed25519_verify EdDSA.verify
                      ed25519params curve25519params
                      EdDSA.E EdDSA.B EdDSA.b EdDSA.l EdDSA.H
                      EdDSA.PointEncoding EdDSA.FlEncoding EdDSA.FqEncoding].

  (* zoom in to the interesting case *)
  repeat match goal with |- context[match ?a with Some x => _ | _ => _ end] =>
                    let n := fresh x in
                    let H := fresh "Heq" x in
                    destruct a as [x|]
  end.

  let p1 := constr:(scalarMultM1_rep eq_refl) in
  let p2 := constr:(unifiedAddM1_rep eq_refl) in
  repeat match goal with
  | |- context [(?n * ?P)%E] =>
    rewrite <-(unExtendedPoint_mkExtendedPoint P);
    erewrite <-p1
  | |- context [(?P + unExtendedPoint _)%E] =>
    rewrite <-(unExtendedPoint_mkExtendedPoint P);
    erewrite p2
  end.
  rewrite !Znat.Z_nat_N, <-!Word.wordToN_nat.
  
  cbv [scalarMultM1 iter_op].
  Local Arguments funexp {_} _ {_} {_}. (* do not display the initializer and iteration bound for now *)
  cbv iota zeta delta [test_and_op].


Admitted.