Require Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Crypto.Encoding.EncodingTheorems.
Require Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Bedrock.Word.
Require Crypto.Tactics.VerdiTactics.
Require Crypto.Encoding.PointEncodingPre.
Obligation Tactic := eauto using PointEncodingPre.point_encoding_canonical.

Require Import Crypto.Spec.Encoding Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.CompleteEdwardsCurve.

Local Open Scope F_scope.

Section PointEncoding.
  Context {prm: CompleteEdwardsCurve.TwistedEdwardsParams} {sz : nat}
   {FqEncoding : encoding of ModularArithmetic.F (CompleteEdwardsCurve.q) as Word.word sz}.

  Definition sign_bit (x : F CompleteEdwardsCurve.q) :=
    match (enc x) with
      | Word.WO => false
      | Word.WS b _ w' => b
    end.

  Definition point_enc (p : CompleteEdwardsCurve.point) : Word.word (S sz) := let '(x,y) := proj1_sig p in
    Word.WS (sign_bit x) (enc y).

  Program Definition point_dec_with_spec :
    {point_dec : Word.word (S sz) -> option CompleteEdwardsCurve.point
               | forall w x, point_dec w = Some x -> (point_enc x = w)
               } := PointEncodingPre.point_dec.
   
  Definition point_dec := Eval hnf in (proj1_sig point_dec_with_spec).

  Instance point_encoding : encoding of CompleteEdwardsCurve.point as (Word.word (S sz)) := {
    enc := point_enc;
    dec := point_dec;
    encoding_valid := PointEncodingPre.point_encoding_valid
  }.

End PointEncoding.
