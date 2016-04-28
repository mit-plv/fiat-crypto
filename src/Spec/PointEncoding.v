Require Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Crypto.Encoding.EncodingTheorems.
Require Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Bedrock.Word.
Require Crypto.Tactics.VerdiTactics.
Require Crypto.Encoding.PointEncodingPre.
Obligation Tactic := eauto; exact PointEncodingPre.point_encoding_canonical.

Require Import Crypto.Spec.Encoding Crypto.Spec.ModularWordEncoding.
Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Spec.ModularArithmetic.

Local Open Scope F_scope.

Section PointEncoding.
  Context {prm: TwistedEdwardsParams} {sz : nat} {sz_nonzero : (0 < sz)%nat}
   {bound_check : (BinInt.Z.to_nat q < NPeano.Nat.pow 2 sz)%nat} {q_5mod8 : (q mod 8 = 5)%Z}
   {sqrt_minus1_valid : (@ZToField q 2 ^ BinInt.Z.to_N (q / 4)) ^ 2 = opp 1}
   {FqEncoding : encoding of (F q) as (Word.word sz)}
   {sign_bit : F q -> bool} {sign_bit_zero : sign_bit 0 = false}
   {sign_bit_opp : forall x, x <> 0 -> negb (sign_bit x) = sign_bit (opp x)}.
  Existing Instance prime_q.

  Definition point_enc (p : E.point) : Word.word (S sz) := let '(x,y) := proj1_sig p in
    Word.WS (sign_bit x) (enc y).

  Program Definition point_dec_with_spec :
    {point_dec : Word.word (S sz) -> option E.point
               | forall w x, point_dec w = Some x -> (point_enc x = w)
               } := @PointEncodingPre.point_dec _ _ _ sign_bit.

  Definition point_dec := Eval hnf in (proj1_sig point_dec_with_spec).

   Definition point_encoding_valid : forall p : E.point, point_dec (point_enc p) = Some p :=
     @PointEncodingPre.point_encoding_valid _ _ q_5mod8 sqrt_minus1_valid _ _ sign_bit_zero sign_bit_opp.

   Definition point_encoding_canonical : forall x_enc x, point_dec x_enc = Some x -> point_enc x = x_enc :=
     PointEncodingPre.point_encoding_canonical.

  Instance point_encoding : encoding of E.point as (Word.word (S sz)) := {
    enc := point_enc;
    dec := point_dec;
    encoding_valid := point_encoding_valid;
    encoding_canonical := point_encoding_canonical
  }.
End PointEncoding.