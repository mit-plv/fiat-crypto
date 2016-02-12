Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.CompleteEdwardsCurve.

Section ExtendedCoordinates.
  Local Open Scope F_scope.

  (* 
  Context {prm:TwistedEdwardsParams}.                 (* DOESN'T WORK   *)
  *)
  Context {q:BinInt.Z} {prime_q:Znumtheory.prime q}.  (* WORKS OKAY-ish *)

  Check q : BinInt.Z.
  Check prime_q : Znumtheory.prime q.
  Existing Instance prime_q.

  Add Field Ffield_Z : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

  Lemma biggerFraction : forall XP YP ZP XQ YQ ZQ d : F q, 
   ZQ <> 0 ->
   ZP <> 0 ->
   ZP * ZQ * ZP * ZQ + d * XP * XQ * YP * YQ <> 0 ->
   ZP * ZToField 2 * ZQ * (ZP * ZQ) + XP * YP * ZToField 2 * d * (XQ * YQ) <> 0 ->
   ZP * ZToField 2 * ZQ * (ZP * ZQ) - XP * YP * ZToField 2 * d * (XQ * YQ) <> 0 ->

   ((YP + XP) * (YQ + XQ) - (YP - XP) * (YQ - XQ)) *
   (ZP * ZToField 2 * ZQ - XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ)) /
   ((ZP * ZToField 2 * ZQ - XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ)) *
    (ZP * ZToField 2 * ZQ + XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ))) =
   (XP / ZP * (YQ / ZQ) + YP / ZP * (XQ / ZQ)) / (1 + d * (XP / ZP) * (XQ / ZQ) * (YP / ZP) * (YQ / ZQ)).
  Proof.
    intros.
    field; assumption.
  Qed.
End ExtendedCoordinates.