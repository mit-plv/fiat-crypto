Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.CompleteEdwardsCurve.

Section ExtendedCoordinates.
  Local Open Scope F_scope.

  Context {prm:TwistedEdwardsParams}.
  Context {p:BinInt.Z} {p_eq_q:p = q}.
  Lemma prime_p : Znumtheory.prime p.
    rewrite p_eq_q; exact prime_q.
  Qed.

  Add Field Ffield_Z : (@Ffield_theory p prime_p)
    (morphism (@Fring_morph p),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess],
     constants [Fconstant],
     div (@Fmorph_div_theory p),
     power_tac (@Fpower_theory p) [Fexp_tac]). 

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
    rewrite <-p_eq_q.
    intros.
    abstract (field; assumption).
  Qed.
End ExtendedCoordinates.