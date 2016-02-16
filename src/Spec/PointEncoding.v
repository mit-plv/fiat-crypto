Require Import ZArith.ZArith Zpower ZArith Znumtheory.
Require Import NPeano NArith.
Require Import Crypto.Spec.Encoding.
Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems Crypto.ModularArithmetic.ModularArithmeticTheorems.
Require Import Crypto.Curves.PointFormats.
Require Import Crypto.Util.NatUtil Crypto.Util.ZUtil Crypto.Util.NumTheoryUtil.
Require Import Bedrock.Word.
Require Import VerdiTactics.

Local Open Scope F_scope.

Section PointEncoding.
  Context {prm:TwistedEdwardsParams} {sz : nat} {FqEncoding : encoding of F q as word sz} {q_5mod8 : q mod 8 = 5} {sqrt_minus1_valid : (@ZToField q 2 ^ Z.to_N (q / 4)) ^ 2 = opp 1}.
  Existing Instance prime_q.

  Add Field Ffield : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]).

Definition sign_bit (x : F q) := (wordToN (enc (opp x)) <? wordToN (enc x))%N.
Definition point_enc (p : point) : word (S sz) := let '(x,y) := proj1_sig p in
  WS (sign_bit x) (enc y).
Definition point_dec (w : word (S sz)) : option point :=
  match dec (wtl w) with
  | None => None
  | Some y => let x2 := solve_for_x2 y in
      let x := sqrt_mod_q x2 in
      match (F_eq_dec (x ^ 2) x2) with
      | right _ => None
      | left EQ => if Bool.eqb (whd w) (sign_bit x)
                   then Some (mkPoint (x, y) (solve_onCurve y EQ))
                   else Some (mkPoint (opp x, y) (solve_opp_onCurve y EQ))
      end
  end.

Lemma y_decode : forall p, dec (wtl (point_enc p)) = Some (snd (proj1_sig p)).
Admitted.

Lemma sign_bit_match : forall x x' y : F q, onCurve (x, y) -> onCurve (x', y) ->
  sign_bit x = sign_bit x' -> x = x'.
Admitted.

Lemma sign_bit_opp : forall x y, sign_bit x <> sign_bit y -> sign_bit x = sign_bit (opp y).
Admitted.

Lemma point_encoding_valid : forall p, point_dec (point_enc p) = Some p.
Proof.
  intros.
  unfold point_dec.
  rewrite y_decode.
  pose proof solve_sqrt_valid p as solve_sqrt_valid_p.
  unfold sqrt_valid in *.
  destruct p as [[x y] onCurve_p].
  simpl in *.
  destruct (F_eq_dec ((sqrt_mod_q (solve_for_x2 y)) ^ 2) (solve_for_x2 y)); intuition.
  break_if; f_equal; apply point_eq.
  + rewrite Bool.eqb_true_iff in Heqb.
    pose proof (solve_onCurve y solve_sqrt_valid_p).
    f_equal.
    apply (sign_bit_match _ _ y); auto.
  + rewrite Bool.eqb_false_iff in Heqb.
    pose proof (solve_opp_onCurve y solve_sqrt_valid_p).
    f_equal.
    apply sign_bit_opp in Heqb.
    apply (sign_bit_match _ _ y); auto.
Qed.

Instance point_encoding : encoding of point as (word (S sz)) := {
  enc := point_enc;
  dec := point_dec;
  encoding_valid := point_encoding_valid
}.

End PointEncoding.
