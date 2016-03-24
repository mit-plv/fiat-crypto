Require Import Crypto.Spec.EdDSA Crypto.Spec.Encoding.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Bedrock.Word.
Require Import Coq.ZArith.Znumtheory Coq.ZArith.BinInt Coq.ZArith.ZArith.
Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems Crypto.ModularArithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.Tactics.VerdiTactics.
Local Open Scope nat_scope.

Section EdDSAProofs.
  Context {prm:EdDSAParams}.
  Existing Instance E.
  Existing Instance PointEncoding.
  Existing Instance FqEncoding.
  Existing Instance FlEncoding.
  Existing Instance n_le_b.
  Hint Rewrite sign_spec split1_combine split2_combine.
  Hint Rewrite Nat.mod_mod using omega.

  Ltac arith' := intros; autorewrite with core; try (omega || congruence).

  Ltac arith := arith';
             repeat match goal with
                    | [ H : _ |- _ ] => rewrite H; arith'
                    end.

  (* for signature (R_, S_), R_ = encode_point (r * B) *) 
  Lemma decode_sign_split1 : forall A_ sk {n} (M : word n),
    split1 b b (sign A_ sk M) = enc (wordToNat (H (prngKey sk ++ M)) * B)%E.
  Proof.
    unfold sign; arith.
  Qed.
  Hint Rewrite decode_sign_split1.

  (* for signature (R_, S_), S_ = encode_scalar (r + H(R_, A_, M)s) *) 
  Lemma decode_sign_split2 : forall sk {n} (M : word n),
    split2 b b (sign (public sk) sk M) =
    let r : nat := H (prngKey sk ++ M) in (* secret nonce *)
    let R : point := (r * B)%E in (* commitment to nonce *)
    let s : nat := curveKey sk in (* secret scalar *)
    let S : F (Z.of_nat l) := ZToField (Z.of_nat (r + H (enc R ++ public sk ++ M) * s)) in
        enc S.
  Proof.
    unfold sign; arith.
  Qed.
  Hint Rewrite decode_sign_split2.

  Lemma zero_times : forall P, (0 * P = zero)%E.
  Proof.
    auto.
  Qed.

  Lemma zero_plus : forall P, (zero + P = P)%E.
  Proof.
    intros; rewrite twistedAddComm; apply zeroIsIdentity.
  Qed.

  Lemma times_S : forall n m, S n * m = m + n * m.
  Proof.
    auto.
  Qed.

  Lemma times_S_nat : forall n m, (S n * m = m + n * m)%nat.
  Proof.
    auto.
  Qed.

  Hint Rewrite plus_O_n plus_Sn_m times_S times_S_nat.
  Hint Rewrite zeroIsIdentity zero_times zero_plus twistedAddAssoc.

  Lemma scalarMult_distr : forall n0 m, ((n0 + m)%nat * B)%E = unifiedAdd (n0 * B)%E (m * B)%E.
  Proof.
    unfold scalarMult; induction n0; arith. 
  Qed.
  Hint Rewrite scalarMult_distr.

  Lemma scalarMult_assoc : forall (n0 m : nat), (n0 * (m * B) = (n0 * m)%nat * B)%E.
  Proof.
    induction n0; arith; simpl; arith.
  Qed.
  Hint Rewrite scalarMult_assoc.

  Lemma scalarMult_zero : forall m, (m * zero = zero)%E.
  Proof.
    unfold scalarMult; induction m; arith.
  Qed.
  Hint Rewrite scalarMult_zero.
  Hint Rewrite l_order_B.

  Lemma l_order_B' : forall x, (l * x * B = zero)%E.
  Proof.
    intros; rewrite Mult.mult_comm. rewrite <- scalarMult_assoc. arith.
  Qed.

  Hint Rewrite l_order_B'.

  Lemma scalarMult_mod_l : forall n0, (n0 mod l * B = n0 * B)%E.
  Proof.
    intros.
    rewrite (div_mod n0 l) at 2 by (generalize l_odd; omega).
    arith.
  Qed.
  Hint Rewrite scalarMult_mod_l.

  Hint Rewrite @encoding_valid.
  Hint Rewrite @FieldToZ_ZToField.
  Hint Rewrite <-mod_Zmod.
  Hint Rewrite Nat2Z.id.

  Lemma l_nonzero : l <> O. pose l_odd; omega. Qed.
  Hint Resolve l_nonzero.

  Lemma verify_valid_passes : forall sk {n} (M : word n),
    verify (public sk) M (sign (public sk) sk M) = true.
  Proof.
    unfold verify, sign, public; arith; try break_if; intuition.
  Qed.
End EdDSAProofs.
