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
    let R : E.point := (r * B)%E in (* commitment to nonce *)
    let s : nat := curveKey sk in (* secret scalar *)
    let S : F (Z.of_nat l) := ZToField (Z.of_nat (r + H (enc R ++ public sk ++ M) * s)) in
        enc S.
  Proof.
    unfold sign; arith.
  Qed.
  Hint Rewrite decode_sign_split2.

  Hint Rewrite E.add_0_r E.add_0_l E.add_assoc.
  Hint Rewrite E.mul_assoc E.mul_add_l E.mul_0_l E.mul_zero_r.
  Hint Rewrite plus_O_n plus_Sn_m mult_0_l mult_succ_l.
  Hint Rewrite l_order_B.
  Lemma l_order_B' : forall x, (l * x * B = E.zero)%E.
  Proof.
    intros; rewrite Mult.mult_comm. rewrite <- E.mul_assoc. arith.
  Qed. Hint Rewrite l_order_B'.

  Lemma scalarMult_mod_l : forall n0, (n0 mod l * B = n0 * B)%E.
  Proof.
    intros.
    rewrite (div_mod n0 l) at 2 by (generalize l_odd; omega).
    arith.
  Qed. Hint Rewrite scalarMult_mod_l.

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

  (*  This is just an experiment, talk to andreser if you think this is a good idea *)
  Inductive valid {n:nat} : word b -> Word.word n -> word (b+b) -> Prop :=
    Valid : forall (A:E.point) (M:Word.word n) (S:nat) (R:E.point),
      (S * B = R + (H (enc R ++ enc A ++ M)) * A)%E
      -> valid (enc A) M (enc R ++ enc (ZToField (BinInt.Z.of_nat S))).
  Goal forall A_ {n} (M:Word.word n) sig, verify A_ M sig = true <-> valid A_ M sig.
    split; unfold verify.
    Focus 2. {
      intros.
      inversion H. subst.
      rewrite !Word.split2_combine, !Word.split1_combine, !encoding_valid.
      rewrite FieldToZ_ZToField.
      rewrite <-Zdiv.mod_Zmod by admit.
      rewrite Znat.Nat2Z.id.
      rewrite <-H0.
      assert ((S mod l) * B = S * B)%E as Hl by admit; rewrite Hl.
      destruct (E.point_eq_dec (S * B)%E); congruence.
    } Unfocus. {
      repeat match goal with |- context [match ?x with _ => _ end] => case_eq x; intro end; try congruence.
      intros. clear H.
      repeat match goal with [H: _ |- _ ] => apply encoding_canonical in H end; subst.
      rewrite <-(Word.combine_split b b sig).
      rewrite <-H0 in *; clear H0. rewrite <-H2  in *; clear H2.
      assert (f = (ZToField (BinInt.Z.of_nat (BinInt.Z.to_nat (FieldToZ f))))) as H1. {
        rewrite Znat.Z2Nat.id by admit. rewrite ZToField_FieldToZ; reflexivity. }
      rewrite H1; clear H1.
      econstructor; trivial.
     }
  Qed.
End EdDSAProofs.
