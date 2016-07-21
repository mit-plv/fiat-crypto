Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.NArith.NArith.
Require Import Crypto.Spec.ModularWordEncoding.
Require Import Crypto.Encoding.ModularWordEncodingTheorems.
Require Import Crypto.Spec.EdDSA.
Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems Crypto.ModularArithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.NatUtil Crypto.Util.ZUtil Crypto.Util.WordUtil Crypto.Util.NumTheoryUtil.
Require Import Bedrock.Word.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Logic.Decidable.
Require Import Coq.omega.Omega.

(* TODO: move to PrimeFieldTheorems *)
Lemma minus1_is_square {q} :  prime q -> (q mod 4)%Z = 1%Z -> isSquare (opp 1 : F q)%F.
  intros; pose proof prime_ge_2 q _.
  apply square_Zmod_F.
  destruct (minus1_square_1mod4 q) as [b b_id]; trivial.
  exists b; rewrite b_id.
  rewrite opp_ZToField, !FieldToZ_ZToField, !Z.mod_small; omega.
Qed.

Lemma euler_criterion_nonsquare {q} (prime_q:prime q) (two_lt_q:(2<q)%Z) (d:F q) : 
  ((d =? 0)%Z || (Pre.powmod q d (Z.to_N (q / 2)) =? 1)%Z)%bool = false -> 
   forall x : F q, (x ^ 2)%F <> d.
Proof.
  pose proof @euler_criterion_if q prime_q d two_lt_q;
    break_if; intros; try discriminate; eauto.
Qed.

Definition q : Z := (2 ^ 255 - 19)%Z.
Global Instance prime_q : prime q. Admitted.
Lemma two_lt_q : (2 < q)%Z. Proof. reflexivity. Qed.
Lemma char_gt_2 : (1 + 1 <> (0:F q))%F. Proof. rewrite F_eq; compute; discriminate. Qed.

Definition a : F q := opp 1%F.
Lemma nonzero_a : a <> 0%F. Proof. rewrite F_eq; compute; discriminate. Qed.
Lemma square_a : exists b, (b*b=a)%F.
Proof. setoid_rewrite <-F_pow_2_r. apply (minus1_is_square _); reflexivity. Qed.

Definition d : F q := (opp (ZToField 121665) / (ZToField 121666))%F.
Lemma nonsquare_d : forall x, (x*x <> d)%F.
Proof.
  intros; rewrite <-F_pow_2_r.
  apply (euler_criterion_nonsquare prime_q two_lt_q); vm_cast_no_check (eq_refl false).
Qed. (* 3s *)

Instance curve25519params : @E.twisted_edwards_params (F q) eq (ZToField 0) (ZToField 1) add mul a d :=
  {
    nonzero_a := nonzero_a;
    char_gt_2 := char_gt_2;
    square_a := square_a;
    nonsquare_d := nonsquare_d
  }.

Lemma two_power_nat_Z2Nat : forall n, Z.to_nat (two_power_nat n) = (2 ^ n)%nat.
Admitted.

Definition b := 256%nat.
Lemma b_valid : (2 ^ (b - 1) > Z.to_nat q)%nat.
Proof.
  unfold q, gt.
  replace (2 ^ (b - 1))%nat with (Z.to_nat (2 ^ (Z.of_nat (b - 1))))
    by (rewrite <- two_power_nat_equiv; apply two_power_nat_Z2Nat).
  rewrite <- Z2Nat.inj_lt; compute; congruence.
Qed.

Definition c := 3%nat.
Lemma c_valid : (c = 2 \/ c = 3)%nat.
Proof.
  right; auto.
Qed.

Definition n := (b - 2)%nat.
Lemma n_ge_c : (n >= c)%nat.
Proof.
  unfold n, c, b; omega.
Qed.
Lemma n_le_b : (n <= b)%nat.
Proof.
  unfold n, b; omega.
Qed.

Definition l : nat := Z.to_nat (252 + 27742317777372353535851937790883648493)%Z.
Lemma prime_l : prime (Z.of_nat l). Admitted.
Lemma l_odd : (l > 2)%nat.
Proof.
  unfold l, proj1_sig.
  rewrite Z2Nat.inj_add; try omega.
  apply lt_plus_trans.
  compute; omega.
Qed.

Require Import Crypto.Spec.Encoding.

Lemma q_pos : (0 < q)%Z. pose proof prime_ge_2 q _; omega. Qed.
Definition FqEncoding : canonical encoding of (F q) as word (b-1) :=
  @modular_word_encoding q (b - 1) q_pos b_valid.

Lemma l_pos : (0 < Z.of_nat l)%Z. pose proof prime_l; prime_bound. Qed.
Lemma l_bound : (Z.to_nat (Z.of_nat l) < 2 ^ b)%nat.
Proof.
  rewrite Nat2Z.id.
  rewrite <- pow2_id.
  rewrite Zpow_pow2.
  unfold l.
  apply Z2Nat.inj_lt; compute; congruence.
Qed.
Definition FlEncoding : canonical encoding of F (Z.of_nat l) as word b :=
  @modular_word_encoding (Z.of_nat l) b l_pos l_bound.

Lemma q_5mod8 : (q mod 8 = 5)%Z. cbv; reflexivity. Qed.

Lemma sqrt_minus1_valid : ((@ZToField q 2 ^ Z.to_N (q / 4)) ^ 2 = opp 1)%F.
Proof. apply F_eq; vm_compute; reflexivity. Qed.

Local Notation point := (@E.point (F q) eq (ZToField 1) add mul a d).
Local Notation zero := (E.zero(H:=field_modulo)).
Local Notation add := (E.add(H0:=curve25519params)).
Local Infix "*" := (E.mul(H0:=curve25519params)).
Axiom H : forall n : nat, word n -> word (b + b).
Axiom B : point. (* TODO: B = decodePoint (y=4/5, x="positive") *)
Axiom B_nonzero : B <> zero.
Axiom l_order_B : E.eq (l * B) zero.
Axiom Eenc : point -> word b.
Axiom Senc : nat -> word b.

Global Instance Ed25519 : @EdDSA point E.eq add zero E.opp E.mul b H c n l B Eenc Senc :=
  {
    EdDSA_c_valid := c_valid;
    EdDSA_n_ge_c := n_ge_c;
    EdDSA_n_le_b := n_le_b;
    EdDSA_B_not_identity := B_nonzero;
    EdDSA_l_prime := prime_l;
    EdDSA_l_odd := l_odd;
    EdDSA_l_order_B := l_order_B
  }.
