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

Local Open Scope nat_scope.
Definition q : Z := (2 ^ 255 - 19)%Z.
Global Instance prime_q : prime q. Admitted.
Lemma two_lt_q : (2 < q)%Z. reflexivity. Qed.

Definition a : F q := opp 1%F.

(* TODO (jadep) : make the proofs about a and d more general *)
Lemma nonzero_a : a <> 0%F.
Proof.
  unfold a.
  intro eq_opp1_0.
  apply (@Fq_1_neq_0 q prime_q).
  rewrite <- (F_opp_spec 1%F).
  rewrite eq_opp1_0.
  symmetry; apply F_add_0_r.
Qed.

Ltac q_bound := pose proof two_lt_q; omega.
Lemma square_a : isSquare a.
Proof.
  assert (q_1mod4 : (q mod 4 = 1)%Z) by abstract reflexivity.
  intros.
  pose proof (minus1_square_1mod4 q prime_q q_1mod4) as minus1_square.
  destruct minus1_square as [b b_id].
  apply square_Zmod_F.
  exists b; rewrite b_id.
  unfold a.
  rewrite opp_ZToField.
  rewrite FieldToZ_ZToField.
  rewrite Z.mod_small; q_bound.
Qed.

Hint Rewrite
 @FieldToZ_add
 @FieldToZ_mul
 @FieldToZ_opp
 @FieldToZ_inv_efficient
 @FieldToZ_pow_efficient
 @FieldToZ_ZToField
 @Zmod_mod
 : ZToField.

Definition d : F q := (opp (ZToField 121665) / (ZToField 121666))%F.
Lemma nonsquare_d : forall x, (x^2 <> d)%F.
  pose proof @euler_criterion_if q prime_q d two_lt_q.
  match goal with
    [H: if ?b then ?x else ?y |- ?y ] => replace b with false in H; [exact H|clear H]
  end.
  unfold d, div. autorewrite with ZToField; [|eauto using prime_q, two_lt_q..].
  vm_compute. (* 10s *)
  exact eq_refl.
Qed. (* 10s *)

Instance curve25519params : @E.twisted_edwards_params (F q) eq (ZToField 0) (ZToField 1) add mul a d :=
  {
    nonzero_a := nonzero_a
                   (* TODO:port
    char_gt_2 : ~ Feq (Fadd Fone Fone) Fzero;
    nonzero_a : ~ Feq a Fzero;
    nonsquare_d : forall x : F, ~ Feq (Fmul x x) d }
                    *)
  }.
Admitted.

Lemma two_power_nat_Z2Nat : forall n, Z.to_nat (two_power_nat n) = 2 ^ n.
Admitted.

Definition b := 256.
Lemma b_valid : (2 ^ (b - 1) > Z.to_nat q)%nat.
Proof.
  unfold q, gt.
  replace (2 ^ (b - 1)) with (Z.to_nat (2 ^ (Z.of_nat (b - 1))))
    by (rewrite <- two_power_nat_equiv; apply two_power_nat_Z2Nat).
  rewrite <- Z2Nat.inj_lt; compute; congruence.
Qed.

Definition c := 3.
Lemma c_valid : c = 2 \/ c = 3.
Proof.
  right; auto.
Qed.

Definition n := b - 2.
Lemma n_ge_c : n >= c.
Proof.
  unfold n, c, b; omega.
Qed.
Lemma n_le_b : n <= b.
Proof.
  unfold n, b; omega.
Qed.

Definition l : nat := Z.to_nat (252 + 27742317777372353535851937790883648493)%Z.
Lemma prime_l : prime (Z.of_nat l). Admitted.
Lemma l_odd : l > 2.
Proof.
  unfold l, proj1_sig.
  rewrite Z2Nat.inj_add; try omega.
  apply lt_plus_trans.
  compute; omega.
Qed.

Require Import Crypto.Spec.Encoding.

Lemma q_pos : (0 < q)%Z. q_bound. Qed.
Definition FqEncoding : canonical encoding of (F q) as word (b-1) :=
  @modular_word_encoding q (b - 1) q_pos b_valid.

Lemma l_pos : (0 < Z.of_nat l)%Z. pose proof prime_l; prime_bound. Qed.
Lemma l_bound : Z.to_nat (Z.of_nat l) < 2 ^ b.
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
Proof.
  apply F_eq.
  autorewrite with ZToField.
  vm_compute.
  reflexivity.
Qed.

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
