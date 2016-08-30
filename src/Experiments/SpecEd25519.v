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
Require Import Coq.Logic.Decidable Crypto.Util.Decidable.
Require Import Coq.omega.Omega.

(* TODO: move to PrimeFieldTheorems *)
Lemma minus1_is_square {q} : prime q -> (q mod 4)%Z = 1%Z -> (exists y, y*y = F.opp (F.of_Z q 1))%F.
  intros; pose proof prime_ge_2 q _.
  rewrite F.square_iff.
  destruct (minus1_square_1mod4 q) as [b b_id]; trivial; exists b.
  rewrite b_id, F.to_Z_opp, F.to_Z_of_Z, Z.mod_opp_l_nz, !Zmod_small;
    (repeat (omega || rewrite Zmod_small)).
Qed.
Lemma F_sqrt_5mod8_correct : 
  forall q : Z,
    prime q ->
    q mod 8 = 5 ->
    ((F.of_Z q 2 ^ Z.to_N (q / 4)) ^ 2)%F = F.opp 1 ->
    forall x root : F q, x = (root * root)%F -> F.sqrt_5mod8 x = root.
Admitted.

Global Instance dec_onCurve : forall F Feq Fone Fadd Fmul (a d:F) (P:F*F)
    (Hdec:DecidableRel Feq), Decidable (@Pre.onCurve F Feq Fone Fadd Fmul a d P).
Proof. intros. destruct P. eapply Hdec. Defined.

Global Instance dec_eq_word : forall w, DecidableRel (@eq (word w)).
Proof. intros. eapply Decidable_iff_to_impl. eapply weqb_true_iff. exact _. Defined.

Lemma two_power_nat_Z2Nat : forall n, Z.to_nat (two_power_nat n) = (2 ^ n)%nat.
Admitted.

Definition q : Z := (2 ^ 255 - 19)%Z.
Global Instance prime_q : prime q. Admitted.
Lemma two_lt_q : (2 < q)%Z. Proof. reflexivity. Qed.
Lemma char_gt_2 : (1 + 1 <> (0:F q))%F. vm_decide_no_check. Qed.

Definition a : F q := F.opp 1%F.
Lemma nonzero_a : a <> 0%F. Proof. vm_decide_no_check. Qed.
Lemma square_a : exists b, (b*b=a)%F.
Proof. pose (@F.Decidable_square q _ two_lt_q a); vm_decide_no_check. Qed.
Definition d : F q := (F.opp (F.of_Z _ 121665) / (F.of_Z _ 121666))%F.

Lemma nonsquare_d : forall x, (x*x <> d)%F.
Proof. pose (@F.Decidable_square q _ two_lt_q d). vm_decide_no_check. Qed.

Instance curve25519params : @E.twisted_edwards_params (F q) eq 0%F 1%F F.add F.mul a d :=
  {
    nonzero_a := nonzero_a;
    char_gt_2 := char_gt_2;
    square_a := square_a;
    nonsquare_d := nonsquare_d
  }.

Definition b := 256%nat.
Lemma b_valid : (2 ^ (b - 1) > Z.to_nat q)%nat.
Proof.
  unfold q, gt.
  replace (2 ^ (b - 1))%nat with (Z.to_nat (2 ^ (Z.of_nat (b - 1))))
    by (rewrite <- two_power_nat_equiv; apply two_power_nat_Z2Nat).
  rewrite <- Z2Nat.inj_lt; compute; congruence.
Qed.

Definition c := 3%nat.
Definition c_valid : (c = 2 \/ c = 3)%nat := or_intror eq_refl.

Definition n := (b - 2)%nat.
Lemma n_ge_c : (n >= c)%nat. Proof. unfold n, c, b; omega. Qed.
Lemma n_le_b : (n <= b)%nat. Proof. unfold n, b; omega. Qed.

Definition l : Z := (2^252 + 27742317777372353535851937790883648493)%Z.
Lemma prime_l : prime l. Admitted.
Lemma l_odd : (2 < l)%Z. Proof. reflexivity. Qed.

Require Import Crypto.Spec.Encoding.

Lemma q_pos : (0 < q)%Z. pose proof prime_ge_2 q _; omega. Qed.
Global Instance FqEncoding : canonical encoding of (F q) as word (b-1) :=
  @modular_word_encoding q (b - 1) q_pos b_valid.

Lemma l_pos : (0 < l)%Z. reflexivity. Qed.
Lemma l_bound : (Z.to_nat l < 2 ^ b)%nat.
Proof.
  rewrite <- pow2_id, Zpow_pow2.
  apply Z2Nat.inj_lt; compute; congruence.
Qed.

Global Instance FlEncoding : canonical encoding of F l as word b :=
  @modular_word_encoding _ _ l_pos l_bound.

Lemma q_5mod8 : (q mod 8 = 5)%Z. cbv; reflexivity. Qed.

Lemma sqrt_minus1_valid : ((F.of_Z q 2 ^ Z.to_N (q / 4)) ^ 2 = F.opp 1)%F.
Proof. vm_decide_no_check. Qed.

Local Notation point := (@E.point (F q) eq 1%F F.add F.mul a d).
Local Notation zero := (E.zero(field:=F.field_modulo q)).
Local Notation add := (E.add(H:=curve25519params)).
Local Infix "*" := (E.mul(H:=curve25519params)).
Axiom H : forall n : nat, word n -> word (b + b).
Require Import Crypto.Encoding.PointEncodingPre.
Definition Eenc : E.point -> word 256 := point_enc FqEncoding (eq:=Logic.eq)(one:=F.one)(add:=F.add)(mul:=F.mul)(a:=a)(d:=d)(sign_bit:=ModularWordEncoding.sign_bit(sz:=b-1)).

Definition B_coords :=
  (F.of_Z q 15112221349535400772501151409588531511454012693041857206046113283949847762202,
   F.of_Z q 46316835694926478169428394003475163141307993866256225615783033603165251855960).

Program Definition B : point. refine (exist _ B_coords _). vm_decide_no_check. Defined.

Lemma B_correct : Eenc B = WS false (enc (F.div (F.of_Z q 4) (F.of_Z q 5))).
Proof. vm_decide_no_check. Qed.

(* FIXME: from is_eq_dec from monoid *)
Module E.
  Global Instance eq_dec F Feq Fone Fadd Fmul a d (Hdec:DecidableRel Feq) :
    DecidableRel (@E.eq F Feq Fone Fadd Fmul a d).
  Proof. intros [? ?] [? ?]; eapply @dec_and; eapply Hdec. Defined.
End E.

Lemma B_nonzero : not (E.eq B E.zero). Proof. vm_decide. Qed.
Axiom l_order_B : E.eq (Z.to_nat l * B) zero.

Global Instance Ed25519 : @EdDSA point E.eq add zero E.opp E.mul b H c n l B Eenc enc :=
  {
    EdDSA_c_valid := c_valid;
    EdDSA_n_ge_c := n_ge_c;
    EdDSA_n_le_b := n_le_b;
    EdDSA_B_not_identity := B_nonzero;
    EdDSA_l_prime := prime_l;
    EdDSA_l_odd := l_odd;
    EdDSA_l_order_B := l_order_B
  }.
