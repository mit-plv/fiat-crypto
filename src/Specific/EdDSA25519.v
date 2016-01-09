Require Import ZArith.ZArith Zpower ZArith Znumtheory.
Require Import NPeano.
Require Import Crypto.Galois.EdDSA Crypto.Galois.GaloisField.
Require Import Crypto.Curves.PointFormats.
Require Import Crypto.Util.NatUtil Crypto.Util.ZUtil Crypto.Util.NumTheoryUtil.
Require Import Bedrock.Word.
Require Import VerdiTactics.
Require Import Decidable.
Require Import Omega.

Module Modulus25519 <: Modulus.
  Local Open Scope Z_scope.
  Definition two_255_19 := two_p 255 - 19.
  Lemma two_255_19_prime : prime two_255_19. Admitted.
  Definition prime25519 := exist _ two_255_19 two_255_19_prime.
  Definition modulus := prime25519.
End Modulus25519.

Local Open Scope nat_scope.

Module EdDSA25519_Params <: EdDSAParams.
  Definition q : Prime := Modulus25519.modulus.
  Ltac prime_bound := pose proof (prime_ge_2 q (proj2_sig q)); try omega.

  Lemma q_odd : Z.to_nat q > 2.
  Proof.
    assert (q >= 0)%Z by (cbv; congruence).
    assert (q > 2)%Z by (simpl; cbv; auto).
    rewrite Nat2Z.inj_gt.
    rewrite Z2Nat.id by omega; auto.
  Qed.

  Module Modulus_q := Modulus25519.

  Definition b := 256.
  Lemma b_valid : (2 ^ (Z.of_nat b - 1) > q)%Z.
  Proof.
    remember 19%Z as y.
    replace (Z.of_nat b - 1)%Z with 255%Z by auto.
    assert (y > 0)%Z by (rewrite Heqy; cbv; auto).
    remember (2 ^ 255)%Z as x.
    simpl. unfold Modulus25519.two_255_19.
    rewrite two_p_equiv.
    rewrite <- Heqy.
    rewrite <- Heqx.
    omega.
  Qed.

  (* TODO *)
  Parameter H : forall {n}, word n -> word (b + b).
  
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

  Module GFDefs := GaloisField Modulus_q.
  Import GFDefs.
  Local Open Scope GF_scope.

  Definition a := GFopp 1%GF.
  Lemma a_nonzero : a <> 0%GF.
  Proof.
    unfold a, GFopp; simpl.
    intuition.
    assert (proj1_sig 0%GF = proj1_sig (0 - 1)%GF) by (rewrite H0; reflexivity).
    assert (proj1_sig 0%GF = 0%Z) by auto.
    assert (proj1_sig (0 - 1)%GF <> 0%Z). {
      simpl; intuition.
      apply Z.rem_mod_eq_0 in H3; [|unfold two_255_19; cbv; omega].
      unfold Z.rem in H3; simpl in H3.
      congruence.
    }
    omega.
  Qed.

  Lemma q_1mod4 : (q mod 4 = 1)%Z.
  Proof.
    simpl.
    unfold Modulus25519.two_255_19.
    rewrite Zminus_mod.
    simpl.
    auto.
  Qed.

  Lemma square_mod_GF : forall (a x : Z),
    (0 <= x < q /\ x * x mod q = a)%Z ->
    (inject x * inject x = inject a)%GF.
  Proof.
    intros.
    destruct H0.
    rewrite <- inject_distr_mul.
    rewrite inject_mod_eq.
    replace modulus with q by auto.
    rewrite H1; reflexivity.
  Qed.

  Lemma a_square_old : exists x, (x * x = a)%GF.
  Proof.
    intros.
    pose proof (minus1_square_1mod4 q (proj2_sig q) q_1mod4).
    destruct H0.
    pose proof (square_mod_GF (q - 1)%Z x H0).
    exists (inject x).
    unfold a.
    replace (GFopp 1) with (inject (q - 1)) by galois.
    auto.
  Qed.
  
  (* TODO *)
  Parameter d : GF.
  Parameter sqrt_a : GF.
  Axiom d_nonsquare : forall x, x^2 <> d.
  Axiom a_square: (sqrt_a^2 = a)%GF.
  Axiom char_gt_2: (1+1 <> 0)%GF.

  Module CurveParameters <: TwistedEdwardsParams Modulus_q.
    Module GFDefs := GFDefs.
    Definition a : GF := a.
    Definition sqrt_a := sqrt_a.
    Definition a_nonzero := a_nonzero.
    Definition a_square := a_square.
    Definition d := d.
    Definition d_nonsquare := d_nonsquare.
    Definition char_gt_2 := char_gt_2.
  End CurveParameters.
  Module Facts := CompleteTwistedEdwardsFacts Modulus_q CurveParameters.
  Module Import Curve := Facts.Curve.

  (* TODO *)
  Parameter B : point.
  Axiom B_not_identity : B <> zero.

  (* TODO *)
  Parameter l : Prime.
  Axiom l_odd : (Z.to_nat l > 2)%nat.
  Axiom l_order_B : (scalarMult (Z.to_nat l) B) = zero.

  (* H' is the identity function. *)
  Definition H'_out_len (n : nat) := n.
  Definition H' {n} (w : word n) := w.

  Lemma l_bound : Z.to_nat l < pow2 b. (* TODO *)
  Admitted.

  Lemma GF_mod_bound : forall (x : GF), (0 <= x < q)%Z.
  Proof.
    intros.
    assert (0 < q)%Z by (prime_bound; omega).
    pose proof (Z.mod_pos_bound x q H0).
    rewrite <- (inject_eq x).
    replace q with modulus in * by auto.
    unfold GFToZ, inject in *.
    auto.
  Qed.

  Definition Fq_enc (x : GF) : word (b - 1) := natToWord (b - 1) (Z.to_nat x).
  Definition Fq_dec (x_ : word (b - 1)) : option GF :=
      Some (inject (Z.of_nat (wordToNat x_))).
  Lemma Fq_encoding_valid : forall x : GF, Fq_dec (Fq_enc x) = Some x.
  Proof.
    unfold Fq_dec, Fq_enc; intros.
    f_equal.
    rewrite wordToNat_natToWord_idempotent. {
      rewrite Z2Nat.id by apply GF_mod_bound.
      apply inject_eq.
    } {
      rewrite <- Nnat.N2Nat.id.
      rewrite Npow2_nat.
      apply (Nat2N_inj_lt (Z.to_nat x) (pow2 (b - 1))).
      replace (pow2 (b - 1)) with (Z.to_nat (2 ^ (Z.of_nat b - 1))%Z) by (rewrite Zpow_pow2; auto).
      pose proof (GF_mod_bound x).
      pose proof b_valid.
      apply Z2Nat.inj_lt; try omega.
    }
  Qed.
  Definition FqEncoding : encoding of GF as word (b-1) :=
    Build_Encoding GF (word (b-1)) Fq_enc Fq_dec Fq_encoding_valid.

  Definition Fl_enc (x : {s : nat | s mod (Z.to_nat l) = s}) : word b :=
    natToWord b (proj1_sig x).
  Definition Fl_dec (x_ : word b) : option {s:nat | s mod (Z.to_nat l) = s} :=
    match (lt_dec (wordToNat x_) (Z.to_nat l)) with
    | left A => Some (exist _ _ (Nat.mod_small _ (Z.to_nat l) A))
    | _ => None
    end.
  Lemma Fl_encoding_valid : forall x, Fl_dec (Fl_enc x) = Some x.
  Proof.
    unfold Fl_enc, Fl_dec; intros.
    assert (proj1_sig x < (Z.to_nat l)). {
      destruct x; simpl.
      apply Nat.mod_small_iff in e; auto.
      pose proof l_odd; omega.
    }
    rewrite wordToNat_natToWord_idempotent by 
      (pose proof l_bound; apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id; rewrite Npow2_nat; omega).
    case_eq (lt_dec (proj1_sig x) (Z.to_nat l)); intros; try omega.
    destruct x.
    do 2 (simpl in *; f_equal).
    apply Eqdep_dec.UIP_dec.
    apply eq_nat_dec.
  Qed.
  Definition FlEncoding :=
    Build_Encoding {s:nat | s mod (Z.to_nat l) = s} (word b) Fl_enc Fl_dec Fl_encoding_valid.
  
  (* TODO *)
  Parameter PointEncoding : encoding of point as word b.
End EdDSA25519_Params.
