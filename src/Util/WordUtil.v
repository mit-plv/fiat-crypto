Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.NatUtil.
Require Import Bedrock.Word.

Local Open Scope nat_scope.

Lemma pow2_id : forall n, pow2 n = 2 ^ n.
Proof.
  induction n; intros; simpl; auto.
Qed.

Lemma Zpow_pow2 : forall n, pow2 n = Z.to_nat (2 ^ (Z.of_nat n)).
Proof.
  induction n; intros; auto.
  simpl pow2.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by apply Zle_0_nat.
  rewrite untimes2.
  rewrite Z2Nat.inj_mul by (try apply Z.pow_nonneg; omega).
  rewrite <- IHn.
  auto.
Qed.

Lemma wordToN_NToWord_idempotent : forall sz n, (n < Npow2 sz)%N ->
  wordToN (NToWord sz n) = n.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat.
  rewrite wordToNat_natToWord_idempotent; rewrite Nnat.N2Nat.id; auto.
Qed.

Lemma NToWord_wordToN : forall sz w, NToWord sz (wordToN w) = w.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat, Nnat.Nat2N.id.
  apply natToWord_wordToNat.
Qed.

Lemma bound_check_nat_N : forall x n, (Z.to_nat x < 2 ^ n)%nat -> (Z.to_N x < Npow2 n)%N.
Proof.
  intros x n bound_nat.
  rewrite <- Nnat.N2Nat.id, Npow2_nat.
  replace (Z.to_N x) with (N.of_nat (Z.to_nat x)) by apply Z_nat_N.
  apply (Nat2N_inj_lt _ (pow2 n)).
  rewrite pow2_id; assumption.
Qed.

Definition wfirstn n {m} (w : Word.word m) {H : n <= m} : Word.word n.
  refine (Word.split1 n (m - n) (match _ in _ = N return Word.word N with
                            | eq_refl => w
                            end)); abstract omega. Defined.
