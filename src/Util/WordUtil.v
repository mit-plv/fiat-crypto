Require Import NPeano.
Require Import ZArith.ZArith.
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

Definition wfirstn n {m} (w : Word.word m) {H : n <= m} : Word.word n.
  refine (Word.split1 n (m - n) (match _ in _ = N return Word.word N with
                            | eq_refl => w
                            end)); abstract omega. Defined.
