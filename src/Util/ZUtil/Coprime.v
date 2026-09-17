From Stdlib Require Import ZArith Zdivisibility Lia.
Local Open Scope Z_scope.

Module Z.
  Lemma coprime_comm a b : Z.coprime a b <-> Z.coprime b a.
  Proof. cbv [Z.coprime]; rewrite Z.gcd_comm; reflexivity. Qed.

  Lemma coprime_mul_r_iff a b c : Z.coprime a (b * c) <-> Z.coprime a b /\ Z.coprime a c.
  Proof.
    split; [|intros []; auto using Z.coprime_mul_r].
    cbv [Z.coprime]; intros H; split;
      apply Z.divide_1_r_nonneg; auto using Z.gcd_nonneg; rewrite <-H;
      apply Z.gcd_greatest; auto using Z.gcd_divide_l;
      [apply Z.divide_mul_l|apply Z.divide_mul_r]; apply Z.gcd_divide_r.
  Qed.

  Lemma coprime_mul_l_iff a b c : Z.coprime (a * b) c <-> Z.coprime a c /\ Z.coprime b c.
  Proof.
    split; [|intros []; auto using Z.coprime_mul_l].
    intros H; symmetry in H; apply coprime_mul_r_iff in H; intuition symmetry; trivial.
  Qed.

  Lemma coprime_pow_r_iff a b n (Hn : 0 < n) : Z.coprime a (b ^ n) <-> Z.coprime a b.
  Proof.
    rewrite <-(Z.succ_pred n), Z.pow_succ_r, coprime_mul_r_iff by lia.
    split; [intros []; trivial|]; intros; split; trivial; apply Z.coprime_pow_r; trivial; lia.
  Qed.

  Lemma coprime_pow_l_iff a b n (Hn : 0 < n) : Z.coprime (a ^ n) b <-> Z.coprime a b.
  Proof. split; intros; symmetry; apply (coprime_pow_r_iff _ _ _ Hn); symmetry; trivial. Qed.

  Lemma coprime_prime_prime p q (Hp : Z.prime p) (Hq : Z.prime q) (H : p <> q) : Z.coprime p q.
  Proof. apply Z.coprime_prime_l; trivial; intros ?%Z.divide_prime_prime; auto. Qed.

  Lemma coprime_sqr_l_iff a b : Z.coprime (a ^ 2) b <-> Z.coprime a b.
  Proof. apply coprime_pow_l_iff; lia. Qed.

  Lemma coprime_prime_r a p (H : Z.prime p) : Z.coprime a p <-> a mod p <> 0.
  Proof.
    rewrite coprime_comm. etransitivity. { apply Z.coprime_prime_l_iff; trivial. }
    pose proof Z.not_prime_0.
    rewrite Z.mod_divide; intuition subst; contradiction.
  Qed.

  Lemma prime_odd (p : Z) : Z.prime p -> 3 <= p -> p mod 2 = 1.
  Proof.
    case (Z.mod_pos_bound p 2 eq_refl) as [[]%Zle_lt_or_eq ?]; trivial.
    { intros _ _; eapply Z.le_antisymm;
      solve [ eapply Z.lt_pred_le + eapply Zlt_succ_le; trivial ]. }
    intros [? A] B.
    case (A 2). { split. exact eq_refl. eapply Z.le_succ_l; trivial. }
    apply Z.mod_divide. inversion 1. congruence.
  Qed.
End Z.
