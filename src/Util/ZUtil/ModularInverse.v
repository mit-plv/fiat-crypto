Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Integer.Abstract.ZGcd.
Local Open Scope Z_scope.

Module Z.
  Definition bezout n m : Z * Z :=
    let (u, v, d, _, _) := euclid n m in
    if (Z_le_dec 0 d)
    then (u, v)
    else (-u, -v).

  Lemma bezout_correct n m :
    (fst (bezout n m)) * n + (snd (bezout n m)) * m = Z.gcd n m.
  Proof.
    unfold bezout.
    destruct (euclid n m) as [u v d Heq Hgcd].
    destruct (Z_le_dec 0 d) as [ Hle | Hnle ]; cbn [fst snd].
    (* 0 <= d *)
    apply (Zis_gcd_gcd n m d Hle) in Hgcd. rewrite <-Hgcd in Heq. apply Heq.
    (* d < 0 *)
    pose proof Z.gcd_nonneg n m.
    destruct (Zis_gcd_unique n m _ _ Hgcd (Zgcd_is_gcd n m)) as [Hpos | Hneg].
    (* d = Z.gcd n m *)
    rewrite Hpos in Hnle. contradiction.
    (* d = - Z.gcd n m *)
    rewrite !Z.opp_eq_mul_m1.
    rewrite <-!(Z.mul_assoc _ (-1) _), !(Z.mul_comm (-1)), !Z.mul_assoc.
    rewrite <-Z.mul_add_distr_r. rewrite Heq.
    rewrite <-Z.opp_eq_mul_m1. apply Z.eq_opp_r. assumption.
  Qed. 

  Definition mod_inv n m : Z := fst (bezout n m).

  (* mod_inv is correct if n and m are relatively prime *)
  Lemma mod_inv_correct_full n m :
    1 < m -> Z.gcd n m = 1 -> (n * mod_inv n m) mod m = 1.
  Proof.
    unfold mod_inv; intros ? Hgcd.
    transitivity (1 mod m); [ | apply Z.mod_1_l; omega ].
    rewrite <-Hgcd, <-bezout_correct.
    rewrite Z.mod_add by omega.
    f_equal; auto using Z.mul_comm.
  Qed.

  (* mod_inv is correct if m is prime *)
  Lemma mod_inv_correct n m :
    prime m -> 0 < n < m -> (n * mod_inv n m) mod m = 1.
  Proof.
    intros Hprime ?.
    pose proof prime_ge_2 _ Hprime.
    pose proof rel_prime_le_prime n m Hprime ltac:(omega).
    apply mod_inv_correct_full; [ omega | ].
    apply Zgcd_1_rel_prime; auto.
  Qed.
End Z.