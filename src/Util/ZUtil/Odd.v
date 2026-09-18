From Coq Require Import ZArith.
From Coq Require Import Znumtheory.
From Coq Require Import Lia.
Require Import Crypto.Util.ZUtil.Divide.
Local Open Scope Z_scope.

Module Z.
  Lemma prime_odd_or_2 : forall p (prime_p : prime p), p = 2 \/ Z.odd p = true.
  Proof.
    intros p prime_p.
    apply Decidable.imp_not_l; try apply Z.eq_decidable.
    intros p_neq2.
    pose proof (Zmod_odd p) as mod_odd.
    destruct (Sumbool.sumbool_of_bool (Z.odd p)) as [? | p_not_odd]; auto.
    rewrite p_not_odd in mod_odd.
    apply Zmod_divides in mod_odd; try lia.
    destruct mod_odd as [c c_id].
    rewrite Z.mul_comm in c_id.
    apply Zdivide_intro in c_id.
    apply prime_divisors in c_id; auto.
    destruct c_id; [lia | destruct H; [lia | destruct H; auto] ].
    pose proof (prime_ge_2 p prime_p); lia.
  Qed.

  Lemma odd_mod : forall a b, (b <> 0)%Z ->
    Z.odd (a mod b) = if Z.odd b then xorb (Z.odd a) (Z.odd (a / b)) else Z.odd a.
  Proof.
    intros a b H.
    rewrite Zmod_eq_full by assumption.
    rewrite <-Z.add_opp_r, Z.odd_add, Z.odd_opp, Z.odd_mul.
    case_eq (Z.odd b); intros; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; auto using Bool.xorb_false_r.
  Qed.

  Lemma odd_square_mod_pow2_1mod8 n a 
    (Hnn : 0 < n) (H : 0 <= a < 2 ^ n) (Hodd : a mod 2 = 1)
    (Hr :exists r, r ^ 2 mod 2 ^ n = a mod 2 ^ n) : a mod 8 = 1.
  Proof.
    case Hr as [r Hr].
    rewrite <-(Z.mod_small a (2^n)) by trivial.
    case (Z.eqb_spec n 1) as [->|].
    { rewrite Z.mod_small; zify; Z.to_euclidean_division_equations; lia. }
    case (Z.eqb_spec n 2) as [->|].
    { rewrite <-Z.mod_pow_l in Hr; set (r mod 2 ^ 2) as r' in *.
      assert (r' = 0 \/ r' = 1 \/ r' = 2 \/ r' = 3);
        zify; Z.to_euclidean_division_equations; lia. }
    rewrite Z.mod_mod_divide by (apply (Z.divide_pow_le 2 3); lia).
    apply (f_equal (fun x => x mod 8)) in Hr.
    rewrite 2Z.mod_mod_divide, <-Z.mod_pow_l in Hr by (apply (Z.divide_pow_le 2 3); lia).
    set (r mod 8) as r' in *.
    assert (r' = 0 \/ r' = 1 \/ r' = 2 \/ r' = 3 \/ r' = 4 \/ r' = 5 \/ r' = 6 \/ r' = 7)
      by (zify; Z.to_euclidean_division_equations; lia).
    clearbody r'; intuition subst r'; cbn in *; (zify; Z.to_euclidean_division_equations; lia).
  Qed.
End Z.
