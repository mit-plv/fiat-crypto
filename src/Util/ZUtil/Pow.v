Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ListUtil.
Require Import Lists.List.
Local Open Scope Z_scope.

Module Z.
  Lemma base_pow_neg b n : n < 0 -> b^n = 0.
  Proof.
    destruct n; intro H; try reflexivity; compute in H; congruence.
  Qed.
  Hint Rewrite base_pow_neg using zutil_arith : zsimplify.

  Lemma nonneg_pow_pos a b : 0 < a -> 0 < a^b -> 0 <= b.
  Proof.
    destruct (Z_lt_le_dec b 0); intros; auto.
    erewrite Z.pow_neg_r in * by eassumption.
    lia.
  Qed.
  Hint Resolve nonneg_pow_pos (fun n => nonneg_pow_pos 2 n Z.lt_0_2) : zarith.
  Lemma nonneg_pow_pos_helper a b dummy : 0 < a -> 0 <= dummy < a^b -> 0 <= b.
  Proof. eauto with zarith lia. Qed.
  Hint Resolve nonneg_pow_pos_helper (fun n dummy => nonneg_pow_pos_helper 2 n dummy Z.lt_0_2) : zarith.

  Lemma div_pow2succ : forall n x, (0 <= x) ->
    n / 2 ^ Z.succ x = Z.div2 (n / 2 ^ x).
  Proof.
    intros.
    rewrite Z.pow_succ_r, Z.mul_comm by auto.
    rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
    rewrite Zdiv2_div.
    reflexivity.
  Qed.

  Definition pow_sub_r'
    := fun a b c y H0 H1 => @Logic.eq_trans _ _ _ y (@Z.pow_sub_r a b c H0 H1).
  Definition pow_sub_r'_sym
    := fun a b c y p H0 H1 => Logic.eq_sym (@Logic.eq_trans _ y _ _ (Logic.eq_sym p) (@Z.pow_sub_r a b c H0 H1)).
  Hint Resolve pow_sub_r' pow_sub_r'_sym Z.eq_le_incl : zarith.
  Hint Resolve (fun b => f_equal (fun e => b ^ e)) (fun e => f_equal (fun b => b ^ e)) : zarith.

  Lemma two_p_two_eq_four : 2^(2) = 4.
  Proof. reflexivity. Qed.
  Hint Rewrite <- two_p_two_eq_four : push_Zpow.

  Lemma pow_pos_le a b : 0 < a -> 0 < b -> a <= a ^ b.
  Proof.
    intros; transitivity (a ^ 1).
    { rewrite Z.pow_1_r; reflexivity. }
    { apply Z.pow_le_mono; auto with zarith. }
  Qed.
  Hint Resolve pow_pos_le : zarith.

  Lemma pow_pos_lt a b : 1 < a -> 1 < b -> a < a ^ b.
  Proof.
    intros; eapply Z.le_lt_trans with (m:=a ^ 1).
    { rewrite Z.pow_1_r; reflexivity. }
    { apply Z.pow_lt_mono_r; auto with zarith. }
  Qed.
  Hint Resolve pow_pos_lt : zarith.

  Lemma pow_div_base a b : a <> 0 -> 0 < b -> a ^ b / a = a ^ (b - 1).
  Proof. intros; rewrite Z.pow_sub_r, Z.pow_1_r; lia. Qed.
  Hint Rewrite pow_div_base using zutil_arith : pull_Zpow.

  Lemma pow_mul_base a b : 0 <= b -> a * a ^ b = a ^ (b + 1).
  Proof. intros; rewrite <-Z.pow_succ_r, <-Z.add_1_r by lia; reflexivity. Qed.
  Hint Rewrite pow_mul_base using zutil_arith : pull_Zpow.

  (* faster modular exponentation for computing (not sure where to put this) *)
  Definition sq_and_multiply_mod_aux a p m n :=
    fold_right
      (fun i res =>
         ((a - 1) * ((p / (2 ^ (Z.of_nat i))) mod 2) + 1) * (res ^ 2) mod m)
      (a mod m) (seq 0 n).

  Definition sq_and_multiply_mod a p m :=
    sq_and_multiply_mod_aux a p m (Z.to_nat (Z.log2 p)).

  Lemma sq_and_multiply_mod_aux_S a p m n :
    sq_and_multiply_mod_aux a p m (S n) =
    ((a - 1) * (p mod 2) + 1) * (sq_and_multiply_mod_aux a (p / 2) m n) ^ 2 mod m.
  Proof.
    unfold sq_and_multiply_mod_aux; simpl.
    repeat apply f_equal2; try lia; [now rewrite Z.div_1_r|].
    rewrite map_seq_succ, fold_right_map; apply fold_right_ext; intros i j.
    rewrite Z.div_div, pow_mul_base by (try apply Z.pow_pos_nonneg; lia).
    replace (Z.of_nat i + 1) with (Z.of_nat (i + 1)) by lia; reflexivity. Qed.

  Lemma sq_and_multiply_mod_correct_aux a p m n
        (Hm : 0 < m)
        (Hp : 1 <= p)
        (Hn : (Z.to_nat (Z.log2 p)) = n) :
    sq_and_multiply_mod_aux a p m n = a ^ p mod m.
  Proof.
    assert (0 <= Z.log2 p) by apply Z.log2_nonneg.
    assert (logpn : Z.log2 p = Z.of_nat n) by (rewrite <- (Z2Nat.id (Z.log2 p)) by assumption; apply f_equal; assumption).
    generalize dependent p; induction n as [|n IHn]; intros.
    - assert (log2p0 : Z.log2 p = 0) by lia.
      pose proof ((proj1 (Z.log2_null p)) log2p0).
      assert (p = 1) by lia; subst.
      rewrite Z.pow_1_r; reflexivity.
    - assert (0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
      assert (1 < p) by (apply Z.log2_lt_cancel; simpl; lia).
      assert (1 <= p / 2) by (apply Zdiv_le_lower_bound; lia).
      rewrite sq_and_multiply_mod_aux_S, IHn; try apply Z.log2_nonneg; [|lia| |].
      rewrite Z.pow_2_r, Z.mul_assoc, Z.mul_mod_idemp_r by lia.
      rewrite Z.mul_comm, Z.mul_assoc, Z.mul_mod_idemp_r by lia.
      rewrite Z.mul_comm; apply f_equal2; [|lia].
      rewrite Z.mul_assoc, <- Z.pow_add_r by lia.
      rewrite Z.add_diag. rewrite (Z.div_mod p 2) at 3 by lia.
      rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia).
      apply f_equal2. reflexivity.
      pose proof (Z.mod_pos_bound p 2 ltac:(lia)).
      assert (p01 : p mod 2 = 0 \/ p mod 2 = 1) by lia; destruct p01 as [p0|p1];
        rewrite ?p0, ?p1; lia. 
      replace 2 with (2 ^ 1) by reflexivity. 
      rewrite <- Z.shiftr_div_pow2, Z.log2_shiftr, Z.max_r by lia.
      rewrite logpn, Nat2Z.inj_succ, Z.sub_1_r, Z.pred_succ by lia; apply Nat2Z.id.
      replace 2 with (2 ^ 1) by reflexivity.
      rewrite <- Z.shiftr_div_pow2, Z.log2_shiftr, Z.max_r; lia. Qed.

  Lemma sq_and_multiply_mod_correct a p m
        (Hm : 0 < m)
        (Hp : 1 <= p) :
    sq_and_multiply_mod a p m = a ^ p mod m.
  Proof. apply sq_and_multiply_mod_correct_aux; auto. Qed.
End Z.
