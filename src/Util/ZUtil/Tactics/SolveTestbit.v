Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Notations.

Require Import Crypto.Util.Decidable.

Local Open Scope Z_scope.

Import Notations.

(* Tactic for solving equality of testbits of operators. testbit_pos assumes all
testbit indices will be positive, but can probably be faster in those cases *)

Local Lemma mod_pow2_ones a m :
  a mod 2 ^ m = if (Z_lt_dec m 0) then 0 else a &' Z.ones m.
Proof. destruct (Z_lt_dec m 0). rewrite Z.pow_neg_r, Zmod_0_r; lia.
       symmetry; apply Z.land_ones; lia. Qed.

Local Lemma bits_1 m :
  Z.testbit 1 m = if Z.eq_dec m 0 then true else false.
Proof.
  destruct (Z.eq_dec m 0); subst. reflexivity.
  destruct (Z_lt_dec m 0). rewrite Z.testbit_neg_r by lia. reflexivity.
  rewrite Z.bits_above_log2; simpl; try reflexivity; lia. Qed.

Hint Rewrite Z.bits_opp Z.shiftr_spec Z.shiftl_spec Z.lor_spec Z.land_spec Z.ones_spec_full Z.bits_0 bits_1 andb_false_r andb_true_r orb_false_r orb_true_r mod_pow2_ones : testbit_pos_rewrite.

Hint Rewrite <- Z.ones_equiv : testbit_pos_rewrite.

Ltac solve_pos_testbit :=
  repeat (match goal with
          | [ |- _ ] => progress autorewrite with testbit_pos_rewrite
          | [ |- context[Z.testbit (2 ^ ?m) ?m] ] => rewrite Z.pow2_bits_true
          | [ |- context[Z.testbit (2 ^ ?m) ?i] ] => rewrite Z.pow2_bits_false by lia
          | [ |- context[Z.testbit (?a / 2)] ] =>
            replace (a / 2) with (a / 2 ^ 1) by (apply f_equal2; [reflexivity|apply Z.pow_1_r]); rewrite <- Z.shiftr_div_pow2
          | [ |- context[Z.testbit (?a / 2 ^ ?k)] ] =>
            rewrite <- Z.shiftr_div_pow2
          | [ |- context[_ - ?a + ?a] ] => rewrite Z.sub_simpl_r
          | [ |- context[Z_lt_dec ?a ?b] ] =>
            destruct (Z_lt_dec a b)
          | [ |- context[?a <? ?b] ] =>
            let E := fresh in
            destruct (a <? b) eqn:E; [rewrite Z.ltb_lt in E|rewrite Z.ltb_ge in E]
          | [ |- context[?a <=? ?b] ] =>
            let E := fresh in
            destruct (a <=? b) eqn:E; [rewrite Z.leb_le in E|rewrite Z.leb_gt in E]
          | [ |- context[?a =? ?b] ] =>
            let E := fresh in
            destruct (a =? b) eqn:E; [rewrite Z.eqb_eq in E; subst|rewrite Z.eqb_neq in E]
          | [ H: 0 <= ?a < 2 ^ ?m |- context[Z.testbit ?a ?i] ] =>
            assert (m <= i) by lia;
            assert (2 ^ m <= 2 ^ i) by (apply Z.pow_le_mono; lia);
            rewrite (Z.bits_above_log2 a i) by (try apply Log2.Z.log2_lt_pow2_alt; lia)
          | [ |- Z.testbit _ _ = Z.testbit _ _ ] =>
            apply f_equal2; lia
          | [ |- _ <= _ < _] => auto with zarith
          end; simpl; subst);
  try reflexivity; try discriminate; try lia.

Local Lemma shiftr_spec_full a k i :
  Z.testbit (a >> k) i = if (Z_lt_dec i 0) then false else Z.testbit a (i + k).
Proof.
  destruct (Z_lt_dec i 0). rewrite Z.testbit_neg_r by lia. reflexivity.
  apply Z.shiftr_spec; lia. Qed.

Local Lemma shiftl_spec_full a k i :
  Z.testbit (a << k) i = if (Z_lt_dec i 0) then false else Z.testbit a (i - k).
Proof.
  destruct (Z_lt_dec i 0). rewrite Z.testbit_neg_r by lia. reflexivity.
  apply Z.shiftl_spec; lia. Qed.

Local Lemma bits_opp_full a i :
  Z.testbit (- a) i = if (Z_lt_dec i 0) then false else negb (Z.testbit (Z.pred a) i).
Proof.
  destruct (Z_lt_dec i 0). rewrite Z.testbit_neg_r by lia. reflexivity.
  apply Z.bits_opp; lia. Qed.

Local Lemma pow2_bits_full m i :
  Z.testbit (2 ^ m) i =
  if (Z_lt_dec m 0) then false else if (Z.eq_dec i m) then true else false.
Proof.
  destruct (Z_lt_dec m 0); [now rewrite Z.pow_neg_r, Z.bits_0|].
  destruct (Z.eq_dec i m); subst.
  - apply Z.pow2_bits_true; lia.
  - apply Z.pow2_bits_false; lia. Qed.

Hint Rewrite bits_opp_full shiftl_spec_full shiftr_spec_full Z.lor_spec Z.land_spec Z.ones_spec_full Z.bits_0 bits_1 andb_false_r andb_true_r orb_false_r orb_true_r mod_pow2_ones : testbit_rewrite.

Hint Rewrite <- Z.ones_equiv : testbit_rewrite.

Ltac solve_testbit :=
  repeat (match goal with
          | [ |- _ ] => progress autorewrite with testbit_rewrite
          | [ |- context[Z.testbit (2 ^ ?m) ?i] ] => rewrite pow2_bits_full
          | [ |- context[Z.testbit (?a / 2)] ] =>
            replace (a / 2) with (a / 2 ^ 1) by (apply f_equal2; [reflexivity|apply Z.pow_1_r]); rewrite <- Z.shiftr_div_pow2 by lia
          | [ |- context[Z.testbit (?a / 2 ^ ?k)] ] =>
            rewrite <- Z.shiftr_div_pow2 by lia
          | [ |- context[_ - ?a + ?a] ] => rewrite Z.sub_simpl_r
          | [ |- context[Z_lt_dec ?a ?b] ] =>
            destruct (Z_lt_dec a b)
          | [ |- context[Z.eq_dec ?a ?b] ] =>
            destruct (Z.eq_dec a b)
          | [ |- context[?a <? ?b] ] =>
            let E := fresh in
            destruct (a <? b) eqn:E; [rewrite Z.ltb_lt in E|rewrite Z.ltb_ge in E]
          | [ |- context[?a <=? ?b] ] =>
            let E := fresh in
            destruct (a <=? b) eqn:E; [rewrite Z.leb_le in E|rewrite Z.leb_gt in E]
          | [ |- context[?a =? ?b] ] =>
            let E := fresh in
            destruct (a =? b) eqn:E; [rewrite Z.eqb_eq in E; subst|rewrite Z.eqb_neq in E]
          | [ H: 0 <= ?a < 2 ^ ?m |- context[Z.testbit ?a ?i] ] =>
            assert (m <= i) by lia;
            assert (2 ^ m <= 2 ^ i) by (apply Z.pow_le_mono; lia);
            rewrite (Z.bits_above_log2 a i) by (try apply Log2.Z.log2_lt_pow2_alt; lia)
          | [ |- Z.testbit _ _ = Z.testbit _ _ ] =>
            apply f_equal2; lia
          | [ |- false = _ ] => rewrite Z.testbit_neg_r by lia
          | [ |- _ = false ] => rewrite Z.testbit_neg_r by lia
          | [ |- _ <= _ < _] => auto with zarith
          end; simpl; subst);
  try reflexivity; try discriminate; try lia.

Ltac solve_using_pos_testbit := apply Z.bits_inj'; intros; solve_pos_testbit.
Ltac solve_using_testbit := apply Z.bits_inj'; intros; solve_testbit.
