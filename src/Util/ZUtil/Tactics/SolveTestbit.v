Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

(* Require Import Crypto.Util.ZUtil.Definitions. *)
(* Require Import Crypto.Util.ZUtil.Notations. *)
Require Import Crypto.Util.ZUtil.Log2.
(* Require Import Crypto.Util.ZUtil.Ones. *)
Require Import Crypto.Util.ZUtil.Testbit.
(* Require Import Crypto.Util.ZUtil.SignBit. *)
(* Require Import Crypto.Util.ZUtil.Zselect. *)

(* Require Import Crypto.Util.LetIn. *)

(* Import Notations. *)

Local Open Scope Z_scope.

Hint Rewrite Z.bits_opp Z.shiftr_spec Z.lor_spec Z.land_spec Z.shiftl_spec Z.ones_spec_full Z.bits_0 andb_false_r andb_true_r orb_false_r orb_true_r : testbit_rewrite.

Hint Rewrite <- Z.ones_equiv Z.land_ones : testbit_rewrite.

Ltac solve_testbit :=
  repeat (match goal with
          | [ |- _ ] => progress autorewrite with testbit_rewrite
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
  try reflexivity; try discriminate; lia.

Ltac solve_using_testbit := apply Z.bits_inj'; intros; solve_testbit.
