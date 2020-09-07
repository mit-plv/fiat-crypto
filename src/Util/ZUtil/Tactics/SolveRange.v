Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Local Open Scope Z_scope.

(** Extension of lia to solve ranges involving bitwise operations and power *)

Module Z.

Ltac solve_range :=
    repeat match goal with
           | [ |- context[?a ^ ?b] ] => unique assert (0 <= a ^ b) by (apply Z.pow_nonneg; lia)
           | [ |- context[?a ^ ?b] ] => unique assert (0 < a ^ b) by (apply Z.pow_pos_nonneg; lia)
           | [ |- ?a &' ?b < _ ] => unique assert (a &' b <= a) by (apply Z.land_upper_bound_l; lia)
           | [ |- ?a &' ?b < _ ] => unique assert (a &' b <= b) by (apply Z.land_upper_bound_r; lia)
           | [ |- _ /\ _ ] => split
           | [ |- _ <= _ < _ ] => split
           | [ |- _ / _ < _ ] => apply Z.div_lt_upper_bound
           | [ |- _ |' _ < 2 ^ _ ] => apply Z.lor_range
           | [ |- Z.truncating_shiftl _ _ _ < 2 ^ _ ] => apply Z.truncating_shiftl_range
           | _ => progress Z.zero_bounds
           | [ |- 0 <= Z.truncating_shiftl _ _ _ ] => apply Z.truncating_shiftl_nonneg
           | [ |- context[ ?a ^ _ * ?a] ] => rewrite (Z.mul_comm _ a), Z.pow_mul_base
           | [ |- context[ ?a * ?a ^ _] ] => rewrite Z.pow_mul_base
           | [ |- context[ _ - ?a + ?a] ] => rewrite Z.sub_simpl_r
           | [ |- context[ _ >> _] ] => rewrite Z.shiftr_div_pow2 by lia
           | [ |- context[ _ >> _] ] => rewrite Z.shiftr_mul_pow2 by lia
           | [ |- context[ _ << _] ] => rewrite Z.shiftl_mul_pow2 by lia
           | [ |- context[ _ << _] ] => rewrite Z.shiftl_div_pow2 by lia
           | [ |- context[ ?a ^ ?b * ?a ^ ?c ] ] =>
             let Hn := fresh in
             let Hm := fresh in
             rewrite <- Z.pow_add_r;
             assert (Hn : a ^ b <= a ^ (b + c)) by (apply Z.pow_le_mono_r; lia);
             assert (Hm : a ^ c <= a ^ (b + c)) by (apply Z.pow_le_mono_r; lia);
             ring_simplify (b + c) in Hn;
             ring_simplify (b + c) in Hm;
             ring_simplify (b + c)
           | [ |- context[ Z.ones_from _ _ ] ] => unfold Z.ones_from
           | [ |- context[ Z.ones_at _ _ ] ] => unfold Z.ones_at
           | [ |- context[ Z.ones _ ] ] => rewrite Z.ones_equiv, <- Z.sub_1_r; ring_simplify
           | [ |- context[ Z.pred _ ] ] => rewrite <- Z.sub_1_r; ring_simplify
           | [ |- _ ] => nia
    end.

End Z.
