Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.
Local Open Scope Z_scope.

Module Z.
  Lemma truncating_shiftl_correct bw x y
  : Z.truncating_shiftl bw x y = (x << y) mod 2^bw.
  Proof. reflexivity. Qed.

  Lemma truncating_shiftl_correct_land_ones bw x y
  : Z.truncating_shiftl bw x y = (x << y) &' 
      Z.ones ltac:(match eval hnf in (1 mod 0) with | 0 => exact (Z.max 0 bw) | _ => exact bw end).
  Proof.
    rewrite truncating_shiftl_correct.
    destruct (Z_lt_le_dec bw 0).
    - assert (Hbw : Z.max 0 bw = 0) by lia.
      assert (H0 : Z.pred (2 ^ 0) = 0) by reflexivity.
      now rewrite ?Hbw, Z.ones_equiv, ?H0, ?(Z.base_pow_neg 2 bw), ?Z.land_0_r, ?Z.land_m1_r, ?Zmod_0_r.
    - assert (Hbw : Z.max 0 bw = bw) by lia.
      rewrite ?Hbw. now rewrite Z.land_ones.
  Qed.

  Lemma truncating_shiftl_correct_land_pow2 bw x y
  : Z.truncating_shiftl bw x y = (x << y) &' (2^(ltac:(match eval hnf in (1 mod 0) with | 0 => exact (Z.max 0 bw) | _ => exact bw end)) - 1).
  Proof.
    rewrite truncating_shiftl_correct_land_ones, Z.ones_equiv, <- Z.sub_1_r.
    reflexivity.
  Qed.

  Lemma truncating_shiftl_mod a b (Hb : 0 < b):
    Z.truncating_shiftl b a (b - 1) = 2 ^ (b - 1) * (a mod 2).
  Proof.
    unfold Definitions.Z.truncating_shiftl. rewrite Z.shiftl_mul_pow2 by lia.
    replace (2^b) with (2 * 2^(b-1)) by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
    rewrite Zmult_mod_distr_r; ring. Qed.

  Lemma truncating_shiftl_testbit_spec_full m a k i :
    Z.testbit (Z.truncating_shiftl m a k) i
    = if (i <? 0) then false else if (orb (i <? m) ((1 mod 0 =? 1) && (m <? 0))) then Z.testbit a (i - k) else false.
  Proof. unfold Z.truncating_shiftl. Z.solve_testbit. Qed.

  Hint Rewrite truncating_shiftl_testbit_spec_full : testbit_rewrite.

  Lemma truncating_shiftl_truncating_shiftl m a p q
        (Hp : 0 <= p)
        (Hq : 0 <= q) :
    Z.truncating_shiftl m (Z.truncating_shiftl m a p) q
    = Z.truncating_shiftl m a (p + q).
  Proof. Z.solve_using_testbit. Qed.
  Lemma truncating_shiftl0 m k :
    Z.truncating_shiftl m 0 k = 0.
  Proof. Z.solve_using_testbit. Qed.

  Lemma truncating_shiftl_lor m a b k :
    Z.truncating_shiftl m (a |' b) k
    = (Z.truncating_shiftl m a k) |' (Z.truncating_shiftl m b k).
  Proof. Z.solve_using_testbit. Qed.

  (* (* not compatible with x mod 0 = x *)
  Lemma truncating_shiftl_large m a k (Hk : k >= m) :
    Z.truncating_shiftl m a k = 0.
  Proof. Z.solve_using_testbit. Qed. *)

  Lemma truncating_shiftl_range m a k (Hm : 0 <= m) :
    0 <= Z.truncating_shiftl m a k < 2 ^ m.
  Proof. unfold Z.truncating_shiftl; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia. Qed.

  Hint Resolve truncating_shiftl_range : zarith.

  Lemma truncating_shiftl_nonneg m a k (Hm : 0 <= m) :
    0 <= Z.truncating_shiftl m a k.
  Proof. unfold Z.truncating_shiftl; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia. Qed.
End Z.
