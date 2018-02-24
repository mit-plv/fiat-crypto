Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.


(** This file proves an implementation of the variant of Barrett reduction
    described in
    http://www.ridiculousfish.com/blog/posts/labor-of-division-episode-i.html *)


(** To simulate C behavior with fixed-width words, we introduce a word data type
    and associated operations that automatically take a modulus. We'll then
    prove the moduli are all no-ops (save one which is a subtraction).

    TODO(davidben): This does not perfectly match C's behavior. In C, operations
    on types smaller than [int], notably [uint16_t], promote both types to [int]
    first. Assuming a standard 32-bit [int], multiplying two [uint32_t]s is
    always defined, but multiplying two [uint16_t]s may not be! However, we
    never multiply [uint16_t]s, and we would otherwise need an unreasonably
    large expression to overflow [int] by way of promoted [uint16_t]
    additions. *)

(** First, the C data types will ultimately compile down to a bunch of extra
    modulus operations, which we must remove. Define a primitive [wrap]
    operation operations which we'll instruct [cbn] to leave alone and match on
    in the proof script. *)
Definition wrap (bits val : Z) : Z := val mod 2^bits.

(** A [word] is a C data type with a specified bit size. *)
Inductive word (bits : Z) :=
| Word : Z -> word bits.

Definition to_Z {bits : Z} (a : word bits) : Z :=
  match a with Word v => v end.
Definition to_word {bits : Z} (val : Z) :=
  Word bits (wrap bits val).

Definition word_binop
           (aw bw : Z)
           (op : Z -> Z -> Z)
           (a : word aw) (b : word bw) : word (Z.max aw bw) :=
  to_word (op (to_Z a) (to_Z b)).

Definition word_add {aw bw : Z} := word_binop aw bw Z.add.
Definition word_sub {aw bw : Z} := word_binop aw bw Z.sub.
Definition word_mul {aw bw : Z} := word_binop aw bw Z.mul.
Definition word_div {aw bw : Z} := word_binop aw bw Z.div.

(** The type of a shift expression in C is the type of the first argument, not
    the larger of the two type. *)
Definition word_shiftl {aw bw : Z} (a : word aw) (b : word bw) : word aw :=
  to_word (Z.shiftl (to_Z a) (to_Z b)).
Definition word_shiftr {aw bw : Z} (a : word aw) (b : word bw) : word aw :=
  to_word (Z.shiftr (to_Z a) (to_Z b)).

Definition word_cast (from to : Z) (a : word from) : word to :=
  to_word (to_Z a).

Definition u16 := word 16.
Definition u32 := word 32.
Definition u64 := word 64.

Definition to_u16 {bits : Z} := word_cast bits 16.
Definition to_u32 {bits : Z} := word_cast bits 32.
Definition to_u64 {bits : Z} := word_cast bits 64.

Definition Z_to_u16 := @to_word 16.
Definition Z_to_u32 := @to_word 32.
Definition Z_to_u64 := @to_word 64.

(** [to_u32'] is identical to [to_u32], but it is expected to be a subtraction
    of 2^32, rather than a no-op. *)
Definition to_u32' {bits : Z} (a : word bits) : u32 :=
  Z_to_u32 ((to_Z a) - 2^32).

Delimit Scope word_scope with word.
Bind Scope word_scope with word.
Infix "+" := word_add : word_scope.
Infix "-" := word_sub : word_scope.
Infix "*" := word_mul : word_scope.
Infix "/" := word_div : word_scope.
Infix "<<" := word_shiftl : word_scope.
Infix ">>" := word_shiftr : word_scope.
Notation "1" := (Z_to_u32 1) : word_scope.
Notation "32" := (Z_to_u32 32) : word_scope.


Definition num_bits (a : Z) : Z :=
  match a with
  | Z0 => 0
  | Zpos p => Zpos (Pos.size p)
  | Zneg _ => 0 (* A [u32] is always non-negative, so this does not come up. *)
  end.

Definition BN_num_bits_word (a : u32) : u32 :=
  Z_to_u32 (num_bits (to_Z a)).

(** See [mod_u16] in
    https://boringssl-review.googlesource.com/#/c/boringssl/+/25887. *)
Definition mod_u16 (n : u32) (d : u16) : u16 :=
  let p := to_u32 (BN_num_bits_word (to_u32 (d - 1))) in
  let m := to_u32' ((((to_u64 1) << (32 + p)) + d - 1) / d) in
  let q := to_u32 (((to_u64 m) * n) >> 32) in
  let t := to_u32 (((n - q) >> 1) + q) in
  let t := to_u32 (t >> (p - 1)) in
  let n := to_u32 (n - d * t) in
  to_u16 n.


(** Proofs *)

Lemma num_bits_log2_up (a : Z) :
  num_bits (a - 1) = Z.log2_up a.
Proof.
  unfold Z.log2_up, Z.log2, num_bits.
  destruct (1 ?= a) eqn:H.
  { (* [1 = a] *)
    rewrite Z.compare_eq_iff in H.
    rewrite <- H.
    reflexivity. }
  { (* [1 < a] *)
    rewrite Z.compare_lt_iff in H.
    assert (0 < a - 1) by lia.
    rewrite Z.sub_1_r in *.
    destruct (Z.pred a); try lia.
    destruct p; cbn; lia. }
  { (* [1 > a] *)
    rewrite Z.compare_gt_iff in H.
    assert (a - 1 < 0) by lia.
    destruct (a - 1); lia. }
Qed.

Lemma wrap_bound (a b : Z) (H : 0 < a) :
  0 <= wrap a b < 2^a.
Proof.
  unfold wrap.
  Z.div_mod_to_quot_rem.
  lia.
Qed.

Lemma remove_outer_wrap (a a' b : Z) (H : 0 < a' <= a) :
  wrap a (wrap a' b) = wrap a' b.
Proof.
  unfold wrap.
  apply Z.mod_small.
  Z.div_mod_to_quot_rem.
  assert (2^a' <= 2^a) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma divide_pow (a b c : Z) (Ha : 0 < a) (Hb : 0 <= b <= c) :
  (a^b | a^c).
Proof.
  exists (a^(c - b)).
  rewrite <- Z.pow_add_r; try f_equal; lia.
Qed.

Lemma remove_inner_wrap (a a' b : Z) (H : 0 < a <= a') :
  wrap a (wrap a' b) = wrap a b.
Proof.
  unfold wrap.
  rewrite (Znumtheory.Zmod_div_mod (2^a) (2^a') b);
    try apply Z.pow_pos_nonneg;
    try apply divide_pow;
    lia.
Qed.

Lemma double_wrap (a a' b : Z) (Ha : 0 < a) (Ha' : 0 < a') :
  wrap a (wrap a' b) = wrap (Z.min a a') b.
Proof.
  destruct (a <? a') eqn:H.
  { apply Z.ltb_lt in H.
    rewrite Z.min_l by lia.
    apply remove_inner_wrap.
    lia. }
  { apply Z.ltb_ge in H.
    rewrite Z.min_r by lia.
    apply remove_outer_wrap.
    lia. }
Qed.

Lemma a_minus_b_div_2_plus_b (a b : Z) (H : a >= b) :
  (a - b) / 2 + b = (a + b) / 2.
Proof. Z.div_mod_to_quot_rem; lia. Qed.

Lemma p_bound (d bits : Z) (Hbits : 0 < bits) (H : 1 < d < 2^bits) :
  0 < Z.log2_up d <= bits.
Proof.
  split.
  - apply Z.log2_up_pos; lia.
  - apply Z.log2_up_le_pow2; lia.
Qed.

Lemma pow2_log2_up_bounds (d : Z) (H : 1 < d) :
  d <= 2^(Z.log2_up d) < d + d.
Proof.
  pose proof (Z.log2_up_spec d H).
  assert (2 ^ Z.log2_up d = 2 * (2 ^ Z.pred (Z.log2_up d))).
  { rewrite <- Z.pow_succ_r by (apply Z.lt_le_pred; apply Z.log2_up_pos; lia).
    f_equal.
    lia. }
  lia.
Qed.

Lemma m_bound (d bits : Z) (Hbits : 0 < bits) (H : 1 < d < 2^bits) :
  2^bits <= (2^(bits + Z.log2_up d) + d - 1) / d < 2 * 2^bits.
Proof.
  rewrite !Z.pow_add_r by (auto with zarith).
  pose proof (pow2_log2_up_bounds d (proj1 H)).
  split.
  - apply Z.div_le_lower_bound; nia.
  - apply Z.div_lt_upper_bound; nia.
Qed.

Lemma division_shrinks (a b c : Z) (Hb : 0 < b) (H : 0 <= a < c) :
  a / b < c.
Proof. Z.div_mod_to_quot_rem; nia. Qed.

Lemma mul_div_ceil_ge (a b : Z) (Hb : 0 < b) :
  a <= b * ((a + b - 1) / b).
Proof. Z.div_mod_to_quot_rem; nia. Qed.

(** This is the main theorem this algorithm relies on. *)
Lemma division_algorithm (bits n d k : Z)
      (Hbits : 0 < bits)
      (Hn : 0 <= n < 2^bits)
      (Hd : 1 < d)
      (Hk : bits + Z.log2_up d <= k) :
  n * ((2^k + d - 1) / d) / 2^k = n / d.
Proof.
  (* Help [lia] and [nia] out. *)
  pose proof (Z.log2_up_nonneg d).
  pose proof (pow2_log2_up_bounds d Hd).
  assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).

  assert (n/d <= n * ((2^k + d - 1) / d) / 2^k).
  { (* This direction is true independent of [Hk]. *)
    assert (2^k <= d * ((2 ^ k + d - 1) / d)) by (apply mul_div_ceil_ge; lia).
    apply Z.div_le_lower_bound; try lia.
    rewrite Z.div_mul_le by (try auto with zarith; lia).
    apply Z.div_le_upper_bound; try lia.
    nia. }
  assert (n * ((2^k + d - 1) / d) / 2^k <= n / d).
  { assert (div_mul_le_inner : n * ((2^k + d - 1) / d) / 2^k <=
                               (n * (2^k + d - 1) / d) / 2^k).
    { apply Z.div_le_mono; try apply Z.div_mul_le; lia. }
    rewrite div_mul_le_inner.
    replace (n * (2^k + d - 1)) with (n * 2^k + n * (d - 1)) by nia.
    (* Swap [d] and [2^k] in the denominator. *)
    rewrite Z.div_div by lia.
    rewrite (Z.mul_comm d (2^k)).
    rewrite <- Z.div_div by lia.
    (* We now can extract the [n * 2^k] term from the inner division. *)
    rewrite Z.div_add_l by lia.
    (* We show the error term is zero, which allows the inequality to hold. *)
    assert (zero_error : n * (d - 1) / 2 ^ k = 0).
    { apply Z.div_small.
      assert (2^bits * 2^(Z.log2_up d) <= 2^k) by
          (rewrite <- Z.pow_add_r; try apply Z.pow_le_mono_r; lia).
      nia. }
    rewrite zero_error.
    auto with zarith. }
  lia.
Qed.

(** Peel off one innermost [wrap], and replace it with the expected
    bounds. Before doing so, introduce a lemma into the context that the value
    is bounded. This is allows later goals to make use of earlier bounds.

    TODO(davidben): Most of the slowness comes from these intermediate
    hypotheses. The proofs need them, but only those one or two layers down. Can
    we be smarter about retaining them? *)
Local Ltac replace_innermost_wrap expr :=
  match expr with
  | context[wrap ?x ?y] =>
    first [ replace_innermost_wrap y |
            assert (0 <= (wrap x y) < 2^x) by (apply wrap_bound; lia);
            replace (wrap x y) with y in * ]
  end.

(** Finally, the correctness proof. *)
Theorem mod_u16_spec (n d : Z) (Hn : 0 <= n < 2^32) (Hd : 1 < d < 2^16) :
  to_Z (mod_u16 (Z_to_u32 n) (Z_to_u16 d)) = n mod d.
Proof.
  unfold mod_u16.
  (* Evaluate away everything except for exponentations, which are
     still useful, and our [wrap] metadata. *)
  cbn -[Z.pow num_bits wrap].

  (* The solver needs some help getting these in the context. *)
  assert (Hlog : 0 < Z.log2_up d <= 16) by (apply p_bound; lia).
  assert (d <= 2^(Z.log2_up d) < d + d) by (apply pow2_log2_up_bounds; lia).
  assert (2^(Z.log2_up d) < 2 ^ 17) by lia.
  assert (2^32 <= (2^32 * 2^(Z.log2_up d) + d - 1) / d < 2 * 2^32) by
      (rewrite <- Z.pow_add_r by lia; apply m_bound; lia).

  (* Convert shifts to multiplication and divison. *)
  rewrite !Z.shiftl_mul_pow2 by (apply wrap_bound; lia).
  rewrite !Z.shiftr_div_pow2 by (apply wrap_bound; lia).
  rewrite !Z.mul_1_l.
  rewrite !Z.pow_1_r.

  (* Replace all the [to_word] calls with their expected bounds. *)
  repeat match goal with
         | [ |- ?x = n mod d ] =>
           match goal with
           (* Evaluate away the [Z.min]s. *)
           | _ => progress cbn -[Z.pow Z.add Z.mul wrap]
           (* Remove obviously pointless casts. The solver could handle them,
              but this cuts down on the number of generated hypotheses. *)
           | [ |- context[wrap ?x (wrap ?x' ?y)] ] =>
             replace (wrap x (wrap x' y)) with (wrap (Z.min x x') y) by
                 (symmetry; apply double_wrap; lia)
           | [ |- context[wrap ?x n] ] =>
             replace (wrap x n) with n by (unfold wrap; rewrite Z.mod_small; lia)
           | [ |- context[wrap ?x d] ] =>
             replace (wrap x d) with d by (unfold wrap; rewrite Z.mod_small; lia)
           | [ |- context[wrap ?x (Zpos ?p)] ] =>
             replace (wrap x (Zpos p)) with (Zpos p) by reflexivity
           (* Perform rewrites as soon as possible, so the generated hypotheses
              match too. *)
           | _ => rewrite a_minus_b_div_2_plus_b
           | _ => rewrite num_bits_log2_up
           | _ => rewrite Z.pow_add_r by lia
           | _ => replace_innermost_wrap x
           end
         end;

    repeat unfold wrap in *;

    repeat match goal with
           (* Normalize a few things. *)
           | _ => apply Z.le_ge
           | _ => apply Z.lt_gt
           | [ |- _ = _ mod _ ] => symmetry
           (* Apply these transforms everywhere. *)
           | _ => apply Z.mod_small
           | _ => split
           (* Everything is positive, so these tend to be easy. *)
           | [ |- 0 <= _ * _ ] => nia
           (* Don't touch the goals that involve the final division
              expression. We'll dispatch them separately. *)
           | [ |- context[d * (_ / 2^_)] ] => fail 1
           (* The solver needs some help for this one, otherwise the [Z.div_*]
              theorems below break apart the numerator term. *)
           | [ _ : 0 <= ?x < ?y |- ?x / _ < ?y ] => apply division_shrinks
           (* Simplify the various inequalities. *)
           | _ => apply Z.div_le_upper_bound
           | _ => apply Z.div_lt_upper_bound
           | _ => apply Z.div_le_lower_bound
           | _ => apply Z.pow_nonneg
           | _ => apply Z.pow_pos_nonneg
           (* Only apply in one direction. *)
           | [ |- 0 <= _ - _ ] => apply Z.le_0_sub
           | _ => apply Z.mul_le_mono_nonneg_r
           (* [nia] is rather slow, and only one case needs it. *)
           | [ _ : 0 <= ?x < _, _ : 0 <= ?y < _ |- ?x * ?y < ?z ] => nia
           | _ => lia
           end;

    (* Clear the now unnecessary intermediate hypotheses. *)
    clear - Hn Hd Hlog;

    (* Invert the various transforms to get to the main theorem. *)
    repeat match goal with
           | _ => rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia)
           | _ => rewrite <- Z.pow_succ_r by lia
           | _ => rewrite <- Z.add_1_r
           | _ => rewrite Z.sub_add
           | _ => rewrite Zplus_minus
           | _ => rewrite <- Z.pow_add_r by lia
           | _ => rewrite <- Z.mul_add_distr_l
           | _ => rewrite <- Z.div_add_l by lia
           | [ |- context[?x * ?y + ?z * ?x] ] => rewrite (Z.mul_comm z x)
           end;

    (* And finish with the main theorem. *)
    rewrite (division_algorithm 32) by lia;
    Z.div_mod_to_quot_rem;
    nia.
Qed.
