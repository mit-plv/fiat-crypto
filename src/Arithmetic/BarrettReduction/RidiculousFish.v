Require Import Coq.NArith.BinNat.
Require Import Coq.micromega.Lia.

Open Scope N_scope.


(* This file proves an implementation of the variant of Barrett
   reduction described in
   http://www.ridiculousfish.com/blog/posts/labor-of-division-episode-i.html *)


(* To simulate C behavior with fixed-width words, we introduce a word
   data type and associated operations that automatically take
   modulus. We'll then prove the moduli are all no-ops (save one which
   is a subtraction).

   TODO(davidben): This does not perfectly match C's behavior. In C,
   operations on types smaller than [int], notably [uint16_t], promote
   both types to [int] first. Assuming a standard 32-bit [int],
   multiplying two [uint32_t]s is always defined, but multiplying two
   [uint16_t]s may not be! However, we never multiply [uint16_t]s, and
   we would otherwise need an unreasonable large expression to
   overflow [int] by way of promoted [uint16_t] additions. *)

(* First, the C data types will ultimately compile down to a bunch of
   extra modulus operations, which we must remove. Define three
   primitive wrapping operations which we'll instruct [cbn] to leave
   alone and match on in the proof script.

   [wrap] is used when we expect [val] to already be reduced. [wrap']
   is when we expect one subtraction by [2^bits]. [sub_wrapped] can be
   implemented in terms of [wrap'], but we make it a primitive so the
   proof script can treat it more efficiently. *)
Definition wrap (bits val : N) : N := val mod 2^bits.
Definition wrap' := wrap.
Definition sub_wrapped (bits a b : N) : N := wrap' bits (a + 2^bits - b).

(* A [word] is a C data type with a specified bit size. *)
Inductive word (bits : N) :=
| Word : N -> word bits.

Definition to_N {bits : N} (a : word bits) : N :=
  match a with Word _ v => v end.
Definition to_word {bits : N} (val : N) :=
  Word bits (wrap bits val).

Definition word_binop
           (aw bw : N)
           (op : N -> N -> N)
           (a : word aw) (b : word bw) : word (N.max aw bw) :=
  to_word (op (to_N a) (to_N b)).

Definition word_add {aw bw : N} := word_binop aw bw N.add.
Definition word_sub {aw bw : N} := word_binop aw bw (sub_wrapped (N.max aw bw)).
Definition word_mul {aw bw : N} := word_binop aw bw N.mul.
Definition word_div {aw bw : N} := word_binop aw bw N.div.
Definition word_shiftl {aw bw : N} := word_binop aw bw N.shiftl.
Definition word_shiftr {aw bw : N} := word_binop aw bw N.shiftr.

Definition word_cast (from to : N) (a : word from) : word to :=
  to_word (to_N a).

Definition u16 := word 16.
Definition u32 := word 32.
Definition u64 := word 64.

Definition to_u16 {bits : N} := word_cast bits 16.
Definition to_u32 {bits : N} := word_cast bits 32.
Definition to_u64 {bits : N} := word_cast bits 64.

(* [to_u32'] is identical to [to_u32], but it is expected to be a
   subtraction of 2^32, rather than a no-op. *)
Definition to_u32' {bits : N} (a : word bits) : u32 :=
  Word 32 (wrap' 32 (to_N a)).

Definition N_to_u16 := @to_word 16.
Definition N_to_u32 := @to_word 32.
Definition N_to_u64 := @to_word 64.

Delimit Scope word_scope with word.
Bind Scope word_scope with word.
Infix "+" := word_add : word_scope.
Infix "-" := word_sub : word_scope.
Infix "*" := word_mul : word_scope.
Infix "/" := word_div : word_scope.
Infix "<<" := word_shiftl (at level 30, no associativity) : word_scope.
Infix ">>" := word_shiftr (at level 30, no associativity) : word_scope.
Notation "1" := (N_to_u32 1) : word_scope.
Notation "32" := (N_to_u32 32) : word_scope.


Definition BN_num_bits_word (a : u32) : u32 :=
  N_to_u32 (N.size (to_N a)).

(* See [mod_u16] in https://boringssl-review.googlesource.com/#/c/boringssl/+/25887. *)
Definition mod_u16 (n : u32) (d : u16) : u16 :=
  let p := to_u32 (BN_num_bits_word (to_u32 (d - 1))) in
  let m := to_u32' ((((to_u64 1) << (32 + p)) + d - 1) / d) in
  let q := to_u32 (((to_u64 m) * n) >> 32) in
  let t := to_u32 (((n - q) >> 1) + q) in
  let t := to_u32 (t >> (p - 1)) in
  let n := to_u32 (n - d * t) in
  to_u16 n.


(* Proofs *)

Lemma wrap_bound (a b : N) :
  wrap a b < 2^a.
Proof.
  unfold wrap.
  apply N.mod_upper_bound.
  apply N.pow_nonzero.
  lia.
Qed.

Lemma remove_outer_wrap (a a' b : N) (H : a' <= a) :
  wrap a (wrap a' b) = wrap a' b.
Proof.
  unfold wrap.
  apply N.mod_small.
  assert (b mod 2^a' < 2^a') by (apply N.mod_upper_bound; apply N.pow_nonzero; lia).
  assert (2^a' <= 2^a) by (apply N.pow_le_mono_r; lia).
  lia.
Qed.

Lemma remove_inner_wrap (a a' b : N) (H : a' >= a) :
  wrap a (wrap a' b) = wrap a b.
Proof.
  unfold wrap.
  rewrite <- (N.sub_add a a') by lia.
  rewrite N.pow_add_r.
  rewrite N.mul_comm.
  rewrite N.mod_mul_r by (apply N.pow_nonzero; lia).
  rewrite N.mul_comm.
  rewrite N.mod_add by (apply N.pow_nonzero; lia).
  apply N.mod_mod.
  apply N.pow_nonzero.
  lia.
Qed.

Lemma double_wrap (a a' b : N) :
  wrap a (wrap a' b) = wrap (N.min a a') b.
Proof.
  destruct (a <? a') eqn:H.
  { apply N.ltb_lt in H.
    rewrite N.min_l by lia.
    apply remove_inner_wrap.
    lia. }
  { apply N.ltb_ge in H.
    rewrite N.min_r by lia.
    apply remove_outer_wrap.
    lia. }
Qed.

(* [lia] and [nia] need some help with exponents, and [cbn] alone
   often unfolds too much. *)
Ltac unfold_exponents :=
  cbn [N.pow BinPos.Pos.pow BinPos.Pos.iter BinPos.Pos.mul] in *.

Lemma sub_wrapped_noop (bits a b : N) (H : b <= a < 2^bits) :
  sub_wrapped bits a b = a - b.
Proof.
  unfold sub_wrapped, wrap', wrap.
  rewrite N.add_comm.
  rewrite <- N.add_sub_assoc by lia.
  rewrite N.add_mod by lia.
  rewrite N.mod_same by lia.
  cbn.
  rewrite N.mod_mod by lia.
  apply N.mod_small.
  lia.
Qed.

Lemma a_minus_b_div_2_plus_b (a b : N) (H : a >= b) :
  (a - b) / 2 + b = (a + b) / 2.
Proof.
  rewrite <- N.div_add by lia.
  f_equal.
  lia.
Qed.

Lemma p_bound (d bits : N) (H : 1 < d < 2^bits) :
  1 <= N.size (d - 1) <= bits.
Proof.
  rewrite N.size_log2 by lia.
  assert (N.log2 (d - 1) < bits) by (apply N.log2_lt_pow2; lia).
  lia.
Qed.

Lemma ceil_log2_lt (d : N) (H : 1 < d) :
  2^(N.size (d - 1)) < d + d.
Proof.
  pose proof (N.size_le (d - 1)).
  rewrite N.succ_double_spec in *.
  lia.
Qed.

Lemma ceil_log2_ge (d : N) (H : 1 < d) :
  2^(N.size (d - 1)) >= d.
Proof.
  pose proof (N.size_gt (d - 1)).
  lia.
Qed.

Lemma m_bound (d bits : N) (H : 1 < d < 2^bits) :
  2^bits <= (2^(bits + N.size (d - 1)) + d - 1) / d < 2 * 2^bits.
Proof.
  rewrite !N.pow_add_r.
  split.
  { (* 2^e <= m *)
    apply N.div_le_lower_bound; try lia.
    assert (2^(N.size (d - 1)) >= d).
    { apply ceil_log2_ge; lia. }
    nia. }
  { (* m < 2 * 2^e *)
    apply N.div_lt_upper_bound; try lia.
    assert (2^(N.size (d - 1)) < d + d).
    { apply ceil_log2_lt; lia. }
    (* Subtraction is saturating, so nia needs a bit of help to group
       [d - 1] together. *)
    rewrite <- N.add_sub_assoc by lia.
    nia. }
Qed.

Lemma mod_sub_once (a b : N) (H : b <= a < 2*b) :
  a mod b = a - b.
Proof.
  assert (1 = a / b).
  { apply (N.div_unique a b 1 (a - b)); lia. }
  rewrite N.mod_eq; nia.
Qed.

Lemma division_shrinks (a b c : N) (Hnz : b <> 0) (H : a < c) :
  a / b < c.
Proof.
  apply N.div_lt_upper_bound; try lia.
  nia.
Qed.

Lemma mul_div_ceil_ge (a b : N) (H : b <> 0) :
  a <= b * ((a + b - 1) / b).
Proof.
  rewrite (N.div_mod a b) by lia.
  set (q := a / b).
  set (r := a mod b).
  assert (r < b) by (apply N.mod_upper_bound; lia).
  destruct (r =? 0) eqn:Hr.
  { (* r = 0 *)
    apply N.eqb_eq in Hr.
    replace r with 0.
    rewrite !N.add_0_r.
    replace ((b * q + b - 1) / b) with q by
        (rewrite <- N.add_sub_assoc by lia;
         apply (N.div_unique _ b q (b - 1));
         lia).
    lia. }
  { (* r != 0 *)
    apply N.eqb_neq in Hr.
    replace ((b * q + r + b - 1) / b) with (q + 1) by
        (replace (b * q + r + b - 1) with (b * (q + 1) + (r - 1)) by lia;
         apply (N.div_unique _ b (q + 1) (r - 1));
         lia).
    lia. }
Qed.

(* This is the main theorem this algorithm relies on. *)
Lemma division_algorithm (bits n d k : N)
      (Hn : n < 2^bits)
      (Hd : 1 < d)
      (Hk : bits + N.size (d - 1) <= k) :
  n * ((2^k + d - 1) / d) / 2^k = n / d.
Proof.
  assert (n/d <= n * ((2^k + d - 1) / d) / 2^k).
  { (* This direction is true independent of [Hk]. *)
    apply N.div_le_lower_bound; try apply N.pow_nonzero; try lia.
    rewrite N.div_mul_le by lia.
    apply N.div_le_upper_bound; try apply N.pow_nonzero; try lia.
    rewrite (N.mul_comm n _).
    rewrite N.mul_assoc.
    assert (2^k <= d * ((2 ^ k + d - 1) / d)) by (apply mul_div_ceil_ge; lia).
    nia. }
  assert (n * ((2^k + d - 1) / d) / 2^k <= n / d).
  { assert (div_mul_le_inner : n * ((2 ^ k + d - 1) / d) / 2^k <=
                               (n * (2 ^ k + d - 1) / d) / 2 ^ k).
    { apply N.div_le_mono; try (apply N.pow_nonzero; lia).
      apply N.div_mul_le.
      lia. }
    rewrite div_mul_le_inner.
    replace (n * (2^k + d - 1)) with (n * 2^k + n * (d - 1)) by nia.
    (* Swap [d] and [2^k] in the denominator. *)
    rewrite N.div_div by (try apply N.pow_nonzero; lia).
    rewrite (N.mul_comm d (2^k)).
    rewrite <- N.div_div by (try apply N.pow_nonzero; lia).
    (* We now can extract the [n * 2^k] term from the inner division. *)
    rewrite N.div_add_l by (try apply N.pow_nonzero; lia).
    (* We show the error term is zero, which allows the inequality to hold. *)
    assert (zero_error : n * (d - 1) / 2 ^ k = 0).
    { apply N.div_small.
      assert (2^bits * 2^(N.size (d - 1)) <= 2^k) by
          (rewrite <- N.pow_add_r; apply N.pow_le_mono_r; lia).
      assert (d <= 2^(N.size (d - 1))) by (apply N.ge_le; apply ceil_log2_ge; lia).
      nia. }
    rewrite zero_error.
    rewrite N.add_0_r.
    lia. }
  lia.
Qed.

(* Peel off one innermost [wrap], and replace it with the expected
   bounds. Before doing so, introduce a lemma into the context that
   the value is bounded. This is allows later goals to make use of
   earlier bounds. *)
Ltac replace_innermost_to_word expr :=
  match expr with
  | context[wrap ?x ?y] =>
    first [ replace_innermost_to_word y |
            assert ((wrap x y) < 2^x) by (apply wrap_bound);
            replace (wrap x y) with y in * ]
  | context[wrap' ?x ?y] =>
    first [ replace_innermost_to_word y |
            assert ((wrap' x y) < 2^x) by (unfold wrap'; apply wrap_bound);
            replace (wrap' x y) with (y - 2^x) in * ]
  | context[sub_wrapped ?x ?y ?z] =>
    first [ replace_innermost_to_word y |
            replace_innermost_to_word z |
            assert ((sub_wrapped x y z) < 2^x) by (unfold sub_wrapped, wrap';
                                                   apply wrap_bound);
            replace (sub_wrapped x y z) with (y - z) in * ]
  end.

Theorem mod_u16_spec (n d : N) (Hn : n < 2^32) (Hd : 1 < d < 2^16) :
  to_N (mod_u16 (N_to_u32 n) (N_to_u16 d)) = n mod d.
Proof.
  unfold mod_u16.
  (* Evaluate away everything except for exponentations, which are
     still useful, and our [wrap], etc., metadata. *)
  cbn -[N.pow wrap wrap' sub_wrapped].

  (* The solver needs some help getting these in the context. *)
  assert (1 <= N.size (d - 1) <= 16) by (apply p_bound; lia).
  assert (2^(N.size (d - 1)) < d + d) by (apply ceil_log2_lt; lia).
  assert (2^(N.size (d - 1)) < 2 ^ 17) by (unfold_exponents; lia).
  assert (2^32 <= (2^(32 + N.size (d - 1)) + d - 1) / d < 2 * 2^32) by
      (apply m_bound; unfold_exponents; lia).

  (* Convert shifts to multiplication and divison. *)
  rewrite !N.shiftl_mul_pow2.
  rewrite !N.shiftr_div_pow2.
  rewrite !N.mul_1_l.
  rewrite !N.pow_1_r.

  (* Replace all the [to_word] calls with their expected bounds. *)
  repeat match goal with
         | [ |- ?x = n mod d ] =>
           match goal with
           (* Evaluate away the [N.min]s. *)
           | _ => progress cbn -[N.pow N.add N.mul wrap wrap']
           (* Remove obviously pointless casts, before the solver expands too
              much. *)
           | [ |- context[wrap ?x (wrap' ?x ?y)] ] =>
             replace (wrap x (wrap' x y)) with (wrap' x y) by
                 (unfold wrap'; symmetry; apply remove_outer_wrap; lia)
           | [ |- context[wrap ?x (sub_wrapped ?x ?y ?z)] ] =>
             replace (wrap x (sub_wrapped x y z)) with (sub_wrapped x y z) by
                 (unfold sub_wrapped, wrap';
                  symmetry;
                  apply remove_outer_wrap;
                  lia)
           | [ |- context[wrap ?x (wrap ?x' ?y)] ] =>
             replace (wrap x (wrap x' y)) with (wrap (N.min x x') y) by
                 (symmetry; apply double_wrap; lia)
           (* Perform [a_minus_b_div_2_plus_b] earlier, so the
              generated hypotheses match too. *)
           | _ => rewrite a_minus_b_div_2_plus_b
           | _ => replace_innermost_to_word x
           end
         | _ => rewrite sub_wrapped_noop
         end;

    repeat unfold sub_wrapped, wrap', wrap in *;

    repeat match goal with
           (* Normalize a few things. *)
           | _ => apply N.le_ge
           | _ => apply N.lt_gt
           | [ |- _ = _ mod _ ] => symmetry
           (* Apply these transforms everywhere. *)
           | _ => apply N.mod_small
           | _ => split
           (* Don't touch the goals that involve the final division
              expression. We'll dispatch them separately. *)
           | [ |- context[d * (_ / 2^_)] ] => fail 1
           (* The solver needs some help for this one. *)
           | [ _ : ?x < ?y |- ?x / _ < ?y ] => apply division_shrinks
           (* Smash the bounds subgoals away. *)
           | _ => apply mod_sub_once
           | _ => rewrite N.pow_add_r in *
           | _ => apply N.div_le_upper_bound
           | _ => apply N.div_lt_upper_bound
           | _ => apply N.pow_nonzero
           | _ => apply N.mul_le_mono_r
           | _ => progress unfold_exponents
           (* Erase irrelevant hypotheses before we start running the
              slow solvers. *)
           | [ H : context[n] |- _ ] => match goal with
                                        | [ |- context[n] ] => fail 1
                                        | _ => clear H
                                        end
           | [ H : context[d] |- _ ] => match goal with
                                        | [ |- context[d] ] => fail 1
                                        | _ => clear H
                                        end
           (* [nia] is rather slow, and only one case needs it. *)
           | [ _ : ?x < _, _ : ?y < _ |- ?x * ?y < ?z ] => nia
           | _ => lia
           end;

    (* Invert the various transforms to get to the main theorem. *)
    repeat match goal with
           | [ |- _ <= N.size _ ] => rewrite N.size_log2; lia
           | [ |- context[?x * ?y + ?z * ?x]] => rewrite (N.mul_comm z x)
           | [ |- context[?x + ?y - ?x]] => rewrite (N.add_comm x y)
           | _ => rewrite N.div_div
           | _ => apply N.pow_nonzero
           | _ => rewrite <- N.pow_succ_r'
           | _ => rewrite <- N.add_1_r
           | _ => rewrite <- N.pow_add_r
           | _ => rewrite <- N.mul_add_distr_l
           | _ => rewrite N.sub_add
           | _ => rewrite N.add_sub
           | _ => rewrite N.add_sub_assoc
           | _ => rewrite <- N.div_add_l
           | _ => lia
           end;

    (* And finish with the main theorem. *)
    rewrite (division_algorithm 32) by lia;
    try rewrite <- N.mod_eq;
    try apply N.mul_div_le;
    (* [lia] needs some help on these two. *)
    try match goal with
        | [ |- ?x mod ?y < 2^_ ] =>
          assert (x mod y < y) by (apply N.mod_upper_bound; lia)
        | [ |- ?x * (?y / ?x) < 2^_ ] =>
          assert (x * (y / x) <= y) by (apply N.mul_div_le; lia)
        end;
    lia.
Qed.
