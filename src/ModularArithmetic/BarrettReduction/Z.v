(*** Barrett Reduction *)
(** This file implements Barrett Reduction on [Z].  We follow Wikipedia. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics.

Local Open Scope Z_scope.

Section barrett.
  Context (n a : Z)
          (n_reasonable : n <> 0).
  (** Quoting Wikipedia <https://en.wikipedia.org/wiki/Barrett_reduction>: *)
  (** In modular arithmetic, Barrett reduction is a reduction
      algorithm introduced in 1986 by P.D. Barrett. A naive way of
      computing *)
  (** [c = a mod n] *)
  (** would be to use a fast division algorithm. Barrett reduction is
      an algorithm designed to optimize this operation assuming [n] is
      constant, and [a < n²], replacing divisions by
      multiplications. *)

  (** * General idea *)
  Section general_idea.
    (** Let [m = 1 / n] be the inverse of [n] as a floating point
        number. Then *)
    (** [a mod n = a - ⌊a m⌋ n] *)
    (** where [⌊ x ⌋] denotes the floor function. The result is exact,
        as long as [m] is computed with sufficient accuracy. *)

    (* [/] is [Z.div], which means truncated division *)
    Local Notation "⌊am⌋" := (a / n) (only parsing).

    Theorem naive_barrett_reduction_correct
      : a mod n = a - ⌊am⌋ * n.
    Proof.
      apply Zmod_eq_full; assumption.
    Qed.
  End general_idea.

  (** * Barrett algorithm *)
  Section barrett_algorithm.
    (** Barrett algorithm is a fixed-point analog which expresses
        everything in terms of integers. Let [k] be the smallest
        integer such that [2ᵏ > n]. Think of [n] as representing the
        fixed-point number [n 2⁻ᵏ]. We precompute [m] such that [m =
        ⌊4ᵏ / n⌋]. Then [m] represents the fixed-point number
        [m 2⁻ᵏ ≈ (n 2⁻ᵏ)⁻¹]. *)
    (** N.B. We don't need [k] to be the smallest such integer. *)
    Context (k : Z)
            (k_good : n < 2 ^ k)
            (m : Z)
            (m_good : m = 4^k / n). (* [/] is [Z.div], which is truncated *)
    (** Wikipedia neglects to mention non-negativity, but we need it.
        It might be possible to do with a relaxed assumption, such as
        the sign of [a] and the sign of [n] being the same; but I
        figured it wasn't worth it. *)
    Context (n_pos : 0 < n) (* or just [0 <= n], since we have [n <> 0] above *)
            (a_nonneg : 0 <= a).

    Lemma k_nonnegative : 0 <= k.
    Proof.
      destruct (Z_lt_le_dec k 0); try assumption.
      rewrite !Z.pow_neg_r in * by lia; lia.
    Qed.

    (** Now *)
    Let q := (m * a) / 4^k.
    Let r := a - q * n.
    (** Because of the floor function (in Coq, because [/] means
        truncated division), [q] is an integer and [r ≡ a mod n]. *)
    Theorem barrett_reduction_equivalent
      : r mod n = a mod n.
    Proof.
      subst r q m.
      rewrite <- !Z.add_opp_r, !Zopp_mult_distr_l, !Z_mod_plus_full by assumption.
      reflexivity.
    Qed.

    Lemma qn_small
      : q * n <= a.
    Proof.
      pose proof k_nonnegative; subst q r m.
      assert (0 <= 2^(k-1)) by zero_bounds.
      Z.simplify_fractions_le.
    Qed.

    (** Also, if [a < n²] then [r < 2n]. *)
    (** N.B. It turns out that it is sufficient to assume [a < 4ᵏ]. *)
    Context (a_small : a < 4^k).
    Lemma r_small : r < 2 * n.
    Proof.
      Hint Rewrite (Z.div_small a (4^k)) (Z.mod_small a (4^k)) using lia : zsimplify.
      Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
      cut (r + 1 <= 2 * n); [ lia | ].
      pose proof k_nonnegative; subst r q m.
      assert (0 <= 2^(k-1)) by zero_bounds.
      assert (4^k <> 0) by auto with zarith lia.
      assert (a mod n < n) by auto with zarith lia.
      pose proof (Z.mod_pos_bound (a * 4^k / n) (4^k)).
      transitivity (a - (a * 4 ^ k / n - a) / 4 ^ k * n + 1).
      { rewrite <- (Z.mul_comm a); auto 6 with zarith lia. }
      rewrite (Z_div_mod_eq (_ * 4^k / n) (4^k)) by lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      break_match; auto with lia.
    Qed.

    (** In that case, we have *)
    Theorem barrett_reduction_small
      : a mod n = if r <? n
                  then r
                  else r - n.
    Proof.
      pose proof r_small. pose proof qn_small.
      destruct (r <? n) eqn:rlt; Z.ltb_to_lt.
      { symmetry; apply (Zmod_unique a n q); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 1)); subst r; lia. }
    Qed.
  End barrett_algorithm.
End barrett.
