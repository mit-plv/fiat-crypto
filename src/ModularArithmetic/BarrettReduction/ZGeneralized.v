(*** Barrett Reduction *)
(** This file implements a slightly-generalized version of Barrett
    Reduction on [Z].  This version follows a middle path between the
    Handbook of Applied Cryptography (Algorithm 14.42) and Wikipedia.
    We split up the shifting and the multiplication so that we don't
    need to store numbers that are quite so large, but we don't do
    early reduction modulo [b^(k+offset)] (we generalize from HAC's [k
    ± 1] to [k ± offset]).  This leads to weaker conditions on the
    base ([b]), exponent ([k]), and the [offset] than those given in
    the HAC. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics Crypto.Algebra.

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
    (** N.B. We generalize to an arbitrary base. *)
    (** N.B. We generalize from [k ± 1] to [k ± offset]. *)
    Context (b : Z)
            (base_good : 0 < b)
            (k : Z)
            (k_good : n < b ^ k)
            (m : Z)
            (m_good : m = b^(2*k) / n) (* [/] is [Z.div], which is truncated *)
            (offset : Z)
            (offset_nonneg : 0 <= offset).
    (** Wikipedia neglects to mention non-negativity, but we need it.
        It might be possible to do with a relaxed assumption, such as
        the sign of [a] and the sign of [n] being the same; but I
        figured it wasn't worth it. *)
    Context (n_pos : 0 < n) (* or just [0 <= n], since we have [n <> 0] above *)
            (a_nonneg : 0 <= a).

    Context (k_big_enough : offset <= k)
            (a_small : a < b^(2*k))
            (** We also need that [n] is large enough; [n] larger than
                [bᵏ⁻¹] works, but we ask for something more precise. *)
            (n_large : a mod b^(k-offset) <= n).

    (** Now *)

    Let q := (m * (a / b^(k-offset))) / b^(k+offset).
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
      subst q r m.
      assert (0 < b^(k-offset)). zero_bounds.
      assert (0 < b^(k+offset)) by zero_bounds.
      assert (0 < b^(2 * k)) by zero_bounds.
      Z.simplify_fractions_le.
      autorewrite with pull_Zpow pull_Zdiv zsimplify; reflexivity.
    Qed.

    Lemma q_nice : { b : bool * bool | q = a / n + (if fst b then -1 else 0) + (if snd b then -1 else 0) }.
    Proof.
      assert (0 < b^(k+offset)) by zero_bounds.
      assert (0 < b^(k-offset)) by zero_bounds.
      assert (a / b^(k-offset) <= b^(2*k) / b^(k-offset)) by auto with zarith lia.
      assert (a / b^(k-offset) <= b^(k+offset)) by (autorewrite with pull_Zpow zsimplify in *; assumption).
      subst q r m.
      rewrite (Z.div_mul_diff_exact''' (b^(2*k)) n (a/b^(k-offset))) by auto with lia zero_bounds.
      rewrite (Z_div_mod_eq (b^(2*k) * _ / n) (b^(k+offset))) by lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div zdiv_to_mod.
      rewrite Z.div_sub_mod_cond, !Z.div_sub_small by auto with zero_bounds zarith.
      eexists (_, _); reflexivity.
    Qed.

    Lemma r_small : r < 3 * n.
    Proof.
      Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
      assert (a mod n < n) by auto with zarith lia.
      subst r; rewrite (proj2_sig q_nice); generalize (proj1_sig q_nice); intro; subst q m.
      autorewrite with push_Zmul zsimplify zstrip_div.
      break_match; auto with lia.
    Qed.

    (** In that case, we have *)
    Theorem barrett_reduction_small
      : a mod n = let r := if r <? n then r else r-n in
                  let r := if r <? n then r else r-n in
                  r.
    Proof.
      pose proof r_small. pose proof qn_small. cbv zeta.
      destruct (r <? n) eqn:Hr, (r-n <? n) eqn:?; try rewrite Hr; Z.ltb_to_lt; try lia.
      { symmetry; apply (Zmod_unique a n q); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 1)); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 2)); subst r; lia. }
    Qed.
  End barrett_algorithm.
End barrett.
