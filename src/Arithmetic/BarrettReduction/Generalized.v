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
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics.BreakMatch.

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
    Proof using n_reasonable.
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
    Proof using m_good offset.
      subst r q m.
      rewrite <- !Z.add_opp_r, !Zopp_mult_distr_l, !Z_mod_plus_full by assumption.
      reflexivity.
    Qed.

    Lemma qn_small
      : q * n <= a.
    Proof using a_nonneg a_small base_good k_big_enough m_good n_pos n_reasonable offset_nonneg.
      subst q r m.
      assert (0 < b^(k-offset)). zero_bounds.
      assert (0 < b^(k+offset)) by zero_bounds.
      assert (0 < b^(2 * k)) by zero_bounds.
      Z.simplify_fractions_le.
      autorewrite with pull_Zpow pull_Zdiv zsimplify; reflexivity.
    Qed.

    Lemma q_nice : { b : bool * bool | q = a / n + (if fst b then -1 else 0) + (if snd b then -1 else 0) }.
    Proof using a_nonneg a_small base_good k_big_enough m_good n_large n_pos n_reasonable offset_nonneg.
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
    Proof using a_nonneg a_small base_good k_big_enough m_good n_large n_pos n_reasonable offset_nonneg q.
      Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
      assert (a mod n < n) by auto with zarith lia.
      unfold r; rewrite (proj2_sig q_nice); generalize (proj1_sig q_nice); intro; subst q m.
      autorewrite with push_Zmul zsimplify zstrip_div.
      break_match; auto with lia.
    Qed.

    (** In that case, we have *)
    Theorem barrett_reduction_small
      : a mod n = let r := if r <? n then r else r-n in
                  let r := if r <? n then r else r-n in
                  r.
    Proof using a_nonneg a_small base_good k_big_enough m_good n_large n_pos n_reasonable offset_nonneg q.
      pose proof r_small. pose proof qn_small. cbv zeta.
      destruct (r <? n) eqn:Hr, (r-n <? n) eqn:?; try rewrite Hr; Z.ltb_to_lt; try lia.
      { symmetry; apply (Zmod_unique a n q); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 1)); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 2)); subst r; lia. }
    Qed.

    Section StrongerBounds.
      Context (n_good : b ^ offset * (b^(2*k) mod n) <= b ^ (k+offset) - m) (a_good : a < n * b ^ k).

      Lemma helper_1 : b ^ (2 * k) * ((a / n) - 1) <= m * (n * (a / n) - b ^ (k - offset)).
      Proof.
        autorewrite with push_Zmul. ring_simplify.
        replace (a / n * m * n) with (m * n * (a / n)) by ring.
        assert (a/n < b ^ k) by auto using Z.div_lt_upper_bound with zarith.
        assert (b ^ (2 * k) - m * n = b ^ (2 * k) mod n).
        { subst m.
          rewrite Z.mul_div_eq' by (auto using Z.lt_gt with zarith).
          auto with zarith. }
        assert (0 < b ^ (k - offset)) by auto with zarith.
        assert (b ^ (2*k) = b ^ (k - offset) * b ^ (k + offset)) by (rewrite <-Z.pow_add_r; auto with zarith).
        pose proof (Z.mod_pos_bound (b ^ (2*k)) n ltac:(lia)).
        match goal with |- ?x * (a/n) - ?c <= ?d * (a/n) - ?e =>
                        assert ((b ^ k) * (x - d) <= c  - e); [|nia] end.
        replace (b ^ k) with (b ^ (k - offset) * b ^ offset) by (rewrite <-Z.pow_add_r; auto with zarith).
        nia.
      Qed.

      Lemma helper_2 : n * (a / n) - b ^ (k - offset) < b ^ (k - offset) * (a / b ^ (k - offset)).
      Proof.
        rewrite !Z.mul_div_eq by auto using Z.lt_gt with zarith.
        pose proof (Z.mod_pos_bound a n ltac:(omega)).
        pose proof (Z.mod_pos_bound a (b ^ (k - offset)) ltac:(auto with zarith)).
        lia.
      Qed.

      Let epsilon := (a / n) * b ^ (k+offset) - (a / b ^ (k - offset)) * m.

      Lemma q_epsilon : q = (a / n) + (- epsilon) / b ^ (k + offset).
      Proof.
        subst q. subst epsilon.
        rewrite Z.opp_sub_distr.
        rewrite <-Z.mul_opp_l.
        rewrite Z.div_add_l by auto with zarith.
        ring_simplify. f_equal; ring.
      Qed.

      Lemma epsilon_lower : - b ^ (k + offset) < epsilon.
      Proof.
        pose proof q_epsilon as Hq_epsilon.
        rewrite (proj2_sig q_nice) in Hq_epsilon.
        apply Z.opp_lt_mono. rewrite Z.opp_involutive.
        apply Z.div_le_zero; auto with zarith.
        destruct (proj1_sig q_nice) as [ [|] [|]]; cbn [fst snd] in *; omega.
      Qed.

      Lemma m_pos : 0 < m.
      Proof.
        subst m. Z.zero_bounds.
        split; auto with zarith.
        transitivity (b ^ k); auto with zarith.
      Qed.

      Lemma epsilon_bound : epsilon < b ^ (k + offset).
      Proof.
        subst epsilon. pose proof helper_1. pose proof helper_2. pose proof m_pos.
        replace (b ^ (2 * k)) with (b^(k - offset) * b ^ (k + offset)) in *
          by (rewrite <-Z.pow_add_r; auto with zarith).
        apply Z.mul_lt_mono_pos_l with (p:=b^(k-offset)); auto with zarith.
        nia.
      Qed.

      Lemma q_nice_strong : { b : bool | q = a / n + if b then -1 else 0}.
      Proof.
        exists (0 <? epsilon).
        rewrite q_epsilon.
        apply Z.add_cancel_l.
        pose proof epsilon_bound. pose proof epsilon_lower.
        break_match; Z.ltb_to_lt.
        { rewrite Z.div_opp_l_complete by auto with zarith.
          rewrite Z.div_small, Z.mod_small by auto with zarith.
          break_match; omega. }
        { rewrite Z.div_small; auto with zarith. }
      Qed.

      Lemma q_bound : a / n - 1 <= q.
      Proof.
        rewrite (proj2_sig q_nice_strong).
        break_match; omega.
      Qed.

      Lemma r_small_strong : r < 2 * n.
      Proof.
        Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
        assert (a mod n < n) by auto with zarith lia.
        unfold r.
        apply Z.le_lt_trans with (m:= a - (a / n - 1) * n); [pose proof q_bound; nia | ].
        autorewrite with push_Zmul zsimplify zstrip_div.
        auto with lia.
      Qed.
    End StrongerBounds.
  End barrett_algorithm.
End barrett.