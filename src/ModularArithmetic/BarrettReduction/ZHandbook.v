(*** Barrett Reduction *)
(** This file implements a slightly-generalized version of Barrett
    Reduction on [Z].  This version follows the Handbook of Applied
    Cryptography (Algorithm 14.42) rather closely; the only deviations
    are that we generalize from [k ± 1] to [k ± offset] for an
    arbitrary offset, and we weaken the conditions on the base [b] in
    [bᵏ] slightly.  Contrasted with some other versions, this version
    does reduction modulo [b^(k+offset)] early (ensuring that we don't
    have to carry around extra precision), but requires more stringint
    conditions on the base ([b]), exponent ([k]), and the [offset]. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics Crypto.Algebra.

Local Open Scope Z_scope.

Section barrett.
  (** Quoting the Handbook of Applied Cryptography <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>: *)
  (** Barrett reduction (Algorithm 14.42) computes [r = x mod m] given
      [x] and [m]. The algorithm requires the precomputation of the
      quantity [µ = ⌊b²ᵏ/m⌋]; it is advantageous if many reductions
      are performed with a single modulus. For example, each RSA
      encryption for one entity requires reduction modulo that
      entity’s public key modulus. The precomputation takes a fixed
      amount of work, which is negligible in comparison to modular
      exponentiation cost.  Typically, the radix [b] is chosen to be
      close to the word-size of the processor. Hence, assume [b > 3] in
      Algorithm 14.42 (see Note 14.44 (ii)). *)

  (** * Barrett modular reduction *)
  Section barrett_modular_reduction.
    Context (m b x k μ offset : Z)
            (m_pos : 0 < m)
            (base_pos : 0 < b)
            (k_good : m < b^k)
            (μ_good : μ = b^(2*k) / m) (* [/] is [Z.div], which is truncated *)
            (x_nonneg : 0 <= x)
            (offset_nonneg : 0 <= offset)
            (k_big_enough : offset <= k)
            (x_small : x < b^(2*k))
            (m_small : 3 * m <= b^(k+offset))
            (** We also need that [m] is large enough; [m] larger than
                [bᵏ⁻¹] works, but we ask for something more precise. *)
            (m_large : x mod b^(k-offset) <= m).

    Let q1 := x / b^(k-offset). Let q2 := q1 * μ. Let q3 := q2 / b^(k+offset).
    Let r1 := x mod b^(k+offset). Let r2 := (q3 * m) mod b^(k+offset).
    (** At this point, the HAC says "If [r < 0] then [r ← r + bᵏ⁺¹]".
        This is equivalent to reduction modulo [b^(k+offset)], as we
        prove below.  The version involving modular reduction has the
        benefit of being cheaper to implement, and making the proofs
        simpler, so we primarily use that version. *)
    Let r_mod_3m      := (r1 - r2) mod b^(k+offset).
    Let r_mod_3m_orig := let r := r1 - r2 in
                         if r <? 0 then r + b^(k+offset) else r.

    Lemma r_mod_3m_eq_orig : r_mod_3m = r_mod_3m_orig.
    Proof.
      assert (0 <= r1 < b^(k+offset)) by (subst r1; auto with zarith).
      assert (0 <= r2 < b^(k+offset)) by (subst r2; auto with zarith).
      subst r_mod_3m r_mod_3m_orig; cbv zeta.
      break_match; Z.ltb_to_lt.
      { symmetry; apply (Zmod_unique (r1 - r2) _ (-1)); lia. }
      { symmetry; apply (Zmod_unique (r1 - r2) _ 0); lia. }
    Qed.

    (** 14.43 Fact By the division algorithm (Definition 2.82), there
        exist integers [Q] and [R] such that [x = Qm + R] and [0 ≤ R <
        m]. In step 1 of Algorithm 14.42 (Barrett modular reduction),
        the following inequality is satisfied: [Q - 2 ≤ q₃ ≤ Q]. *)
    (** We prove this by providing a more useful form for [q₃]. *)
    Let Q := x / m.
    Let R := x mod m.
    Lemma q3_nice : { b : bool * bool | q3 = Q + (if fst b then -1 else 0) + (if snd b then -1 else 0) }.
    Proof.
      assert (0 < b^(k+offset)) by zero_bounds.
      assert (0 < b^(k-offset)) by zero_bounds.
      assert (x / b^(k-offset) <= b^(2*k) / b^(k-offset)) by auto with zarith lia.
      assert (x / b^(k-offset) <= b^(k+offset)) by (autorewrite with pull_Zpow zsimplify in *; assumption).
      subst q1 q2 q3 Q r_mod_3m r_mod_3m_orig r1 r2 R μ.
      rewrite (Z.div_mul_diff_exact' (b^(2*k)) m (x/b^(k-offset))) by auto with lia zero_bounds.
      rewrite (Z_div_mod_eq (_ * b^(2*k) / m) (b^(k+offset))) by lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div zdiv_to_mod.
      rewrite Z.div_sub_mod_cond, !Z.div_sub_small; auto with zero_bounds zarith.
      eexists (_, _); reflexivity.
    Qed.

    Fact q3_in_range : Q - 2 <= q3 <= Q.
    Proof.
      rewrite (proj2_sig q3_nice).
      break_match; lia.
    Qed.

    (** 14.44 Note (partial justification of correctness of Barrett reduction) *)
    (** (i) Algorithm 14.42 is based on the observation that [⌊x/m⌋]
            can be written as [Q =
            ⌊(x/bᵏ⁻¹)(b²ᵏ/m)(1/bᵏ⁺¹)⌋]. Moreover, [Q] can be
            approximated by the quantity [q₃ = ⌊⌊x/bᵏ⁻¹⌋µ/bᵏ⁺¹⌋].
            Fact 14.43 guarantees that [q₃] is never larger than the
            true quotient [Q], and is at most 2 smaller. *)
    Lemma x_minus_q3_m_in_range : 0 <= x - q3 * m < 3 * m.
    Proof.
      pose proof q3_in_range.
      assert (0 <= R < m) by (subst R; auto with zarith).
      assert (0 <= (Q - q3) * m + R < 3 * m) by nia.
      subst Q R; autorewrite with push_Zmul zdiv_to_mod in *; lia.
    Qed.

    Lemma r_mod_3m_eq_alt : r_mod_3m = x - q3 * m.
    Proof.
      pose proof x_minus_q3_m_in_range.
      subst r_mod_3m r_mod_3m_orig r1 r2.
      autorewrite with pull_Zmod zsimplify; reflexivity.
    Qed.

    (** This version uses reduction modulo [b^(k+offset)]. *)
    Theorem barrett_reduction_equivalent
      : r_mod_3m mod m = x mod m.
    Proof.
      rewrite r_mod_3m_eq_alt.
      autorewrite with zsimplify push_Zmod; reflexivity.
    Qed.

    (** This version, which matches the original in the HAC, uses
        conditional addition of [b^(k+offset)]. *)
    Theorem barrett_reduction_orig_equivalent
      : r_mod_3m_orig mod m = x mod m.
    Proof. rewrite <- r_mod_3m_eq_orig; apply barrett_reduction_equivalent. Qed.

    Lemma r_small : 0 <= r_mod_3m < 3 * m.
    Proof.
      pose proof x_minus_q3_m_in_range.
      subst Q R r_mod_3m r_mod_3m_orig r1 r2.
      autorewrite with pull_Zmod zsimplify; lia.
    Qed.


    (** This version uses reduction modulo [b^(k+offset)]. *)
    Theorem barrett_reduction_small (r := r_mod_3m)
      : x mod m = let r := if r <? m then r else r-m in
                  let r := if r <? m then r else r-m in
                  r.
    Proof.
      pose proof r_small. cbv zeta.
      destruct (r <? m) eqn:Hr, (r-m <? m) eqn:?; subst r; rewrite !r_mod_3m_eq_alt, ?Hr in *; Z.ltb_to_lt; try lia.
      { symmetry; eapply (Zmod_unique x m q3); lia. }
      { symmetry; eapply (Zmod_unique x m (q3 + 1)); lia. }
      { symmetry; eapply (Zmod_unique x m (q3 + 2)); lia. }
    Qed.

    (** This version, which matches the original in the HAC, uses
        conditional addition of [b^(k+offset)]. *)
    Theorem barrett_reduction_small_orig (r := r_mod_3m_orig)
      : x mod m = let r := if r <? m then r else r-m in
                  let r := if r <? m then r else r-m in
                  r.
    Proof. subst r; rewrite <- r_mod_3m_eq_orig; apply barrett_reduction_small. Qed.
  End barrett_modular_reduction.
End barrett.
