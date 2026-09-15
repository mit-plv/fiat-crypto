Require Export Crypto.Spec.ModularArithmetic.
Require Export Crypto.Arithmetic.ModularArithmeticTheorems.
From Coq Require Export Ring_theory Field_theory Field_tac.

From Coq Require Import Nsatz.
From Coq Require Import Lia Zmod.
Require Import Crypto.Util.NumTheoryUtil.
From Coq Require Import Morphisms Setoid.
From Coq Require Import BinInt BinNat ZArith Znumtheory NArith. (* import Zdiv before Znumtheory *)
From Coq Require Import Eqdep_dec.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Util.ZUtil.Odd.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Decidable.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Crypto.Algebra.Hierarchy Crypto.Algebra.Field.

Existing Class prime.
Local Open Scope F_scope.

Module F.
  Section Field.
    Context (q:Z) {prime_q:prime q}.

    Lemma inv_nonzero (x:F q) : (x <> 0 -> F.inv x * x%F = 1)%F.
    Proof using Type*. apply Zmod.mul_inv_same_l_prime, prime_alt, prime_q. Qed.

    Global Instance field_modulo : @Algebra.Hierarchy.field (F q) Logic.eq 0%F 1%F F.opp F.add F.sub F.mul F.inv F.div.
    Proof using Type*.
      pose proof (prime_ge_2 q prime_q).
      split.
      { apply F.commutative_ring_modulo. }
      { split; apply inv_nonzero. }
      { split; apply not_eq_sym, Zmod.one_neq_zero; lia. }
      { reflexivity. }
      { solve_proper. }
      { solve_proper. }
    Qed.
  End Field.

  Section NumberThoery.
    Context {q:Z} {prime_q:prime q} {two_lt_q: 2 < q}.

    Lemma Fq_inv_fermat (x:F q) : F.inv x = x ^ (q - 2)%Z.
    Proof using Type*.
      destruct (dec (x = 0%F)) as [->|Hnz].
      { rewrite Zmod.inv_0, Zmod.pow_0_l by lia; reflexivity. }
      symmetry; apply Zmod.fermat_inv, prime_alt; assumption.
    Qed.

    Lemma euler_criterion (a : F q) (a_nonzero : a <> 0) :
      (a ^ (q / 2) = 1) <-> (exists b, b*b = a).
    Proof using Type*.
      pose proof F.to_Z_nonzero_range a; pose proof (odd_as_div q).
      specialize_by (destruct (Z.prime_odd_or_2 _ prime_q); try lia; trivial).
      rewrite <-Zmod.unsigned_inj_iff, !Zmod.unsigned_pow_nonneg_r, !Zmod.unsigned_1_pos by (Z.to_euclidean_division_equations; lia).
      rewrite F.square_iff, <-(euler_criterion (q/2)) by (trivial || lia); reflexivity.
    Qed.

    Global Instance Decidable_square : forall (x:F q), Decidable (exists y, y*y = x).
    Proof.
      intro x; destruct (dec (x = 0)).
      { left. abstract (exists 0; subst; apply Ring.mul_0_l). }
      { eapply Decidable_iff_to_impl; [eapply euler_criterion; assumption | exact _]. }
    Defined.
  End NumberThoery.

  Section SquareRootsPrime3Mod4.
    Context {q:Z} {prime_q: prime q} {q_3mod4 : q mod 4 = 3}.

    Add Field _field2 : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
                          (morphism (F.ring_morph q),
                           constants [F.is_constant],
                           div (F.morph_div_theory q),
                           power_tac (F.power_theory q) [F.is_pow_constant]).

    Definition sqrt_3mod4 (a : F q) : F q := a ^ (q / 4 + 1).

    Global Instance Proper_sqrt_3mod4 : Proper (eq ==> eq ) sqrt_3mod4.
    Proof using Type. repeat intro; subst; reflexivity. Qed.

    Lemma two_lt_q_3mod4 : 2 < q.
    Proof using Type*.
      pose proof (prime_ge_2 q _) as two_le_q.
      Z.to_euclidean_division_equations; lia.
    Qed.
    Local Hint Resolve two_lt_q_3mod4 : core.

    Lemma sqrt_3mod4_correct (x:F q) :
      ((exists y, y*y = x) <-> (sqrt_3mod4 x)*(sqrt_3mod4 x) = x)%F.
    Proof using Type*.
      pose proof two_lt_q_3mod4; cbv [sqrt_3mod4].
      destruct (F.eq_dec x 0) as [->|Hnz].
      { rewrite Zmod.pow_0_l by (Z.to_euclidean_division_equations; lia).
        split; intros; [ring | exists 0; ring]. }
      rewrite <-(euler_criterion (two_lt_q:=two_lt_q_3mod4) x Hnz).
      rewrite <-Zmod.pow_add_r_nonneg by (Z.to_euclidean_division_equations; lia).
      replace (q / 4 + 1 + (q / 4 + 1))%Z with (Z.succ (q / 2)) by (Z.to_euclidean_division_equations; lia).
      rewrite Zmod.pow_succ_nonneg_r by (Z.to_euclidean_division_equations; lia).
      rewrite Zmod.mul_comm; symmetry; apply Algebra.Field.mul_cancel_l_iff; assumption.
    Qed.
  End SquareRootsPrime3Mod4.

  Section SquareRootsPrime5Mod8.
    Context {q:Z} {prime_q: prime q} {q_5mod8 : q mod 8 = 5}.
    Local Open Scope F_scope.
    Add Field _field3 : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
                          (morphism (F.ring_morph q),
                           constants [F.is_constant],
                           div (F.morph_div_theory q),
                           power_tac (F.power_theory q) [F.is_pow_constant]).

    (* Any nonsquare element raised to (q-1)/4 (real implementations use 2 ^ ((q-1)/4) )
       would work for sqrt_minus1 *)
    Context (sqrt_minus1 : F q) (sqrt_minus1_valid : sqrt_minus1 * sqrt_minus1 = F.opp 1).

    Lemma two_lt_q_5mod8 : 2 < q.
    Proof using prime_q q_5mod8.
      pose proof (prime_ge_2 q _) as two_le_q.
      Z.to_euclidean_division_equations; lia.
    Qed.
    Local Hint Resolve two_lt_q_5mod8 : core.

    Definition sqrt_5mod8 (a : F q) : F q :=
      let b := a ^ (q / 8 + 1) in
      if dec (b ^ 2 = a)
      then b
      else sqrt_minus1 * b.

    Global Instance Proper_sqrt_5mod8 : Proper (eq ==> eq ) sqrt_5mod8.
    Proof using Type. repeat intro; subst; reflexivity. Qed.

    Lemma eq_b4_a2 (x : F q) (Hex:exists y, y*y = x) :
      ((x ^ (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2.
    Proof using prime_q q_5mod8.
      pose proof two_lt_q_5mod8.
      destruct (F.eq_dec x 0) as [->|Hnz].
      { rewrite !Zmod.pow_0_l by (Z.to_euclidean_division_equations; lia); reflexivity. }
      rewrite <-!Zmod.pow_mul_r_nonneg by (Z.to_euclidean_division_equations; lia).
      replace ((q / 8 + 1) * (2 * 2))%Z with (q / 2 + 2)%Z by (Z.to_euclidean_division_equations; lia).
      rewrite Zmod.pow_add_r_nonneg by (Z.to_euclidean_division_equations; lia).
      rewrite (proj2 (euler_criterion (two_lt_q:=two_lt_q_5mod8) x Hnz) Hex).
      apply Zmod.mul_1_l.
    Qed.

    Lemma mul_square_sqrt_minus1 : forall x, sqrt_minus1 * x * (sqrt_minus1 * x) = F.opp (x * x).
    Proof using prime_q sqrt_minus1_valid.
      intros x.
      transitivity (F.opp 1 * (x * x)); [ | field].
      rewrite <-sqrt_minus1_valid.
      field.
    Qed.

    Lemma eq_b4_a2_iff (x : F q) : x <> 0 ->
      ((exists y, y*y = x) <-> ((x ^ (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2).
    Proof using Type*.
      split; try apply eq_b4_a2.
      intro Hyy.
      rewrite !@Zmod.pow_2_r in *.
      destruct (Field.only_two_square_roots_choice _ x (x * x) Hyy eq_refl); clear Hyy;
        [ eexists; eassumption | ].
      match goal with H : ?a * ?a = F.opp _ |- _ => exists (sqrt_minus1 * a);
        rewrite mul_square_sqrt_minus1; rewrite H end.
      field.
    Qed.

    Lemma sqrt_5mod8_correct : forall x,
      ((exists y, y*y = x) <-> (sqrt_5mod8 x)*(sqrt_5mod8 x) = x).
    Proof using Type*.
      cbv [sqrt_5mod8]; intros x.
      pose proof two_lt_q_5mod8.
      destruct (F.eq_dec x 0) as [->|Hnz].
      {
        rewrite !Zmod.pow_0_l by (Z.to_euclidean_division_equations; lia).
        break_match;
          match goal with |- _ <-> ?G => assert G by field end; intuition eauto.
      } {
        rewrite eq_b4_a2_iff by auto.
        rewrite !@Zmod.pow_2_r in *.
        break_match.
        intuition (f_equal; eauto).
        split; intro A. {
          destruct (Field.only_two_square_roots_choice _ x (x * x) A eq_refl) as [B | B];
            clear A; try congruence.
          rewrite mul_square_sqrt_minus1, B; field.
        } {
          rewrite mul_square_sqrt_minus1 in A.
          transitivity (F.opp x * F.opp x); [ | field ].
          f_equal; rewrite <-A at 3; field.
        }
      }
    Qed.
  End SquareRootsPrime5Mod8.
End F.
