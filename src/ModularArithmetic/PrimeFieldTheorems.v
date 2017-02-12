Require Export Crypto.Spec.ModularArithmetic Crypto.ModularArithmetic.ModularArithmeticTheorems.
Require Export Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.

Require Import Coq.nsatz.Nsatz.
Require Import Crypto.ModularArithmetic.Pre.
Require Import Crypto.Util.NumTheoryUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.ZArith.BinInt Coq.NArith.BinNat Coq.ZArith.ZArith Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Util.NumTheoryUtil Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Decidable.
Require Export Crypto.Util.FixCoqMistakes.
Require Crypto.Algebra Crypto.Algebra.Field.

Existing Class prime.

Module F.
  Section Field.
    Context (q:Z) {prime_q:prime q}.
    Lemma inv_spec : F.inv 0%F = (0%F : F q)
                     /\ (prime q -> forall x : F q, x <> 0%F -> (F.inv x * x)%F = 1%F).
    Proof. change (@F.inv q) with (proj1_sig (@F.inv_with_spec q)); destruct (@F.inv_with_spec q); eauto. Qed.

    Lemma inv_0 : F.inv 0%F = F.of_Z q 0. Proof. destruct inv_spec; auto. Qed.
    Lemma inv_nonzero (x:F q) : (x <> 0 -> F.inv x * x%F = 1)%F. Proof. destruct inv_spec; auto. Qed.

    Global Instance field_modulo : @Algebra.field (F q) Logic.eq 0%F 1%F F.opp F.add F.sub F.mul F.inv F.div.
    Proof.
      repeat match goal with
             | _ => solve [ solve_proper
                          | apply F.commutative_ring_modulo
                          | apply inv_nonzero
                          | cbv [not]; pose proof prime_ge_2 q prime_q;
                            rewrite F.eq_to_Z_iff, !F.to_Z_of_Z, !Zmod_small; omega ]
             | _ => split
             end.
    Qed.

    Definition field_theory : field_theory 0%F 1%F F.add F.mul F.sub F.opp F.div F.inv eq
      := Algebra.Field.field_theory_for_stdlib_tactic.
  End Field.

  (** A field tactic hook that can be imported *)
  Module Type PrimeModulus.
    Parameter modulus : Z.
    Parameter prime_modulus : prime modulus.
  End PrimeModulus.
  Module FieldModulo (Export M : PrimeModulus).
    Module Import RingM := F.RingModulo M.
    Add Field _field : (F.field_theory modulus)
                         (morphism (F.ring_morph modulus),
                          constants [F.is_constant],
                          div (F.morph_div_theory modulus),
                          power_tac (F.power_theory modulus) [F.is_pow_constant]).
  End FieldModulo.

  Section NumberThoery.
    Context {q:Z} {prime_q:prime q} {two_lt_q: 2 < q}.
    Local Open Scope F_scope.
    Add Field _field : (field_theory q)
                         (morphism (F.ring_morph q),
                          constants [F.is_constant],
                          div (F.morph_div_theory q),
                          power_tac (F.power_theory q) [F.is_pow_constant]).

    (* TODO: move to PrimeFieldTheorems *)
    Lemma to_Z_1 : @F.to_Z q 1 = 1%Z.
    Proof. simpl. rewrite Zmod_small; omega. Qed.

    Lemma Fq_inv_fermat (x:F q) : F.inv x = x ^ Z.to_N (q - 2)%Z.
    Proof.
      destruct (dec (x = 0%F)) as [?|Hnz].
      { subst x; rewrite inv_0, F.pow_0_l; trivial.
        change (0%N) with (Z.to_N 0%Z); rewrite Z2N.inj_iff; omega. }
      erewrite <-Algebra.Field.inv_unique; try reflexivity.
      rewrite F.eq_to_Z_iff, F.to_Z_mul, F.to_Z_pow, Z2N.id, to_Z_1 by omega.
      apply (fermat_inv q _ (F.to_Z x)); rewrite F.mod_to_Z; eapply F.to_Z_nonzero; trivial.
    Qed.

    Lemma euler_criterion (a : F q) (a_nonzero : a <> 0) :
      (a ^ (Z.to_N (q / 2)) = 1) <-> (exists b, b*b = a).
    Proof.
      pose proof F.to_Z_nonzero_range a; pose proof (odd_as_div q).
      specialize_by (destruct (Z.prime_odd_or_2 _ prime_q); try omega; trivial).
      rewrite F.eq_to_Z_iff, !F.to_Z_pow, !to_Z_1, !Z2N.id by omega.
      rewrite F.square_iff, <-(euler_criterion (q/2)) by (trivial || omega); reflexivity.
    Qed.

    Global Instance Decidable_square (x:F q) : Decidable (exists y, y*y = x).
    Proof.
      destruct (dec (x = 0)).
      { left. abstract (exists 0; subst; ring). }
      { eapply Decidable_iff_to_impl; [eapply euler_criterion; assumption | exact _]. }
    Defined.
  End NumberThoery.

  Section SquareRootsPrime3Mod4.
    Context {q:Z} {prime_q: prime q} {q_3mod4 : q mod 4 = 3}.

    Local Open Scope F_scope.
    Add Field _field2 : (field_theory q)
                          (morphism (F.ring_morph q),
                           constants [F.is_constant],
                           div (F.morph_div_theory q),
                           power_tac (F.power_theory q) [F.is_pow_constant]).

    Definition sqrt_3mod4 (a : F q) : F q := a ^ Z.to_N (q / 4 + 1).

    Global Instance Proper_sqrt_3mod4 : Proper (eq ==> eq ) sqrt_3mod4.
    Proof. repeat intro; subst; reflexivity. Qed.

    Lemma two_lt_q_3mod4 : 2 < q.
    Proof.
      pose proof (prime_ge_2 q _) as two_le_q.
      apply Zle_lt_or_eq in two_le_q.
      destruct two_le_q; auto.
      subst_max.
      discriminate.
    Qed.
    Local Hint Resolve two_lt_q_3mod4.
    
    Lemma sqrt_3mod4_correct : forall x,
      ((exists y, y*y = x) <-> (sqrt_3mod4 x)*(sqrt_3mod4 x) = x).
    Proof.
      cbv [sqrt_3mod4]; intros.
      destruct (F.eq_dec x 0);
      repeat match goal with
             | |- _ => progress subst
             | |- _ => progress rewrite ?F.pow_0_l, <-?F.pow_add_r
             | |- _ => progress rewrite <-?Z2N.inj_0, <-?Z2N.inj_add by zero_bounds
             | |- _ => rewrite <-@euler_criterion by auto
             | |- ?x ^ (?f _) = ?a <-> ?x ^ (?f _) = ?a => do 3 f_equiv; [ ]
             | |- _ => rewrite !Zmod_odd in *; repeat break_if; omega
             | |- _ => rewrite Z.rem_mul_r in * by omega
             | |- (exists x, _) <-> ?B => assert B by field; solve [intuition eauto]
             | |- (?x ^ Z.to_N ?a = 1) <-> _ =>
               transitivity (x ^ Z.to_N a * x ^ Z.to_N 1 = x);
                 [ rewrite F.pow_1_r, Algebra.Field.mul_cancel_l_iff by auto; reflexivity | ]
             | |- (_ <> _)%N => rewrite Z2N.inj_iff by zero_bounds
             | |- (?a <> 0)%Z => assert (0 < a) by zero_bounds; omega
             | |- (_ = _)%Z => replace 4 with (2 * 2)%Z in * by ring;
                                 rewrite <-Z.div_div by zero_bounds;
                                 rewrite Z.add_diag, Z.mul_add_distr_l, Z.mul_div_eq by omega
             end.
    Qed.
  End SquareRootsPrime3Mod4.

  Section SquareRootsPrime5Mod8.
    Context {q:Z} {prime_q: prime q} {q_5mod8 : q mod 8 = 5}.

    Local Open Scope F_scope.
    Add Field _field3 : (field_theory q)
                          (morphism (F.ring_morph q),
                           constants [F.is_constant],
                           div (F.morph_div_theory q),
                           power_tac (F.power_theory q) [F.is_pow_constant]).
    
    (* Any nonsquare element raised to (q-1)/4 (real implementations use 2 ^ ((q-1)/4) )
       would work for sqrt_minus1 *)
    Context (sqrt_minus1 : F q) (sqrt_minus1_valid : sqrt_minus1 * sqrt_minus1 = F.opp 1).

    Lemma two_lt_q_5mod8 : 2 < q.
    Proof.
      pose proof (prime_ge_2 q _) as two_le_q.
      apply Zle_lt_or_eq in two_le_q.
      destruct two_le_q; auto.
      subst_max.
      discriminate.
    Qed.
    Local Hint Resolve two_lt_q_5mod8.

    Definition sqrt_5mod8 (a : F q) : F q :=
      let b := a ^ Z.to_N (q / 8 + 1) in
      if dec (b ^ 2 = a)
      then b
      else sqrt_minus1 * b.

    Global Instance Proper_sqrt_5mod8 : Proper (eq ==> eq ) sqrt_5mod8.
    Proof. repeat intro; subst; reflexivity. Qed.

    Lemma eq_b4_a2 (x : F q) (Hex:exists y, y*y = x) :
      ((x ^ Z.to_N (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2.
    Proof.
      pose proof two_lt_q_5mod8.
      assert (0 <= q/8)%Z by (apply Z.div_le_lower_bound; rewrite ?Z.mul_0_r; omega).
      assert (Z.to_N (q / 8 + 1) <> 0%N) by
          (intro Hbad; change (0%N) with (Z.to_N 0%Z) in Hbad; rewrite Z2N.inj_iff in Hbad; omega).
      destruct (dec (x = 0)); [subst; rewrite !F.pow_0_l by (trivial || lazy_decide); reflexivity|].
      rewrite !F.pow_pow_l.

      replace (Z.to_N (q / 8 + 1) * (2*2))%N with (Z.to_N (q / 2 + 2))%N.
      Focus 2. { (* this is a boring but gnarly proof :/ *)
        change (2*2)%N with (Z.to_N 4).
        rewrite <- Z2N.inj_mul by zero_bounds.
        apply Z2N.inj_iff; try zero_bounds.
        rewrite <- Z.mul_cancel_l with (p := 2) by omega.
        ring_simplify.
        rewrite Z.mul_div_eq by omega.
        rewrite Z.mul_div_eq by omega.
        rewrite (Zmod_div_mod 2 8 q) by
            (try omega; apply Zmod_divide; omega || auto).
        rewrite q_5mod8.
        replace (5 mod 2)%Z with 1%Z by auto.
        ring.
      } Unfocus.

      rewrite Z2N.inj_add, F.pow_add_r by zero_bounds.
      replace (x ^ Z.to_N (q / 2)) with (F.of_Z q 1) by
          (symmetry; apply @euler_criterion; eauto).
      change (Z.to_N 2) with 2%N; ring.
    Qed.

    Lemma mul_square_sqrt_minus1 : forall x, sqrt_minus1 * x * (sqrt_minus1 * x) = F.opp (x * x).
    Proof.
      intros.
      transitivity (F.opp 1 * (x * x)); [ | field].
      rewrite <-sqrt_minus1_valid.
      field.
    Qed.

    Lemma eq_b4_a2_iff (x : F q) : x <> 0 ->
      ((exists y, y*y = x) <-> ((x ^ Z.to_N (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2).
    Proof.
      split; try apply eq_b4_a2.
      intro Hyy.
      rewrite !@F.pow_2_r in *.
      destruct (Field.only_two_square_roots_choice _ x (x * x) Hyy eq_refl); clear Hyy;
        [ eexists; eassumption | ].
      match goal with H : ?a * ?a = F.opp _ |- _ => exists (sqrt_minus1 * a);
        rewrite mul_square_sqrt_minus1; rewrite H end.
      field.
    Qed.

    Lemma sqrt_5mod8_correct : forall x,
      ((exists y, y*y = x) <-> (sqrt_5mod8 x)*(sqrt_5mod8 x) = x).
    Proof.
      cbv [sqrt_5mod8]; intros.
      destruct (F.eq_dec x 0).
      {
        repeat match goal with
             | |- _ => progress subst
             | |- _ => progress rewrite ?F.pow_0_l
             | |- _ => break_if
             | |- (exists x, _) <-> ?B => assert B by field; solve [intuition eauto]
             | |- (_ <> _)%N => rewrite <-Z2N.inj_0, Z2N.inj_iff by zero_bounds
             | |- (?a <> 0)%Z => assert (0 < a) by zero_bounds; omega
             | |- _ => congruence
             end.
      } {
        rewrite eq_b4_a2_iff by auto.
        rewrite !@F.pow_2_r in *.
        break_if.
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
