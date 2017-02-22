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
Local Open Scope F_scope.

Module F.
  Section Field.
    Context (q:positive) {prime_q:prime q}.
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
  End Field.

  Section NumberThoery.
    Context {q:positive} {prime_q:prime q} {two_lt_q: 2 < q}.

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
      { left. abstract (exists 0; subst; apply Ring.mul_0_l). }
      { eapply Decidable_iff_to_impl; [eapply euler_criterion; assumption | exact _]. }
    Defined.
  End NumberThoery.

  Section SquareRootsPrime3Mod4.
    Context {q:positive} {prime_q: prime q} {q_3mod4 : q mod 4 = 3}.

    Add Field _field2 : (Algebra.Field.field_theory_for_stdlib_tactic(T:=F q))
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
      destruct (Zle_lt_or_eq _ _ two_le_q) as [H|H]; [exact H|].
      rewrite <-H in q_3mod4; discriminate.
    Qed.
    Local Hint Resolve two_lt_q_3mod4.
    
    Lemma sqrt_3mod4_correct (x:F q) :
      ((exists y, y*y = x) <-> (sqrt_3mod4 x)*(sqrt_3mod4 x) = x)%F.
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
    Context {q:positive} {prime_q: prime q} {q_5mod8 : q mod 8 = 5}.
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
    Proof.
      pose proof (prime_ge_2 q _) as two_le_q.
      destruct (Zle_lt_or_eq _ _ two_le_q) as [H|H]; [exact H|].
      rewrite <-H in *. discriminate.
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

  Module Iso.
    Section IsomorphicRings.
      Context {q:positive} {prime_q:prime q} {two_lt_q:2 < Z.pos q}.
      Context 
        {H : Type} {eq : H -> H -> Prop} {zero one : H}
        {opp : H -> H} {add sub mul : H -> H -> H}
        {phi : F q -> H} {phi' : H -> F q}
        {phi'_phi : forall A : F q, Logic.eq (phi' (phi A)) A}
        {phi'_iff : forall a b : H, iff (Logic.eq (phi' a) (phi' b)) (eq a b)}
        {phi'_zero : Logic.eq (phi' zero) F.zero} {phi'_one : Logic.eq (phi' one) F.one}
        {phi'_opp : forall a : H, Logic.eq (phi' (opp a)) (F.opp (phi' a))}
        {phi'_add : forall a b : H, Logic.eq (phi' (add a b)) (F.add (phi' a) (phi' b))}
        {phi'_sub : forall a b : H, Logic.eq (phi' (sub a b)) (F.sub (phi' a) (phi' b))}
        {phi'_mul : forall a b : H, Logic.eq (phi' (mul a b)) (F.mul (phi' a) (phi' b))}
        {P:Type} {pow : H -> P -> H} {NtoP:N->P}
        {pow_is_scalarmult:ScalarMult.is_scalarmult(G:=H)(eq:=eq)(add:=mul)(zero:=one)(mul:=fun (n:nat) (k:H) => pow k (NtoP (N.of_nat n)))}.
      Definition inv (x:H) := pow x (NtoP (Z.to_N (q - 2)%Z)).
      Definition div x y := mul (inv y) x.
      
      Lemma ring :
        @Algebra.ring H eq zero one opp add sub mul
        /\ @Ring.is_homomorphism (F q) Logic.eq F.one F.add F.mul H eq one add mul phi
        /\ @Ring.is_homomorphism H eq one add mul (F q) Logic.eq F.one F.add F.mul phi'.
      Proof. eapply @Ring.ring_by_isomorphism; assumption || exact _. Qed.
      Local Instance _iso_ring : Algebra.ring := proj1 ring.
      Local Instance _iso_hom1 : Ring.is_homomorphism := proj1 (proj2 ring).
      Local Instance _iso_hom2 : Ring.is_homomorphism := proj2 (proj2 ring).

      Let inv_proof : forall a : H, phi' (inv a) = F.inv (phi' a).
      Proof.
        intros.
        cbv [inv]. rewrite (Fq_inv_fermat(q:=q)(two_lt_q:=two_lt_q)).
        rewrite <-Z_nat_N at 1 2.
        rewrite (ScalarMult.homomorphism_scalarmult(phi:=phi')(MUL_is_scalarmult:=pow_is_scalarmult)(mul_is_scalarmult:=F.pow_is_scalarmult)).
        reflexivity.
        assumption.
      Qed.

      Let div_proof : forall a b : H, phi' (mul (inv b) a) = phi' a / phi' b.
      Proof.
        intros.
        rewrite phi'_mul, inv_proof, Algebra.field_div_definition, Algebra.commutative.
        reflexivity.
      Qed.

      Lemma field_and_iso :
        @Algebra.field H eq zero one opp add sub mul inv div
        /\ @Ring.is_homomorphism (F q) Logic.eq F.one F.add F.mul H eq one add mul phi
        /\ @Ring.is_homomorphism H eq one add mul (F q) Logic.eq F.one F.add F.mul phi'.
      Proof. eapply @Field.field_and_homomorphism_from_redundant_representation;
               assumption || exact _ || exact inv_proof || exact div_proof. Qed.
    End IsomorphicRings.
  End Iso.
End F.