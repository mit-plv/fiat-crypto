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

Existing Class prime.

Lemma F_inv_spec : forall {m}, inv 0%F = (0%F : F m)
      /\ (prime m -> forall a0 : F m, a0 <> 0%F -> (a0 * inv a0)%F = 1%F).
Proof.
  intros m.
  pose (@inv_with_spec m) as H.
  change (@inv m) with (proj1_sig H).
  destruct H; eauto.
Qed.

Section FieldModuloPre.
  Context {q:Z} {prime_q:prime q}.
  Local Open Scope F_scope.

  Lemma Fq_1_neq_0 : (1:F q) <> (0:F q).
  Proof.
    pose proof prime_ge_2 q _.
    rewrite F_eq, !FieldToZ_ZToField, !Zmod_small by omega; congruence.
  Qed.

  Lemma F_mul_inv_r : forall x : F q, x <> 0 -> x * inv x = 1.
  Proof.
    intros.
    edestruct @F_inv_spec; eauto.
  Qed.

  Lemma F_mul_inv_l : forall x : F q, x <> 0 -> inv x * x = 1.
  Proof.
    intros.
    edestruct @F_inv_spec as [Ha Hb]; eauto.
    erewrite <-Hb; eauto.
    Fdefn.
  Qed.

  (* Add an abstract field (without modifiers) *)
  Definition Ffield_theory : field_theory 0%F 1%F (@add q) (@mul q) (@sub q) (@opp q) (@div q) (@inv q) eq.
  Proof.
    constructor; auto using Fring_theory, Fq_1_neq_0, F_mul_inv_l.
  Qed.
End FieldModuloPre.

Module Type PrimeModulus.
  Parameter modulus : Z.
  Parameter prime_modulus : prime modulus.
End PrimeModulus.

Module FieldModulo (Import M : PrimeModulus).
  (* Add our field with all the fixin's *)
  Module Import RingM := RingModulo M.
  Definition field_theory_modulo := @Ffield_theory modulus prime_modulus.
  Add Field Ffield_Z : field_theory_modulo
    (morphism ring_morph_modulo,
     preprocess [Fpreprocess],
     postprocess [Fpostprocess],
     constants [Fconstant],
     div morph_div_theory_modulo,
     power_tac power_theory_modulo [Fexp_tac]). 
End FieldModulo.

Section VariousModPrime.
  Context {q:Z} {prime_q:prime q}.
  Local Open Scope F_scope.
  Add Field Ffield_Z : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 
  
  Lemma Fq_mul_eq : forall x y z : F q, z <> 0 -> x * z = y * z -> x = y.
  Proof.
    intros ? ? ? z_nonzero mul_z_eq.
    assert (x * z * inv z = y * z * inv z) as H by (rewrite mul_z_eq; reflexivity).
    replace (x * z * inv z) with (x * (z * inv z)) in H by (field; trivial).
    replace (y * z * inv z) with (y * (z * inv z)) in H by (field; trivial).
    rewrite F_mul_inv_r in H by assumption.
    replace (x * 1) with x in H by field.
    replace (y * 1) with y in H by field.
    trivial.
  Qed.

  Lemma Fq_mul_eq_l : forall x y z : F q, z <> 0 -> z * x = z * y -> x = y.
  Proof.
    intros ? ? ? Hz Heq.
    apply (Fq_mul_eq _ _ z); auto.
    apply (Fq_sub_eq _ _ _ _ Heq); ring.
  Qed.

  Lemma Fq_inv_unique' : forall
      inv1 (inv1ok: inv1 0 = 0 /\ forall x : F q, x <> 0 ->  x * inv1 x = 1)
      inv2 (inv2ok: inv2 0 = 0 /\ forall x : F q, x <> 0 ->  x * inv2 x = 1),
      forall x, inv1 x = inv2 x.
  Proof.
    intros inv1 [inv1_0 inv1_x] inv2 [inv2_0 inv2_x] x.
    destruct (F_eq_dec x 0) as [H|H]; [congruence|].
    apply (Fq_mul_eq_l _ _ x H). rewrite inv1_x, inv2_x; trivial.
  Qed.

  Lemma Fq_inv_unique : forall
      inv' (inv'ok: inv' 0 = 0 /\ forall x : F q, x <> 0 -> x * inv' x = 1),
      forall x, inv x = inv' x.
  Proof.
    intros ? [? ?] ?.
    pose proof (@F_inv_spec q) as [? ?].
    eauto using Fq_inv_unique'.
  Qed.

  Let inv_fermat_powmod (x:Z) : Z := powmod q x (Z.to_N (q-2)).
  Lemma FieldToZ_inv_efficient : 2 < q ->
                                 forall x : F q, FieldToZ (inv x) = inv_fermat_powmod x.
  Proof.
    intros.
    rewrite (fun pf => Fq_inv_unique (fun x : F q => ZToField (inv_fermat_powmod (FieldToZ x))) pf);
    subst inv_fermat_powmod; intuition; rewrite powmod_Zpow_mod;
    replace (Z.of_N (Z.to_N (q - 2))) with (q-2)%Z by (rewrite Z2N.id ; omega).
    - (* inv in range *) rewrite FieldToZ_ZToField, Zmod_mod; reflexivity.
    - (* inv 0 *) replace (FieldToZ 0) with 0%Z by auto.
      rewrite Z.pow_0_l by omega.
      rewrite Zmod_0_l; trivial.
    - (* inv nonzero *) rewrite <- (fermat_inv q _ x0) by
        (rewrite mod_FieldToZ; eauto using FieldToZ_nonzero).
      rewrite <-(ZToField_FieldToZ x0).
      rewrite <-ZToField_mul.
      rewrite ZToField_FieldToZ.
      apply ZToField_eqmod.
      demod; reflexivity.
  Qed.
 
  Lemma Fq_mul_zero_why : forall a b : F q, a*b = 0 -> a = 0 \/ b = 0.
    intros.
    assert (Z := F_eq_dec a 0); destruct Z.
  
    - left; intuition.
  
    - assert (a * b / a = 0) by
        ( rewrite H; field; intuition ).
  
      replace (a*b/a) with (b) in H0 by (field; trivial).
      right; intuition.
  Qed.
  
  Lemma Fq_mul_nonzero_nonzero : forall a b : F q, a <> 0 -> b <> 0 -> a*b <> 0.
    intros; intuition; subst.
    apply Fq_mul_zero_why in H1.
    destruct H1; subst; intuition.
  Qed.
  Hint Resolve Fq_mul_nonzero_nonzero.
  
  Lemma Fq_pow_zero : forall (p: N), p <> 0%N -> (0^p = @ZToField q 0)%F.
    induction p using N.peano_ind;
    rewrite <-?N.add_1_l, ?(proj2 (@F_pow_spec q _) _), ?(proj1 (@F_pow_spec q _)).
    - intuition.
    - intro H. apply F_mul_0_l.
  Qed.

  Lemma Fq_root_zero : forall (x: F q) (p: N), x^p = 0 -> x = 0.
    induction p using N.peano_ind;
    rewrite <-?N.add_1_l, ?(proj2 (@F_pow_spec q _) _), ?(proj1 (@F_pow_spec q _)).
    - intros; destruct Fq_1_neq_0; auto.
    - intro H; destruct (Fq_mul_zero_why x (x^p) H); auto.
  Qed.

  Lemma Fq_root_nonzero : forall (x:F q) p, x^p <> 0 -> (p <> 0)%N -> x <> 0.
    induction p using N.peano_ind;
    rewrite <-?N.add_1_l, ?(proj2 (@F_pow_spec q _) _), ?(proj1 (@F_pow_spec q _)).
    - intuition.
    - destruct (N.eq_dec p 0); intro H; intros; subst.
      + rewrite (proj1 (@F_pow_spec q _)) in H; replace (x*1) with (x) in H by ring; trivial.
      + apply IHp; auto. intro Hz; rewrite Hz in *. apply H, F_mul_0_r.
  Qed.

  Lemma Fq_pow_nonzero : forall (x : F q) p, x <> 0 -> x^p <> 0.
  Proof.
    induction p using N.peano_ind;
    rewrite <-?N.add_1_l, ?(proj2 (@F_pow_spec q _) _), ?(proj1 (@F_pow_spec q _)).
    - intuition. auto using Fq_1_neq_0.
    - intros H Hc. destruct (Fq_mul_zero_why _ _ Hc).
      + intuition.
      + apply IHp; auto.
  Qed.

  Lemma F_minus_swap : forall x y : F q, x - y = 0 -> y - x = 0.
  Proof.
    intros ? ? eq_zero.
    replace x with (x - y + y); try ring.
    rewrite eq_zero.
    ring.
  Qed.

  Lemma Fq_square_mul : forall x y z : F q, (y <> 0) ->
    x ^ 2 = z * y ^ 2 -> exists sqrt_z, sqrt_z ^ 2 = z.
  Proof.
    intros ? ? ? y_nonzero A.
    exists (x / y).
    assert ((x / y) ^ 2 = x ^ 2 / y ^ 2) as square_distr_div by (field; trivial).
    assert (y ^ 2 <> 0) as y2_nonzero by (
      change (2%N) with (1+(1+0))%N;
      rewrite !(proj2 (@F_pow_spec q _) _), !(proj1 (@F_pow_spec q _));
      auto 10 using Fq_mul_nonzero_nonzero, Fq_1_neq_0).
    rewrite (Fq_mul_eq _ z (y ^ 2)); auto.
    rewrite <- A.
    field; trivial.
  Qed.

  Lemma Fq_square_mul_sub : forall x y z : F q,
    0 = z * y ^ 2 - x ^ 2 -> (exists sqrt_z, sqrt_z ^ 2 = z) \/ x = 0.
  Proof.
    intros ? ? ? eq_zero_sub.
    destruct (F_eq_dec y 0). {
      subst_max.
      rewrite Fq_pow_zero in eq_zero_sub by congruence.
      rewrite F_mul_0_r in eq_zero_sub.
      assert (x ^ 2 = 0 - x ^ 2 + x ^ 2) as minus_plus_x2 by (rewrite <- eq_zero_sub; ring).
      assert (x ^ 2 = 0) as x2_zero by (rewrite minus_plus_x2; ring).
      apply Fq_root_zero in x2_zero.
      right; auto.
    } {
      left.
      eapply Fq_square_mul; eauto.
      instantiate (1 := x).
      assert (x ^ 2 = z * y ^ 2 - x ^ 2 + x ^ 2) as plus_minus_x2 by 
        (rewrite <- eq_zero_sub; ring).
      rewrite plus_minus_x2; ring.
    }
  Qed.

  Lemma F_div_mul : forall x y z : F q, y <> 0 -> (z = (x / y) <-> z * y = x).
  Proof.
    split; intros; subst; field.
  Qed.

  Lemma F_div_1_r : forall x : F q, (x/1)%F = x.
  Proof.
    intros; field. (* TODO: Warning: Collision between bound variables ... *)
  Qed.

  Lemma F_eq_opp_zero : forall x : F q, 2 < q -> (x = opp x <-> x = 0).
  Proof.
    split; intro A.
    + pose proof (F_opp_spec x) as opp_spec.
      rewrite <- A in opp_spec.
      replace (x + x) with (ZToField 2 * x) in opp_spec by ring.
      apply Fq_mul_zero_why in opp_spec.
      destruct opp_spec as [eq_2_0 | ?]; auto.
      apply F_eq in eq_2_0.
      rewrite FieldToZ_ZToField in eq_2_0.
      replace (FieldToZ 0) with 0%Z in eq_2_0 by auto.
      replace (2 mod q) with 2 in eq_2_0; try discriminate.
      symmetry; apply Z.mod_small; omega.
    + subst.
      rewrite <- (F_opp_spec 0) at 1.
      ring.
  Qed.

  Lemma euler_criterion_F : forall (a : F q) (q_odd : 2 < q) (a_nonzero : a <> 0),
    (a ^ (Z.to_N (q / 2)) = 1) <-> isSquare a.
  Proof.
    (*pose proof q_odd.*)
    split; intros A. {
      apply square_Zmod_F; auto.
      eapply euler_criterion; omega || auto.
      + apply div2_p_1mod4; auto; omega.
      + pose proof (FieldToZ_nonzero_range a a_nonzero); omega.
      + replace (q / 2)%Z with (Z.of_N (Z.to_N (q / 2)))
          by (apply Z2N.id; apply Z.div_pos; prime_bound).
        rewrite FieldToZ_pow_Zpow_mod by omega.
        rewrite A.
        replace (FieldToZ 1) with (1 mod q) by auto.
        apply Z.mod_1_l; omega.
    } {
      apply F_eq.
      rewrite <- FieldToZ_pow_Zpow_mod by omega.
      rewrite Z2N.id by (apply Z.div_pos; omega).
      replace (FieldToZ 1) with 1%Z
        by (rewrite FieldToZ_ZToField at 1; symmetry; apply Zmod_1_l; omega).
      apply euler_criterion; try prime_bound; auto.
      + apply div2_p_1mod4; auto; omega.
      + pose proof (FieldToZ_nonzero_range a a_nonzero); omega.
      + apply square_Zmod_F; auto.
    }
  Qed.

  Lemma euler_criterion_if : forall (a : F q) (q_odd : 2 < q),
    if (orb (F_eqb a 0) (F_eqb (a ^ (Z.to_N (q / 2))) 1))
    then (isSquare a) else (forall b, b ^ 2 <> a).
  Proof.
    unfold orb; intros.
    rewrite <- if_F_eq_dec_if_F_eqb.
    do 2 break_if; try congruence.
    + subst; exists 0; apply Fq_pow_zero; congruence.
    + unfold isSquare; apply F_eqb_eq in Heqb; apply euler_criterion_F; eauto.
    + intros b b_id.
      apply F_eqb_neq in Heqb.
      assert (isSquare a) as a_square by (eexists; eauto).
      apply euler_criterion_F in a_square; auto.
  Qed.

  Lemma sqrt_solutions : forall x y : F q, y ^ 2 = x ^ 2 -> y = x \/ y = opp x.
  Proof.
    intros ? ? squares_eq.
    remember (y - x) as z.
    replace y with (x + z) in * by (rewrite Heqz; ring).
    replace (x ^ 2) with (0 + x ^ 2) in squares_eq by ring.
    replace ((x + z) ^ 2) with (z * (x + (x + z)) + x ^ 2) in squares_eq by ring.
    apply F_add_reg_r in squares_eq.
    apply Fq_mul_zero_why in squares_eq.
    destruct squares_eq as [? | z_2x_0]; [ left; subst; ring | right ].
    pose proof (F_opp_spec x) as opp_spec.
    rewrite <- z_2x_0 in opp_spec.
    apply F_add_reg_l in opp_spec; auto.
  Qed.

  Global Instance Fq_Ring_ops : @Ring_ops (F q) 0 1 add mul sub opp eq.
  Global Instance Fq_Ring: @Ring (F q) 0 1 add mul sub opp eq Fq_Ring_ops.
  Proof.
    econstructor; eauto with typeclass_instances;
      unfold R2, equality, eq_notation, addition, add_notation, one, one_notation,
      multiplication, mul_notation, zero, zero_notation, subtraction,
      sub_notation, opposite, opp_notation; intros; ring.
    Qed.

  Global Instance Fq_Cring: @Cring (F q) 0 1 add mul sub opp eq Fq_Ring_ops Fq_Ring.
  Proof.
    repeat intro. apply F_mul_comm.
  Qed.

  Global Instance Fq_Integral_domain : @Integral_domain (F q) 0 1 add mul sub opp eq Fq_Ring_ops Fq_Ring Fq_Cring.
  Proof.
    econstructor; eauto using Fq_mul_zero_why, Fq_1_neq_0.
  Qed.
End VariousModPrime.

Section SquareRootsPrime5Mod8.
  Context {q:Z} {prime_q: prime q} {q_5mod8 : q mod 8 = 5}.

  (* This is always true, but easier to check by computation than to prove *)
  Context (sqrt_minus1_valid : ((ZToField 2 ^ Z.to_N (q / 4)) ^ 2 = @opp q 1)%F).

  Local Open Scope F_scope.
  Add Field Ffield_8mod5 : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

  (* This is only the square root of -1 if q mod 8 is 3 or 5 *)
  Definition sqrt_minus1 : F q :=  ZToField 2 ^ Z.to_N (q / 4).

  Lemma two_lt_q_5mod8 : 2 < q.
  Proof.
    pose proof (prime_ge_2 q _) as two_le_q.
    apply Zle_lt_or_eq in two_le_q.
    destruct two_le_q; auto.
    subst_max.
    discriminate.
  Qed.

  (* square root mod q relies on the fact that q is 5 mod 8 *)
  Definition sqrt_mod_q (a : F q) := 
    let b := a ^ Z.to_N (q / 8 + 1) in
    (match (F_eq_dec (b ^ 2) a) with
    | left A => b
    | right A => (sqrt_minus1 * b)%F
    end).

  Lemma eq_b4_a2 : forall x : F q, isSquare x ->
    ((x ^ Z.to_N (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2.
  Proof.
    intros.
    destruct (F_eq_dec x 0). {
      subst.
      repeat rewrite Fq_pow_zero; try (intuition; discriminate).
      intro false_eq.
      assert (0 <= q / 8)%Z by zero_bounds.
      assert (0 < q / 8 + 1) by omega.
      replace 0%N with (Z.to_N 0) in * by auto.
      apply Z2N.inj in false_eq; omega.
    } {
      rewrite F_pow_compose.
      replace (2 * 2)%N with 4%N by auto.
      rewrite F_pow_compose.
      replace (4 * Z.to_N (q / 8 + 1))%N with (Z.to_N (q / 2 + 2))%N.

      Focus 2.
      replace 4%N with (Z.to_N 4) by auto.
      rewrite <- Z2N.inj_mul by zero_bounds.
      apply Z2N.inj_iff; try zero_bounds.
      rewrite <- Z.mul_cancel_l with (p := 2) by omega.
      ring_simplify.
      rewrite mul_div_eq by omega.
      rewrite mul_div_eq by omega.
      rewrite (Zmod_div_mod 2 8 q) by
        (try omega; apply Zmod_divide; omega || auto).
      rewrite q_5mod8.
      replace (5 mod 2)%Z with 1%Z by auto.
      ring.
      (* End Focus *)

      rewrite Z2N.inj_add by zero_bounds.
      rewrite <- F_pow_add by zero_bounds.
      replace (x ^ Z.to_N (q / 2)) with (@ZToField q 1).
      replace (Z.to_N 2) with 2%N by auto.
      ring.

      symmetry; apply euler_criterion_F; auto using two_lt_q_5mod8.
    }
  Qed.

  Lemma sqrt_mod_q_valid : forall x, isSquare x ->
    (sqrt_mod_q x) ^ 2 = x.
  Proof.
    intros x x_square.
    destruct (sqrt_solutions x _ (eq_b4_a2 x x_square)) as [? | eq_b2_oppx];
      unfold sqrt_mod_q; break_if; intuition.
    ring_simplify.
    unfold sqrt_minus1.
    rewrite sqrt_minus1_valid.
    rewrite eq_b2_oppx.
    field.
  Qed.

End SquareRootsPrime5Mod8.