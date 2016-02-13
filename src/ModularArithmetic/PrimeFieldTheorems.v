Require Export Spec.ModularArithmetic ModularArithmetic.ModularArithmeticTheorems.
Require Export Ring_theory Field_theory Field_tac.

Require Import Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms Setoid.
Require Import BinInt BinNat ZArith Znumtheory NArith. (* import Zdiv before Znumtheory *)
Require Import Eqdep_dec.

Existing Class prime.

Section FieldModuloPre.
  Context {q:Z} {prime_q:prime q}.
  Local Open Scope F_scope.

  Lemma Fq_1_neq_0 : (1:F q) <> (0:F q).
  Proof.
    pose proof prime_ge_2 q _.
    rewrite F_eq, !FieldToZ_ZToField, !Zmod_small by omega; congruence.
  Qed.

  Lemma F_mul_inv_l : forall x : F q, inv x * x = 1.
  Proof.
    intros.
    rewrite <-(proj1 (F_inv_spec _ x)).
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
    rewrite (proj1 (@F_inv_spec q _ _)) in H.
    replace (x * 1) with x in H by field.
    replace (y * 1) with y in H by field.
    trivial.
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

  Lemma F_div_1_r : forall x : F q, (x/1)%F = x.
  Proof.
    intros; field. (* TODO: Warning: Collision between bound variables ... *)
  Qed.
  
  Lemma sqrt_solutions : forall x y : F q, y ^ 2 = x ^ 2 -> y = x \/ y = opp x.
  Proof.
    intros.
    (* TODO(jadep) *)
  Admitted.
End VariousModPrime.