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