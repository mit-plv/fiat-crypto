(*** Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on [ZLikeOps].  We follow [Montgomery/Z.v]. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Classes.Morphisms Coq.micromega.Psatz.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.LegacyArithmetic.ZBounded.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.Test.
Require Import Crypto.Util.Tactics.Not.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.

Local Open Scope small_zlike_scope.
Local Open Scope large_zlike_scope.
Local Open Scope Z_scope.

Section montgomery.
  Context (small_bound modulus : Z) {ops : ZLikeOps small_bound small_bound modulus} {props : ZLikeProperties ops}
          (modulus' : SmallT)
          (modulus'_valid : small_valid modulus')
          (modulus_nonzero : modulus <> 0).

  (** pull out a common subexpression *)
  Local Ltac cse :=
    let RHS := match goal with |- _ = ?decode ?RHS /\ _ => RHS end in
    let v := fresh in
    match RHS with
    | context[?e] => not is_var e; set (v := e) at 1 2; test clearbody v
    end;
    revert v;
    match goal with
    | [ |- let v := ?val in ?LHS = ?decode ?RHS /\ ?P ]
      => change (LHS = decode (dlet v := val in RHS) /\ P)
    end.

  Definition partial_reduce : forall v : LargeT,
      { partial_reduce : SmallT
      | large_valid v
        -> decode_small partial_reduce = MontgomeryReduction.Definition.partial_reduce modulus small_bound (decode_small modulus') (decode_large v)
           /\ small_valid partial_reduce }.
  Proof.
    intro T. evar (pr : SmallT); exists pr. intros T_valid.
    assert (0 <= decode_large T < small_bound * small_bound) by auto using decode_large_valid.
    assert (0 <= decode_small (Mod_SmallBound T) < small_bound) by auto using decode_small_valid, Mod_SmallBound_valid.
    assert (0 <= decode_small modulus' < small_bound) by auto using decode_small_valid.
    assert (0 <= decode_small modulus_digits < small_bound) by auto using decode_small_valid, modulus_digits_valid.
    assert (0 <= modulus) by apply (modulus_nonneg _).
    assert (modulus < small_bound) by (rewrite <- modulus_digits_correct; omega).
    rewrite <- partial_reduce_alt_eq by omega.
    cbv [MontgomeryReduction.Definition.partial_reduce MontgomeryReduction.Definition.partial_reduce_alt MontgomeryReduction.Definition.prereduce].
    pull_zlike_decode.
    cse.
    subst pr; split; [ reflexivity | exact _ ].
  Defined.

  Definition reduce_via_partial : forall v : LargeT,
      { reduce : SmallT
      | large_valid v
        -> decode_small reduce = MontgomeryReduction.Definition.reduce_via_partial modulus small_bound (decode_small modulus') (decode_large v)
           /\ small_valid reduce }.
  Proof.
    intro T. evar (pr : SmallT); exists pr. intros T_valid.
    assert (0 <= decode_large T < small_bound * small_bound) by auto using decode_large_valid.
    assert (0 <= decode_small (Mod_SmallBound T) < small_bound) by auto using decode_small_valid, Mod_SmallBound_valid.
    assert (0 <= decode_small modulus' < small_bound) by auto using decode_small_valid.
    assert (0 <= decode_small modulus_digits < small_bound) by auto using decode_small_valid, modulus_digits_valid.
    assert (0 <= modulus) by apply (modulus_nonneg _).
    assert (modulus < small_bound) by (rewrite <- modulus_digits_correct; omega).
    unfold reduce_via_partial.
    rewrite <- partial_reduce_alt_eq by omega.
    cbv [MontgomeryReduction.Definition.partial_reduce MontgomeryReduction.Definition.partial_reduce_alt MontgomeryReduction.Definition.prereduce].
    pull_zlike_decode.
    cse.
    subst pr; split; [ reflexivity | exact _ ].
  Defined.

  Section correctness.
    Context (R' : Z)
            (Hmod : Z.equiv_modulo modulus (small_bound * R') 1)
            (Hmod' : Z.equiv_modulo small_bound (modulus * (decode_small modulus')) (-1))
            (v : LargeT)
            (H : large_valid v)
            (Hv : 0 <= decode_large v <= small_bound * modulus).
    Lemma reduce_via_partial_correct'
      : Z.equiv_modulo modulus
                       (decode_small (proj1_sig (reduce_via_partial v)))
                       (decode_large v * R')
        /\ Z.min 0 (small_bound - modulus) <= (decode_small (proj1_sig (reduce_via_partial v))) < modulus.
    Proof using H Hmod Hmod' Hv.
      rewrite (proj1 (proj2_sig (reduce_via_partial v) H)).
      eauto 6 using reduce_via_partial_correct, reduce_via_partial_in_range, decode_small_valid.
    Qed.

    Lemma reduce_via_partial_correct''
      : Z.equiv_modulo modulus
                       (decode_small (proj1_sig (reduce_via_partial v)))
                       (decode_large v * R')
        /\ 0 <= (decode_small (proj1_sig (reduce_via_partial v))) < modulus.
    Proof using H Hmod Hmod' Hv.
      pose proof (proj2 (proj2_sig (reduce_via_partial v) H)) as H'.
      apply decode_small_valid in H'.
      destruct reduce_via_partial_correct'; split; eauto; omega.
    Qed.

    Theorem reduce_via_partial_correct
      : decode_small (proj1_sig (reduce_via_partial v)) = (decode_large v * R') mod modulus.
    Proof using H Hmod Hmod' Hv.
      rewrite <- (proj1 reduce_via_partial_correct'').
      rewrite Z.mod_small by apply reduce_via_partial_correct''.
      reflexivity.
    Qed.
  End correctness.
End montgomery.
