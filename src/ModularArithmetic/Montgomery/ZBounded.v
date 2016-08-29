(*** Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on [ZLikeOps].  We follow [Montgomery/Z.v]. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Classes.Morphisms Coq.micromega.Psatz.
Require Import Crypto.ModularArithmetic.Montgomery.Z.
Require Import Crypto.ModularArithmetic.Montgomery.ZProofs.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.ZBounded.
Require Import Crypto.BaseSystem.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Local Open Scope small_zlike_scope.
Local Open Scope large_zlike_scope.
Local Open Scope Z_scope.

Section montgomery.
  Context (small_bound modulus : Z) {ops : ZLikeOps small_bound small_bound modulus} {props : ZLikeProperties ops}
          (modulus' : SmallT)
          (modulus'_valid : small_valid modulus')
          (modulus_nonzero : modulus <> 0).

  Definition partial_reduce : forall v : LargeT,
      { partial_reduce : SmallT
      | large_valid v
        -> decode_small partial_reduce = Montgomery.Z.partial_reduce modulus small_bound (decode_small modulus') (decode_large v)
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
    cbv [Montgomery.Z.partial_reduce Montgomery.Z.partial_reduce_alt Montgomery.Z.prereduce].
    pull_zlike_decode.
    subst pr; split; [ reflexivity | exact _ ].
  Defined.

  Definition reduce_via_partial : forall v : LargeT,
      { reduce : SmallT
      | large_valid v
        -> decode_small reduce = Montgomery.Z.reduce_via_partial modulus small_bound (decode_small modulus') (decode_large v)
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
    cbv [Montgomery.Z.partial_reduce Montgomery.Z.partial_reduce_alt Montgomery.Z.prereduce].
    pull_zlike_decode.
    subst pr; split; [ reflexivity | exact _ ].
  Defined.
End montgomery.
