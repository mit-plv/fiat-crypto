(*** Barrett Reduction *)
(** This file implements Barrett Reduction on [ZLikeOps].  We follow
    [BarretReduction/ZHandbook.v]. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Classes.Morphisms Coq.micromega.Psatz.
Require Import Crypto.Arithmetic.BarrettReduction.HAC.
Require Import Crypto.LegacyArithmetic.ZBounded.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Local Open Scope small_zlike_scope.
Local Open Scope large_zlike_scope.
Local Open Scope Z_scope.

Section barrett.
  Context (m b k μ offset : Z)
          (m_pos : 0 < m)
          (base_pos : 0 < b)
          (k_good : m < b^k)
          (μ_good : μ = b^(2*k) / m) (* [/] is [Z.div], which is truncated *)
          (offset_nonneg : 0 <= offset)
          (k_big_enough : offset <= k)
          (m_small : 3 * m <= b^(k+offset))
          (m_large : b^(k-offset) <= m + 1).
  Context {ops : ZLikeOps (b^(k+offset)) (b^(k-offset)) m} {props : ZLikeProperties ops}
          (μ' : SmallT)
          (μ'_good : small_valid μ')
          (μ'_eq : decode_small μ' = μ).

  Definition barrett_reduce : forall x : LargeT,
      { barrett_reduce : SmallT
      | medium_valid x
        -> decode_small barrett_reduce = (decode_large x) mod m
           /\ small_valid barrett_reduce }.
  Proof.
    intro x. evar (pr : SmallT); exists pr. intros x_valid.
    assert (0 <= decode_large x < b^(k+offset) * b^(k-offset)) by auto using decode_medium_valid.
    assert (0 <= decode_large x < b^(2 * k)) by (autorewrite with pull_Zpow zsimplify in *; omega).
    assert ((decode_large x) mod b^(k-offset) < b^(k-offset)) by auto with zarith omega.
    rewrite (barrett_reduction_small m b (decode_large x) k μ offset) by omega.
    rewrite <- μ'_eq.
    pull_zlike_decode; cbv zeta; pull_zlike_decode. (* Extra [cbv iota; pull_zlike_decode] to work around bug #4165 (https://coq.inria.fr/bugs/show_bug.cgi?id=4165) in 8.4 *)
    subst pr; split; [ reflexivity | exact _ ].
  Defined.

  Definition barrett_reduce_function : LargeT -> SmallT
    := Eval cbv [proj1_sig barrett_reduce]
      in fun x => proj1_sig (barrett_reduce x).
  Lemma barrett_reduce_correct x
    : medium_valid x
      -> decode_small (barrett_reduce_function x) = (decode_large x) mod m
         /\ small_valid (barrett_reduce_function x).
  Proof using base_pos k_big_enough m_large m_pos m_small offset_nonneg μ'_eq μ'_good μ_good.
    exact (proj2_sig (barrett_reduce x)).
  Qed.
End barrett.

Module BarrettBundled.
  Class BarrettParameters :=
    { m : Z;
      b : Z;
      k : Z;
      offset : Z;
      μ := b ^ (2 * k) / m;
      ops : ZLikeOps (b ^ (k + offset)) (b ^ (k - offset)) m;
      μ' : SmallT }.
  Global Existing Instance ops.

  Class BarrettParametersCorrect {params : BarrettParameters} :=
    { m_pos : 0 < m;
      base_pos : 0 < b;
      offset_nonneg : 0 <= offset;
      k_big_enough : offset <= k;
      m_small : 3 * m <= b ^ (k + offset);
      m_large : b ^ (k - offset) <= m + 1;
      props : ZLikeProperties ops;
      μ'_good : small_valid μ';
      μ'_eq : decode_small μ' = μ }.
  Global Arguments BarrettParametersCorrect : clear implicits.
  Global Existing Instance props.

  Module Export functions.
    Definition barrett_reduce_function_bundled {params : BarrettParameters}
    : LargeT -> SmallT
      := barrett_reduce_function m b k offset μ'.
    Definition barrett_reduce_correct_bundled {params : BarrettParameters} {params_proofs : BarrettParametersCorrect params}
      : forall x, medium_valid x
                  -> decode_small (barrett_reduce_function_bundled x) = (decode_large x) mod m
                     /\ small_valid (barrett_reduce_function_bundled x)
      := @barrett_reduce_correct
           m b k μ offset
           m_pos base_pos eq_refl offset_nonneg
           k_big_enough m_small m_large
           ops props μ' μ'_good μ'_eq.
  End functions.
End BarrettBundled.
Export BarrettBundled.functions.
Global Existing Instance BarrettBundled.ops.
Global Arguments BarrettBundled.BarrettParametersCorrect : clear implicits.
Global Existing Instance BarrettBundled.props.
