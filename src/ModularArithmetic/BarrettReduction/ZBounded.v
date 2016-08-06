(*** Barrett Reduction *)
(** This file implements Barrett Reduction on [ZLikeOps].  We follow
    [BarretReduction/ZHandbook.v]. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Classes.Morphisms Coq.micromega.Psatz.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZHandbook.
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
    pull_zlike_decode.
    subst pr; split; [ reflexivity | exact _ ].
  Defined.
End barrett.
