(** * Batched Unsaturated Solinas: Reification Cache + Pipeline *)
(** Defines batched versions of primitives: apply the scalar operation
    independently to 4 slices of flat input lists. Each slice has [n]
    elements; inputs/outputs are flat lists of [4*n] elements.
    Reifies each for use with [BoundsPipeline] and the equivalence checker. *)
From Coq Require Import ZArith List.
From Coq Require Import Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinasReificationCache.

Import ListNotations.
Import Associational Positional.
Local Open Scope Z_scope.

Local Set Keyed Unification.

Section batched_ops.
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (len_c : nat)
          (idxs : list nat)
          (len_idxs : nat)
          (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
          (Hn_nz : n <> 0%nat)
          (Hc : length c = len_c)
          (Hidxs : length idxs = len_idxs).

  Definition batched_carry_mulmod (a b : list Z) : list Z :=
    carry_mulmod limbwidth_num limbwidth_den s c n idxs
      (firstn n a) (firstn n b) ++
    carry_mulmod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn n a)) (firstn n (skipn n b)) ++
    carry_mulmod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn (n+n) a)) (firstn n (skipn (n+n) b)) ++
    carry_mulmod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn (n+n+n) a)) (firstn n (skipn (n+n+n) b)).

  Definition batched_addmod (a b : list Z) : list Z :=
    addmod limbwidth_num limbwidth_den n
      (firstn n a) (firstn n b) ++
    addmod limbwidth_num limbwidth_den n
      (firstn n (skipn n a)) (firstn n (skipn n b)) ++
    addmod limbwidth_num limbwidth_den n
      (firstn n (skipn (n+n) a)) (firstn n (skipn (n+n) b)) ++
    addmod limbwidth_num limbwidth_den n
      (firstn n (skipn (n+n+n) a)) (firstn n (skipn (n+n+n) b)).

  Definition batched_carrymod (f : list Z) : list Z :=
    carrymod limbwidth_num limbwidth_den s c n idxs
      (firstn n f) ++
    carrymod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn n f)) ++
    carrymod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn (n+n) f)) ++
    carrymod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn (n+n+n) f)).

  Definition batched_carry_addmod (a b : list Z) : list Z :=
    carry_addmod limbwidth_num limbwidth_den s c n idxs
      (firstn n a) (firstn n b) ++
    carry_addmod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn n a)) (firstn n (skipn n b)) ++
    carry_addmod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn (n+n) a)) (firstn n (skipn (n+n) b)) ++
    carry_addmod limbwidth_num limbwidth_den s c n idxs
      (firstn n (skipn (n+n+n) a)) (firstn n (skipn (n+n+n) b)).

  Context (balance : list Z).

  Definition batched_submod (a b : list Z) : list Z :=
    submod limbwidth_num limbwidth_den n balance
      (firstn n a) (firstn n b) ++
    submod limbwidth_num limbwidth_den n balance
      (firstn n (skipn n a)) (firstn n (skipn n b)) ++
    submod limbwidth_num limbwidth_den n balance
      (firstn n (skipn (n+n) a)) (firstn n (skipn (n+n) b)) ++
    submod limbwidth_num limbwidth_den n balance
      (firstn n (skipn (n+n+n) a)) (firstn n (skipn (n+n+n) b)).

  Definition batched_oppmod (f : list Z) : list Z :=
    oppmod limbwidth_num limbwidth_den n balance
      (firstn n f) ++
    oppmod limbwidth_num limbwidth_den n balance
      (firstn n (skipn n f)) ++
    oppmod limbwidth_num limbwidth_den n balance
      (firstn n (skipn (n+n) f)) ++
    oppmod limbwidth_num limbwidth_den n balance
      (firstn n (skipn (n+n+n) f)).

  Definition batched_carry_submod (a b : list Z) : list Z :=
    carry_submod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n a) (firstn n b) ++
    carry_submod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n (skipn n a)) (firstn n (skipn n b)) ++
    carry_submod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n (skipn (n+n) a)) (firstn n (skipn (n+n) b)) ++
    carry_submod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n (skipn (n+n+n) a)) (firstn n (skipn (n+n+n) b)).

  Definition batched_carry_oppmod (f : list Z) : list Z :=
    carry_oppmod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n f) ++
    carry_oppmod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n (skipn n f)) ++
    carry_oppmod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n (skipn (n+n) f)) ++
    carry_oppmod limbwidth_num limbwidth_den s c n idxs balance
      (firstn n (skipn (n+n+n) f)).
End batched_ops.

Derive reified_batched_carry_mul_gen
       SuchThat (is_reification_of reified_batched_carry_mul_gen batched_carry_mulmod)
       As reified_batched_carry_mul_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_carry_mul_gen_correct_proj1 := proj1 reified_batched_carry_mul_gen_correct.
Local Definition reified_batched_carry_mul_gen_correct_proj2 := proj2 reified_batched_carry_mul_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_carry_mulmod reified_batched_carry_mul_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_carry_mul_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_carry_mul_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_carry_mul_gen.

Derive reified_batched_add_gen
       SuchThat (is_reification_of reified_batched_add_gen batched_addmod)
       As reified_batched_add_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_add_gen_correct_proj1 := proj1 reified_batched_add_gen_correct.
Local Definition reified_batched_add_gen_correct_proj2 := proj2 reified_batched_add_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_addmod reified_batched_add_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_add_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_add_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_add_gen.

Derive reified_batched_sub_gen
       SuchThat (is_reification_of reified_batched_sub_gen batched_submod)
       As reified_batched_sub_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_sub_gen_correct_proj1 := proj1 reified_batched_sub_gen_correct.
Local Definition reified_batched_sub_gen_correct_proj2 := proj2 reified_batched_sub_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_submod reified_batched_sub_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_sub_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_sub_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_sub_gen.

Derive reified_batched_carry_gen
       SuchThat (is_reification_of reified_batched_carry_gen batched_carrymod)
       As reified_batched_carry_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_carry_gen_correct_proj1 := proj1 reified_batched_carry_gen_correct.
Local Definition reified_batched_carry_gen_correct_proj2 := proj2 reified_batched_carry_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_carrymod reified_batched_carry_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_carry_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_carry_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_carry_gen.

Derive reified_batched_opp_gen
       SuchThat (is_reification_of reified_batched_opp_gen batched_oppmod)
       As reified_batched_opp_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_opp_gen_correct_proj1 := proj1 reified_batched_opp_gen_correct.
Local Definition reified_batched_opp_gen_correct_proj2 := proj2 reified_batched_opp_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_oppmod reified_batched_opp_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_opp_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_opp_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_opp_gen.

Derive reified_batched_carry_add_gen
       SuchThat (is_reification_of reified_batched_carry_add_gen batched_carry_addmod)
       As reified_batched_carry_add_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_carry_add_gen_correct_proj1 := proj1 reified_batched_carry_add_gen_correct.
Local Definition reified_batched_carry_add_gen_correct_proj2 := proj2 reified_batched_carry_add_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_carry_addmod reified_batched_carry_add_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_carry_add_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_carry_add_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_carry_add_gen.

Derive reified_batched_carry_sub_gen
       SuchThat (is_reification_of reified_batched_carry_sub_gen batched_carry_submod)
       As reified_batched_carry_sub_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_carry_sub_gen_correct_proj1 := proj1 reified_batched_carry_sub_gen_correct.
Local Definition reified_batched_carry_sub_gen_correct_proj2 := proj2 reified_batched_carry_sub_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_carry_submod reified_batched_carry_sub_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_carry_sub_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_carry_sub_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_carry_sub_gen.

Derive reified_batched_carry_opp_gen
       SuchThat (is_reification_of reified_batched_carry_opp_gen batched_carry_oppmod)
       As reified_batched_carry_opp_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_batched_carry_opp_gen_correct_proj1 := proj1 reified_batched_carry_opp_gen_correct.
Local Definition reified_batched_carry_opp_gen_correct_proj2 := proj2 reified_batched_carry_opp_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification batched_carry_oppmod reified_batched_carry_opp_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_batched_carry_opp_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_batched_carry_opp_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_batched_carry_opp_gen.
