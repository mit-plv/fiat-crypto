(** * Push-Button Synthesis of Bitcoin Multiplication: Reification Cache *)
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.Arithmetic.DettmanMultiplication.
Local Open Scope Z_scope.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export DettmanMultiplication.
  Definition mulmod
             (e : nat)
             (c : list (Z*Z))
             (limbs : nat)
             (limb_size : nat)
    := mulmod_general e c limbs limb_size.

  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)
End DettmanMultiplication.
