(** * Push-Button Synthesis of Solinas Reduction: Reification Cache *)
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.SolinasReduction.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export SolinasReductionCache.

  Import SolinasReduction.SolinasReduction.

  Definition mul
             (base : Z)
             (s : Z)
             (c : list (Z * Z))
             (n: nat)
    := mulmod base s c n.
  Check mul.
  Print mul.

  Derive reified_solred_gen
         SuchThat (is_reification_of reified_solred_gen mul)
         As reified_solred_gen_correct.
  Proof. Time cache_reify (). Time Qed.
#[global]
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen_correct) : reify_cache_gen.
#[global]
  Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
#[global]
  Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)
End SolinasReduction.
