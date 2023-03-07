(** * Push-Button Synthesis of Bitcoin Multiplication: Reification Cache *)
Require Import Coq.derive.Derive.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.Arithmetic.DettmanMultiplication.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export DettmanMultiplication.
  Import dettman_multiplication_mod_ops.
  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
#[global]
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen_correct) : reify_cache_gen.
#[global]
  Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
#[global]
  Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)
End DettmanMultiplication.
