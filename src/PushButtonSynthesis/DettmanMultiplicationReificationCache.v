(** * Push-Button Synthesis of Bitcoin Multiplication: Reification Cache *)
From Coq Require Import Derive.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.Arithmetic.DettmanMultiplication.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export DettmanMultiplication.
  Import dettman_multiplication_mod_ops.
  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_mul_gen_correct_proj1 := proj1 reified_mul_gen_correct.
  Local Definition reified_mul_gen_correct_proj2 := proj2 reified_mul_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod reified_mul_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_mul_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_mul_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_square_gen
         SuchThat (is_reification_of reified_square_gen squaremod)
         As reified_square_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_square_gen_correct_proj1 := proj1 reified_square_gen_correct.
  Local Definition reified_square_gen_correct_proj2 := proj2 reified_square_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification squaremod reified_square_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_square_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_square_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_square_gen. (* needed for making [autorewrite] not take a very long time *)
End DettmanMultiplication.
