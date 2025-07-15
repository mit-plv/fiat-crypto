(** * Push-Button Synthesis of Unsaturated Solinas: Reification Cache *)
From Coq Require Import ZArith.
From Coq Require Import Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.BaseConversion.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export BaseConversion.
  Derive reified_convert_bases_gen
         SuchThat (is_reification_of reified_convert_bases_gen convert_basesmod)
         As reified_convert_bases_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_convert_bases_gen_correct_proj1 := proj1 reified_convert_bases_gen_correct.
  Local Definition reified_convert_bases_gen_correct_proj2 := proj2 reified_convert_bases_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification convert_basesmod reified_convert_bases_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_convert_bases_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_convert_bases_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_convert_bases_gen. (* needed for making [autorewrite] not take a very long time *)
End BaseConversion.
