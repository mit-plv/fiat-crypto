(** * Push-Button Synthesis of Unsaturated Solinas: Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
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
  Hint Extern 1 (_ = _) => apply_cached_reification convert_basesmod (proj1 reified_convert_bases_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_convert_bases_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_convert_bases_gen_correct) : interp_gen_cache.
  Local Opaque reified_convert_bases_gen. (* needed for making [autorewrite] not take a very long time *)
End BaseConversion.
