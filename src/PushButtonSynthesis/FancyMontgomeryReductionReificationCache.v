(** * Push-Button Synthesis of fancy mongomery reduction : Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.FancyMontgomeryReduction.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Import Associational Positional.
Import FancyMontgomeryReduction.MontgomeryReduction.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export MontgomeryReduction.
  Derive reified_montred_gen
         SuchThat (is_reification_of reified_montred_gen montred')
         As reified_montred_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Module Export ReifyHints.
    Hint Extern 1 (_ = _) => apply_cached_reification montred' (proj1 reified_montred_gen_correct) : reify_cache_gen.
    Hint Immediate (proj2 reified_montred_gen_correct) : wf_gen_cache.
    Hint Rewrite (proj1 reified_montred_gen_correct) : interp_gen_cache.
  End ReifyHints.
  Local Opaque reified_montred_gen. (* needed for making [autorewrite] not take a very long time *)
End MontgomeryReduction.
