(** * Push-Button Synthesis of Solinas Reduction: Reification Cache *)
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.SolinasReduction.
Require Import Crypto.PushButtonSynthesis.ReificationCache.

Require Import Crypto.Language.IdentifierParameters.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Language.PreExtra.

Local Open Scope Z_scope.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Import
  Language.API.Compilers
  Language.Wf.Compilers.
Import SolinasReduction.SolinasReduction.

Derive reified_mul_gen
       SuchThat (is_reification_of reified_mul_gen mulmod)
       As reified_mul_gen_correct.
Proof. Time cache_reify (). Time Qed.

#[global]
 Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen) : reify_cache_gen.
#[global]
 Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
#[global]
 Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)
