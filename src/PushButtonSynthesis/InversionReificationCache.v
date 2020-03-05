(** * Push-Button Synthesis of Word-By-Word Montgomery: Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.Inv.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.UniformWeight.
Require Import Lists.List.

Import
  Language.Wf.Compilers
  Language.Compilers
  Language.API.Compilers.
Import Compilers.API.

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export WordByWordMontgomeryInversion.
  Import WordByWordMontgomery.WordByWordMontgomery.

  Definition msat bitwidth n m := encode_no_reduce (uweight bitwidth) n m. (* m in saturated representation *)
  (* Precomputed value for the inversion algorithm in the montgomery domain (not sure where to put this) *)
  Definition precompmod bitwidth n m m' :=
  let bits := (Z.log2 m) + 1 in
  let i := if bits <? 46 then (49 * bits + 80) / 17 else (49 * bits + 57) / 17 in
  let k := (m + 1) / 2 in
  let precomp := (Z.sq_and_multiply_mod k i m) in
  encodemod bitwidth n m m' precomp.

  Derive reified_precomp_gen
         SuchThat (is_reification_of reified_precomp_gen precompmod)
         As reified_precomp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification precompmod (proj1 reified_precomp_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_precomp_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_precomp_gen_correct) : interp_gen_cache.
  Local Opaque reified_precomp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_divstep_gen
         SuchThat (is_reification_of reified_divstep_gen divstep)
         As reified_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification divstep (proj1 reified_divstep_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_divstep_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_divstep_gen_correct) : interp_gen_cache.
  Local Opaque reified_divstep_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_msat_gen
         SuchThat (is_reification_of reified_msat_gen msat)
         As reified_msat_gen_correct.
  Proof.
    Time cache_reify ().
    Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification msat (proj1 reified_msat_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_msat_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_msat_gen_correct) : interp_gen_cache.
  Local Opaque reified_msat_gen. (* needed for making [autorewrite] not take a very long time *)
End WordByWordMontgomeryInversion.
