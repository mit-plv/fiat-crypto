(** * Push-Button Synthesis of Bernstein-Yang Inversion: Reification Cache *)
From Coq Require Import ZArith.
From Coq Require Import Derive.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.BYInv.
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

  Definition msat bitwidth n m := Partition.partition (uweight bitwidth) n m. (* m in saturated representation *)

  Derive reified_divstep_gen
         SuchThat (is_reification_of reified_divstep_gen divstep)
         As reified_divstep_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_divstep_gen_correct_proj1 := proj1 reified_divstep_gen_correct.
  Local Definition reified_divstep_gen_correct_proj2 := proj2 reified_divstep_gen_correct.
#[global]
  Hint Extern 1 (_ = _) => apply_cached_reification divstep reified_divstep_gen_correct_proj1 : reify_cache_gen.
#[global]
  Hint Immediate reified_divstep_gen_correct_proj2 : wf_gen_cache.
#[global]
  Hint Rewrite reified_divstep_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_divstep_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_msat_gen
         SuchThat (is_reification_of reified_msat_gen msat)
         As reified_msat_gen_correct.
  Proof.
    Time cache_reify ().
  Time Qed.
  Local Definition reified_msat_gen_correct_proj1 := proj1 reified_msat_gen_correct.
  Local Definition reified_msat_gen_correct_proj2 := proj2 reified_msat_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification msat reified_msat_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_msat_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_msat_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_msat_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_eval_twos_complement_gen
         SuchThat (is_reification_of reified_eval_twos_complement_gen eval_twos_complement)
         As reified_eval_twos_complement_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_eval_twos_complement_gen_correct_proj1 := proj1 reified_eval_twos_complement_gen_correct.
  Local Definition reified_eval_twos_complement_gen_correct_proj2 := proj2 reified_eval_twos_complement_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification eval_twos_complement reified_eval_twos_complement_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_eval_twos_complement_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_eval_twos_complement_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_eval_twos_complement_gen. (* needed for making [autorewrite] not take a very long time *)
End WordByWordMontgomeryInversion.
