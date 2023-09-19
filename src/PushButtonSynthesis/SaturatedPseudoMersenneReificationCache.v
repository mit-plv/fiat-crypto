(** * Push-Button Synthesis of Saturated pseude-Mersenne reduction: Reification Cache *)

Require Import Crypto.Language.IdentifierParameters.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Language.PreExtra.

Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.SaturatedPseudoMersenne.
Require Import Crypto.PushButtonSynthesis.ReificationCache.

Import WeightStream WeightStream.Saturated.

Local Open Scope Z_scope.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Import
  Language.API.Compilers
  Language.Wf.Compilers.

Module Export SolinasReduction.

  Derive reified_add_gen
         SuchThat (is_reification_of reified_add_gen addmod)
         As reified_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.

  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. 
    Time
    instantiate (1:=(ltac:(
        let e := constr:(mulmod) in
        let e := eval cbv delta [mulmod mul add_mul add_mul_limb_ add_mul_limb reduce' product_scan stream.map weight stream.prefixes] in e in
        let r := Reify e in
        exact r)))
      in (value of reified_mul_gen).
    split. { intros. exact eq_refl. }
    { prove_Wf ltac:(()). }
  Time Qed.

  Derive reified_square_gen
         SuchThat (is_reification_of reified_square_gen (fun bound n z a => mulmod bound n z a a))
         As reified_square_gen_correct.
  Proof. 
    Time
    instantiate (1:=(ltac:(
        let e := constr:((fun bound n z a => mulmod bound n z a a)) in
        let e := eval cbv delta [mulmod mul add_mul add_mul_limb_ add_mul_limb reduce' product_scan stream.map weight stream.prefixes] in e in
        let r := Reify e in
        exact r)))
      in (value of reified_square_gen).
    split. { intros. exact eq_refl. }
    { prove_Wf ltac:(()). }
  Time Qed.

  #[global]
   Hint Extern 1 (_ = _) => apply_cached_reification addmod (proj1 reified_add_gen) : reify_cache_gen.
  #[global]
   Hint Immediate (proj2 reified_add_gen_correct) : wf_gen_cache.
  #[global]
   Hint Rewrite (proj1 reified_add_gen_correct) : interp_gen_cache.
  Local Opaque reified_add_gen. (* needed for making [autorewrite] not take a very long time *)

  #[global]
   Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen) : reify_cache_gen.
  #[global]
   Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
  #[global]
   Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  #[global]
   Hint Extern 1 (_ = _) => apply_cached_reification Positional.squaremod (proj1 reified_square_gen) : reify_cache_gen.
  #[global]
   Hint Immediate (proj2 reified_square_gen_correct) : wf_gen_cache.
  #[global]
   Hint Rewrite (proj1 reified_square_gen_correct) : interp_gen_cache.
  Local Opaque reified_square_gen. (* needed for making [autorewrite] not take a very long time *)

End SolinasReduction.
