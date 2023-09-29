Require Import Coq.ZArith.ZArith.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.
Require Import Crypto.Arithmetic.P256ADX. Import WeightStream Saturated.
Import
  Language.API.Compilers
  Language.Wf.Compilers.
Import Basic.GallinaAndReifiedIdentList IdentifiersBasicGENERATED.Compilers.
Import Coq.ZArith.ZArith.
Import Coq.derive.Derive.
Import Crypto.PushButtonSynthesis.ReificationCache.
Import
  Language.API.Compilers
  Language.Wf.Compilers.

Derive reified_p256_mul
       SuchThat (is_reification_of reified_p256_mul p256_mul)
       As reified_p256_mul_correct.
Proof. 
  Time
  instantiate (1:=
    (ltac:(
      let e := constr:(p256_mul) in
       let e := eval cbv delta [two_steps_of_p256_montgomery_reduction p256_mul mul add_mul add_mul_limb_ product_scan product_scan_ stream.map weight stream.prefixes stream.firstn condsub] in e in
      let r := Reify e in
      exact r))
    ) in (value of reified_p256_mul).
  split. { intros. exact eq_refl. }
  { prove_Wf ltac:(()). }
Time Qed.

Derive reified_p256_sqr
       SuchThat (is_reification_of reified_p256_sqr p256_sqr)
       As reified_p256_sqr_correct.
Proof. 
  Time
  instantiate (1:=
    (ltac:(
      let e := constr:(p256_sqr) in
       let e := eval cbv delta [p256_sqr sqr4 two_steps_of_p256_montgomery_reduction p256_mul mul add_mul add_mul_limb_ product_scan product_scan_ stream.map weight stream.prefixes stream.firstn condsub] in e in
      let r := Reify e in
      exact r))
    ) in (value of reified_p256_sqr).
  split. { intros. exact eq_refl. }
  { prove_Wf ltac:(()). }
Time Qed.

#[global]
 Hint Extern 1 (_ = _) => apply_cached_reification p256_mul (proj1 reified_p256_mul) : reify_cache_gen.
#[global]
 Hint Immediate (proj2 reified_p256_mul_correct) : wf_gen_cache.
#[global]
 Hint Rewrite (proj1 reified_p256_mul_correct) : interp_gen_cache.
Local Opaque reified_p256_mul. (* needed for making [autorewrite] not take a very long time *)

#[global]
 Hint Extern 1 (_ = _) => apply_cached_reification p256_sqr (proj1 reified_p256_sqr) : reify_cache_gen.
#[global]
 Hint Immediate (proj2 reified_p256_sqr_correct) : wf_gen_cache.
#[global]
 Hint Rewrite (proj1 reified_p256_sqr_correct) : interp_gen_cache.
Local Opaque reified_p256_sqr. (* needed for making [autorewrite] not take a very long time *)
