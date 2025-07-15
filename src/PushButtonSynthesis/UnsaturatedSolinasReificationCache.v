(** * Push-Button Synthesis of Unsaturated Solinas: Reification Cache *)
From Coq Require Import ZArith.
From Coq Require Import Derive.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export UnsaturatedSolinas.
  Definition zeromod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 0.
  Definition onemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 1.
  Definition primemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n (s - Associational.eval c).
  Definition evalmod limbwidth_num limbwidth_den n := Positional.eval (weight limbwidth_num limbwidth_den) n.
  Definition bytes_evalmod s := Positional.eval (weight 8 1) (bytes_n s).

(**
<<
#!/usr/bin/env python

indent = '  '

print((indent + '(' + r'''**
<<
%s
>>
*''' + ')\n') % open(__file__, 'r').read())

same_ops = ('carry_mul', 'carry_square', 'carry_scmul', 'carry', 'encode', 'add', 'sub', 'opp', 'carry_add', 'carry_sub', 'carry_opp', 'zero', 'one', 'prime', 'eval', 'bytes_eval')
ops = [(op, f'{op}mod') for op in same_ops] + [('to_bytes', 'freeze_to_bytesmod'), ('from_bytes', 'from_bytesmod')]
for op, opmod in ops:
    print((fr'''{indent}Derive reified_{op}_gen
       SuchThat (is_reification_of reified_{op}_gen {opmod})
       As reified_{op}_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_{op}_gen_correct_proj1 := proj1 reified_{op}_gen_correct.
Local Definition reified_{op}_gen_correct_proj2 := proj2 reified_{op}_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification {opmod} reified_{op}_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_{op}_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_{op}_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_{op}_gen. (* needed for making [autorewrite] not take a very long time *)''').replace('\n', f'\n{indent}') + '\n')

>>
*)

  Derive reified_carry_mul_gen
         SuchThat (is_reification_of reified_carry_mul_gen carry_mulmod)
         As reified_carry_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_carry_mul_gen_correct_proj1 := proj1 reified_carry_mul_gen_correct.
  Local Definition reified_carry_mul_gen_correct_proj2 := proj2 reified_carry_mul_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification carry_mulmod reified_carry_mul_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_carry_mul_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_carry_mul_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_carry_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_square_gen
         SuchThat (is_reification_of reified_carry_square_gen carry_squaremod)
         As reified_carry_square_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_carry_square_gen_correct_proj1 := proj1 reified_carry_square_gen_correct.
  Local Definition reified_carry_square_gen_correct_proj2 := proj2 reified_carry_square_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification carry_squaremod reified_carry_square_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_carry_square_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_carry_square_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_carry_square_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_scmul_gen
         SuchThat (is_reification_of reified_carry_scmul_gen carry_scmulmod)
         As reified_carry_scmul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_carry_scmul_gen_correct_proj1 := proj1 reified_carry_scmul_gen_correct.
  Local Definition reified_carry_scmul_gen_correct_proj2 := proj2 reified_carry_scmul_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification carry_scmulmod reified_carry_scmul_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_carry_scmul_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_carry_scmul_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_carry_scmul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_gen
         SuchThat (is_reification_of reified_carry_gen carrymod)
         As reified_carry_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_carry_gen_correct_proj1 := proj1 reified_carry_gen_correct.
  Local Definition reified_carry_gen_correct_proj2 := proj2 reified_carry_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification carrymod reified_carry_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_carry_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_carry_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_carry_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_encode_gen
         SuchThat (is_reification_of reified_encode_gen encodemod)
         As reified_encode_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_encode_gen_correct_proj1 := proj1 reified_encode_gen_correct.
  Local Definition reified_encode_gen_correct_proj2 := proj2 reified_encode_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification encodemod reified_encode_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_encode_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_encode_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_encode_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_add_gen
         SuchThat (is_reification_of reified_add_gen addmod)
         As reified_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_add_gen_correct_proj1 := proj1 reified_add_gen_correct.
  Local Definition reified_add_gen_correct_proj2 := proj2 reified_add_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification addmod reified_add_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_add_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_add_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_add_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_sub_gen
         SuchThat (is_reification_of reified_sub_gen submod)
         As reified_sub_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_sub_gen_correct_proj1 := proj1 reified_sub_gen_correct.
  Local Definition reified_sub_gen_correct_proj2 := proj2 reified_sub_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification submod reified_sub_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_sub_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_sub_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_sub_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_opp_gen
         SuchThat (is_reification_of reified_opp_gen oppmod)
         As reified_opp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_opp_gen_correct_proj1 := proj1 reified_opp_gen_correct.
  Local Definition reified_opp_gen_correct_proj2 := proj2 reified_opp_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification oppmod reified_opp_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_opp_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_opp_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_opp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_add_gen
         SuchThat (is_reification_of reified_carry_add_gen carry_addmod)
         As reified_carry_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_carry_add_gen_correct_proj1 := proj1 reified_carry_add_gen_correct.
  Local Definition reified_carry_add_gen_correct_proj2 := proj2 reified_carry_add_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification carry_addmod reified_carry_add_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_carry_add_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_carry_add_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_carry_add_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_sub_gen
         SuchThat (is_reification_of reified_carry_sub_gen carry_submod)
         As reified_carry_sub_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_carry_sub_gen_correct_proj1 := proj1 reified_carry_sub_gen_correct.
  Local Definition reified_carry_sub_gen_correct_proj2 := proj2 reified_carry_sub_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification carry_submod reified_carry_sub_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_carry_sub_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_carry_sub_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_carry_sub_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_opp_gen
         SuchThat (is_reification_of reified_carry_opp_gen carry_oppmod)
         As reified_carry_opp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_carry_opp_gen_correct_proj1 := proj1 reified_carry_opp_gen_correct.
  Local Definition reified_carry_opp_gen_correct_proj2 := proj2 reified_carry_opp_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification carry_oppmod reified_carry_opp_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_carry_opp_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_carry_opp_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_carry_opp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_zero_gen
         SuchThat (is_reification_of reified_zero_gen zeromod)
         As reified_zero_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_zero_gen_correct_proj1 := proj1 reified_zero_gen_correct.
  Local Definition reified_zero_gen_correct_proj2 := proj2 reified_zero_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification zeromod reified_zero_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_zero_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_zero_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_zero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_one_gen
         SuchThat (is_reification_of reified_one_gen onemod)
         As reified_one_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_one_gen_correct_proj1 := proj1 reified_one_gen_correct.
  Local Definition reified_one_gen_correct_proj2 := proj2 reified_one_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification onemod reified_one_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_one_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_one_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_one_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_prime_gen
         SuchThat (is_reification_of reified_prime_gen primemod)
         As reified_prime_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_prime_gen_correct_proj1 := proj1 reified_prime_gen_correct.
  Local Definition reified_prime_gen_correct_proj2 := proj2 reified_prime_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification primemod reified_prime_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_prime_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_prime_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_prime_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_eval_gen
         SuchThat (is_reification_of reified_eval_gen evalmod)
         As reified_eval_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_eval_gen_correct_proj1 := proj1 reified_eval_gen_correct.
  Local Definition reified_eval_gen_correct_proj2 := proj2 reified_eval_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification evalmod reified_eval_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_eval_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_eval_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_eval_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_bytes_eval_gen
         SuchThat (is_reification_of reified_bytes_eval_gen bytes_evalmod)
         As reified_bytes_eval_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_bytes_eval_gen_correct_proj1 := proj1 reified_bytes_eval_gen_correct.
  Local Definition reified_bytes_eval_gen_correct_proj2 := proj2 reified_bytes_eval_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification bytes_evalmod reified_bytes_eval_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_bytes_eval_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_bytes_eval_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_bytes_eval_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_to_bytes_gen
         SuchThat (is_reification_of reified_to_bytes_gen freeze_to_bytesmod)
         As reified_to_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_to_bytes_gen_correct_proj1 := proj1 reified_to_bytes_gen_correct.
  Local Definition reified_to_bytes_gen_correct_proj2 := proj2 reified_to_bytes_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification freeze_to_bytesmod reified_to_bytes_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_to_bytes_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_to_bytes_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_to_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_bytes_gen
         SuchThat (is_reification_of reified_from_bytes_gen from_bytesmod)
         As reified_from_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_from_bytes_gen_correct_proj1 := proj1 reified_from_bytes_gen_correct.
  Local Definition reified_from_bytes_gen_correct_proj2 := proj2 reified_from_bytes_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification from_bytesmod reified_from_bytes_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_from_bytes_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_from_bytes_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_from_bytes_gen. (* needed for making [autorewrite] not take a very long time *)
End UnsaturatedSolinas.
