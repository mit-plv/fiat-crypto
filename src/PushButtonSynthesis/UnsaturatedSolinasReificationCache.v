(** * Push-Button Synthesis of Unsaturated Solinas: Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Arithmetic.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export UnsaturatedSolinas.
  Definition zeromod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 0.
  Definition onemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 1.
  Definition primemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n (s - Associational.eval c).

  (**
<<
#!/usr/bin/env python

indent = '  '

print((indent + '(' + r'''**
<<
%s
>>
*''' + ')\n') % open(__file__, 'r').read())

for i in ('carry_mul', 'carry_square', 'carry_scmul', 'carry', 'encode', 'add', 'sub', 'opp', 'zero', 'one', 'prime'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')

for (op, opmod) in (('to_bytes', 'freeze_to_bytesmod'), ('from_bytes', 'from_bytesmod')):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %s)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %s (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, op, op, opmod, op, opmod, op, op, op, op)).replace('\n', '\n%s' % indent) + '\n')

>>
*)

  Derive reified_carry_mul_gen
         SuchThat (is_reification_of reified_carry_mul_gen carry_mulmod)
         As reified_carry_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carry_mulmod (proj1 reified_carry_mul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_mul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_square_gen
         SuchThat (is_reification_of reified_carry_square_gen carry_squaremod)
         As reified_carry_square_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carry_squaremod (proj1 reified_carry_square_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_square_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_square_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_square_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_scmul_gen
         SuchThat (is_reification_of reified_carry_scmul_gen carry_scmulmod)
         As reified_carry_scmul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carry_scmulmod (proj1 reified_carry_scmul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_scmul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_scmul_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_scmul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_gen
         SuchThat (is_reification_of reified_carry_gen carrymod)
         As reified_carry_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carrymod (proj1 reified_carry_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_encode_gen
         SuchThat (is_reification_of reified_encode_gen encodemod)
         As reified_encode_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification encodemod (proj1 reified_encode_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_encode_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_encode_gen_correct) : interp_gen_cache.
  Local Opaque reified_encode_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_add_gen
         SuchThat (is_reification_of reified_add_gen addmod)
         As reified_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification addmod (proj1 reified_add_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_add_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_add_gen_correct) : interp_gen_cache.
  Local Opaque reified_add_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_sub_gen
         SuchThat (is_reification_of reified_sub_gen submod)
         As reified_sub_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification submod (proj1 reified_sub_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_sub_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_sub_gen_correct) : interp_gen_cache.
  Local Opaque reified_sub_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_opp_gen
         SuchThat (is_reification_of reified_opp_gen oppmod)
         As reified_opp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification oppmod (proj1 reified_opp_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_opp_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_opp_gen_correct) : interp_gen_cache.
  Local Opaque reified_opp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_zero_gen
         SuchThat (is_reification_of reified_zero_gen zeromod)
         As reified_zero_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification zeromod (proj1 reified_zero_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_zero_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_zero_gen_correct) : interp_gen_cache.
  Local Opaque reified_zero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_one_gen
         SuchThat (is_reification_of reified_one_gen onemod)
         As reified_one_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification onemod (proj1 reified_one_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_one_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_one_gen_correct) : interp_gen_cache.
  Local Opaque reified_one_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_prime_gen
         SuchThat (is_reification_of reified_prime_gen primemod)
         As reified_prime_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification primemod (proj1 reified_prime_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_prime_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_prime_gen_correct) : interp_gen_cache.
  Local Opaque reified_prime_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_to_bytes_gen
         SuchThat (is_reification_of reified_to_bytes_gen freeze_to_bytesmod)
         As reified_to_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification freeze_to_bytesmod (proj1 reified_to_bytes_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_to_bytes_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_to_bytes_gen_correct) : interp_gen_cache.
  Local Opaque reified_to_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_bytes_gen
         SuchThat (is_reification_of reified_from_bytes_gen from_bytesmod)
         As reified_from_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification from_bytesmod (proj1 reified_from_bytes_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_from_bytes_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_from_bytes_gen_correct) : interp_gen_cache.
  Local Opaque reified_from_bytes_gen. (* needed for making [autorewrite] not take a very long time *)
End UnsaturatedSolinas.
