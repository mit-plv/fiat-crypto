(** * Push-Button Synthesis of Word-By-Word Montgomery: Reification Cache *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Import
  Language.Wf.Compilers
  Language.Compilers
  Language.API.Compilers.
Import Compilers.API.

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export WordByWordMontgomery.
  Import WordByWordMontgomery.WordByWordMontgomery.

  Definition zeromod bitwidth n m m' := encodemod bitwidth n m m' 0.
  Definition onemod bitwidth n m m' := encodemod bitwidth n m m' 1.
  Definition evalmod bitwidth n := @eval bitwidth n.
  Definition bytes_evalmod s := @eval 8 (bytes_n s).

  (* we would do something faster, but it generally breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
  Local Ltac precache_reify_faster _ :=
    split;
    [ let marker := fresh "marker" in
      pose I as marker;
      intros;
      let LHS := lazymatch goal with |- ?LHS = _ => LHS end in
      let reified_op_gen := lazymatch LHS with context[expr.Interp _ ?reified_op_gen] => reified_op_gen end in
      subst reified_op_gen;
      etransitivity;
      [
      | let opmod := match goal with |- _ = ?RHS => head RHS end in
        cbv [opmod]; solve [ eauto with reify_cache_gen nocore ] ];
      repeat lazymatch goal with
             | [ H : _ |- _ ] => tryif constr_eq H marker then fail else revert H
             end;
      clear marker
    | ].
  Local Ltac cache_reify_faster_2arg _ :=
    precache_reify_faster ();
    [ lazymatch goal with
      | [ |- forall bw n m m' v, ?interp ?ev bw n m m' v = ?interp' ?reified_mul_gen bw n m m' (@?A bw n m m' v) (@?B bw n m m' v) ]
        => let rv := constr:(fun F bw n m m' v => (F bw n m m' (A bw n m m' v) (B bw n m m' v)):list Z) in
           intros;
           instantiate (1:=ltac:(let r := Reify rv in
                                 refine (r @ reified_mul_gen)%Expr))
      end;
      reflexivity
    | prove_Wf () ].
  Local Ltac cache_reify_faster_1arg _ :=
    precache_reify_faster ();
    [ lazymatch goal with
      | [ |- forall bw n m m', ?interp ?ev bw n m m' = ?interp' ?reified_op_gen bw n m m' (@?A bw n m m') ]
        => let rv := constr:(fun F bw n m m' => (F bw n m m' (A bw n m m')):list Z) in
           intros;
           instantiate (1:=ltac:(let r := Reify rv in
                                 refine (r @ reified_op_gen)%Expr))
      end;
      reflexivity
    | prove_Wf () ].

  (**
<<
#!/usr/bin/env python

indent = '  '

print((indent + '(' + r'''**
<<
%s
>>
*''' + ')\n') % open(__file__, 'r').read())

for i in ('mul', 'add', 'sub', 'opp', 'to_bytes', 'from_bytes', 'nonzero', 'eval', 'bytes_eval'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')

for i in ('square', 'encode', 'from_montgomery', 'to_montgomery'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof.
  Time cache_reify ().
  (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
  (* Time cache_reify_faster_2arg (). *)
Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')


for i in ('zero', 'one'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof.
  (* Time cache_reify (). *)
  (* we do something faster *)
  Time cache_reify_faster_1arg ().
Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')

>>
*)

  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)

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

  Derive reified_to_bytes_gen
         SuchThat (is_reification_of reified_to_bytes_gen to_bytesmod)
         As reified_to_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification to_bytesmod (proj1 reified_to_bytes_gen_correct) : reify_cache_gen.
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

  Derive reified_nonzero_gen
         SuchThat (is_reification_of reified_nonzero_gen nonzeromod)
         As reified_nonzero_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification nonzeromod (proj1 reified_nonzero_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_nonzero_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_nonzero_gen_correct) : interp_gen_cache.
  Local Opaque reified_nonzero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_eval_gen
         SuchThat (is_reification_of reified_eval_gen evalmod)
         As reified_eval_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification evalmod (proj1 reified_eval_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_eval_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_eval_gen_correct) : interp_gen_cache.
  Local Opaque reified_eval_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_bytes_eval_gen
         SuchThat (is_reification_of reified_bytes_eval_gen bytes_evalmod)
         As reified_bytes_eval_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification bytes_evalmod (proj1 reified_bytes_eval_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_bytes_eval_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_bytes_eval_gen_correct) : interp_gen_cache.
  Local Opaque reified_bytes_eval_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_square_gen
         SuchThat (is_reification_of reified_square_gen squaremod)
         As reified_square_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification squaremod (proj1 reified_square_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_square_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_square_gen_correct) : interp_gen_cache.
  Local Opaque reified_square_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_encode_gen
         SuchThat (is_reification_of reified_encode_gen encodemod)
         As reified_encode_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification encodemod (proj1 reified_encode_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_encode_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_encode_gen_correct) : interp_gen_cache.
  Local Opaque reified_encode_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_montgomery_gen
         SuchThat (is_reification_of reified_from_montgomery_gen from_montgomerymod)
         As reified_from_montgomery_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification from_montgomerymod (proj1 reified_from_montgomery_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_from_montgomery_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_from_montgomery_gen_correct) : interp_gen_cache.
  Local Opaque reified_from_montgomery_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_to_montgomery_gen
         SuchThat (is_reification_of reified_to_montgomery_gen to_montgomerymod)
         As reified_to_montgomery_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification to_montgomerymod (proj1 reified_to_montgomery_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_to_montgomery_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_to_montgomery_gen_correct) : interp_gen_cache.
  Local Opaque reified_to_montgomery_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_zero_gen
         SuchThat (is_reification_of reified_zero_gen zeromod)
         As reified_zero_gen_correct.
  Proof.
    (* Time cache_reify (). *)
    (* we do something faster *)
    Time cache_reify_faster_1arg ().
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification zeromod (proj1 reified_zero_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_zero_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_zero_gen_correct) : interp_gen_cache.
  Local Opaque reified_zero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_one_gen
         SuchThat (is_reification_of reified_one_gen onemod)
         As reified_one_gen_correct.
  Proof.
    Time cache_reify ().
    (* Note that the following speed up breaks compilation of binaries /benjamin *)
    (* we do something faster *)
    (* Time cache_reify_faster_1arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification onemod (proj1 reified_one_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_one_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_one_gen_correct) : interp_gen_cache.
  Local Opaque reified_one_gen. (* needed for making [autorewrite] not take a very long time *)
End WordByWordMontgomery.
