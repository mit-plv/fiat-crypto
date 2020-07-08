Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Bvector.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Stabilization.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Create HintDb bitlist discriminated.

Module Import Bitlist.
  Local Set Primitive Projections.
  Record t := { internal_bitlist : list bool ; test_signbit : bool }.
  Definition signbit (v : t) : Z := if test_signbit v then -1 else 0.
  Definition sgn (v : t) : Z
    := if test_signbit v then -1 else if List.existsb (fun b => b) (internal_bitlist v) then 1 else 0.
  Definition testbit (v : t) (n : Z) : bool
    := if n <? 0
       then false
       else List.nth_default (Z.testbit (signbit v) n) (internal_bitlist v) (Z.to_nat n).
  Definition bitcount (v : t) : nat := List.length (internal_bitlist v).
  Hint Transparent bitcount : rewrite bitlist.
  Definition bitlist (v : t) (len : nat) : list bool
    := firstn len (internal_bitlist v) ++ repeat (Z.testbit (signbit v) 0) (len - bitcount v).
  Notation bitlist_default v := (bitlist v (bitcount v)) (only parsing).
  Definition to_Z (v : t) : Z
    := List.fold_right
         (fun '(n, b) a => (if b : bool then Z.setbit else Z.clearbit) a (Z.of_nat n))
         (signbit v)
         (List.enumerate (bitlist_default v)).
  Definition of_Z_len (v : Z) (len : Z) : t
    := Build_t
         (List.map (fun n => Z.testbit v (Z.of_nat n)) (seq 0 (Z.to_nat len)))
         (v <? 0).
  Definition of_Z (v : Z) : t := of_Z_len v (Z.stabilization_time v + 1).

  Lemma length_bitlist v len : length (bitlist v len) = len.
  Proof.
    cbv [bitlist bitcount]; autorewrite with distr_length.
    apply Nat.min_case_strong; try lia.
  Qed.
  Hint Rewrite length_bitlist : distr_length bitlist.

  Lemma bitcount_of_Z_len v len : bitcount (of_Z_len v len) = Z.to_nat len.
  Proof. cbv [bitcount of_Z_len internal_bitlist]; now autorewrite with distr_length. Qed.
  Hint Rewrite bitcount_of_Z_len : distr_length bitlist.

  Lemma bitcount_of_Z v : bitcount (of_Z v) = Z.to_nat (Z.stabilization_time v + 1).
  Proof. apply bitcount_of_Z_len. Qed.
  Hint Rewrite bitcount_of_Z : distr_length bitlist.

  Lemma enumerate_bitlist_default_eq v
    : enumerate (bitlist_default v) = List.combine (List.seq 0 (bitcount v)) (internal_bitlist v).
  Proof.
    cbv [enumerate]; autorewrite with distr_length.
    cbv [bitlist bitcount]; autorewrite with natsimplify; cbn [repeat].
    now rewrite List.app_nil_r, List.firstn_all.
  Qed.

  Lemma testbit_to_Z v n : Z.testbit (to_Z v) n = testbit v n.
  Proof.
    cbv [to_Z testbit].
    destruct (n <? 0) eqn:?; Z.ltb_to_lt.
    { now rewrite Z.testbit_neg_r by assumption. }
    rewrite enumerate_bitlist_default_eq.
    cbv [bitcount].
    set (offset := 0%nat) at 1.
    change 0 with (Z.of_nat offset) in * |- .
    replace n with (n - Z.of_nat offset) at 3 by lia.
    clearbody offset; revert dependent offset.
    revert dependent n.
    induction (internal_bitlist v) as [|x xs IHxs];
      cbn [length seq List.combine fold_right];
      intros; [ now rewrite nth_default_nil | ].
    specialize (fun n => IHxs n (S offset)).
    assert (H' : n = Z.of_nat offset \/ Z.of_nat offset < n) by lia.
    destruct H'; subst.
    { break_innermost_match;
        first [ rewrite Z.setbit_eq by lia | rewrite Z.clearbit_eq by lia ].
      all: autorewrite with zsimplify; reflexivity. }
    { lazymatch goal with
      | [ |- Z.testbit (?f ?x ?y) ?n = _ ] => transitivity (Z.testbit x n)
      end.
      { now break_innermost_match;
          first [ rewrite Z.setbit_neq by lia | rewrite Z.clearbit_neq by lia ]. }
      rewrite IHxs by lia.
      replace (Z.to_nat (n - Z.of_nat (S offset))) with (pred (Z.to_nat (n - Z.of_nat offset)))
        by (* could just use [lia], but only in Coq >= 8.11 *)
          (now rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.sub_add_distr, Z.sub_1_r, Z2Nat.inj_pred).
      destruct (Z.to_nat (n - Z.of_nat offset)) eqn:H'; [ exfalso | ].
      { (* could just use [lia], but only in Coq >= 8.11 *)
        apply (f_equal Z.of_nat) in H'; rewrite Z2Nat.id in H' by lia.
        lia. }
      rewrite nth_default_cons_S; reflexivity. }
  Qed.
  Hint Rewrite testbit_to_Z : bitlist Ztestbit.

  Lemma testbit_of_Z_len v n len
    : testbit (of_Z_len v len) n = if n <? len then Z.testbit v n else Z.testbit (if v <? 0 then -1 else 0) n.
  Proof.
    cbv [testbit of_Z_len signbit test_signbit internal_bitlist].
    cbv [nth_default].
    rewrite nth_error_map, nth_error_seq.
    break_innermost_match; Z.ltb_to_lt; try solve [ exfalso; lia ].
    all: repeat first [ reflexivity
                      | congruence
                      | progress cbn [option_map Nat.add] in *
                      | progress inversion_option
                      | rewrite Z.testbit_neg_r by lia
                      | progress rewrite Z2Nat.id in * by lia
                      | fail (* the rest are only needed in Coq < 8.11 *)
                      | rewrite Z.bits_m1 by lia
                      | lia
                      | match goal with
                        | [ H : ?x < 0, H' : context[Z.to_nat ?x] |- _ ]
                          => replace (Z.to_nat x) with 0%nat in * by now destruct n
                        | [ H : (_ < _)%nat |- _ ]
                          => apply inj_lt in H; rewrite ?Z2Nat.id in H by lia
                        | [ H : context[Z.of_nat (Z.to_nat ?x)] |- _ ]
                          => let H' := fresh in
                             assert (H' : x < 0 \/ 0 <= x) by lia;
                             destruct H';
                             [ replace (Z.to_nat x) with 0%nat in * by now destruct x
                             | rewrite Z2Nat.id in H by assumption ]
                        end
                      | progress zify ].
  Qed.
  Hint Rewrite testbit_of_Z_len : bitlist Ztestbit.

  Lemma testbit_of_Z v n : testbit (of_Z v) n = Z.testbit v n.
  Proof.
    cbv [of_Z]; rewrite testbit_of_Z_len.
    destruct (stabilization_time v) as [b H].
    pose proof (H n) as H'.
    break_innermost_match_step; Z.ltb_to_lt; [ reflexivity | ].
    rewrite H' by lia.
    pose proof (Z.stabilization_time_nonneg v).
    break_innermost_match_step; Z.ltb_to_lt;
      [ destruct (proj1 (Z.bits_iff_neg_ex v) ltac:(lia)) as [k H'']
      | pose proof (proj2 (Z.bits_iff_neg_ex v)) as H'' ].
    { rewrite Z.bits_m1 by lia.
      specialize (H (Z.max (Z.stabilization_time v + 1) (k + 1)) ltac:(lia)).
      rewrite H'' in H by lia; congruence. }
    { rewrite Z.testbit_0_l.
      destruct b; [ cut (v < 0); [ lia | ] | reflexivity ].
      apply H''; eexists; eassumption. }
  Qed.
  Hint Rewrite testbit_of_Z : bitlist Ztestbit.

  Lemma path_t (v1 v2 : t) : internal_bitlist v1 = internal_bitlist v2 -> test_signbit v1 = test_signbit v2 -> v1 = v2.
  Proof. destruct v1, v2; cbn; intros; subst; reflexivity. Qed.

  Definition bitwise (f : bool -> bool -> bool) (v1 v2 : t) : t
    := let len := Nat.max (bitcount v1) (bitcount v2) in
       Build_t (List.map (fun '(a, b) => f a b) (List.combine (bitlist v1 len) (bitlist v2 len)))
               (f (test_signbit v1) (test_signbit v2)).

  Lemma testbit_signbit v n : 0 <= n -> Z.testbit (signbit v) n = test_signbit v.
  Proof.
    cbv [signbit]; break_innermost_match; intro.
    { now rewrite Z.bits_m1. }
    { now rewrite Z.testbit_0_l. }
  Qed.
  Hint Rewrite testbit_signbit : bitlist Ztestbit.

  Lemma testbit_bitwise f v1 v2 n : testbit (bitwise f v1 v2) n = if n <? 0 then false else f (testbit v1 n) (testbit v2 n).
  Proof.
    cbv [testbit bitwise nth_default];
      cbn [internal_bitlist test_signbit].
    rewrite nth_error_map, nth_error_combine.
    break_innermost_match_step; Z.ltb_to_lt; [ reflexivity | ].
    rewrite testbit_signbit by lia; cbn [test_signbit].
    apply Nat.max_case_strong; intro.
    all: cbv [bitlist bitcount] in *;
      autorewrite with natsimplify;
      cbn [List.repeat]; rewrite List.app_nil_r, !firstn_all2, nth_error_app, nth_error_repeat_alt, testbit_signbit by lia.
    all: cbv [option_map].
    all: break_innermost_match.
    all: repeat first [ reflexivity
                      | rewrite testbit_signbit by lia
                      | progress inversion_option
                      | match goal with
                        | [ H : nth_error _ _ = None |- _ ] => apply nth_error_error_length in H; exfalso; lia
                        | [ H : context[nth_error _ _] |- _ ] => rewrite nth_error_length_error in H by lia
                        end ].
  Qed.
  Hint Rewrite testbit_bitwise : bitlist Ztestbit.
End Bitlist.
Hint Rewrite length_bitlist bitcount_of_Z_len bitcount_of_Z : distr_length bitlist.
Hint Rewrite testbit_to_Z testbit_of_Z_len testbit_of_Z testbit_bitwise testbit_signbit : bitlist Ztestbit.
Hint Transparent bitcount : rewrite.

Module Z2Bitlist.
  Lemma id (v : Z) : to_Z (of_Z v) = v.
  Proof. now apply Z.bits_inj; intro; autorewrite with bitlist. Qed.
End Z2Bitlist.

Definition bitwise (f : bool -> bool -> bool) (v1 v2 : Z) : Z
  := to_Z (Bitlist.bitwise f (of_Z v1) (of_Z v2)).

Lemma testbit_bitwise f v1 v2 n : Z.testbit (bitwise f v1 v2) n = if n <? 0 then false else f (Z.testbit v1 n) (Z.testbit v2 n).
Proof. now cbv [bitwise]; autorewrite with bitlist. Qed.
Hint Rewrite testbit_bitwise : Ztestbit.

Lemma bitwise_land v1 v2 : bitwise andb v1 v2 = Z.land v1 v2.
Proof.
  apply Z.bits_inj; intro; rewrite Z.land_spec, testbit_bitwise.
  break_innermost_match; Z.ltb_to_lt; [ | reflexivity ].
  now rewrite !Z.testbit_neg_r by lia.
Qed.

Lemma bitwise_lor v1 v2 : bitwise orb v1 v2 = Z.lor v1 v2.
Proof.
  apply Z.bits_inj; intro; rewrite Z.lor_spec, testbit_bitwise.
  break_innermost_match; Z.ltb_to_lt; [ | reflexivity ].
  now rewrite !Z.testbit_neg_r by lia.
Qed.

Lemma bitwise_lxor v1 v2 : bitwise xorb v1 v2 = Z.lxor v1 v2.
Proof.
  apply Z.bits_inj; intro; rewrite Z.lxor_spec, testbit_bitwise.
  break_innermost_match; Z.ltb_to_lt; [ | reflexivity ].
  now rewrite !Z.testbit_neg_r by lia.
Qed.
