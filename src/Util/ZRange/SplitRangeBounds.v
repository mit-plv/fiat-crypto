Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Module ZRange.
  Import Operations.ZRange.
  Lemma split_range_at_0_covers r
        (Hr : goodb r = true)
    : covers
        match split_range_at_0 r with
        | (Some n, Some z, Some p) => [n; p; z]
        | (x, y, z)
          => let f o := match o with Some v => [v] | None => [] end in
             List.flat_map f [x; y; z]
        end r.
  Proof.
    intros z Hz.
    exists (let '(a, b, c) := split_range_at_0 r in
            let extract o := match o with Some v => v | None => r[0~>0]%zrange end in
            if z <? 0 then extract a else if z =? 0 then extract b else extract c).
    destruct r as [l u];
      repeat first [ progress cbv [andb orb is_bounded_by_bool goodb] in *
                   | progress cbn in *
                   | break_innermost_match_step
                   | congruence
                   | break_innermost_match_hyps_step
                   | progress Z.ltb_to_lt
                   | lia ].
    all: split; [ | let rec tac := first [ left; reflexivity | right; tac ] in tac ].
    all: Z.ltb_to_lt.
    all: lia.
  Qed.

  Lemma is_bounded_by_fold_left_union (f : Z -> Z) (fr : zrange -> zrange) z r r' rs
        (Hf : is_bounded_by_bool (f z) (fr r') = true)
        (Hr' : is_bounded_by_bool (f z) r = true \/ In r' rs)
    : is_bounded_by_bool (f z) (fold_left (fun x y : zrange => union x (fr y)) rs r) = true.
  Proof.
    revert dependent r; induction rs as [|r0 rs IH]; cbn -[union] in *; intros;
      [ now destruct Hr' | ].
    apply IH; clear IH.
    destruct_head'_or; subst; first [ right; assumption | left ].
    all: now (apply ZRange.is_bounded_by_bool_union_l + apply ZRange.is_bounded_by_bool_union_r).
  Qed.

  Lemma nary_is_bounded_by_under_args2_union {n f fr z rs r}
        (Hr : covers rs r)
        (Hf : @nary_is_bounded_by (S n) f fr)
        (Hzr : is_bounded_by_bool z r = true)
    : match List.map fr rs with
      | nil => False
      | r0 :: rs
        => nary_is_bounded_by (f z) (List.fold_left (under_args2 union) rs r0)
      end.
  Proof.
    specialize (Hr _ Hzr).
    destruct Hr as [r' [Hr Hr']].
    destruct rs as [|r0 rs]; [ exfalso; assumption | ].
    cbn [List.map List.In] in *.
    cbn [nary_is_bounded_by] in *.
    specialize (Hf _ _ Hr).
    rewrite fold_left_map.
    induction n as [|n IHn].
    { cbn [nary_T nary_is_bounded_by under_args2] in *.
      eapply is_bounded_by_fold_left_union;
        [ | destruct Hr'; [ left | right; eassumption ]; subst ]; assumption. }
    { cbn [under_args2 nary_is_bounded_by nary_T] in *; intros.
      rewrite_fold_left_fun_apply.
      apply (fun z0 r2 => IHn (fun z => f z z0) (fun r => fr r r2)); clear IHn.
      auto. }
  Qed.

  Lemma apply_to_n_split_range_is_bounded_by {n f fr}
        (Hf : @nary_is_bounded_by n f fr)
    : @nary_is_bounded_by n f (apply_to_n_split_range fr).
  Proof.
    induction n as [|n IHn]; [ assumption | ].
    cbn [nary_is_bounded_by apply_to_n_split_range].
    intros z r Hzr.
    apply IHn; clear IHn.
    pose proof (split_range_at_0_covers r ltac:(eapply ZRange.goodb_of_is_bounded_by_bool; eassumption)) as Hcover.
    cbv [apply_to_split_range_under_args].
    break_innermost_match;
      pose proof (nary_is_bounded_by_under_args2_union Hcover Hf Hzr) as H.
    all: first [ exact H | exfalso; assumption ].
  Qed.
End ZRange.
