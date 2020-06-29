Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Local Open Scope Z_scope.

Module Z.
  Lemma positive_is_nonzero : forall x, x > 0 -> x <> 0.
  Proof. intros; lia. Qed.
  Hint Resolve positive_is_nonzero : zarith.

  Lemma le_lt_trans n m p : n <= m -> m < p -> n < p.
  Proof. lia. Qed.

  Lemma le_fold_right_max : forall low l x, (forall y, List.In y l -> low <= y) ->
    List.In x l -> x <= List.fold_right Z.max low l.
  Proof.
    induction l as [|a l IHl]; intros ? lower_bound In_list; [cbv [List.In] in *; intuition | ].
    simpl.
    destruct (List.in_inv In_list); subst.
    + apply Z.le_max_l.
    + etransitivity.
      - apply IHl; auto; intuition auto with datatypes.
      - apply Z.le_max_r.
  Qed.

  Lemma le_fold_right_max_initial : forall low l, low <= List.fold_right Z.max low l.
  Proof.
    induction l as [|a l IHl]; intros; try reflexivity.
    etransitivity; [ apply IHl | apply Z.le_max_r ].
  Qed.

  Lemma add_compare_mono_r: forall n m p, (n + p ?= m + p) = (n ?= m).
  Proof.
    intros n m p.
    rewrite <-!(Z.add_comm p).
    apply Z.add_compare_mono_l.
  Qed.

  Lemma leb_add_same x y : (x <=? y + x) = (0 <=? y).
  Proof. destruct (x <=? y + x) eqn:?, (0 <=? y) eqn:?; Z.ltb_to_lt; try reflexivity; lia. Qed.
  Hint Rewrite leb_add_same : zsimplify.

  Lemma ltb_add_same x y : (x <? y + x) = (0 <? y).
  Proof. destruct (x <? y + x) eqn:?, (0 <? y) eqn:?; Z.ltb_to_lt; try reflexivity; lia. Qed.
  Hint Rewrite ltb_add_same : zsimplify.

  Lemma geb_add_same x y : (x >=? y + x) = (0 >=? y).
  Proof. destruct (x >=? y + x) eqn:?, (0 >=? y) eqn:?; Z.ltb_to_lt; try reflexivity; lia. Qed.
  Hint Rewrite geb_add_same : zsimplify.

  Lemma gtb_add_same x y : (x >? y + x) = (0 >? y).
  Proof. destruct (x >? y + x) eqn:?, (0 >? y) eqn:?; Z.ltb_to_lt; try reflexivity; lia. Qed.
  Hint Rewrite gtb_add_same : zsimplify.

  Lemma sub_pos_bound a b X : 0 <= a < X -> 0 <= b < X -> -X < a - b < X.
  Proof. lia. Qed.

  Lemma le_sub_1_iff x y : x <= y - 1 <-> x < y.
  Proof. lia. Qed.

  Lemma le_add_1_iff x y : x + 1 <= y <-> x < y.
  Proof. lia. Qed.
End Z.