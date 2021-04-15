Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Local Open Scope Z_scope.

Module ZRange.
  Lemma is_bounded_by_bool_split_bounds_pos x r m (Hm : 0 < m)
  : is_bounded_by_bool x r = true
    -> andb (is_bounded_by_bool (x mod m) (fst (Operations.ZRange.split_bounds_pos r m)))
            (is_bounded_by_bool (x / m) (snd (Operations.ZRange.split_bounds_pos r m))) = true.
  Proof.
    cbv [is_bounded_by_bool Operations.ZRange.split_bounds_pos andb].
    repeat first [ progress intros
                 | break_innermost_match_step
                 | break_innermost_match_hyps_step
                 | progress subst
                 | progress cbn [fst snd lower upper] in *
                 | reflexivity
                 | discriminate
                 | lia
                 | progress Z.ltb_to_lt
                 | progress Z.peel_le
                 | match goal with
                   | [ r : zrange |- _ ] => let l := fresh "l" in let u := fresh "u" in destruct r as [l u]
                   | [ H : (?x < ?m)%Z, H' : (?m * ?q + _ <= ?x)%Z |- _ ]
                     => assert (q < 0 \/ q = 0 \/ 0 < q)%Z by nia; destruct_head'_or;
                        [ assert (m * q < 0)%Z by nia; nia | progress subst | assert (0 < m * q)%Z by nia; nia ]
                   end
                 | progress autorewrite with zsimplify_const in *
                 | progress Z.div_mod_to_quot_rem
                 | nia ].
  Qed.

  Lemma is_bounded_by_bool_fst_split_bounds_pos x r m (Hm : 0 < m)
    : is_bounded_by_bool x r = true
      -> (is_bounded_by_bool (x mod m) (fst (Operations.ZRange.split_bounds_pos r m))) = true.
  Proof. intro H; pose proof (@is_bounded_by_bool_split_bounds_pos x r m Hm H); Bool.split_andb; assumption. Qed.

  Lemma is_bounded_by_bool_snd_split_bounds_pos x r m (Hm : 0 < m)
    : is_bounded_by_bool x r = true
      -> (is_bounded_by_bool (x / m) (snd (Operations.ZRange.split_bounds_pos r m))) = true.
  Proof. intro H; pose proof (@is_bounded_by_bool_split_bounds_pos x r m Hm H); Bool.split_andb; assumption. Qed.

  Lemma is_bounded_by_bool_split_bounds x r m
    : is_bounded_by_bool x r = true
      -> andb (is_bounded_by_bool (x mod m) (fst (Operations.ZRange.split_bounds r m)))
              (is_bounded_by_bool (x / m) (snd (Operations.ZRange.split_bounds r m))) = true.
  Proof.
    intro; cbv [ZRange.split_bounds]; eta_expand; break_match; cbn [fst snd] in *.
    all: Z.ltb_to_lt.
    all: Z.replace_all_neg_with_pos.
    - now apply is_bounded_by_bool_split_bounds_pos.
    - autorewrite with zsimplify_const. now rewrite 1?Bool.andb_comm.
    - rewrite Z.div_opp_r, Z.mod_opp_r, ZRange.is_bounded_by_bool_opp.
      now apply is_bounded_by_bool_split_bounds_pos; [lia|rewrite ZRange.is_bounded_by_bool_opp].
  Qed.

  Lemma is_bounded_by_bool_split_bounds_and x r m
    : is_bounded_by_bool x r = true
      -> and (is_bounded_by_bool (x mod m) (fst (Operations.ZRange.split_bounds r m)) = true)
             (is_bounded_by_bool (x / m) (snd (Operations.ZRange.split_bounds r m)) = true).
  Proof.
    intro H; pose proof (@is_bounded_by_bool_split_bounds x r m H).
    Bool.split_andb; split; assumption.
  Qed.
End ZRange.
