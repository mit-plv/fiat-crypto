Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  Local Ltac fin_div_ltz :=
    intros; cbv [Z.ltz]; Z.div_mod_to_quot_rem; break_innermost_match; Z.ltb_to_lt; try nia.

  Lemma ltz_mod_pow2_small x y z :
    0 < z ->
    (Z.ltz x y) mod (2 ^ z) = Z.ltz x y.
  Proof.
    cbv [Z.ltz]; break_match; intros; Z.ltb_to_lt;
      apply Z.mod_small; auto with zarith.
  Qed.

  Lemma add_div_ltz_1 s x y :
    0 <= x < s
    -> 0 <= y < s
    -> (x + y) / s = Z.ltz ((x + y) mod s) x.
  Proof. fin_div_ltz. Qed.

  Lemma add_div_ltz_2 s x y :
    0 <= x < s
    -> 0 <= y < s
    -> (x + y) / s = Z.ltz ((x + y) mod s) y.
  Proof. fin_div_ltz. Qed.

  Lemma add_add_div_ltz_2 s c x y :
    0 <= c < s
    -> 0 <= x < s
    -> 0 <= y < s
    -> (c + x + y) / s =
       Z.ltz ((c + x) mod s) x + Z.ltz ((c + x + y) mod s) y.
  Proof.
    intros. rewrite <-(Z.add_mod_idemp_l (c + x)) by lia.
    rewrite <-!add_div_ltz_2 by auto with zarith.
    fin_div_ltz.
  Qed.

  Lemma sub_div_ltz s x y :
    0 <= x < s
    -> 0 <= y < s
    -> - ((x - y) / s) = Z.ltz x ((x - y) mod s).
  Proof. fin_div_ltz. Qed.

  Lemma sub_sub_div_ltz s x y c :
    0 <= c < s
    -> 0 <= x < s
    -> 0 <= y < s
    -> - ((x - y - c) / s) =
       Z.ltz x ((x - y) mod s) + Z.ltz ((x - y) mod s) ((x - y - c) mod s).
  Proof.
    intros. rewrite (Z.sub_mod_l (x-y)).
    rewrite <-!sub_div_ltz by auto with zarith.
    fin_div_ltz.
  Qed.
End Z.
