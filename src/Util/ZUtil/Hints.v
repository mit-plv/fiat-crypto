(** * Hint Databases with lemmas about ℤ from the standard library *)
Require Import Coq.ZArith.ZArith.
Require Export Crypto.Util.ZUtil.Hints.Core.
Require Export Crypto.Util.ZUtil.Hints.ZArith.
Require Export Crypto.Util.ZUtil.Hints.Ztestbit.
Require Export Crypto.Util.ZUtil.Hints.PullPush.
Require Export Crypto.Util.ZUtil.ZSimplify.Core.

Global Hint Resolve -> Z.log2_lt_pow2 Z.log2_le_pow2 : concl_log2.
Global Hint Resolve <- Z.log2_lt_pow2 Z.log2_le_pow2 : hyp_log2.

(** For the occasional lemma that can remove the use of [Z.div] *)
Hint Rewrite Z.div_small_iff using zutil_arith : zstrip_div.
