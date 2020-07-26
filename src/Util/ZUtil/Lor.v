Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma lor_m1'_r x : Z.lor x (-1) = -1.
  Proof. apply Z.lor_m1_r. Qed.
  Hint Rewrite lor_m1'_r : zsimplify_const zsimplify zsimplify_fast.

  Lemma lor_m1'_l x : Z.lor (-1) x = -1.
  Proof. apply Z.lor_m1_l. Qed.
  Hint Rewrite lor_m1'_l : zsimplify_const zsimplify zsimplify_fast.
End Z.
