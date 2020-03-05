Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Testbit.

Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma lor_m1'_r x : Z.lor x (-1) = -1.
  Proof. apply Z.lor_m1_r. Qed.
  Hint Rewrite lor_m1'_r : zsimplify_const zsimplify zsimplify_fast.

  Lemma lor_m1'_l x : Z.lor (-1) x = -1.
  Proof. apply Z.lor_m1_l. Qed.
  Hint Rewrite lor_m1'_l : zsimplify_const zsimplify zsimplify_fast.

  Lemma lor_add a b (Hand : a &' b = 0) : a |' b = a + b.
  Proof. rewrite <- Z.lxor_lor, Z.add_nocarry_lxor by assumption; reflexivity. Qed.

  Lemma lor_small_neg a b
        (Ha : - 2^b <= a < 0)
        (Hb : 0 < b) :
    2^b |' a = a.
  Proof.
    apply Z.bits_inj_iff; red; intros; rewrite Z.lor_spec.
    destruct (Z.eqb_spec b n); subst.
    - now rewrite (Testbit.Z.testbit_small_neg a), orb_true_r.
    - now rewrite Z.pow2_bits_false, orb_false_l. Qed.
End Z.
