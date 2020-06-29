Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module N2Z.
  Lemma inj_land n m : Z.of_N (N.land n m) = Z.land (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.
  Hint Rewrite inj_land : push_Zof_N.
  Hint Rewrite <- inj_land : pull_Zof_N.

  Lemma inj_lor n m : Z.of_N (N.lor n m) = Z.lor (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.
  Hint Rewrite inj_lor : push_Zof_N.
  Hint Rewrite <- inj_lor : pull_Zof_N.

  Lemma inj_shiftl: forall x y, Z.of_N (N.shiftl x y) = Z.shiftl (Z.of_N x) (Z.of_N y).
  Proof.
    intros x y.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftl_spec; [|assumption].

    assert ((Z.to_N k) >= y \/ (Z.to_N k) < y)%N as g by (
        unfold N.ge, N.lt; induction (N.compare (Z.to_N k) y); [left|auto|left];
        intro H; inversion H).

    destruct g as [g|g];
    [ rewrite N.shiftl_spec_high; [|apply N2Z.inj_le; rewrite Z2N.id|apply N.ge_le]
    | rewrite N.shiftl_spec_low]; try assumption.

    - rewrite <- N2Z.inj_testbit; f_equal.
        rewrite N2Z.inj_sub, Z2N.id; [reflexivity|assumption|apply N.ge_le; assumption].

    - apply N2Z.inj_lt in g.
        rewrite Z2N.id in g; [symmetry|assumption].
        apply Z.testbit_neg_r; lia.
  Qed.
  Hint Rewrite inj_shiftl : push_Zof_N.
  Hint Rewrite <- inj_shiftl : pull_Zof_N.

  Lemma inj_shiftr: forall x y, Z.of_N (N.shiftr x y) = Z.shiftr (Z.of_N x) (Z.of_N y).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftr_spec, N.shiftr_spec; [|apply N2Z.inj_le; rewrite Z2N.id|]; try assumption.
    rewrite <- N2Z.inj_testbit; f_equal.
    rewrite N2Z.inj_add; f_equal.
    apply Z2N.id; assumption.
  Qed.
  Hint Rewrite inj_shiftr : push_Zof_N.
  Hint Rewrite <- inj_shiftr : pull_Zof_N.
End N2Z.
