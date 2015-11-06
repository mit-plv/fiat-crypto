Require Import Galois.BaseSystem.
Require Import List Util.ListUtil.
Import ListNotations.
Require Import ZArith.ZArith.
Require Import QArith.QArith QArith.Qround.
Require Import VerdiTactics.

Module Base25Point5_10limbs <: BaseCoefs.
  Definition base := map (fun i => two_p (Qceiling (Z_of_nat i *255 # 10))) (seq 0 10).
  Local Open Scope Z_scope.
  Lemma base_positive : forall b, In b base -> b > 0.
  Proof.
    compute; intros; repeat break_or_hyp; intuition.
  Qed.
  Lemma base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    intros.
    assert (In i (seq 0 (length base))) by nth_tac.
    assert (In j (seq 0 (length base))) by nth_tac.
    subst b; subst r; simpl in *.
    repeat break_or_hyp; try omega; auto.
  Qed.
End Base25Point5_10limbs.
