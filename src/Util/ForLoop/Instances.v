Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ForLoop.
Require Import Crypto.Util.Notations.

Lemma repeat_function_Proper_rel_le {stateT} R f g n
      (Hfg : forall c, 0 < c <= n -> forall s1 s2, R s1 s2 -> R (f c s1) (g c s2))
      s1 s2 (Hs : R s1 s2)
  : R (@repeat_function stateT f n s1) (@repeat_function stateT g n s2).
Proof.
  revert s1 s2 Hs.
  induction n; simpl; auto.
  intros; apply IHn; auto;
    intros; apply Hfg; auto;
      omega.
Qed.

Global Instance repeat_function_Proper_rel {stateT} R
  : Proper (pointwise_relation _ (R ==> R) ==> eq ==> R ==> R) (@repeat_function stateT) | 10.
Proof.
  unfold pointwise_relation, respectful.
  intros body1 body2 Hbody c y ?; subst y.
  induction c; simpl; auto.
Qed.

Lemma repeat_function_Proper_le {stateT} f g n
      (Hfg : forall c, 0 < c <= n -> forall st, f c st = g c st)
      st
  : @repeat_function stateT f n st = @repeat_function stateT g n st.
Proof.
  apply repeat_function_Proper_rel_le; try reflexivity; intros; subst; auto.
Qed.

Global Instance repeat_function_Proper {stateT}
  : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@repeat_function stateT).
Proof.
  intros ???; eapply repeat_function_Proper_rel; repeat intro; subst.
  unfold pointwise_relation, respectful in *; auto.
Qed.
About for_loop.

Global Instance for_loop_Proper_rel {stateT} R i0 final step
  : Proper (R ==> pointwise_relation _ (R ==> R) ==> R) (@for_loop stateT i0 final step) | 10.
Proof.
  intros ?? Hinitial ?? Hbody; revert Hinitial.
  unfold for_loop; eapply repeat_function_Proper_rel;
    unfold pointwise_relation, respectful in *; auto.
Qed.

Global Instance for_loop_Proper_rel_full {stateT} R
  : Proper (eq ==> eq ==> eq ==> R ==> pointwise_relation _ (R ==> R) ==> R) (@for_loop stateT) | 20.
Proof.
  intros ?????????; subst; apply for_loop_Proper_rel.
Qed.

Global Instance for_loop_Proper {stateT} i0 final step initial
  : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq) (@for_loop stateT i0 final step initial).
Proof.
  unfold pointwise_relation.
  intros ???; eapply for_loop_Proper_rel; try reflexivity; repeat intro; subst; auto.
Qed.

Global Instance for_loop_Proper_full {stateT}
  : Proper (eq ==> eq ==> eq ==> eq ==> pointwise_relation _ (pointwise_relation _ eq) ==> eq) (@for_loop stateT) | 5.
Proof.
  intros ????????????; subst; apply for_loop_Proper.
Qed.
