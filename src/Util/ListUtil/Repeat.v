From Stdlib Require Import List.
Import ListNotations.

Lemma Forall_repeat [A] (P : A -> Prop) x n : P x -> Forall P (repeat x n).
Proof. intros; induction n; cbn [repeat]; constructor; trivial. Qed.

Lemma repeat_inj [A] (x y : A) n m :
  repeat x n = repeat y m -> n = m /\ (x = y \/ n = 0).
Proof.
  revert m; induction n as [|n IH]; intros [|m]; cbn [repeat]; try discriminate; auto.
  intros [= -> ?%IH]; intuition auto.
Qed.
