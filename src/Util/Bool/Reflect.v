(** * Some lemmas about [Bool.reflect] *)
Require Import Coq.Bool.Bool.

Lemma reflect_to_dec_iff {P b1 b2} : reflect P b1 -> (b1 = b2) <-> (if b2 then P else ~P).
Proof.
  intro H; destruct H, b2; split; intuition congruence.
Qed.

Lemma reflect_to_dec {P b1 b2} : reflect P b1 -> (b1 = b2) -> (if b2 then P else ~P).
Proof. intro; apply reflect_to_dec_iff; assumption. Qed.
