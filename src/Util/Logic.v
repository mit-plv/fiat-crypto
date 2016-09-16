Require Import Crypto.Util.FixCoqMistakes.

(* WHY does this solve goals that [intuition] does not solve? *)
Ltac logic :=
  repeat match goal with
         | |- _ => intro
         | H:exists _, _ |- _ => destruct H
         | H:_ /\ _ |- _ => destruct H
         | |- _ => solve [eauto]
         | |- _ => split
         end.

Lemma exists_and_indep_l {A B} P Q :
  (exists a b, P a /\ Q a b) <-> (exists a:A, P a /\ exists b:B, Q a b).
Proof. logic. Qed.

Lemma exists_and_indep_r {A B} P Q :
  (exists a b, Q a b /\ P a) <-> (exists a:A, P a /\ exists b:B, Q a b).
Proof. logic. Qed.
