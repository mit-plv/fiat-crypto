Require Import Coq.Lists.List.

Lemma fold_left_orb_true ls
  : List.fold_left orb ls true = true.
Proof. induction ls as [|?? IHls]; [ reflexivity | assumption ]. Qed.
Lemma fold_left_orb_pull ls v
  : List.fold_left orb ls v = orb v (List.fold_left orb ls false).
Proof. destruct v; [ apply fold_left_orb_true | reflexivity ]. Qed.
