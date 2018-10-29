Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.DestructHead.

Local Ltac t :=
  repeat first [ progress destruct_head'_ex
               | progress destruct_head'_and
               | progress intros
               | progress subst
               | assumption
               | progress repeat esplit ].

Lemma ex_and_eq_l_iff {A P x}
  : (exists y : A, y = x /\ P y) <-> P x.
Proof. t. Qed.

Lemma ex_and_eq_r_iff {A P x}
  : (exists y : A, x = y /\ P y) <-> P x.
Proof. t. Qed.

Lemma ex_eq_and_l_iff {A P x}
  : (exists y : A, P y /\ y = x) <-> P x.
Proof. t. Qed.

Lemma ex_eq_and_r_iff {A P x}
  : (exists y : A, P y /\ x = y) <-> P x.
Proof. t. Qed.
