Require Import Coq.Setoids.Setoid.
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

Ltac ex_eq_and_step :=
  let rew lem := (rewrite lem || setoid_rewrite lem) in
  let rew_in lem H := (rewrite lem in H || setoid_rewrite lem in H) in
  match goal with
  | [ |- context[exists y, _ = y /\ _] ]
    => rew (@ex_and_eq_r_iff)
  | [ |- context[exists y, y = _ /\ _] ]
    => rew (@ex_and_eq_l_iff)
  | [ |- context[exists y, _ /\ _ = y] ]
    => rew (@ex_eq_and_r_iff)
  | [ |- context[exists y, _ /\ y = _] ]
    => rew (@ex_eq_and_l_iff)
  | [ H : context[exists y, _ = y /\ _] |- _ ]
    => rew_in (@ex_and_eq_r_iff) H
  | [ H : context[exists y, y = _ /\ _] |- _ ]
    => rew_in (@ex_and_eq_l_iff) H
  | [ H : context[exists y, _ /\ _ = y] |- _ ]
    => rew_in (@ex_eq_and_r_iff) H
  | [ H : context[exists y, _ /\ y = _] |- _ ]
    => rew_in (@ex_eq_and_l_iff) H
  end.

Ltac ex_eq_and := repeat ex_eq_and_step.
