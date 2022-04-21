Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Set Implicit Arguments.
Local Open Scope list_scope.

Module List.
  Lemma filter_Forall_eq A f ls : @Forall A (fun x => f x = true) ls -> filter f ls = ls.
  Proof.
    induction 1; cbn; [ reflexivity | destruct f ]; try congruence.
  Qed.

  Lemma filter_length_le A f ls : List.length (@filter A f ls) <= List.length ls.
  Proof. induction ls; cbn; [ reflexivity | destruct f ]; cbn; auto with arith. Qed.

  Lemma filter_eq_length_eq A f ls : List.length (filter f ls) = List.length ls -> @filter A f ls = ls.
  Proof.
    induction ls; cbn; [ reflexivity | destruct f ]; cbn; intro; try apply f_equal; eauto with arith.
    pose proof (filter_length_le f ls).
    lia.
  Qed.

  Lemma Forall2_filter_same A B P f g lsA lsB
    : @Forall2 A B (fun a b => match f a, g b with
                               | true, true => P a b
                               | false, false => True
                               | true, false | false, true => False
                               end)
              lsA lsB
      -> Forall2 P (filter f lsA) (filter g lsB).
  Proof.
    induction 1; cbn; [ constructor | ].
    destruct f, g; try constructor; auto; try (exfalso; assumption).
  Qed.
End List.
