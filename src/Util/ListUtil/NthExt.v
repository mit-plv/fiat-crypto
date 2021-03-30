(* We copy some proofs from the standard library so we can use them in older versions of Coq; once we get a new enough Coq, this file should go away *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Local Open Scope list_scope.
Module Export List.
  (* This is in the stdlib since Coq 8.12 *)
  Section Elts.
    Variable A : Type.

    Lemma nth_ext : forall (l l' : list A) d d', length l = length l' ->
                                                 (forall n, n < length l -> nth n l d = nth n l' d') -> l = l'.
    Proof.
      intro l; induction l as [|a l IHl];
        intros l' d d' Hlen Hnth; destruct l' as [| b l'].
      - reflexivity.
      - inversion Hlen.
      - inversion Hlen.
      - change a with (nth 0 (a :: l) d).
        change b with (nth 0 (b :: l') d').
        rewrite Hnth; f_equal.
        + apply IHl with d d'; [ now inversion Hlen | ].
          intros n Hlen'; apply (Hnth (S n)).
          now apply (Nat.succ_lt_mono n (length l)).
        + simpl; apply Nat.lt_0_succ.
    Qed.
  End Elts.
End List.
