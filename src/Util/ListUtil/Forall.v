Require Import Coq.Lists.List.

Definition Forallb {A} (P : A -> bool) (ls : list A) : bool
  := List.fold_right andb true (List.map P ls).

Lemma unfold_Forallb {A P} ls
  : @Forallb A P ls
    = match ls with
      | nil => true
      | cons x xs => andb (P x) (Forallb P xs)
      end.
Proof. destruct ls; reflexivity. Qed.

Lemma Forall_Forallb_iff {A} (P : A -> bool) (Q : A -> Prop) (ls : list A)
      (H : forall x, In x ls -> P x = true <-> Q x)
  : Forallb P ls = true <-> Forall Q ls.
Proof.
  induction ls as [|x xs IHxs]; simpl; rewrite unfold_Forallb.
  { intuition. }
  { simpl in *.
    rewrite Bool.andb_true_iff, IHxs
      by (intros; apply H; eauto).
    split; intro H'; inversion H'; subst; constructor; intuition;
      apply H; eauto. }
Qed.
