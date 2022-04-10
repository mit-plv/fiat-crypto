Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Open Scope list_scope.

Module List.
  Lemma partition_permutation A f (ls : list A) xs ys
        (H : @partition A f ls = (xs, ys))
    : Permutation (xs ++ ys) ls.
  Proof.
    revert xs ys H.
    induction ls as [|x ls IH]; cbn [partition]; intros xs ys H; inversion H; subst; clear H.
    { constructor. }
    { destruct (partition f ls); specialize (IH _ _ eq_refl).
      destruct f; match goal with H : pair _ _ = pair _ _ |- _ => inversion H; clear H end.
      all: subst; cbn.
      { constructor; assumption. }
      { rewrite <- IH.
        cbn.
        rewrite Permutation_app_comm; cbn; rewrite Permutation_app_comm.
        reflexivity. } }
  Qed.

  Lemma Forall_partition A f ls xs ys
        (H : @partition A f ls = (xs, ys))
    : Forall (fun x => f x = true) xs /\ Forall (fun x => f x = false) ys.
  Proof.
    revert xs ys H.
    induction ls as [|x ls IH]; cbn [partition]; intros xs ys H; inversion H; subst; clear H; repeat constructor; destruct partition, (f x) eqn:Hf.
    all: match goal with H : pair _ _ = pair _ _ |- _ => inversion H; clear H end; subst.
    all: specialize (IH _ _ eq_refl).
    all: destruct IH.
    all: repeat first [ constructor | assumption ].
  Qed.

  Lemma partition_eq_filter A f (ls : list A) xs ys
        (H : @partition A f ls = (xs, ys))
    : filter f ls = xs /\ filter (fun x => negb (f x)) ls = ys.
  Proof.
    revert xs ys H.
    induction ls as [|x ls IH]; cbn [partition filter]; intros xs ys H; inversion H; subst; clear H.
    { repeat constructor. }
    { destruct (partition f ls); specialize (IH _ _ eq_refl).
      destruct IH; subst.
      destruct f; match goal with H : pair _ _ = pair _ _ |- _ => inversion H; clear H end.
      all: subst; cbn; repeat constructor. }
  Qed.
End List.
