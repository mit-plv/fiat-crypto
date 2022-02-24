Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil.Partition.
Require Import Crypto.Util.ListUtil.StdlibCompat.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Open Scope list_scope.

Module List.
  Definition groupAllBy' {A} (f : A -> A -> bool)
    := fix groupAllBy' (ls : list A) (fuel : nat) : list (list A)
      := match fuel, ls with
         | (O | S _), [] => []
         | O, ls => [ls]
         | S fuel, x :: xs
           => let '(xs, ys) := partition (f x) xs in
              (x :: xs) :: groupAllBy' ys fuel
         end.

  Definition groupAllBy {A} (f : A -> A -> bool) (ls : list A) : list (list A)
    := groupAllBy' f ls (List.length ls).

  Lemma groupAllBy'_eq_fuel' A f ls fuel fuel'
        (H : List.length ls <= fuel <= fuel')
    : @groupAllBy' A f ls fuel = @groupAllBy' A f ls fuel'.
  Proof using Type.
    revert fuel' fuel ls H.
    induction fuel' as [|fuel' IH], fuel as [|fuel], ls as [|x xs];
      try specialize (IH fuel); cbn [List.length groupAllBy']; try lia; try reflexivity.
    destruct (partition (f x) xs) as [xs' ys] eqn:Hp.
    pose proof (@partition_length _ _ _ _ _ Hp).
    intros; f_equal; apply IH; lia.
  Qed.

  Lemma groupAllBy'_eq_fuel A f ls fuel fuel'
        (H : List.length ls <= fuel)
        (H' : List.length ls <= fuel')
    : @groupAllBy' A f ls fuel = @groupAllBy' A f ls fuel'.
  Proof using Type.
    destruct (le_gt_dec fuel fuel').
    all: (idtac + symmetry); apply groupAllBy'_eq_fuel'; lia.
  Qed.

  Lemma expand_groupAllBy {A f ls}
    : @groupAllBy A f ls = match ls with
                           | [] => []
                           | x :: xs
                             => let '(xs, ys) := partition (f x) xs in
                                (x :: xs) :: groupAllBy f ys
                           end.
  Proof using Type.
    induction ls as [|x xs IH]; cbn; try reflexivity.
    cbv [groupAllBy].
    pose proof (partition_length (f x) xs) as H.
    destruct partition; specialize (H _ _ eq_refl).
    f_equal.
    apply groupAllBy'_eq_fuel; lia.
  Qed.

  Lemma concat_groupAllBy {A} (f : A -> A -> bool) ls
    : Permutation (List.concat (groupAllBy f ls)) ls.
  Proof using Type.
    remember (List.length ls) as n eqn:H.
    revert ls H.
    induction n as [n IH] using lt_wf_ind; intros ls H'; subst.
    destruct ls as [|x xs].
    { constructor. }
    { rewrite expand_groupAllBy.
      destruct (partition (f x) xs) as [xs' ys] eqn:H.
      pose proof H as H'.
      apply partition_length in H'.
      apply List.partition_permutation in H; cbn [concat List.app].
      rewrite IH; [ | try reflexivity .. ]; [ | cbn [List.length]; lia .. ].
      constructor; assumption. }
  Qed.

  Lemma Forall_groupAllBy_full A f ls
    : list_rect (fun _ => Prop)
                True
                (fun xs xss P
                 => match xs with
                    | [] => False
                    | x :: xs => Forall (fun x' => f x x' = true) xs
                                 /\ Forall (Forall (fun y => f x y = false)) xss
                    end
                    /\ P)
                (@groupAllBy A f ls).
  Proof.
    remember (List.length ls) as n eqn:H.
    revert ls H.
    induction n as [n IH] using lt_wf_ind; intros ls H'; subst.
    destruct ls as [|x xs].
    { constructor. }
    { rewrite expand_groupAllBy.
      destruct (partition (f x) xs) as [xs' ys] eqn:H.
      pose proof H as H'.
      apply partition_length in H'.
      apply List.Forall_partition in H; cbn [concat List.app].
      cbn [list_rect].
      constructor;
        [ split; rewrite <- ?Forall_concat, ?concat_groupAllBy; apply H
        | eapply IH; [ | reflexivity ] ].
      cbn [List.length].
      lia. }
  Qed.

  Lemma Forall_groupAllBy A f ls
    : Forall (fun xs => match xs with
                        | [] => False
                        | x :: xs => Forall (fun x' => f x x' = true) xs
                        end)
             (@groupAllBy A f ls).
  Proof.
    generalize (@Forall_groupAllBy_full A f ls).
    induction (groupAllBy f ls) as [|[] xs IH]; cbn; constructor; intuition.
  Qed.
End List.
