Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.

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

Local Ltac t_Forall2_step :=
  first [ progress intros
        | progress subst
        | progress destruct_head'_and
        | progress destruct_head'_ex
        | progress specialize_by_assumption
        | progress split_iff
        | apply conj
        | progress cbn [List.map List.seq List.repeat List.rev List.firstn List.skipn List.length] in *
        | exfalso; assumption
        | solve [ eauto ]
        | match goal with
          | [ |- List.Forall2 _ _ _ ] => constructor
          | [ |- List.Forall _ _ ] => constructor
          | [ H : List.Forall2 _ nil (cons _ _) |- _ ] => inversion H
          | [ H : List.Forall2 _ (cons _ _) nil |- _ ] => inversion H
          | [ H : List.Forall2 _ (cons _ _) (cons _ _) |- _ ] => inversion H; clear H
          | [ H : List.Forall2 _ (cons _ _) ?x |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ ?x (cons _ _) |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ nil ?x |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall2 _ ?x nil |- _ ] => is_var x; inversion H; clear H
          | [ H : List.Forall _ (cons _ _) |- _ ] => inversion H; clear H
          | [ H : List.Forall2 _ (List.app _ _) _ |- _ ] => apply Forall2_app_inv_l in H
          | [ H : List.Forall2 _ _ (List.app _ _) |- _ ] => apply Forall2_app_inv_r in H
          | [ H : nil = _ ++ _ |- _ ] => symmetry in H
          | [ H : _ ++ _ = nil |- _ ] => apply app_eq_nil in H
          | [ H : cons _ _ = nil |- _ ] => inversion H
          | [ H : nil = cons _ _ |- _ ] => inversion H
          | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
          | [ H : _ ++ _ :: nil = _ ++ _ :: nil |- _ ] => apply app_inj_tail in H
          | [ |- List.Forall2 _ (_ ++ _ :: nil) (_ ++ _ :: nil) ] => apply Forall2_app
          end ].
Local Ltac t_Forall2 := repeat t_Forall2_step.

Lemma Forall2_map_l_iff {A A' B R f ls1 ls2}
  : @List.Forall2 A' B R (List.map f ls1) ls2
    <-> @List.Forall2 A B (fun x y => R (f x) y) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.
Lemma Forall2_map_r_iff {A B B' R f ls1 ls2}
  : @List.Forall2 A B' R ls1 (List.map f ls2)
    <-> @List.Forall2 A B (fun x y => R x (f y)) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.
Lemma Forall2_map_map_iff {A A' B B' R f g ls1 ls2}
  : @List.Forall2 A' B' R (List.map f ls1) (List.map g ls2)
    <-> @List.Forall2 A B (fun x y => R (f x) (g y)) ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.
Lemma Forall2_Forall {A R ls}
  : @List.Forall2 A A R ls ls
    <-> @List.Forall A (Proper R) ls.
Proof using Type. induction ls as [|l ls IHls]; t_Forall2. Qed.
Lemma Forall_seq {R start len}
  : List.Forall R (seq start len) <-> (forall x, (start <= x < start + len)%nat -> R x).
Proof using Type.
  revert start; induction len as [|len IHlen]; intro start;
    [ | specialize (IHlen (S start)) ].
  all: repeat first [ t_Forall2_step
                    | lia
                    | exfalso; lia
                    | match goal with
                      | [ H : ?R ?x |- ?R ?y ]
                        => destruct (PeanoNat.Nat.eq_dec x y); [ subst; assumption | clear H ]
                      | [ H : _ |- _ ] => apply H; clear H
                      end ].
Qed.

Lemma Forall2_repeat_iff {A B R x y n m}
  : @List.Forall2 A B R (List.repeat x n) (List.repeat y m)
    <-> ((n <> 0%nat -> R x y) /\ n = m).
Proof using Type.
  revert m; induction n as [|n IHn], m as [|m]; [ | | | specialize (IHn m) ];
    t_Forall2; try congruence.
Qed.

Lemma Forall2_rev_iff {A B R ls1 ls2}
  : @List.Forall2 A B R (List.rev ls1) (List.rev ls2)
    <-> @List.Forall2 A B R ls1 ls2.
Proof using Type.
  revert ls2; induction ls1 as [|l ls IHls], ls2 as [|l' ls'];
    t_Forall2.
Qed.

Lemma Forall2_rev_lr_iff {A B R ls1 ls2}
  : @List.Forall2 A B R (List.rev ls1) ls2 <-> @List.Forall2 A B R ls1 (List.rev ls2).
Proof using Type.
  rewrite <- (rev_involutive ls2), Forall2_rev_iff, !rev_involutive; reflexivity.
Qed.

Lemma Forall2_firstn {A B R ls1 ls2 n}
  : @List.Forall2 A B R ls1 ls2 -> @List.Forall2 A B R (List.firstn n ls1) (List.firstn n ls2).
Proof using Type.
  revert ls1 ls2; induction n as [|n IHn], ls1 as [|l1 ls2], ls2 as [|l2 ls2]; t_Forall2.
Qed.

Lemma Forall2_skipn {A B R ls1 ls2 n}
  : @List.Forall2 A B R ls1 ls2 -> @List.Forall2 A B R (List.skipn n ls1) (List.skipn n ls2).
Proof using Type.
  revert ls1 ls2; induction n as [|n IHn], ls1 as [|l1 ls2], ls2 as [|l2 ls2]; t_Forall2.
Qed.

Lemma eq_length_Forall2 {A B R ls1 ls2}
  : @List.Forall2 A B R ls1 ls2 -> List.length ls1 = List.length ls2.
Proof using Type.
  revert ls2; induction ls1, ls2; t_Forall2.
Qed.

Lemma Forall2_combine {A B C D R1 R2 R3 ls1 ls2 ls3 ls4}
      (HR : forall x y z w, (R1 x y : Prop) -> (R2 z w : Prop) -> (R3 (x, z) (y, w) : Prop))
  : @List.Forall2 A B R1 ls1 ls2
    -> @List.Forall2 C D R2 ls3 ls4
    -> List.Forall2 R3 (List.combine ls1 ls3) (List.combine ls2 ls4).
Proof using Type.
  revert ls2 ls3 ls4; induction ls1, ls2, ls3, ls4; t_Forall2.
Qed.

Lemma Forall2_forall_iff_nth_error {A B R xs ys}
  : @Forall2 A B R xs ys
    <-> forall i, option_eq R (nth_error xs i) (nth_error ys i).
Proof using Type.
  revert ys; induction xs as [|x xs IHxs], ys as [|y ys];
    [ | | | specialize (IHxs ys) ]; t_Forall2.
  all: repeat first [ t_Forall2_step
                    | progress cbn [option_eq nth_error] in *
                    | progress inversion_option
                    | match goal with
                      | [ H : forall x, nth_error (cons _ _) x = None |- _ ] => specialize (H O)
                      | [ H : forall x, option_eq _ (nth_error (cons _ _) x) None |- _ ] => specialize (H O)
                      | [ |- context[nth_error (cons _ _) ?x] ] => is_var x; destruct x
                      | [ H : forall i, option_eq _ _ (nth_error (cons _ _) ?x) |- _ ]
                        => pose proof (H O);
                           pose proof (fun i => H (S i));
                           clear H
                      | [ H : forall i, option_eq _ (nth_error (cons _ _) ?x) _ |- _ ]
                        => pose proof (H O);
                           pose proof (fun i => H (S i));
                           clear H
                      | [ |- context[nth_error nil ?x] ] => is_var x; destruct x
                      end ].
Qed.

Lemma Forall2_forall_iff'' {A B R xs ys d1 d2}
  : (@Forall2 A B R xs ys /\ R d1 d2)
    <-> (length xs = length ys
         /\ (forall i, R (nth_default d1 xs i) (nth_default d2 ys i))).
Proof using Type.
  t_Forall2; cbv [nth_default] in *.
  all: repeat first [ eapply eq_length_Forall2; eassumption
                    | rewrite Forall2_forall_iff_nth_error
                    | t_Forall2_step
                    | progress cbn [option_eq] in *
                    | progress inversion_option
                    | match goal with
                      | [ H : Forall2 _ _ _ |- _ ] => rewrite Forall2_forall_iff_nth_error in H
                      | [ H : forall i : nat, _ |- context[nth_error _ ?n] ]
                        => specialize (H n)
                      | [ H' : List.length ?ls = _, H : forall i : nat, _ |- _ ]
                        => specialize (H (List.length ls)); rewrite ?nth_error_length_error in H by lia
                      end
                    | break_innermost_match_step
                    | break_innermost_match_hyps_step
                    | match goal with
                      | [ H : nth_error _ _ = None |- _ ] => rewrite nth_error_None in H
                      | [ H : nth_error ?l ?n = Some _ |- _ ]
                        => assert (n < List.length l) by (apply nth_error_Some; congruence);
                           clear H
                      end
                    | lia ].
Qed.

Lemma Forall2_forall_In_combine_iff {A B} R xs ys
  : @List.Forall2 A B R xs ys
    <-> (List.length xs = List.length ys
         /\ forall x y, List.In (x, y) (List.combine xs ys) -> R x y).
Proof using Type.
  split; revert ys; induction xs as [|x xs IHxs], ys as [|y ys]; cbn in *; intro H.
  all: inversion_clear H; split_and;
    try solve [ repeat constructor; intuition (congruence + eauto) ].
Qed.

Global Instance Forall2_Proper_impl {A B}
  : Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> eq ==> eq ==> Basics.impl)
           (@List.Forall2 A B) | 10.
Proof.
  cbv [Basics.impl respectful pointwise_relation].
  repeat intro; subst; rewrite Forall2_forall_In_combine_iff in *.
  destruct_head'_and; split; eauto.
Qed.

Global Instance Forall2_Proper_iff {A B}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff)
           (@List.Forall2 A B) | 10.
Proof.
  cbv [respectful pointwise_relation].
  repeat intro; subst; rewrite !Forall2_forall_In_combine_iff in *.
  split_iff.
  repeat (split || destruct_head'_and); eauto.
Qed.
