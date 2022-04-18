Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ListUtil.NthExt.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.

Module ErrorT.
  Module List.
    Fixpoint bind_list {ErrT A B} (v : list (ErrorT ErrT A)) (f : list A -> ErrorT ErrT B) : ErrorT ErrT B
      := match v with
         | nil => f nil
         | x :: xs => (x <- x; bind_list xs (fun xs => f (x :: xs)))
         end%error%list.

    Definition lift {ErrT A} (ls : list (ErrorT ErrT A)) : ErrorT ErrT (list A)
      := fold_right (fun x xs => x <- x; xs <- xs; Success (x :: xs))%error
                    (Success nil)
                    ls.

    Lemma bind_list_cps_id {ErrT A B} v f
      : @bind_list ErrT A B v f = (v <- bind_list v Success; f v)%error.
    Proof.
      revert B f; induction v as [|[x|] xs IHxs]; cbn; try reflexivity.
      intros; etransitivity; rewrite IHxs; [ | reflexivity ]; edestruct bind_list; reflexivity.
    Qed.

    Lemma eq_bind_list_lift {ErrT A} (ls : list (ErrorT ErrT A))
      : lift ls = bind_list ls Success.
    Proof.
      cbv [lift]; induction ls as [|[x|] xs IHxs]; cbn; try reflexivity.
      rewrite IHxs; etransitivity; [ | rewrite bind_list_cps_id; reflexivity ].
      reflexivity.
    Qed.

    Lemma lift_Success_nth_error_all {ErrT A} ol l (H : @lift ErrT A ol = Success l)
      : forall i a, nth_error l i = Some a -> nth_error ol i = Some (Success a).
    Proof.
      cbv [lift] in *; revert dependent l; induction ol as [|x xs IHxs], l as [|y ys], i as [|i]; cbn in *; try congruence;
        intros; inversion_option; subst; destruct_head' ErrorT; cbn in *; try congruence.
      all: edestruct fold_right; cbn in *; inversion_ErrorT; specialize (IHxs _ eq_refl).
      all: match goal with H : cons _ _ = cons _ _ |- _ => inversion H; clear H; subst end.
      all: auto.
    Qed.

    Lemma lift_Success_Forall2_iff {ErrT A} ol l
      : @lift ErrT A ol = Success l
        <-> Forall2 (fun a b => a = Success b) ol l.
    Proof.
      split; cbv [lift] in *; revert dependent l; induction ol as [|x xs IH], l as [|y ys]; try specialize (IH ys); cbn [fold_right].
      all: repeat first [ solve [ eauto ]
                        | progress intros
                        | progress subst
                        | progress inversion_ErrorT
                        | progress inversion_list
                        | progress invlist Forall2
                        | progress specialize_by_assumption
                        | match goal with
                          | [ H : ErrorT.bind ?x ?y = _ |- _ ]
                            => destruct x eqn:?; cbn [ErrorT.bind] in H
                          | [ H : ?x = _ |- context[?x] ] => rewrite H
                          end ].
    Qed.

    Lemma lift_Success_nth_error_all_iff {ErrT A} ol l
      : @lift ErrT A ol = Success l
        <-> (List.length ol = List.length l
             /\ forall i a, nth_error l i = Some a -> nth_error ol i = Some (Success a)).
    Proof.
      rewrite lift_Success_Forall2_iff.
      split; revert dependent l; induction ol as [|x xs IH], l as [|y ys];
        try specialize (IH ys).
      all: repeat first [ constructor
                        | progress subst
                        | progress invlist Forall2
                        | progress destruct_head'_and
                        | progress inversion_option
                        | progress cbn [List.length nth_error] in *
                        | progress specialize_by_assumption
                        | progress intros
                        | progress inversion_nat_eq
                        | congruence
                        | progress specialize_under_binders_by apply conj
                        | progress specialize_under_binders_by eassumption
                        | match goal with
                          | [ H : nth_error nil ?i = _ |- _ ] => is_var i; destruct i
                          | [ H : nth_error (cons _ _) ?i = _ |- _ ] => is_var i; destruct i
                          | [ H : forall i a, nth_error (cons _ _) i = _ -> _ |- _ ]
                            => pose proof (H 0 _ eq_refl); specialize (fun i => H (S i))
                          end ].
    Qed.

    Lemma lift_Error_nth_error_iff {ErrT A} ol
      : (exists e, @lift ErrT A ol = Error e) <-> exists j e, nth_error ol j = Some (Error e).
    Proof.
      cbv [lift]; induction ol as [|[x|] xs IHxs].
      all: repeat first [ progress cbn in *
                        | apply conj
                        | congruence
                        | progress intros
                        | progress destruct_head'_ex
                        | progress split_iff
                        | eexists (S _); cbn; now eauto
                        | exists 0; cbn; now eauto
                        | solve [ eauto ]
                        | progress specialize_by eauto
                        | progress inversion_ErrorT
                        | progress subst
                        | match goal with
                          | [ H : nth_error nil ?i = _ |- _ ] => is_var i; destruct i
                          | [ H : nth_error (cons _ _) ?i = _ |- _ ] => is_var i; destruct i
                          | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                          end
                        | match goal with
                          | [ H : context[@fold_right ?A ?B ?f ?init ?ls] |- _ ] => destruct (@fold_right A B f init ls)
                          end ].
    Qed.

    Module Export Notations.
      Notation "A <-- X ; B" := (bind_list X (fun A => B%error)) : error_scope.
    End Notations.
  End List.
End ErrorT.

Export ErrorT.List.Notations.

Lemma fold_right_ErrorT_seq ErrT A B f init ls v
  : List.fold_right (fun x y => x <- x; y <- y; Success (f x y))%error (Success init) ls = Success v
    <-> exists ls', List.map (@Success ErrT _) ls' = ls
                    /\ @List.fold_right A B f init ls' = v.
Proof.
  revert v; induction ls as [|x xs IHxs]; cbn; intros;
    repeat first [ apply conj
                 | progress intros
                 | progress subst
                 | progress cbn in *
                 | solve [ try (exists nil); cbn; auto ]
                 | congruence
                 | match goal with
                   | [ x : ErrorT _ _ |- _ ] => destruct x
                   | [ H : ex _ |- _ ] => destruct H
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                   | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
                   | [ H : List.map _ ?x = nil |- _ ] => is_var x; destruct x
                   | [ H : List.map _ ?x = cons _ _ |- _ ] => is_var x; destruct x
                   | [ H : forall v, iff _ _ |- _ ]
                     => pose proof (fun v => proj1 (H v)); pose proof (fun v => proj2 (H v)); clear H
                   | [ |- iff _ _ ] => split
                   | [ |- context[ErrorT.bind ?x ?y] ] => destruct x eqn:?
                   | [ H : context[ErrorT.bind ?x ?y] |- _ ] => destruct x eqn:?
                   | [ H : forall v, _ = _ -> _ |- _ ] => specialize (H _ ltac:(eassumption || reflexivity))
                   | [ H : forall v, (exists y, _ = _ /\ _ = _) -> _ |- _ ] => specialize (H _ ltac:(eexists; split; reflexivity))
                   | [ |- exists ls', List.map ?f ls' = (?f ?x :: List.map ?f ?xs)%list /\ _ ]
                     => exists (cons x xs)
                   end ].
Qed.
