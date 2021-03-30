Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ListUtil.NthExt.
Require Import Crypto.Util.Notations.

Module Option.
  Module List.
    Section map.
      Context {A B}
              (f : A -> option B).

      Fixpoint map (ls : list A) : list B
        := match ls with
           | nil => nil
           | cons x xs
             => match f x with
               | Some fx => fx :: map xs
               | None => map xs
               end
           end.
    End map.

    Fixpoint bind_list {A B} (v : list (option A)) (f : list A -> option B) : option B
      := match v with
         | nil => f nil
         | x :: xs => (x <- x; @bind_list A B xs (fun xs => f (x :: xs)))
         end%option%list.

    Definition lift {A} (ls : list (option A)) : option (list A)
      := fold_right (fun x xs => x <- x; xs <- xs; Some (x :: xs))%option
                    (Some nil)
                    ls.

    Lemma bind_list_cps_id {A B} v f
      : @bind_list A B v f = (v <- bind_list v (@Some _); f v)%option.
    Proof.
      revert B f; induction v as [|[x|] xs IHxs]; cbn; try reflexivity.
      intros; etransitivity; rewrite IHxs; [ | reflexivity ]; edestruct bind_list; reflexivity.
    Qed.

    Lemma eq_bind_list_lift {A} (ls : list (option A))
      : lift ls = bind_list ls (@Some _).
    Proof.
      cbv [lift]; induction ls as [|[x|] xs IHxs]; cbn; try reflexivity.
      rewrite IHxs; etransitivity; [ | rewrite bind_list_cps_id; reflexivity ].
      reflexivity.
    Qed.

    Lemma lift_Some_nth_error_all {A} ol l (H : @lift A ol = Some l)
      : forall i a, nth_error l i = Some a -> nth_error ol i = Some (Some a).
    Proof.
      cbv [lift] in *; revert dependent l; induction ol as [|x xs IHxs], l as [|y ys], i as [|i]; cbn in *; try congruence;
        intros; inversion_option; subst; destruct_head' option; cbn in *; try congruence.
      all: edestruct fold_right; cbn in *; inversion_option; specialize (IHxs _ eq_refl).
      all: match goal with H : cons _ _ = cons _ _ |- _ => inversion H; clear H; subst end.
      all: auto.
    Qed.

    Lemma lift_Some_nth_error_all_iff {A} ol l
      : @lift A ol = Some l
        <-> (List.length ol = List.length l
             /\ forall i a, nth_error l i = Some a -> nth_error ol i = Some (Some a)).
    Proof.
      cbv [lift] in *; revert dependent l; induction ol as [|x xs IHxs], l as [|y ys].
      all: repeat first [ apply conj
                        | progress inversion_option
                        | progress destruct_head'_and
                        | progress subst
                        | progress cbn in *
                        | progress intros
                        | congruence
                        | progress destruct_head' option
                        | solve [ eauto ]
                        | match goal with
                          | [ H : nth_error nil ?i = _ |- _ ] => is_var i; destruct i
                          | [ H : nth_error (cons _ _) ?i = _ |- _ ] => is_var i; destruct i
                          | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
                          | [ H : forall x, Some ?y = Some x <-> _ |- _ ] => specialize (H y)
                          | [ H : ?x = ?x <-> _ |- _ ] => destruct H
                          | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                          | [ H : _ -> ?x = ?x |- _ ] => clear H
                          | [ H : S _ = S _ |- _ ] => inversion H; clear H
                          | [ H : forall l, _ -> None = Some _ |- _ ] => specialize (H _ ltac:(eauto))
                          | [ H : forall i a, nth_error (cons _ _) i = _ -> _ |- _ ]
                            => pose proof (H 0 _ eq_refl); specialize (fun i => H (S i))
                          | [ |- Some (?x :: ?xs) = Some (?x :: ?ys) ] => (do 2 apply f_equal)
                          end
                        | match goal with
                          | [ H : context[@fold_right ?A ?B ?f ?init ?ls] |- _ ] => destruct (@fold_right A B f init ls)
                          end
                        | progress split_iff ].
      { unshelve eapply nth_ext; try eassumption; try congruence.
        intros n Hn; rewrite <- !nth_default_eq; cbv [nth_default].
        repeat match goal with H : forall i : nat, _ |- _ => specialize (H n) end.
        break_match.
        all: repeat match goal with H : forall a, Some ?x = Some a -> _ |- _ => specialize (H _ eq_refl) end.
        all: try congruence.
        all: repeat match goal with H : nth_error _ _ = None |- _ => rewrite nth_error_None in H end.
        all: try lia. }
    Qed.

    Lemma lift_None_nth_error_iff {A} ol
      : @lift A ol = None <-> exists j, nth_error ol j = Some None.
    Proof.
      cbv [lift]; induction ol as [|[x|] xs IHxs].
      all: repeat first [ progress cbn in *
                        | apply conj
                        | congruence
                        | progress intros
                        | progress destruct_head'_ex
                        | progress split_iff
                        | eexists (S _); cbn; eassumption
                        | exists 0; reflexivity
                        | progress specialize_by eauto
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
      Notation "A <-- X ; B" := (bind_list X (fun A => B%option)) : option_scope.
    End Notations.
  End List.
End Option.

Export Option.List.Notations.

Lemma fold_right_option_seq A B f init ls v
  : List.fold_right (fun x y => x <- x; y <- y; Some (f x y))%option (Some init) ls = Some v
    <-> exists ls', List.map (@Some _) ls' = ls
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
                   | [ x : option _ |- _ ] => destruct x
                   | [ H : ex _ |- _ ] => destruct H
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                   | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
                   | [ H : List.map _ ?x = nil |- _ ] => is_var x; destruct x
                   | [ H : List.map _ ?x = cons _ _ |- _ ] => is_var x; destruct x
                   | [ H : forall v, iff _ _ |- _ ]
                     => pose proof (fun v => proj1 (H v)); pose proof (fun v => proj2 (H v)); clear H
                   | [ |- iff _ _ ] => split
                   | [ |- context[Option.bind ?x ?y] ] => destruct x eqn:?
                   | [ H : context[Option.bind ?x ?y] |- _ ] => destruct x eqn:?
                   | [ H : forall v, _ = _ -> _ |- _ ] => specialize (H _ ltac:(eassumption || reflexivity))
                   | [ H : forall v, (exists y, _ = _ /\ _ = _) -> _ |- _ ] => specialize (H _ ltac:(eexists; split; reflexivity))
                   | [ |- exists ls', List.map ?f ls' = (?f ?x :: List.map ?f ?xs)%list /\ _ ]
                     => exists (cons x xs)
                   end ].
Qed.
