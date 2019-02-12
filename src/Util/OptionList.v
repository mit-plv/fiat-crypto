Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
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
