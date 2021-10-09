Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.

Module List.
  Section IndexOf.
    Context {A} (f : A -> bool).
    Fixpoint indexof (l : list A) : option nat :=
      match l with
      | nil => None
      | cons a l =>
          if f a then Some 0
          else option_map S (indexof l )
      end.
    Lemma indexof_Some l i (H : indexof l = Some i) :
      exists a, nth_error l i = Some a /\ f a = true.
    Proof using Type.
      revert dependent i; induction l; cbn in *; try congruence; [].
      destruct (f a) eqn:?; cbn.
      { inversion 1; subst. eexists. split. exact eq_refl. eassumption. }
      { cbv [option_map]; destruct (indexof l) eqn:?; inversion 1; subst; eauto. }
    Qed.

    Lemma indexof_None l (H : indexof l = None) :
      forall i a, nth_error l i = Some a -> f a = false.
    Proof using Type.
      induction l, i.
      all: repeat first [ reflexivity
                        | progress cbn in *
                        | progress cbv [option_map] in *
                        | progress intros
                        | progress inversion_option
                        | progress subst
                        | progress break_innermost_match_hyps
                        | solve [ eauto ] ].
    Qed.

    Lemma indexof_app l1 l2
      : indexof (l1 ++ l2) = Option.sequence (indexof l1) (option_map (fun x => List.length l1 + x) (indexof l2)).
    Proof using Type.
      revert l2; induction l1 as [|x xs IH]; cbn; intros; [ | rewrite IH ].
      all: cbv [option_map Option.sequence]; break_innermost_match; reflexivity.
    Qed.
  End IndexOf.
End List.
