Require Import Coq.Lists.List.

Module List.
  Section IndexOf.
    Context [A] (f : A -> bool).
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
  End IndexOf.


  Section FoldMap. (* map over a list in the state monad *)
    Context [A B S] (f : A -> S -> B * S).
    Fixpoint foldmap (l : list A) (s : S) : list B * S :=
      match l with
      | nil => (nil, s)
      | cons a l =>
          let bs_s := foldmap l s in
          let b_s := f a (snd bs_s) in
          (cons (fst b_s) (fst bs_s), snd b_s)
      end.
    Lemma foldmap_ind
      l s
      (P : list A -> list B -> S -> Prop)
      (Hnil : P nil nil s)
      (Hcons : forall (l : list A) (l' : list B) (s : S),
      P l l' s -> forall a, P (cons a l) (cons (fst (f a s)) l') (snd (f a s))) : P l (fst (foldmap l s)) (snd (foldmap l s)).
    Proof using Type. induction l; eauto; []; eapply Hcons; trivial. Qed.
  End FoldMap.
End List.
