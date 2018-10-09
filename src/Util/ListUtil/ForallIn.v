Require Import Coq.Lists.List.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.DestructHead.

Lemma fold_right_impl_Proper {A} {P Q : A -> Prop} ls (concl1 concl2 : Prop)
      (Hconcl : concl1 -> concl2)
      (HPQ : forall a, In a ls -> Q a -> P a)
: fold_right (fun a (concl : Prop) => P a -> concl) concl1 ls
  -> fold_right (fun a (concl : Prop) => Q a -> concl) concl2 ls.
Proof. induction ls as [|x xs IHxs]; cbn [fold_right In] in *; intuition. Qed.

Lemma forall_In_existT {A P} {Q : forall a : A, P a -> Prop} ls
  : fold_right
      (fun xp (concl : Prop)
       => Q (projT1 xp) (projT2 xp) -> concl)
      (forall x p, In (@existT A P x p) ls -> Q x p)
      ls.
Proof.
  induction ls as [|x xs IHxs]; cbn [fold_right In]; intros;
    destruct_head' False; destruct_head'_or.
  eapply fold_right_impl_Proper; [ | | refine IHxs ]; intuition (subst; eauto).
Qed.

Lemma forall_In_pair_existT {A A' P P'} {Q : forall (a : A) (a' : A'), P a -> P' a' -> Prop} ls
  : fold_right
      (fun xp_x'p' (concl : Prop)
       => Q (projT1 (fst xp_x'p')) (projT1 (snd xp_x'p')) (projT2 (fst xp_x'p')) (projT2 (snd xp_x'p')) -> concl)
      (forall x p x' p', In (@existT A P x p, @existT A' P' x' p') ls -> Q x x' p p')
      ls.
Proof.
  induction ls as [|x xs IHxs]; cbn [fold_right In]; intros;
    destruct_head' False; destruct_head'_prod; destruct_head'_or; intros.
  eapply fold_right_impl_Proper; [ | | refine IHxs ]; intuition (inversion_prod; subst; eauto).
Qed.
