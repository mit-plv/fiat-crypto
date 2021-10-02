Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import List Setoid Compare_dec Morphisms FinFun PeanoNat Permutation.
Import ListNotations.
Local Set Implicit Arguments.

(** From Coq's Coq.Sorting.Permutation file on newer versions of Coq than 8.11 *)
Module Export Coq.
Module Export Sorting.
Module Permutation.
Export Coq.Sorting.Permutation.

Section Permutation_properties.

Variable A B:Type.

Implicit Types a b : A.
Implicit Types l m : list A.

(** TODO: Remove this when be bump the minimum version to Coq 8.12 *)
Local Hint Resolve perm_swap perm_trans : core.
Lemma Permutation_Forall2 (P : A -> B -> Prop) :
 forall l1 l1' (l2 : list B), Permutation l1 l1' -> Forall2 P l1 l2 ->
 exists l2' : list B, Permutation l2 l2' /\ Forall2 P l1' l2'.
Proof using Type.
  intros l1 l1' l2 HP.
  revert l2; induction HP; intros l2 HF; inversion HF as [ | ? b ? ? HF1 HF2 ]; subst.
  - now exists nil.
  - apply IHHP in HF2 as [l2' [HP2 HF2]].
    exists (b :: l2'); auto.
  - inversion_clear HF2 as [ | ? b' ? l2' HF3 HF4 ].
    exists (b' :: b :: l2'); auto.
  - apply Permutation_nil in HP1; subst.
    apply Permutation_nil in HP2; subst.
    now exists nil.
  - apply IHHP1 in HF as [l2' [HP2' HF2']].
    apply IHHP2 in HF2' as [l2'' [HP2'' HF2'']].
    exists l2''; split; auto.
    now transitivity l2'.
Qed.

End Permutation_properties.
End Permutation.
End Sorting.
End Coq.
