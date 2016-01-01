Require Import NPeano.
Require Import List.
Require Import Sorting.Permutation.
Require Import BinInt.
Require Import Util.ListUtil.
Require Znumtheory.

Lemma all_neq_NoDup : forall {T} (xs:list T),
  (forall i j x y,
  nth_error xs i = Some x ->
  nth_error xs j = Some y ->
  i <> j -> x <> y) <->  NoDup xs.
Admitted.

Definition F (q:nat) := { n : nat | n = n mod q}.
 
Section Fq.
  Context {q : nat}.
  Axiom q_prime : Znumtheory.prime (Z.of_nat q).
  Let Fq := F q.

  Lemma q_is_succ : q = S (q-1). Admitted.

  Definition natToField (n:nat) : Fq. exists (n mod q). abstract admit. Defined.
  Definition fieldToNat (n:Fq) : nat := proj1_sig n.
  Coercion fieldToNat : Fq >-> nat.

  Definition zero : Fq. exists 0. abstract admit. Defined.
  Definition one : Fq. exists 1. abstract admit. Defined.

  Definition add (a b: Fq) : Fq.  exists (a+b mod q); abstract admit. Defined.
  Infix "+" := add.
  Definition mul (a b: Fq) : Fq.  exists (a*b mod q); abstract admit. Defined.
  Infix "*" := mul.
  Definition pow (a:Fq) (n:nat) : Fq. exists (pow a n mod q). abstract admit. Defined.
  Infix "^" := pow.

  Axiom opp : Fq -> Fq.
  Axiom opp_spec : forall a, opp a + a = zero.
  Definition sub a b := add a (opp b).
  Infix "-" := sub.

  Axiom inv : Fq -> Fq.
  Axiom inv_spec : forall a, inv a * a = one.
  Definition div a b := add a (inv b).
  Infix "/" := div.

  Fixpoint replicate {T} n (x:T) : list T := match n with O => nil | S n' => x::replicate n' x end.
  Definition prod := fold_right mul one.

  Lemma mul_one_l : forall a, one * a = a. Admitted.
  Lemma mul_one_r : forall a, a * one = a. Admitted.

  Lemma mul_cancel_l : forall a, a <> zero -> forall b c, a * b = a * c -> b = c. Admitted.
  Lemma mul_cancel_r : forall a, a <> zero -> forall b c, b * a = c * c -> b = c. Admitted.
  Lemma mul_cancel_l_1 : forall a, a <> zero -> forall b, a * b = a -> b = one. Admitted.
  Lemma mul_cancel_r_1 : forall a, a <> zero -> forall b, b * a = a -> b = one. Admitted.
  
  Lemma mul_0_why : forall a b, a * b = zero -> a = zero \/ b = zero. Admitted.

  Lemma mul_assoc : forall a b c, a * (b * c) = a * b * c. Admitted.
  Lemma mul_assoc_pairs' : forall a b c d, (a * b) * (c * d) = a * (c * (b * d)). Admitted.

  Lemma div_cancel : forall a, a <> zero -> forall b c, b / a = c / a -> b = c. Admitted.
  Lemma div_cancel_neq : forall a, a <> zero -> forall b c, b / a <> c / a -> b <> c. Admitted.

  Lemma div_mul : forall a, a <> zero -> forall b, (a * b) / a = b. Admitted.

  Hint Resolve mul_assoc.
  Hint Rewrite div_mul.

  Lemma pow_zero : forall (n:nat), zero^n = zero. Admitted.

  Lemma pow_S : forall a n, a ^ S n = a * a ^ n. Admitted.

  Lemma prod_replicate : forall a n, a ^ n = prod (replicate n a). Admitted.

  Lemma prod_perm : forall xs ys, Permutation xs ys -> prod xs = prod ys. Admitted.

  Hint Resolve pow_zero mul_one_l mul_one_r prod_replicate.


  Definition F_eq_dec : forall (a b:Fq), {a = b} + {a <> b}. Admitted.

  Definition elements : list Fq := map natToField (seq 0 q).
  Lemma elements_all : forall (a:Fq), In a elements. Admitted.
  Lemma elements_unique : forall (a:Fq), NoDup elements. Admitted.
  Lemma length_elements : length elements = q. Admitted.

  Definition invertibles : list Fq := map natToField (seq 1 (q-1)%nat).
  Lemma invertibles_all : forall (a:Fq), a <> zero -> In a invertibles. Admitted.
  Lemma invertibles_unique : NoDup invertibles. Admitted.
  Lemma prod_invertibles_nonzero : prod invertibles <> zero. Admitted.
  Lemma length_invertibles : length invertibles = (q-1)%nat. Admitted.

  Hint Resolve invertibles_unique.

  Section FermatsLittleTheorem.
    Variable a : Fq.
    Axiom a_nonzero : a <> zero.
    Hint Resolve a_nonzero.

    Definition bag := map (mul a) invertibles.
    Lemma bag_unique : NoDup bag.
    Proof.
      unfold bag; intros.
      eapply all_neq_NoDup; intros.
      eapply div_cancel_neq; eauto.
      eapply all_neq_NoDup; eauto;
      match goal with
      | [H: nth_error (map _ _) ?i = Some _ |- _ ] =>
        destruct (nth_error_map _ _ _ _ _ _ H) as [t [HtIn HtEq]]; rewrite <- HtEq; autorewrite with core; auto
      end.
    Qed.

    Lemma bag_invertibles : forall b, b <> zero -> In b bag.
    Proof.
      unfold bag; intros.
      assert (b/a <> zero) as Hdnz by admit.
      replace b with (a * (b/a)) by admit.
      destruct (In_nth_error_value _ _ (invertibles_all _ Hdnz)).
      eauto using nth_error_value_In, map_nth_error.
    Qed.

    Lemma In_bag_equiv_In_invertibles : forall b, In b bag <-> In b invertibles.
    Proof.
      unfold bag; intros.
      case (F_eq_dec b zero); intuition; subst;
          eauto using invertibles_all, bag_invertibles;
          repeat progress match goal with
          | [ H : In _ (map _ _) |- _ ] => rewrite in_map_iff in H; destruct H;
              pose proof a_nonzero; intuition
          | [ H : ?a * ?b = zero |- _ ] => destruct (mul_0_why a b H); clear H;
              intuition; try solve [subst; auto]
          end.
      assert (In zero invertibles -> In zero (map (mul a) invertibles)) by admit; auto.
    Qed.

    Lemma bag_perm_elements : Permutation bag invertibles.
    Proof.
      eauto using NoDup_Permutation, bag_unique, invertibles_unique, In_bag_equiv_In_invertibles.
    Qed.

    Hint Resolve prod_perm bag_perm_elements.
    Lemma prod_bag_ref : prod bag = prod invertibles.
    Proof.
      auto.
    Qed.

    Lemma prod_bag_interspersed : prod (flat_map (fun b => a::b::nil) invertibles) = prod invertibles.
    Proof.
      intros.
      rewrite <- prod_bag_ref.
      unfold bag.
      induction invertibles; auto; simpl.
      rewrite IHl.
      auto.
    Qed.

    Lemma prod_bag_sorted : prod (replicate (q-1)%nat a) * prod invertibles = prod invertibles.
      rewrite <- length_invertibles.
      rewrite <- prod_bag_interspersed at 2.
      induction invertibles; auto; simpl.
      rewrite mul_assoc_pairs'; repeat f_equal; auto.
    Qed.
      
    Theorem fermat' : a <> zero -> a^(q-1) = one.
    Proof.
      rewrite prod_replicate; eauto using mul_cancel_r_1, prod_bag_sorted, prod_invertibles_nonzero.
    Qed.
  End FermatsLittleTheorem.

  Theorem fermat (a:Fq) : a^q = a.
  Proof.
    case (F_eq_dec a zero); intros; subst; auto.
    rewrite q_is_succ, pow_S, fermat'; auto.
  Qed.
End Fq.
Arguments fermat' : default implicits.
Arguments fermat : default implicits.
Arguments elements : default implicits.
Arguments invertibles : default implicits.

Print Assumptions fermat.
Check fermat.
