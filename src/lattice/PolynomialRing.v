Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.lattice.WeightedMultiplication.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Local Open Scope Z_scope.

Module PolynomialRing.
  Section PolynomialRing.
    Context {n : nat} {q : BinNums.positive}.

    Instance weighted_mul_pre : @weighted_mul_preconditions (F q) nat.
    Proof.
      eapply Build_weighted_mul_preconditions with (lop := Nat.add) (lid := 0%nat) (index_to_loc := id) (loc_to_index := id); try reflexivity; try (repeat econstructor; repeat intro; omega).
      { apply F.commutative_ring_modulo. }
      { intros. cbn. apply le_plus_l. }
    Defined.

    Definition Rq : Type := tuple (F q) n.
    Definition zero : Rq := repeat 0%F n.
    Definition one : Rq := (from_associational n ((1%F, 0%nat) :: nil)).
    Definition opp : Rq -> Rq := map F.opp.
    Definition add : Rq -> Rq -> Rq := map2 cadd.
    Definition sub : Rq -> Rq -> Rq := fun p q => add p (opp q).
    Definition mul : Rq -> Rq -> Rq :=
      fun p q => from_associational n (mul (to_associational p) (to_associational q)).

    Hint Rewrite @map_append @map2_append @Tuple.repeat_append : pull_append.
    Hint Rewrite (@associative (F q)) (@left_identity (F q)) (@right_identity (F q)) (@left_inverse (F q))
         using (apply F.commutative_ring_modulo): fsimpl.
    Hint Rewrite mul_trim_high_l mul_trim_high_r mul_assoc from_associational_mul_one from_associational_to_associational : push_assoc.
    Hint Resolve from_associational_mul_comm mul_add_distr_l.
    Local Ltac simplify :=  cbv [Rq zero one opp add sub mul] in *; change 1%F with cone; change 0%nat with lid; autorewrite with push_assoc.
    Local Ltac obvious :=
      simplify; match goal with
                | _ => auto; reflexivity
                | _ => Tuple.induct n; [ reflexivity | ]; autorewrite with pull_append fsimpl;
                       ( congruence || rewrite commutative; congruence)
                end.

    Lemma add_assoc x y z : add x (add y z) = add (add x y) z.                Proof. obvious. Qed.
    Lemma add_comm x y : add x y = add y x.                                   Proof. obvious. Qed.
    Lemma add_zero_l x : add zero x = x.                                      Proof. obvious. Qed.
    Lemma add_opp_l x : add (opp x) x = zero.                                 Proof. obvious. Qed.
    Lemma mul_assoc x y z : mul x (mul y z) = mul (mul x y) z.                Proof. obvious. Qed.
    Lemma mul_comm x y : mul x y = mul y x.                                   Proof. obvious. Qed.
    Lemma mul_one_r x : mul x one = x.                                        Proof. obvious. Qed.
    Lemma mul_add_distr_l a b c : mul a (add b c) = add (mul a b) (mul a c). Proof. obvious. Qed.
    Local Hint Resolve add_assoc add_comm add_zero_l add_opp_l mul_assoc mul_one_r mul_add_distr_l.

    (* Proofs that follow from commutativity *)
    Lemma add_zero_r x : add x zero = x.       Proof. rewrite add_comm; auto. Qed.
    Lemma add_opp_r x : add x (opp x) = zero.  Proof. rewrite add_comm; auto. Qed.
    Lemma mul_one_l x : mul one x = x.         Proof. rewrite mul_comm; auto. Qed.
    Lemma mul_add_distr_r a b c : mul (add b c) a = add (mul b a) (mul c a).
    Proof. rewrite !(mul_comm _ a); auto. Qed.
    Local Hint Resolve add_zero_r add_opp_r mul_one_l mul_add_distr_r.

    Lemma Rq_ring : @ring Rq eq zero one opp add sub mul.
    Proof. repeat econstructor; auto; try congruence. Qed.
  End PolynomialRing.
End PolynomialRing.