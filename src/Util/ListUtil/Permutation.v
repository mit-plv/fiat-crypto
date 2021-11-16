Require Import Coq.NArith.NArith.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Tactics.BreakMatch.
Import ListNotations.

Lemma Permutation_partition {A} (l : list A) f :
    Permutation.Permutation l (fst (partition f l) ++ snd (partition f l)).
Proof using Type.
  induction l; cbn; break_match; cbn in *; eauto.
  etransitivity. econstructor. eassumption.
  eapply Permutation.Permutation_middle.
Qed.

Global Instance fold_right_Proper_commutative_associative_Permutation {A op}
       (Hcomm : forall x y, op x y = op y x)
       (Hassoc : forall x y z, op x (op y z) = op (op x y) z)
  : Proper (eq ==> @Permutation A ==> eq) (fold_right op) | 1000.
Proof using Type.
  intros init init' <- xs ys; induction 1; cbn;
    rewrite ?Hassoc;
    repeat match goal with
           | [ |- context[op ?x ?y] ]
             => lazymatch goal with
                | [ |- context[op y x] ]
                  => rewrite (Hcomm x y)
                end
           end;
    try reflexivity;
    try now repeat match goal with H : _ |- _ => rewrite H; clear H end.
Qed.

Module Nat.
  Global Instance fold_right_Proper_Permutation_add
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Nat.add) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Nat.add_comm | hnf; apply Nat.add_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_mul
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Nat.mul) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Nat.mul_comm | hnf; apply Nat.mul_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_land
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Nat.land) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Nat.land_comm | hnf; apply Nat.land_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_lor
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Nat.lor) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Nat.lor_comm | hnf; apply Nat.lor_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_lxor
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Nat.lxor) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Nat.lxor_comm | hnf; intros; symmetry; apply Nat.lxor_assoc ]. Qed.
End Nat.

Module N.
  Global Instance fold_right_Proper_Permutation_add
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right N.add) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply N.add_comm | hnf; apply N.add_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_mul
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right N.mul) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply N.mul_comm | hnf; apply N.mul_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_land
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right N.land) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply N.land_comm | hnf; apply N.land_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_lor
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right N.lor) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply N.lor_comm | hnf; apply N.lor_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_lxor
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right N.lxor) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply N.lxor_comm | hnf; intros; symmetry; apply N.lxor_assoc ]. Qed.
End N.

Module Z.
  Global Instance fold_right_Proper_Permutation_add
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Z.add) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Z.add_comm | hnf; apply Z.add_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_mul
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Z.mul) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Z.mul_comm | hnf; apply Z.mul_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_land
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Z.land) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Z.land_comm | hnf; apply Z.land_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_lor
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Z.lor) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Z.lor_comm | hnf; apply Z.lor_assoc ]. Qed.

  Global Instance fold_right_Proper_Permutation_lxor
  : Proper (eq ==> @Permutation _ ==> eq) (fold_right Z.lxor) | 100.
  Proof using Type. apply fold_right_Proper_commutative_associative_Permutation; [ hnf; apply Z.lxor_comm | hnf; intros; symmetry; apply Z.lxor_assoc ]. Qed.
End Z.
