(*** Montgomery Multiplication *)
(** This file implements the proofs for Montgomery Form, Montgomery
    Reduction, and Montgomery Multiplication on [Z].  We follow
    Wikipedia. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.Structures.Equalities.
Require Import Crypto.ModularArithmetic.Montgomery.Z.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Declare Module Nop : Nop.
Module Import ImportEquivModuloInstances := Z.EquivModuloInstances Nop.

Local Existing Instance eq_Reflexive. (* speed up setoid_rewrite as per https://coq.inria.fr/bugs/show_bug.cgi?id=4978 *)

Local Open Scope Z_scope.

Section montgomery.
  Context (N : Z)
          (N_reasonable : N <> 0)
          (R : Z)
          (R_good : Z.gcd N R = 1).
  Local Notation "x ≡ y" := (Z.equiv_modulo N x y) : type_scope.
  Local Notation "x ≡ᵣ y" := (Z.equiv_modulo R x y) : type_scope.
  Context (R' : Z)
          (R'_good : R * R' ≡ 1).

  Lemma R'_good' : R' * R ≡ 1.
  Proof. rewrite <- R'_good; apply f_equal2; lia. Qed.

  Local Notation to_montgomery_naive := (to_montgomery_naive R) (only parsing).
  Local Notation from_montgomery_naive := (from_montgomery_naive R') (only parsing).

  Lemma to_from_montgomery_naive x : to_montgomery_naive (from_montgomery_naive x) ≡ x.
  Proof.
    unfold Z.to_montgomery_naive, Z.from_montgomery_naive.
    rewrite <- Z.mul_assoc, R'_good'.
    autorewrite with zsimplify; reflexivity.
  Qed.
  Lemma from_to_montgomery_naive x : from_montgomery_naive (to_montgomery_naive x) ≡ x.
  Proof.
    unfold Z.to_montgomery_naive, Z.from_montgomery_naive.
    rewrite <- Z.mul_assoc, R'_good.
    autorewrite with zsimplify; reflexivity.
  Qed.

  (** * Modular arithmetic and Montgomery form *)
  Section general.
    Local Infix "+" := add : montgomery_scope.
    Local Infix "-" := sub : montgomery_scope.
    Local Infix "*" := (mul_naive R') : montgomery_scope.

    Lemma add_correct_naive x y : from_montgomery_naive (x + y) = from_montgomery_naive x + from_montgomery_naive y.
    Proof. unfold Z.from_montgomery_naive, add; lia. Qed.
    Lemma add_correct_naive_to x y : to_montgomery_naive (x + y) = (to_montgomery_naive x + to_montgomery_naive y)%montgomery.
    Proof. unfold Z.to_montgomery_naive, add; autorewrite with push_Zmul; reflexivity. Qed.
    Lemma sub_correct_naive x y : from_montgomery_naive (x - y) = from_montgomery_naive x - from_montgomery_naive y.
    Proof. unfold Z.from_montgomery_naive, sub; lia. Qed.
    Lemma sub_correct_naive_to x y : to_montgomery_naive (x - y) = (to_montgomery_naive x - to_montgomery_naive y)%montgomery.
    Proof. unfold Z.to_montgomery_naive, sub; autorewrite with push_Zmul; reflexivity. Qed.

    Theorem mul_correct_naive x y : from_montgomery_naive (x * y) = from_montgomery_naive x * from_montgomery_naive y.
    Proof. unfold from_montgomery_naive, mul_naive; lia. Qed.
    Theorem mul_correct_naive_to x y : to_montgomery_naive (x * y) ≡ (to_montgomery_naive x * to_montgomery_naive y)%montgomery.
    Proof.
      unfold Z.to_montgomery_naive, mul_naive.
      rewrite <- !Z.mul_assoc, R'_good.
      autorewrite with zsimplify; apply (f_equal2 Z.modulo); lia.
    Qed.
  End general.

  (** * The REDC algorithm *)
  Section redc.
    Context (N' : Z)
            (N'_in_range : 0 <= N' < R)
            (N'_good : N * N' ≡ᵣ -1).

    Lemma N'_good' : N' * N ≡ᵣ -1.
    Proof. rewrite <- N'_good; apply f_equal2; lia. Qed.

    Lemma N'_good'_alt x : (((x mod R) * (N' mod R)) mod R) * (N mod R) ≡ᵣ x * -1.
    Proof.
      rewrite <- N'_good', Z.mul_assoc.
      unfold Z.equiv_modulo; push_Zmod.
      reflexivity.
    Qed.

    Section redc.
      Context (T : Z).

      Local Notation m := (((T mod R) * N') mod R).
      Local Notation prereduce := (prereduce N R N').

      Local Ltac t_fin_correct :=
        unfold Z.equiv_modulo; push_Zmod; autorewrite with zsimplify; reflexivity.

      Lemma prereduce_correct : prereduce T ≡ T * R'.
      Proof.
        transitivity ((T + m * N) * R').
        { unfold Z.prereduce.
          autorewrite with zstrip_div; push_Zmod.
          rewrite N'_good'_alt.
          autorewrite with zsimplify pull_Zmod.
          reflexivity. }
        t_fin_correct.
      Qed.

      Lemma reduce_correct : reduce N R N' T ≡ T * R'.
      Proof.
        unfold reduce.
        break_match; rewrite prereduce_correct; t_fin_correct.
      Qed.

      Lemma partial_reduce_correct : partial_reduce N R N' T ≡ T * R'.
      Proof.
        unfold partial_reduce.
        break_match; rewrite prereduce_correct; t_fin_correct.
      Qed.

      Let m_small : 0 <= m < R. Proof. auto with zarith. Qed.

      Section generic.
        Lemma prereduce_in_range_gen B
        : 0 <= N
          -> 0 <= T <= R * B
          -> 0 <= prereduce T < B + N.
        Proof. unfold Z.prereduce; auto with zarith nia. Qed.
      End generic.

      Section N_very_small.
        Context (N_very_small : 0 <= 4 * N < R).

        Lemma prereduce_in_range_very_small
          : 0 <= T <= (2 * N - 1) * (2 * N - 1)
            -> 0 <= prereduce T < 2 * N.
        Proof. pose proof (prereduce_in_range_gen N); nia. Qed.
      End N_very_small.

      Section N_small.
        Context (N_small : 0 <= 2 * N < R).

        Lemma prereduce_in_range_small
          : 0 <= T <= (2 * N - 1) * (N - 1)
            -> 0 <= prereduce T < 2 * N.
        Proof. pose proof (prereduce_in_range_gen N); nia. Qed.

        Lemma prereduce_in_range_small_fully_reduced
          : 0 <= T <= 2 * N
            -> 0 <= prereduce T <= N.
        Proof. pose proof (prereduce_in_range_gen 1); nia. Qed.
      End N_small.

      Section N_small_enough.
        Context (N_small_enough : 0 <= N < R).

        Lemma prereduce_in_range_small_enough
          : 0 <= T <= R * R
            -> 0 <= prereduce T < R + N.
        Proof. pose proof (prereduce_in_range_gen R); nia. Qed.

        Lemma reduce_in_range_R
          : 0 <= T <= R * R
            -> 0 <= reduce N R N' T < R.
        Proof.
          intro H; pose proof (prereduce_in_range_small_enough H).
          unfold reduce, prereduce in *; break_match; Z.ltb_to_lt; nia.
        Qed.

        Lemma partial_reduce_in_range_R
          : 0 <= T <= R * R
            -> 0 <= partial_reduce N R N' T < R.
        Proof.
          intro H; pose proof (prereduce_in_range_small_enough H).
          unfold partial_reduce, prereduce in *; break_match; Z.ltb_to_lt; nia.
        Qed.
      End N_small_enough.

      Section unconstrained.
        Lemma prereduce_in_range
          : 0 <= T <= R * N
            -> 0 <= prereduce T < 2 * N.
        Proof. pose proof (prereduce_in_range_gen N); nia. Qed.

        Lemma reduce_in_range
        : 0 <= T <= R * N
          -> 0 <= reduce N R N' T < N.
        Proof.
          intro H; pose proof (prereduce_in_range H).
          unfold reduce, prereduce in *; break_match; Z.ltb_to_lt; nia.
        Qed.

        Lemma partial_reduce_in_range
        : 0 <= T <= R * N
          -> Z.min 0 (R - N) <= partial_reduce N R N' T < 2 * N.
        Proof.
          intro H; pose proof (prereduce_in_range H).
          unfold partial_reduce, prereduce in *; break_match; Z.ltb_to_lt;
            apply Z.min_case_strong; nia.
        Qed.
      End unconstrained.
    End redc.

    (** * Arithmetic in Montgomery form *)
    Section arithmetic.
      Local Infix "*" := (mul N R N') : montgomery_scope.

      Local Notation to_montgomery := (to_montgomery N R N').
      Local Notation from_montgomery := (from_montgomery N R N').
      Lemma to_from_montgomery a : to_montgomery (from_montgomery a) ≡ a.
      Proof.
        unfold Z.to_montgomery, Z.from_montgomery.
        transitivity ((a * 1) * 1); [ | apply f_equal2; lia ].
        rewrite <- !R'_good, !reduce_correct.
        unfold Z.equiv_modulo; push_Zmod; pull_Zmod.
        apply f_equal2; lia.
      Qed.
      Lemma from_to_montgomery a : from_montgomery (to_montgomery a) ≡ a.
      Proof.
        unfold Z.to_montgomery, Z.from_montgomery.
        rewrite !reduce_correct.
        transitivity (a * ((R * (R * R' mod N) * R') mod N)).
        { unfold Z.equiv_modulo; push_Zmod; pull_Zmod.
          apply f_equal2; lia. }
        { repeat first [ rewrite R'_good
                       | reflexivity
                       | push_Zmod; pull_Zmod; progress autorewrite with zsimplify
                       | progress unfold Z.equiv_modulo ]. }
      Qed.

      Theorem mul_correct x y : from_montgomery (x * y) ≡ from_montgomery x * from_montgomery y.
      Proof.
        unfold Z.from_montgomery, mul.
        rewrite !reduce_correct; apply f_equal2; lia.
      Qed.
      Theorem mul_correct_to x y : to_montgomery (x * y) ≡ (to_montgomery x * to_montgomery y)%montgomery.
      Proof.
        unfold Z.to_montgomery, mul.
        rewrite !reduce_correct.
        transitivity (x * y * R * 1 * 1 * 1);
          [ rewrite <- R'_good at 1
          | rewrite <- R'_good at 1 2 3 ];
          autorewrite with zsimplify;
          unfold Z.equiv_modulo; push_Zmod; pull_Zmod.
        { apply f_equal2; lia. }
        { apply f_equal2; lia. }
      Qed.
    End arithmetic.
  End redc.
End montgomery.

Module Import LocalizeEquivModuloInstances := Z.RemoveEquivModuloInstances Nop.
