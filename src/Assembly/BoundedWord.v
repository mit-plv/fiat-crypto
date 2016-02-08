
Require Import Bedrock.Word.
Require Import NArith PArith Ndigits Compare_dec.
Require Import ProofIrrelevance.
Require Import Ring.

Section BoundedWord.

  Delimit Scope Bounded_scope with bounded.

  Open Scope Bounded_scope.

  (* First, we make our BoundedWord sigma type *)
  Definition wordGeN {n: nat} (a: word n) (b: N): Prop :=
    (wordToN a >= b)%N.

  Definition wordLeN {n: nat} (a: word n) (b: N): Prop :=
    (wordToN a <= b)%N.

  Notation "A >= B" := (wordGeN A B) (at level 70) : Bounded_scope.
  Notation "A <= B" := (wordLeN A B) (at level 70) : Bounded_scope.

  Inductive BoundOn {n: nat} (x: word n) : Prop :=
    | boundBy: forall low high: N, x >= low -> x <= high -> BoundOn x.

  Lemma low_word_bound: forall n (x : word n), x >= 0.
    intros; unfold wordGeN;
      try (apply N.le_ge; apply N.le_0_l);
      rewrite wordToN_nat.
  Qed.

  Lemma high_word_bound: forall n (x : word n), x <= Npow2 n.
    intros; unfold wordLeN; rewrite wordToN_nat.

    assert (B := wordToNat_bound (x));
      rewrite <- Npow2_nat in B;
      apply nat_compare_lt in B.

    unfold N.le; intuition;
      rewrite N2Nat.inj_compare in H;
      rewrite Nat2N.id in H;
      rewrite B in H;
      inversion H.
  Qed.

  (* We start with the functions bound and unbound *)
  Definition bound {n: nat} (x: word n) :=
    boundBy x 0 (Npow2 n) (low_word_bound n x) (high_word_bound n x).

  Definition unbound {n: nat} {x: word n} (b: BoundOn x) := x.

  Lemma bound_inv: forall (n: nat) (x: word n), x = unbound (bound x).
    intros; unfold unbound; intuition.
  Qed.

  Lemma bound_eq: forall (n: nat) (a b: word n), unbound (bound a) = unbound (bound b) -> a = b.
    intros; repeat rewrite <- bound_inv in H; intuition.
  Qed.

  Definition above {n: nat} {x: word n} {low: N} (H: x >= low) :=
    boundBy x low (Npow2 n) H (high_word_bound n x).

  Definition below {n: nat} {x: word n} {high: N} (H: x <= high) :=
    boundBy x 0%N high (low_word_bound n x) H.

  Definition intersect {n: nat} {x: word n} (A: BoundOn x) (B: BoundOn x): BoundOn x :=
    match A with
    | boundBy low0 high0 lb0 hb0 =>
      match B with
      | boundBy low1 high1 lb1 hb1 =>
        match (low0 ?= low1)%N with
        | Eq => 
          match (high0 ?= high1)%N with
          | Eq =>  boundBy x low0 high0 lb0 hb0
          | Lt =>  boundBy x low0 high0 lb0 hb0
          | Gt =>  boundBy x low0 high1 lb0 hb1
          end
        | Gt => 
          match (high0 ?= high1)%N with
          | Eq =>  boundBy x low0 high0 lb0 hb0
          | Lt =>  boundBy x low0 high0 lb0 hb0
          | Gt =>  boundBy x low0 high1 lb0 hb1
          end
        | Lt => 
          match (high0 ?= high1)%N with
          | Eq =>  boundBy x low1 high0 lb1 hb0
          | Lt =>  boundBy x low1 high0 lb1 hb0
          | Gt =>  boundBy x low1 high1 lb1 hb1
          end
        end
      end
    end.

  Lemma replace_intersect {n: nat} {x: word n} (new: BoundOn x):
      forall (old: BoundOn x), old = intersect old new.
    intros; apply proof_irrelevance.
  Qed.

  (* Get inequalities from definitions *)
  Lemma wand_upper_l: forall (n: nat) (x a b: word n), x = wand a b -> x <= (2 * wordToN a)%N.
    admit.
  Qed.

  Lemma wand_upper_r: forall (n: nat) (x a b: word n), x = wand a b -> x <= (2 * wordToN b)%N.
    admit.
  Qed.


  Definition wand_bound_l {n: nat} {x a b: word n} (H: x = wand a b): BoundOn x :=
    below (wand_upper_l n x a b H).

  Definition wand_bound_r {n: nat} {x a b: word n} (H: x = wand a b): BoundOn x :=
    below (wand_upper_r n x a b H).

  Definition zero_dec (x: N): {(x = 0)%N} + {(x > 0)%N}.
    intros; unfold N.gt;
      assert (Z := N.compare_0_r x);
      assert ({x ?= 0 = Eq} + {x ?= 0 = Gt})%N by (induction (x ?= 0)%N; abstract intuition).

    inversion H.

    - left; abstract (
        unfold N.compare in H0;
        destruct x; inversion H0;
        simpl; intuition ).

    - abstract intuition.

  Qed.

  Lemma NToWord_inv: forall (n: nat) (x: word n), x = NToWord n (wordToN x).
    intros; rewrite NToWord_nat, wordToN_nat.
    rewrite Nat2N.id.
    rewrite natToWord_wordToNat; intuition.
  Qed.

  Lemma replace_zero: forall (n: nat) (x: word n), (x <= 0%N) -> x = NToWord n 0.
    intros; unfold wordLeN in H.

    assert (wordToN x = 0)%N by (
      induction (zero_dec (wordToN x));
      unfold N.le, N.gt in *; intuition).

    rewrite <- H0; rewrite <- NToWord_inv; intuition.
  Qed.

  Lemma Npow2_nonzero: forall (n: nat), (Npow2 n <> 0)%N.
    intros; induction n; simpl; intuition.

    - inversion H.
    - apply IHn; induction (Npow2 n); intuition.
      inversion H.
  Qed.

  (* Essential operations on bounded words *)
  Definition bplus {n: nat} {x y: word n} (A: BoundOn x) (B: BoundOn y): BoundOn (wplus x y).
    destruct A as [low0 high0 lb0 hb0], B as [low1 high1 lb1 hb1].

    induction (zero_dec high0), (zero_dec high1).

    - apply (boundBy (x ^+ y) 0%N 0%N); admit.

    - apply (boundBy (x ^+ y) low1 high1); admit.

    - apply (boundBy (x ^+ y) low0 high0); admit.

    - apply (boundBy (x ^+ y) (low0 + low1)%N (high0 + high1)%N); admit.
      (* rewrite wplus_alt;
         unfold wplusN, wordGeN, wordBinN in *; simpl;
           rewrite wordToN_nat, wordToNat_natToWord_idempotent;
           rewrite Nat2N.inj_add; repeat rewrite <- wordToN_nat.*)
  Defined.

  Definition bmult {n: nat} {x y: word n} (A: BoundOn x) (B: BoundOn y): BoundOn (wmult x y).
    destruct A as [low0 high0 lb0 hb0], B as [low1 high1 lb1 hb1].
    apply (boundBy (x ^* y) (low0 * low1)%N (high0 * high1)%N); admit.
      (* rewrite wmult_alt;
        unfold wmultN, wordLeN, wordBinN in *; simpl;
        rewrite wordToN_nat, wordToNat_natToWord_idempotent;
        rewrite Nat2N.inj_mul; repeat rewrite <- wordToN_nat. *)
  Defined.

  (* Operation replacements *)
  Lemma bound_plus: forall (n: nat) (a b: word n), bound (wplus a b) = bplus (bound a) (bound b).
    intros; apply proof_irrelevance.
  Qed.

  Lemma bound_mult: forall (n: nat) (a b: word n), bound (wmult a b) = bmult (bound a) (bound b).
    intros; apply proof_irrelevance.
  Qed.

  (* Tactics to repeatedly apply the simplification strategy *)
  Ltac convert_to_bounded :=
    apply bound_eq;
    repeat first [rewrite bound_plus | rewrite bound_mult].

  Ltac propagate_bounds :=
    match goal with
    | [H : ?x = wzero _ ^& _ |- _] =>
      rewrite (replace_intersect (wand_bound_l H) (bound x))
    | _ => fail
    end.

  Ltac match_match :=
    repeat (
      match goal with
      | [|- context[match (zero_dec ?x) with | _ => _ end]] => destruct (zero_dec x)
      | [|- context[match (N.compare ?x ?y) with | _ => _ end]] => destruct (N.compare x y)
      | [|- context[sumbool_ind _ _ _ (zero_dec ?x)]] => destruct (zero_dec x)
      end; subst).

  (* Miscellaneous simplifications we'll need *)
  Ltac word_simpl :=
    repeat (
      match goal with
      | [|- context [unbound _]] => unfold unbound
      (*| [ H: (Npow2 ?x = 0)%N |- _] =>
        let Z := fresh in
          apply (Npow2_nonzero x) in H; intuition *)
      | [ H: (?x <= 0) |- _] =>
        unfold wordLeN in H;
        apply replace_zero in H;
        rewrite H; clear H
      | _ => fail 
      end; subst);
    simpl; intuition.

  Ltac unfold_ops := 
    unfold intersect, below, above,
           bound, bplus, bmult,
           wand_bound_l, wand_bound_r.

  (* The full tactic *)
  Ltac bound_simpl:=
    convert_to_bounded;
    propagate_bounds;
    unfold_ops;
    repeat match_match;
    word_simpl.

  (* Example Lemma *)

  Lemma example_bound_simpl: forall (n: nat) (a b: word n),
    a = wand (wzero n) b -> b = a ^+ b.
  Proof.
    intros.
    convert_to_bounded.
    propagate_bounds.
    unfold_ops; simpl.
    match_match; word_simpl.
  Qed.

End BoundedWord.