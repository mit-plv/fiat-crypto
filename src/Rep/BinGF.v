
Require Import ZArith.
Require Import Bedrock.Word.
Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory.
Require Import Crypto.Galois.ZGaloisField.
Require Import Eqdep_dec.

Module Type BitSpec.
  Parameter wordSize: nat.
  Parameter numWords: nat.

  Axiom wordSize_pos : (wordSize > 0)%nat.
End BitSpec.

Module GFBits (M: Modulus) (Spec: BitSpec).
  Module Field := ZGaloisField M.
  Import Field Spec.
  Local Open Scope GF_scope.
  Local Open Scope list.

  Definition bits {k} (x: word k) := k.

  Definition BinGF := {lst: list (word wordSize) | length lst = numWords}.

  Definition splitGt {n m} {H : (n > m)%nat} (w : word n) : word m * word (n - m).
  Proof.
    refine (let w' := match _ : (n = m + (n - m))%nat in _ = N return word N with
                     | eq_refl => w
                     end in
            (split1 m (n - m) w', split2 m (n - m) w'));
    abstract omega.
  Defined.

  Fixpoint copies {A} (x : A) (n : nat) : list A :=
    match n with
    | O => nil
    | S n' => x :: copies x n'
    end.

  Definition splitWords' : forall (len : nat) {sz: nat} (x: word sz), list (word wordSize).
  Proof.
    refine (fix splitWords' (len : nat) {sz : nat} (w : word sz) {struct len} : list (word wordSize) :=
              match len with
              | O => nil
              | S len' =>
                if gt_dec sz wordSize
                then let (w1, w2) := splitGt w in
                     w1 :: splitWords' len' w2
                else match _ in _ = N return list (word N) with
                      | eq_refl => zext w (wordSize - sz) :: copies (wzero _) len'
                     end
              end)%nat; clear splitWords'; abstract omega.
  Defined.

  Lemma length_cast : forall A (F : A -> Type) x1 x2 (pf : x1 = x2) x xs,
    length (match pf in _ = X return list (F X) with
            | eq_refl => x :: xs
            end) = S (length xs).
  Proof.
    destruct pf; auto.
  Qed.

  Lemma length_copies : forall A (x : A) n, length (copies x n) = n.
  Proof.
    induction n; simpl; auto.
  Qed.

  Hint Rewrite length_cast length_copies.

  Lemma length_splitWords' : forall len sz (w : word sz), length (splitWords' len w) = len.
  Proof.
    induction len; simpl; intuition;
    match goal with
    | [ |- context[match ?E with _ => _ end] ] => destruct E
    end; simpl; try rewrite IHlen; autorewrite with core; reflexivity.
  Qed.    

  Definition splitWords {sz} (len: nat) (x: word sz):
    {x: list (word wordSize) | length x = len}.
  Proof.
    exists (splitWords' len x); apply length_splitWords'.
  Defined.

  Definition splitGF (x: GF) :=
    splitWords numWords (NToWord (numWords * wordSize)%nat (Z.to_N (proj1_sig x))).

  Fixpoint combineAll' (b: list (word wordSize)): word (wordSize * (length b)).
    induction b.

    - simpl.
      replace (wordSize * 0)%nat with 0%nat; intuition.
      exact (natToWord 0 0).

    - replace (wordSize * length (a :: b))%nat
        with (wordSize + wordSize * length b)%nat.
      + exact (combine a IHb).
      + simpl; rewrite mult_succ_r; intuition.
  Defined.

  Definition combineAll (b: BinGF): GF :=
    inject (Z.of_N (wordToN (combineAll' (proj1_sig b)))).

  Definition binEquiv a b := combineAll a = combineAll b.

  Lemma combine_split:
    forall (x: GF) (len: nat),
    combineAll (splitGF x) = x.
  Admitted.

  Record unaryOp: Set := mkUnary {
    f : GF -> GF;
    binF : BinGF -> BinGF;

    unaryCompat : forall (a b: GF),
      a = b -> f a = f b;

    unaryBinCompat : forall (a b: BinGF),
      binEquiv a b -> binEquiv (binF a) (binF b);

    unaryCorrect: forall (a: GF),
      f a = combineAll (binF (splitGF a))
  }.

  Record binaryOp: Set := mkBinary {
    g : GF -> GF -> GF;
    binG : BinGF -> BinGF -> BinGF;

    binaryCompat : forall (a b c d: GF),
      a = b -> c = d -> g a c = g b d;

    binaryBinCompat : forall (a b c d: BinGF),
      binEquiv a b -> binEquiv c d ->
      binEquiv (binG a c) (binG b d);

    binaryCorrect: forall (a b: GF),
      g a b = combineAll (binG (splitGF a) (splitGF b))
  }.

End GFBits.
