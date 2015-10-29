
Require Import ZArith.
Require Import Bedrock.Word.
Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory.
Require Import Crypto.Galois.ZGaloisField.
Require Import Eqdep_dec.

Module Type BitSpec.
  Parameter wordSize: nat.
  Parameter numWords: nat.
End BitSpec.

Module GFBits (M: Modulus) (Spec: BitSpec).
  Module Field := ZGaloisField M.
  Import Field Spec.
  Local Open Scope GF_scope.
  Local Open Scope list.

  Definition bits {k} (x: word k) := k.

  Definition BinGF := {lst: list (word wordSize) | length lst = numWords}.

  Definition convertWordSize {a b: nat} (x: word a): a = b -> word b.
    intro H; rewrite H in x; exact x.
  Defined.

  Lemma convert_invertible:
    forall (a b: nat) (x: word a) (H1: a = b) (H2: b = a),
      convertWordSize (convertWordSize x H1) H2 = x.
  Proof.
    intros; destruct H2; simpl.
    replace H1 with (eq_refl b); simpl; intuition.
    apply UIP_dec; exact eq_nat_dec.
  Qed.

  Fixpoint splitWords' (sz: nat) (len: nat) (x: word sz): list (word wordSize).
    induction len, (gt_dec sz wordSize).

    - refine nil.

    - refine nil.

    - assert (sz = wordSize + (sz - wordSize))%nat. intuition.
      assert (z := convertWordSize x H).
      refine (
        cons (split1 wordSize (sz - wordSize) z)
             (splitWords' (sz - wordSize)%nat len
               (split2 wordSize (sz - wordSize) z))).

    - assert (sz + (wordSize - sz) = wordSize)%nat. intuition.
      assert (z := convertWordSize (zext x (wordSize - sz)) H).
      refine (cons z nil).

  Admitted.

  Definition splitWords {sz} (len: nat) (x: word sz):
      {x: list (word wordSize) | length x = len}.
    exists (splitWords' sz len x).

    induction len, (gt_dec sz wordSize).
  Admitted.

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

