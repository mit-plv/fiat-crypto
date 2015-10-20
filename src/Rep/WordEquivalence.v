
Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory.

Module GFBits (M: Modulus).
  Module T := GaloisTheory Modulus31.
  Import M T T.Field.
  Local Open Scope GF_scope.

  Definition wordSize: nat := 32.
  Definition bits {k} (word k) := k.

  (* I think we shouldn't fix this, but rather have a lemma for how
   * many bits we need to represent a given prime *)
  Definition numWords: nat :=
    let b := (bits (NtoWord (Z.to_N modulus)))
    in (1 + b / 32)%nat.

  Definition BinGF :=
    {lst: list (word wordSize) | length lst = numWords}.

  Fixpoint splitWords {sz} (len: nat) (x: word sz): {x: list (word wordSize) | length x = len} :=
    match len with
    | O => []
    | S len' =>
      if(sz - wordSize > 0)
      then Cons (split1 wordSize (sz - wordSize) x)
                (words len' (split2 wordSize (sz - wordSize) x))
      else zext x wordSize
    end.

  Fixpoint combineAll (b: BinGF) :=
    match (proj1_sig b) with
    | [] => natToWord 0
    | Cons x xs => combine x (combineAll xs)
    end.

  Definition toZ (b: BinGF) := Z.of_N (wordToN (combineAll b)).
  Definition toGF (b: BinGF) := ZToGF ((toZ b) mod modulus)

  Definition fromZ (x: Z) := splitWords numWords (NToWord (Z.to_N x))
  Definition fromGF (x: GF) := fromZ (proj1_sig x).

  Inductive BinEquiv (x: GF) (y: BinGF) :=
  | EquivGF : forall x, BinEquiv x (fromGF x)
  | EquivBin : forall y, BinEquiv (toGF y) y
  | EquivPlus : forall x1 y1 x2 y2,
    BinEquiv x1 y1 -> binEquiv x2 y2 -> BinEquiv (x1 + x2) (y1 ^+ y2)%word
  | EquivMinus : forall x1 y1 x2 y2,
    BinEquiv x1 y1 -> binEquiv x2 y2 -> BinEquiv (x1 - x2) (y1 ^- y2)%word
  | EquivMult : forall x1 y1 x2 y2,
    BinEquiv x1 y1 -> binEquiv x2 y2 -> BinEquiv (x1 * x2) (y1 ^* y2)%word.

  Lemma equivalent_GF : BinEquiv x y <-> x = toGF y.
  Admitted.

  Lemma equivalent_word : BinEquiv x y <-> weq y (fromGF x).
  Admitted.
End GFBits.
