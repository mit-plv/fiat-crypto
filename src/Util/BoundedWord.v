Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.FixedWordSizes.

Definition BoundedWord n (bitwidth : nat)
           (bounds : tuple zrange n) : Type :=
  { x : tuple (wordT (Nat.log2 bitwidth)) n
  | is_bounded_by None bounds
                  (map wordToZ x)}.

Definition BoundedWordToZ n w b (BW :BoundedWord n w b)
  : tuple Z n :=  map wordToZ (proj1_sig BW).
