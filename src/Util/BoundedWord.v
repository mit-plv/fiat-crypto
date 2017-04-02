Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.FixedWordSizes.

Definition BoundedWord n (bitwidth : nat)
           (bounds : tuple zrange n) : Type :=
  { x : tuple (wordT bitwidth) n
  | is_bounded_by (Some (Z.of_nat bitwidth)) bounds
                  (map wordToZ x)}.

Definition BoundedWordToZ n w b (BW :BoundedWord n w b)
  : tuple Z n :=  map wordToZ (proj1_sig BW).
