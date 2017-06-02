Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.FixCoqMistakes.
Import Nat.

Local Open Scope Z.

Class BaseVector (base : list Z):= {
  base_positive : forall b, In b base -> b > 0; (* nonzero would probably work too... *)
  b0_1 : forall x, nth_default x base 0 = 1; (** TODO(jadep,jgross): change to [nth_error base 0 = Some 1], then use [nth_error_value_eq_nth_default] to prove a [forall x, nth_default x base 0 = 1] as a lemma *)
  base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat
}.

Section BaseSystem.
  Context (base : list Z).
  (** [BaseSystem] implements an constrained positional number system.
      A wide variety of bases are supported: the base coefficients are not
      required to be powers of 2, and it is NOT necessarily the case that
      $b_{i+j} = b_i b_j$. Implementations of addition and multiplication are
      provided, with focus on near-optimal multiplication performance on
      non-trivial but small operands: maybe 10 32-bit integers or so. This
      module does not handle carries automatically: if no restrictions are put
      on the use of a [BaseSystem], each digit is unbounded. This has nothing
      to do with modular arithmetic either.
  *)
  Definition digits : Type := list Z.

  Definition accumulate p acc := fst p * snd p + acc.
  Definition decode' bs u  := fold_right accumulate 0 (combine u bs).
  Definition decode := decode' base.
  Definition mul_each u := map (Z.mul u).
End BaseSystem.
