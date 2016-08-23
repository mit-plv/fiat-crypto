(*** Implementing ℤ-Like via Architecture *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.DoubleBounded.
Require Import Crypto.ModularArithmetic.ZBounded.
Require Import Crypto.Util.Tuple.

Local Open Scope Z_scope.

Section fancy_machine_p256_montgomery_foundation.
  Context {n_over_two : Z}.
  Local Notation n := (2 * n_over_two).
  Context (ops : fancy_machine.instructions n) (modulus : Z).

  Global Instance ZLikeOps_of_ArchitectureBoundedOps (smaller_bound_exp : Z)
    : ZLikeOps (2^n) (2^smaller_bound_exp) modulus :=
    { LargeT := tuple fancy_machine.W 2;
      SmallT := fancy_machine.W;
      modulus_digits := ldi modulus;
      decode_large := decode;
      decode_small := decode;
      Mod_SmallBound v := fst v;
      DivBy_SmallBound v := snd v;
      DivBy_SmallerBound v := shrd (snd v) (fst v) smaller_bound_exp;
      Mul x y := mulhwll (W := tuple _ 2) (sprl x 0) (sprl y 0);
      CarryAdd x y := adc x y false;
      CarrySubSmall x y := subc x y false;
      ConditionalSubtract b x := let v := selc b (ldi modulus) (ldi 0) in snd (subc x v false);
      ConditionalSubtractModulus y := addm y (ldi 0) (ldi modulus) }.
End fancy_machine_p256_montgomery_foundation.
