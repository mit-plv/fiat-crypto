(*** Implementing ℤ-Like via Architecture *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.DoubleBounded.
Require Import Crypto.ModularArithmetic.ZBounded.

Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.

Local Existing Instances DoubleArchitectureBoundedOps DoubleArchitectureBoundedFullMulOpsOfHalfWidthMulOps DoubleArchitectureBoundedHalfWidthMulOpsOfFullMulOps.

Section ops.
  Context {n_over_two : size}.
  Local Notation n := (2 * n_over_two)%nat.
  Context (ops : ArchitectureBoundedOps n) (mops : ArchitectureBoundedHalfWidthMulOps n)
          (modulus : Z).

  Axiom admit : forall {T}, T.

  Global Instance ZLikeOps_of_ArchitectureBoundedOps (smaller_bound_exp : size)
    : ZLikeOps (2^n) (2^smaller_bound_exp) modulus :=
    { LargeT := @BoundedType (2 * n)%nat _;
      SmallT := @BoundedType n _;
      modulus_digits := encode modulus;
      decode_large := decode;
      decode_small := decode;
      Mod_SmallBound v := snd v;
      DivBy_SmallBound v := fst v;
      DivBy_SmallerBound v := ShiftRight smaller_bound_exp v;
      Mul x y := @Interface.Mul n _ _ x y;
      CarryAdd x y := Interface.CarryAdd false x y;
      CarrySubSmall x y := Interface.CarrySub false x y;
      ConditionalSubtract b x := admit;
      ConditionalSubtractModulus y := admit }.
End ops.
