(*** Implementing ℤ-Like via Architecture *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.BoundedArithmetic.StripCF.
Require Import Crypto.ModularArithmetic.ZBounded.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Section x86_gen_barrett_foundation.
  Context (full_width : nat) (n : nat) (ops : x86.instructions n) (modulus : Z).
  Local Notation W := (repeated_tuple x86.W 2 (Nat.log2 (full_width / n))). (* full_width-width words *)

  Local Instance ZLikeOps_of_x86_gen_Factored (smaller_bound_exp : Z)
        (ldi_modulus ldi_0 : W)
    : ZLikeOps (2^full_width) (2^smaller_bound_exp) modulus
    := { LargeT := tuple W 2;
         SmallT := W;
         modulus_digits := ldi_modulus;
         decode_large := decode;
         decode_small := decode;
         Mod_SmallBound v := fst v;
         DivBy_SmallBound v := snd v;
         DivBy_SmallerBound v := if smaller_bound_exp =? n
                                 then snd v
                                 else dlet v := v in shrd (snd v) (fst v) smaller_bound_exp;
         Mul x y := muldw x y;
         CarryAdd x y := adc x y false;
         CarrySubSmall x y := subc x y false;
         ConditionalSubtract b x := let v := selc b (ldi_modulus) (ldi_0) in snd (subc x v false);
         ConditionalSubtractModulus y := let '(CF, _) := subc y ldi_modulus false in
                                         let maybe_modulus := ldi_0 in
                                         let maybe_modulus := selc CF maybe_modulus ldi_modulus in
                                         let '(CF, y) := subc y maybe_modulus false in
                                         y }.

  Local Instance ZLikeOps_of_x86_gen (smaller_bound_exp : Z)
    : ZLikeOps (2^full_width) (2^smaller_bound_exp) modulus :=
    @ZLikeOps_of_x86_gen_Factored smaller_bound_exp (ldi modulus) (ldi 0).
End x86_gen_barrett_foundation.

Section x86_64_barrett_foundation.
  Local Notation n := 64%nat.
  Context (ops : x86.instructions n) (modulus : Z).
  Local Notation W := (tuple (tuple x86.W 2) 2) (* 256-bit words *).

  Local Instance ZLikeOps_of_x86_64_Factored (smaller_bound_exp : Z)
        ldi_modulus ldi_0
    : ZLikeOps (2^256) (2^smaller_bound_exp) modulus
    := @ZLikeOps_of_x86_gen_Factored 256 n ops modulus smaller_bound_exp ldi_modulus ldi_0.
  Global Instance ZLikeOps_of_x86_64 (smaller_bound_exp : Z)
    : ZLikeOps (2^256) (2^smaller_bound_exp) modulus :=
    @ZLikeOps_of_x86_64_Factored smaller_bound_exp (ldi modulus) (ldi 0).
End x86_64_barrett_foundation.

Section x86_32_barrett_foundation.
  Local Notation n := 32%nat.
  Context (ops : x86.instructions n) (modulus : Z).
  Local Notation W := (tuple (tuple (tuple x86.W 2) 2) 2) (* 256-bit words *).

  Local Instance ZLikeOps_of_x86_32_Factored (smaller_bound_exp : Z)
        ldi_modulus ldi_0
    : ZLikeOps (2^256) (2^smaller_bound_exp) modulus
    := @ZLikeOps_of_x86_gen_Factored 256 n ops modulus smaller_bound_exp ldi_modulus ldi_0.
  Global Instance ZLikeOps_of_x86_32 (smaller_bound_exp : Z)
    : ZLikeOps (2^256) (2^smaller_bound_exp) modulus :=
    @ZLikeOps_of_x86_32_Factored smaller_bound_exp (ldi modulus) (ldi 0).
End x86_32_barrett_foundation.
