(*** Implementing Large Bounded Arithmetic via pairs *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).

Section with_single_ops.
  Section single.
    Context (n : size) {base_ops : ArchitectureBoundedOps n}.

    Definition ripple_carry {T} (f : bool -> T -> T -> bool * T)
               (carry : bool) (xs ys : list T) : bool * list T
      := List.fold_right
           (fun x_y carry_zs => let '(x, y) := eta x_y in
                                let '(carry, zs) := eta carry_zs in
                                let '(carry, z) := eta (f carry x y) in
                                (carry, z :: zs))
           (carry, nil)
           (List.combine xs ys).

    Definition two_list_to_tuple {A B} (x : A * list B)
      := match x return match x with
                        | (a, [b0; b1]) => A * (B * B)
                        | _ => True
                        end
         with
         | (a, [b0; b1]) => (a, (b0, b1))
         | _ => I
         end.

    Local Instance DoubleArchitectureBoundedOps : ArchitectureBoundedOps (2 * n)%nat
      := { BoundedType := BoundedType * BoundedType (* [(high, low)] *);
           decode high_low := (decode (fst high_low) * 2^n + decode (snd high_low))%Z;
           encode z := (encode (z / 2^n), encode (z mod 2^n));
           ShiftRight a high_low
           := let '(high, low) := eta high_low in
              if n <=? a then
                (ShiftRight (a - n)%nat (encode 0, fst high), ShiftRight (a - n)%nat high)
              else
                (ShiftRight a (snd high, fst low), ShiftRight a low);
           ShiftLeft a high_low
           := let '(high, low) := eta high_low in
              if 2 * n <=? a then
                let '(high0, low) := eta (ShiftLeft (a - 2 * n)%nat low) in
                let '(high_high, high1) := eta (ShiftLeft (a - 2 * n)%nat high) in
                ((snd (CarryAdd false high0 high1), low), (encode 0, encode 0))
              else if n <=? a then
                     let '(high0, low) := eta (ShiftLeft (a - n)%nat low) in
                     let '(high_high, high1) := eta (ShiftLeft (a - n)%nat high) in
                     ((high_high, snd (CarryAdd false high0 high1)), (low, encode 0))
                   else
                     let '(high0, low) := eta (ShiftLeft a low) in
                     let '(high_high, high1) := eta (ShiftLeft a high) in
                     ((encode 0, high_high), (snd (CarryAdd false high0 high1), low));
           Mod2Pow a high_low
           := let '(high, low) := (fst high_low, snd high_low) in
              (Mod2Pow (a - n)%nat high, Mod2Pow a low);
           CarryAdd carry x_high_low y_high_low
           := let '(xhigh, xlow) := eta x_high_low in
              let '(yhigh, ylow) := eta y_high_low in
              two_list_to_tuple (ripple_carry CarryAdd carry [xhigh; xlow] [yhigh; ylow]);
           CarrySub carry x_high_low y_high_low
           := let '(xhigh, xlow) := eta x_high_low in
              let '(yhigh, ylow) := eta y_high_low in
              two_list_to_tuple (ripple_carry CarrySub carry [xhigh; xlow] [yhigh; ylow]) }.

    Definition BoundedOfHalfBounded (x : @BoundedHalfType (2 * n)%nat _) : @BoundedType n _
      := match x with
         | UpperHalf x => fst x
         | LowerHalf x => snd x
         end.

    Local Instance DoubleArchitectureBoundedHalfWidthMulOpsOfFullMulOps
          {base_mops : ArchitectureBoundedFullMulOps n}
      : ArchitectureBoundedHalfWidthMulOps (2 * n)%nat :=
      { HalfWidthMul a b
        := Mul (BoundedOfHalfBounded a) (BoundedOfHalfBounded b) }.
  End single.

  Local Existing Instance DoubleArchitectureBoundedOps.

  Section full_from_half.
    Context (n : size) {base_ops : ArchitectureBoundedOps (2 * n)%nat}.

    Local Infix "*" := HalfWidthMul.

    Local Instance DoubleArchitectureBoundedFullMulOpsOfHalfWidthMulOps
          {base_mops : ArchitectureBoundedHalfWidthMulOps (2 * n)%nat}
      : ArchitectureBoundedFullMulOps (2 * n)%nat :=
      { Mul a b
        := let '(a1, a0) := (UpperHalf a, LowerHalf a) in
           let '(b1, b0) := (UpperHalf b, LowerHalf b) in
           let out := a0 * b0 in
           let outHigh := a1 * b1 in
           let tmp := a1 * b0 in
           let '(carry, out) := eta (CarryAdd false out (snd (ShiftLeft n tmp))) in
           let '(_, outHigh) := eta (CarryAdd carry outHigh (ShiftRight n (encode 0, tmp))) in
           let tmp := a0 * b1 in
           let '(carry, out) := eta (CarryAdd false out (snd (ShiftLeft n tmp))) in
           let '(_, outHigh) := eta (CarryAdd carry outHigh (ShiftRight n (encode 0, tmp))) in
           (outHigh, out) }.
  End full_from_half.

  Local Existing Instance DoubleArchitectureBoundedFullMulOpsOfHalfWidthMulOps.
End with_single_ops.
