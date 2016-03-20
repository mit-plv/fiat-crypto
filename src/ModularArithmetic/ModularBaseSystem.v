Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystem Crypto.ModularArithmetic.PseudoMersenneBaseParams Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs Crypto.ModularArithmetic.ExtendedBaseVector.
Local Open Scope Z_scope.

Section PseudoMersenneBase.
  Context `{prm :PseudoMersenneBaseParams}.
  Existing Instance bv.
  
  Definition decode (us : digits) : F modulus := ZToField (BaseSystem.decode base us).
  
  Definition rep (us : digits) (x : F modulus) := (length us <= length base)%nat /\ decode us = x.
  Local Notation "u '~=' x" := (rep u x) (at level 70).
  Local Hint Unfold rep.

  Definition encode (x : F modulus) := encode x.

  (* Converts from length of extended base to length of base by reduction modulo M.*)
  Definition reduce (us : digits) : digits :=
    let high := skipn (length base) us in
    let low := firstn (length base) us in
    let wrap := map (Z.mul c) high in
    BaseSystem.add low wrap.

  Definition mul (us vs : digits) := reduce (BaseSystem.mul ext_base us vs).

End PseudoMersenneBase.

Section CarryBasePow2.
  Context `{prm :PseudoMersenneBaseParams}. 

  Definition log_cap i := nth_default 0 limb_widths i.

  Definition add_to_nth n (x:Z) xs :=
    set_nth n (x + nth_default 0 xs n) xs.
  
  Definition pow2_mod n i := Z.land n (Z.ones i).

  Definition carry_simple i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (pow2_mod di (log_cap i)) us in
    add_to_nth (S i) (   (Z.shiftr di (log_cap i))) us'.

  Definition carry_and_reduce i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (pow2_mod di (log_cap i)) us in
    add_to_nth   0  (c * (Z.shiftr di (log_cap i))) us'.

  Definition carry i : digits -> digits := 
    if eq_nat_dec i (pred (length base))
    then carry_and_reduce i
    else carry_simple i.

  Definition carry_sequence is us := fold_right carry us is.

End CarryBasePow2.
