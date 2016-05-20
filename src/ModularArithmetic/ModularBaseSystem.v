Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystem Crypto.ModularArithmetic.PseudoMersenneBaseParams Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs Crypto.ModularArithmetic.ExtendedBaseVector.
Local Open Scope Z_scope.

Section PseudoMersenneBase.
  Context `{prm :PseudoMersenneBaseParams}.
  
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

  Definition sub (xs : digits) (xs_0_mod : (BaseSystem.decode base xs) mod modulus = 0) (us vs : digits) :=
      BaseSystem.sub (add xs us) vs.

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

Section Canonicalization.
  Context `{prm :PseudoMersenneBaseParams}.

  Fixpoint make_chain i :=
    match i with
    | O => nil
    | S i' => i' :: make_chain i'
    end.

  (* compute at compile time *)
  Definition full_carry_chain := make_chain (length limb_widths).

  (* compute at compile time *)
  Definition max_ones := Z.ones
    ((fix loop current_max lw :=
      match lw with
      | nil => current_max
      | w :: lw' => loop (Z.max w current_max) lw'
      end
    ) 0 limb_widths).
  
  (* compute at compile time? *)
  Definition carry_full := carry_sequence full_carry_chain.

  Definition max_bound i := Z.ones (log_cap i).

  Definition isFull us := 
    (fix loop full i :=
      match i with
      | O => full (* don't test 0; the test for 0 is the initial value of [full]. *)
      | S i' => loop (andb (Z.eqb (max_bound i) (nth_default 0 us i)) full) i'
      end
    ) (Z.ltb (max_bound 0 - (c + 1)) (nth_default 0 us 0)) (length us - 1)%nat.

  Fixpoint range' n m :=
    match m with
    | O => nil
    | S m' => (n - m)%nat :: range' n m'
    end.

  Definition range n := range' n n.

  Definition land_max_bound and_term i := Z.land and_term (max_bound i). 
    
  Definition freeze us :=
    let us' := carry_full (carry_full (carry_full us)) in
    let and_term := if isFull us' then max_ones else 0 in
    (* [and_term] is all ones if us' is full, so the subtractions subtract q overall.
       Otherwise, it's all zeroes, and the subtractions do nothing. *)
       map (fun x => (snd x) - land_max_bound and_term (fst x)) (combine (range (length us')) us').
   
End Canonicalization.
