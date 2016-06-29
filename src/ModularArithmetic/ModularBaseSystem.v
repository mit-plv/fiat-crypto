Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Section PseudoMersenneBase.
  Context `{prm :PseudoMersenneBaseParams}.

  Definition decode (us : digits) : F modulus := ZToField (BaseSystem.decode base us).

  Definition rep (us : digits) (x : F modulus) := (length us = length base)%nat /\ decode us = x.
  Local Notation "u ~= x" := (rep u x).
  Local Hint Unfold rep.

  Definition encode (x : F modulus) := encode base x (2 ^ k).

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

  Fixpoint make_chain i :=
    match i with
    | O => nil
    | S i' => i' :: make_chain i'
    end.

  Definition full_carry_chain := make_chain (length limb_widths).

  Definition carry_full := carry_sequence full_carry_chain.

  Definition carry_mul us vs := carry_full (mul us vs).

End CarryBasePow2.

Section Canonicalization.
  Context `{prm :PseudoMersenneBaseParams}.

  (* compute at compile time *)
  Definition max_ones := Z.ones (fold_right Z.max 0 limb_widths).

  Definition max_bound i := Z.ones (log_cap i).

  Fixpoint isFull' us full i :=
    match i with
    | O => andb (Z.ltb (max_bound 0 - c) (nth_default 0 us 0)) full
    | S i' => isFull' us (andb (Z.eqb (max_bound i) (nth_default 0 us i)) full) i'
    end.

  Definition isFull us := isFull' us true (length base - 1)%nat.

  Fixpoint modulus_digits' i :=
    match i with
    | O => max_bound i - c + 1 :: nil
    | S i' => modulus_digits' i' ++ max_bound i :: nil
    end.

  (* compute at compile time *)
  Definition modulus_digits := modulus_digits' (length base - 1).

  Fixpoint map2 {A B C} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
    match la with
    | nil => nil
    | a :: la' => match lb with
                  | nil => nil
                  | b :: lb' => f a b :: map2 f la' lb'
                  end
    end.

  Definition and_term us := if isFull us then max_ones else 0.

  Definition freeze us :=
    let us' := carry_full (carry_full (carry_full us)) in
    let and_term := and_term us' in
    (* [and_term] is all ones if us' is full, so the subtractions subtract q overall.
       Otherwise, it's all zeroes, and the subtractions do nothing. *)
     map2 (fun x y => x - y) us' (map (Z.land and_term) modulus_digits).

End Canonicalization.
