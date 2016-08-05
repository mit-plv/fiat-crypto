Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.ModularBaseSystemList.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListProofs.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Import Crypto.Tactics.VerdiTactics.
Local Open Scope Z_scope.

Section ModularBaseSystem.
  Context `{prm :PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation digits := (tuple Z (length limb_widths)).
  Local Arguments to_list {_ _} _.
  Local Arguments from_list {_ _} _ _.
  Local Arguments length_to_list {_ _ _}.
  Local Notation "[[ u ]]" := (to_list u).

  Definition decode (us : digits) : F modulus := decode [[us]].

  Definition encode (x : F modulus) : digits := from_list (encode x) length_encode.

  Definition add (us vs : digits) : digits := from_list (add [[us]] [[vs]])
    (add_same_length _ _ _ length_to_list length_to_list).

  Definition mul (us vs : digits) : digits := from_list (mul [[us]] [[vs]])
    (length_mul length_to_list length_to_list).

  Definition sub (modulus_multiple us vs : digits) : digits :=
   from_list (sub [[modulus_multiple]] [[us]] [[vs]])
   (length_sub length_to_list length_to_list length_to_list).

  Definition zero : digits := encode (F.of_Z _ 0).

  Definition one : digits := encode (F.of_Z _ 1).

  (* Placeholder *)
  Definition opp (x : digits) : digits := encode (F.opp (decode x)).

  (* Placeholder *)
  Definition inv (x : digits) : digits := encode (F.inv (decode x)).

  (* Placeholder *)
  Definition div (x y : digits) : digits := encode (F.div (decode x) (decode y)).

  Definition rep (us : digits) (x : F modulus) := decode us = x.
  Local Notation "u ~= x" := (rep u x).
  Local Hint Unfold rep.

  Definition carry_full (us : digits) : digits := from_list (carry_full [[us]])
    (length_carry_full length_to_list).

  Definition carry_mul (us vs : digits) : digits := carry_full (mul us vs).

  Definition freeze (us : digits) : digits :=
    let us' := carry_full (carry_full (carry_full us)) in
     from_list (conditional_subtract_modulus [[us']] (ge_modulus [[us']]))
     (length_conditional_subtract_modulus length_to_list).

  Definition eq (x y : digits) : Prop := decode x = decode y.

  Import Morphisms.
  Global Instance eq_Equivalence : Equivalence eq.
  Proof.
    split; cbv [eq]; repeat intro; congruence.
  Qed.

End ModularBaseSystem.