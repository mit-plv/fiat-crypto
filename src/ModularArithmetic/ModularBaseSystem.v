Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.ModularArithmetic.ModularBaseSystemList.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListProofs.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.AdditionChainExponentiation.
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

  Definition sub (modulus_multiple: digits)
                 (modulus_multiple_correct : decode modulus_multiple = 0%F)
                 (us vs : digits) : digits :=
   from_list (sub [[modulus_multiple]] [[us]] [[vs]])
   (length_sub length_to_list length_to_list length_to_list).

  Definition zero : digits := encode (F.of_Z _ 0).

  Definition one : digits := encode (F.of_Z _ 1).

  Definition opp (modulus_multiple : digits)
                 (modulus_multiple_correct : decode modulus_multiple = 0%F)
                 (x : digits) :
    digits := sub modulus_multiple modulus_multiple_correct zero x.

  Definition pow (x : digits) (chain : list (nat * nat)) : digits :=
    fold_chain one mul chain (x :: nil).

  Definition inv (chain : list (nat * nat))
                 (chain_correct : fold_chain 0%N N.add chain (1%N :: nil) = Z.to_N (modulus - 2))
                 (x : digits) : digits := pow x chain.

  (* Placeholder *)
  Definition div (x y : digits) : digits := encode (F.div (decode x) (decode y)).

  Definition carry_ (carry_chain : list nat) (us : digits) : digits :=
    from_list (carry_sequence carry_chain [[us]]) (length_carry_sequence length_to_list).

  Definition carry_add (carry_chain : list nat) (us vs : digits) : digits :=
    carry_ carry_chain (add us vs).
  Definition carry_mul (carry_chain : list nat) (us vs : digits) : digits :=
    carry_ carry_chain (mul us vs).
  Definition carry_sub (carry_chain : list nat) (modulus_multiple: digits)
             (modulus_multiple_correct : decode modulus_multiple = 0%F)
             (us vs : digits) : digits :=
    carry_ carry_chain (sub modulus_multiple modulus_multiple_correct us vs).
  Definition carry_opp (carry_chain : list nat) (modulus_multiple : digits)
             (modulus_multiple_correct : decode modulus_multiple = 0%F)
             (x : digits) : digits :=
    carry_sub carry_chain modulus_multiple modulus_multiple_correct zero x.

  Definition rep (us : digits) (x : F modulus) := decode us = x.
  Local Notation "u ~= x" := (rep u x).
  Local Hint Unfold rep.

  Definition eq (x y : digits) : Prop := decode x = decode y.

  Definition freeze int_width (x : digits) : digits :=
    from_list (freeze int_width [[x]]) (length_freeze length_to_list).

  Definition eqb int_width (x y : digits) : bool := fieldwiseb Z.eqb (freeze int_width x) (freeze int_width y).

  (* Note : both of the following square root definitions will produce garbage output if the input is
            not square mod [modulus]. The caller should either provably only call them with square input,
            or test that the output squared is in fact equal to the input and case split. *)
  Definition sqrt_3mod4 (chain : list (nat * nat))
                  (chain_correct : fold_chain 0%N N.add chain (1%N :: nil) = Z.to_N (modulus / 4 + 1))
                  (x : digits) : digits := pow x chain.

  Definition sqrt_5mod8 int_width powx powx_squared (chain : list (nat * nat))
                  (chain_correct : fold_chain 0%N N.add chain (1%N :: nil) = Z.to_N (modulus / 8 + 1))
                  (sqrt_minus1 x : digits) : digits :=
    if eqb int_width powx_squared x then powx else mul sqrt_minus1 powx.

  Import Morphisms.
  Global Instance eq_Equivalence : Equivalence eq.
  Proof.
    split; cbv [eq]; repeat intro; congruence.
  Qed.

  Definition select int_width (b : Z) (x y : digits) :=
    add (map (Z.land (neg int_width b)) x)
        (map (Z.land (neg int_width (Z.lxor b 1))) x).

  Context {target_widths} (target_widths_nonneg : forall x, In x target_widths -> 0 <= x)
          (bits_eq : sum_firstn limb_widths   (length limb_widths) =
                     sum_firstn target_widths (length target_widths)).
  Local Notation target_digits := (tuple Z (length target_widths)).

  Definition pack (x : digits) : target_digits :=
    from_list (pack target_widths_nonneg bits_eq [[x]]) length_pack.

  Definition unpack (x : target_digits) : digits :=
    from_list (unpack target_widths_nonneg bits_eq [[x]]) length_unpack.

End ModularBaseSystem.
