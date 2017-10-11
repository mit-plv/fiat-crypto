Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^256-2^224+2^192+2^96-1
Base: 64
***)

Module Curve <: CurveParameters.
  Definition sz : nat := 4%nat.
  Definition bitwidth : Z := 64.
  Definition s : Z := 2^256.
  Definition c : list limb := [(1, 1); (2^96, -1); (2^192, -1); (2^224, 1)].
  Definition carry_chains : option (list (list nat)) := Eval vm_compute in None.

  Definition a24 : option Z := None.
  Definition coef_div_modulus : option nat := None. (* add 0*modulus before subtracting *)

  Definition goldilocks : bool := false.
  Definition montgomery : bool := true.

  Definition mul_code : option (Z^sz -> Z^sz -> Z^sz)
    := None.

  Definition square_code : option (Z^sz -> Z^sz)
    := None.

  Definition upper_bound_of_exponent : option (Z -> Z) := None.
  Definition allowable_bit_widths : option (list nat) := None.
  Definition freeze_extra_allowable_bit_widths : option (list nat) := None.
  Definition modinv_fuel : option nat := None.
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End Curve.
