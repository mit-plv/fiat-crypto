Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^448-2^224-1
Base: 56
***)

Module Curve <: CurveParameters.
  Definition sz : nat := 8%nat.
  Definition bitwidth : Z := 64.
  Definition s : Z := 2^448.
  Definition c : list limb := [(1, 1); (2^224, 1)].
  Definition carry_chains : option (list (list nat)) := Eval vm_compute in Some [[3; 7]; [0; 4; 1; 5; 2; 6; 3; 7]; [4; 0]]%nat.

  Definition a24 : option Z := None.
  Definition coef_div_modulus : option nat := Some 2%nat. (* add 2*modulus before subtracting *)

  Definition goldilocks : bool := true.
  Definition montgomery : bool := false.

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
