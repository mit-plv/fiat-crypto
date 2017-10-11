Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^255-5
Base: 130
***)

Module Curve <: CurveParameters.
  Definition sz : nat := 3%nat.
  Definition bitwidth : Z := 128.
  Definition s : Z := 2^255.
  Definition c : list limb := [(1, 5)].
  Definition carry_chains : option (list (list nat)) := Eval vm_compute in Some [seq 0 (pred sz); [0; 1]]%nat.

  Definition a24 : option Z := Some (121665 (* XXX TODO(andreser) FIXME?  Is this right for this curve? *)).
  Definition coef_div_modulus : option nat := Some 2%nat. (* add 2*modulus before subtracting *)

  Definition goldilocks : bool := false.
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
