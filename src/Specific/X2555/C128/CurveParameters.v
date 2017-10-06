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
  Definition carry_chain1 : option (list nat) := Eval vm_compute in Some (seq 0 (pred sz)).
  Definition carry_chain2 : option (list nat) := Eval vm_compute in Some [0; 1]%nat.

  Definition a24 : Z := 121665 (* XXX TODO(andreser) FIXME?  Is this right for this curve? *).
  Definition coef_div_modulus : nat := 2%nat. (* add 2*modulus before subtracting *)

  Definition mul_code : option (Z^sz -> Z^sz -> Z^sz)
    := None.

  Definition square_code : option (Z^sz -> Z^sz)
    := None.

  Definition upper_bound_of_exponent : option (Z -> Z) := None.
  Definition allowable_bit_widths : option (list nat) := None.
  Definition freeze_extra_allowable_bit_widths : option (list nat) := None.
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End Curve.
