Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^255-5
Base: 130
***)

Definition curve : CurveParameters :=
  {|
    sz := 3%nat;
    bitwidth := 128;
    s := 2^255;
    c := [(1, 5)];
    carry_chains := Some [seq 0 (pred 3); [0; 1]]%nat;

    a24 := Some (121665 (* XXX TODO(andreser) FIXME?  Is this right for this curve? *));
    coef_div_modulus := Some 2%nat;

    goldilocks := Some false;
    montgomery := false;

    mul_code := None;

    square_code := None;

    upper_bound_of_exponent := None;
    allowable_bit_widths := None;
    freeze_extra_allowable_bit_widths := None;
    modinv_fuel := None
  |}.

Ltac extra_prove_mul_eq _ := idtac.
Ltac extra_prove_square_eq _ := idtac.
