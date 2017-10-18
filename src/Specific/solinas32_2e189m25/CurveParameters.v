Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^189 - 25
Base: 27
***)

Definition curve : CurveParameters :=
  {|
    sz := 7%nat;
    base := 27;
    bitwidth := 32;
    s := 2^189;
    c := [(1, 25)];
    carry_chains := Some [seq 0 (pred 7); [0; 1]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some false;
    montgomery := false;
    freeze := Some true;
    ladderstep := false;

    mul_code := None;

    square_code := None;

    upper_bound_of_exponent := None;
    allowable_bit_widths := None;
    freeze_extra_allowable_bit_widths := None;
    modinv_fuel := None
  |}.

Ltac extra_prove_mul_eq _ := idtac.
Ltac extra_prove_square_eq _ := idtac.
