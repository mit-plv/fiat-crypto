Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^224 - 2^96 + 1
Base: 28
***)

Definition curve : CurveParameters :=
  {|
    sz := 8%nat;
    base := 28;
    bitwidth := 32;
    s := 2^224;
    c := [(1, -1); (2^96, 1)];
    carry_chains := Some [[2; 7]; [3; 0; 4; 1; 5; 2; 6; 7]; [3; 0]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := None;
    montgomery := false;
    freeze := Some true;
    ladderstep := false;

    mul_code := None;

    square_code := None;

    upper_bound_of_exponent_loose := None;
    upper_bound_of_exponent_tight := None;
    allowable_bit_widths := None;
    freeze_extra_allowable_bit_widths := None;
    modinv_fuel := None
  |}.

Ltac extra_prove_mul_eq _ := idtac.
Ltac extra_prove_square_eq _ := idtac.
