Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^322 - 2^161 - 1
Base: 32
***)

Definition curve : CurveParameters :=
  {|
    sz := 11%nat;
    base := 32;
    bitwidth := 32;
    s := 2^322;
    c := [(1, 1); (2^161, 1)];
    carry_chains := None;

    a24 := None;
    coef_div_modulus := None;

    goldilocks := Some true;
    montgomery := true;
    freeze := Some false;
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
