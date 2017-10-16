Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^254 - 127*2^240 - 1
Base: 23 + 1/11
***)

Definition curve : CurveParameters :=
  {|
    sz := 11%nat;
    base := 23 + 1/11;
    bitwidth := 32;
    s := 2^254;
    c := [(1, 1); (127, 2^240)];
    carry_chains := Some [[9; 10]; [10; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9]; [10; 0]]%nat;

    a24 := None;
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
