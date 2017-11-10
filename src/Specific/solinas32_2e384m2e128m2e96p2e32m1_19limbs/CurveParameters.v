Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^384 - 2^128 - 2^96 + 2^32 - 1
Base: 20 + 4/19
***)

Definition curve : CurveParameters :=
  {|
    sz := 19%nat;
    base := 20 + 4/19;
    bitwidth := 32;
    s := 2^384;
    c := [(1, 1); (2^32, -1); (2^96, 1); (2^128, 1)];
    carry_chains := Some [[5; 3; 0; 18]; [6; 4; 1; 0; 7; 5; 2; 8; 3; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]; [6; 4; 1; 0]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := None;
    karatsuba := None;
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
