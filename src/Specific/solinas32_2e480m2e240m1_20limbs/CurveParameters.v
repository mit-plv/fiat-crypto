Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^480 - 2^240 - 1
Base: 24
***)

Definition curve : CurveParameters :=
  {|
    sz := 20%nat;
    base := 24;
    bitwidth := 32;
    s := 2^480;
    c := [(1, 1); (2^240, 1)];
    carry_chains := Some [[9; 19]; [10; 0; 11; 1; 12; 2; 13; 3; 14; 4; 15; 5; 16; 6; 17; 7; 18; 8; 19; 9]; [10; 0]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some true;
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
