Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^480 - 2^240 - 1 
Base: 30
***)

Definition curve : CurveParameters :=
  {|
    sz := 16%nat;
    base := 30;
    bitwidth := 32;
    s := 2^480;
    c := [(1, 1); (2^240, 1)];
    carry_chains := Some [[7; 15]; [8; 0; 9; 1; 10; 2; 11; 3; 12; 4; 13; 5; 14; 6; 15; 7]; [8; 0]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some true;
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
