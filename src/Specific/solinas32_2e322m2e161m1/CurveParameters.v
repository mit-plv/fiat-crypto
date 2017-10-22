Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^322 - 2^161 - 1
Base: 23
***)

Definition curve : CurveParameters :=
  {|
    sz := 14%nat;
    base := 23;
    bitwidth := 32;
    s := 2^322;
    c := [(1, 1); (2^161, 1)];
    carry_chains := Some [[6; 13]; [7; 0; 8; 1; 9; 2; 10; 3; 11; 4; 12; 5; 13; 6]; [7; 0]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some true;
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
