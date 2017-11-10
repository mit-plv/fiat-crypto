Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^416 - 2^208 - 1
Base: 23 + 1/9
***)

Definition curve : CurveParameters :=
  {|
    sz := 18%nat;
    base := 23 + 1/9;
    bitwidth := 32;
    s := 2^416;
    c := [(1, 1); (2^208, 1)];
    carry_chains := Some [[8; 17]; [9; 0; 10; 1; 11; 2; 12; 3; 13; 4; 14; 5; 15; 6; 16; 7; 17; 8]; [9; 0]]%nat;

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
