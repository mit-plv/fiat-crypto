Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^416 - 2^208 - 1
Base: 46 + 2/9
***)

Definition curve : CurveParameters :=
  {|
    sz := 9%nat;
    base := 46 + 2/9;
    bitwidth := 64;
    s := 2^416;
    c := [(1, 1); (2^208, 1)];
    carry_chains := Some [[3; 8]; [4; 0; 5; 1; 6; 2; 7; 3; 8]; [4; 0]]%nat;

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
