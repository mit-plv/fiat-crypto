Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^322 - 2^161 - 1
Base: 26 + 5/6
***)

Definition curve : CurveParameters :=
  {|
    sz := 12%nat;
    base := 26 + 5/6;
    bitwidth := 32;
    s := 2^322;
    c := [(1, 1); (2^161, 1)];
    carry_chains := Some [[5; 11]; [6; 0; 7; 1; 8; 2; 9; 3; 10; 4; 11; 5]; [6; 0]]%nat;

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
