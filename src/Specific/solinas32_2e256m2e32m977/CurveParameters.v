Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^256 - 2^32 - 977
Base: 21 + 1/3
***)

Definition curve : CurveParameters :=
  {|
    sz := 12%nat;
    base := 21 + 1/3;
    bitwidth := 32;
    s := 2^256;
    c := [(1, 977); (2^32, 1)];
    carry_chains := Some [[0; 11]; [1; 0; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]; [1; 0]]%nat;

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
