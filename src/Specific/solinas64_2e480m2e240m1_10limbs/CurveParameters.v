Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^480 - 2^240 - 1
Base: 48
***)

Definition curve : CurveParameters :=
  {|
    sz := 10%nat;
    base := 48;
    bitwidth := 64;
    s := 2^480;
    c := [(1, 1); (2^240, 1)];
    carry_chains := Some [[4; 9]; [5; 0; 6; 1; 7; 2; 8; 3; 9; 4]; [5; 0]]%nat;

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
