Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^205 - 45*2^198 - 1
Base: 20.5
***)

Definition curve : CurveParameters :=
  {|
    sz := 10%nat;
    base := 20 + 1/2;
    bitwidth := 32;
    s := 2^205;
    c := [(1, 1); (45, 2^198)];
    carry_chains := Some [[8; 9]; [9; 0; 1; 2; 3; 4; 5; 6; 7; 8]; [9; 0]]%nat;

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
