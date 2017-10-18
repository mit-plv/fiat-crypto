Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^192 - 2^64 - 1
Base: 24
***)

Definition curve : CurveParameters :=
  {|
    sz := 8%nat;
    base := 24;
    bitwidth := 32;
    s := 2^192;
    c := [(1, 1); (2^64, 1)];
    carry_chains := Some [[1; 7]; [2; 0; 3; 1; 4; 5; 6; 7]; [2; 0]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some false;
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
