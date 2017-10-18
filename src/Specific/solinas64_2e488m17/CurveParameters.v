Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^488 - 17
Base: 30.5
***)

Definition curve : CurveParameters :=
  {|
    sz := 16%nat;
    base := 30 + 1/2;
    bitwidth := 64;
    s := 2^488;
    c := [(1, 17)];
    carry_chains := Some [seq 0 (pred 16); [0; 1]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some false;
    montgomery := false;

    mul_code := None;

    square_code := None;

    upper_bound_of_exponent := None;
    allowable_bit_widths := None;
    freeze_extra_allowable_bit_widths := None;
    modinv_fuel := None
  |}.

Ltac extra_prove_mul_eq _ := idtac.
Ltac extra_prove_square_eq _ := idtac.
