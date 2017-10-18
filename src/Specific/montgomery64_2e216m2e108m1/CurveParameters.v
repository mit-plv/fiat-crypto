Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^216 - 2^108 - 1
Base: 64
***)

Definition curve : CurveParameters :=
  {|
    sz := 3%nat;
    base := 64;
    bitwidth := 64;
    s := 2^216;
    c := [(1, 1); (2^108, 1)];
    carry_chains := None;

    a24 := None;
    coef_div_modulus := None;

    goldilocks := Some true;
    montgomery := true;

    mul_code := None;

    square_code := None;

    upper_bound_of_exponent := None;
    allowable_bit_widths := None;
    freeze_extra_allowable_bit_widths := None;
    modinv_fuel := None
  |}.

Ltac extra_prove_mul_eq _ := idtac.
Ltac extra_prove_square_eq _ := idtac.
