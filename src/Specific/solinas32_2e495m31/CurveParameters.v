Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^495 - 31
Base: 26 + 1/19
***)

Definition curve : CurveParameters :=
  {|
    sz := 19%nat;
    base := 26 + 1/19;
    bitwidth := 32;
    s := 2^495;
    c := [(1, 31)];
    carry_chains := Some [seq 0 (pred 19); [0; 1]]%nat;

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
