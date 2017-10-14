Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^216 - 2^108 - 1
Base: 27
***)

Definition curve : CurveParameters :=
  {|
    sz := 8%nat;
    bitwidth := 32;
    s := 2^216;
    c := [(1, 1); (2^108, 1)];
    carry_chains := Some [seq 0 (pred 8); [0; 1]]%nat;

    a24 := None;
    coef_div_modulus := Some 2%nat;

    goldilocks := Some true;
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
