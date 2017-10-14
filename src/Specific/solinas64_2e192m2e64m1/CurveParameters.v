Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^192 - 2^64 - 1
Base: 48
***)

Definition curve : CurveParameters :=
  {|
    sz := 4%nat;
    bitwidth := 64;
    s := 2^192;
    c := [(1, 1); (2^64, 1)];
    carry_chains := Some [seq 0 (pred 4); [0; 1]]%nat;

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
