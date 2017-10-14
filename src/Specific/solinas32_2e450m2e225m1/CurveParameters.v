Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^450 - 2^225 - 1
Base: 28
***)

Definition curve : CurveParameters :=
  {|
    sz := 16%nat;
    bitwidth := 32;
    s := 2^450;
    c := [(1, 1); (2^225, 1)];
    carry_chains := Some [seq 0 (pred 16); [0; 1]]%nat;

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
