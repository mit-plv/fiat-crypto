Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^291 - 19
Base: 24.25
***)

Definition curve : CurveParameters :=
  {|
    sz := 12%nat;
    base := 24 + 1/4;
    bitwidth := 32;
    s := 2^291;
    c := [(1, 19)];
    carry_chains := Some [seq 0 (pred 12); [0; 1]]%nat;

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
