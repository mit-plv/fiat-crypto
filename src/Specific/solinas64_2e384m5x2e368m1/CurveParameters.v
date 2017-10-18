Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^384 - 5*2^368 - 1
Base: 48
***)

Definition curve : CurveParameters :=
  {|
    sz := 8%nat;
    base := 48;
    bitwidth := 64;
    s := 2^384;
    c := [(1, 1); (5, 2^368)];
    carry_chains := Some [[6; 7]; [7; 0; 1; 2; 3; 4; 5; 6]; [7; 0]]%nat;

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
