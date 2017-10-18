Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^256 - 2^32 - 977 
Base: 51.2
***)

Definition curve : CurveParameters :=
  {|
    sz := 5%nat;
    base := 51 + 1/5;
    bitwidth := 64;
    s := 2^256;
    c := [(1, 977); (2^32, 1)];
    carry_chains := Some [[4; 4]; [0; 1; 2; 3]; [0; 0]]%nat;

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
