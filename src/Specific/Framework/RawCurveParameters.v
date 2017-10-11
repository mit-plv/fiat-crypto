Require Export Coq.ZArith.BinInt.
Require Export Coq.Lists.List.
Require Export Crypto.Util.ZUtil.Notations.
Require Crypto.Util.Tuple.

Local Set Primitive Projections.

Module Export Notations. (* import/export tracking *)
  Export ListNotations.

  Open Scope list_scope.
  Open Scope Z_scope.

  Notation limb := (Z * Z)%type.
  Infix "^" := Tuple.tuple : type_scope.
End Notations.

Record CurveParameters :=
  {
    sz : nat;
    bitwidth : Z;
    s : Z;
    c : list limb;
    carry_chains
    : option (list (list nat)) (* defaults to [seq 0 (pred sz) :: (0 :: 1 :: nil) :: nil] *);
    a24 : option Z;
    coef_div_modulus : option nat;

    goldilocks : option bool; (* defaults to true iff the prime ([s-c]) is of the form [2²ᵏ - 2ᵏ - 1] *)
    montgomery : bool;

    mul_code : option (Z^sz -> Z^sz -> Z^sz);
    square_code : option (Z^sz -> Z^sz);
    upper_bound_of_exponent
    : option (Z -> Z) (* defaults to [fun exp => 2^exp + 2^(exp-3)] for non-montgomery, [fun exp => 2^exp - 1] for montgomery *);
    allowable_bit_widths
    : option (list nat) (* defaults to [bitwidth :: 2*bitwidth :: nil] *);
    freeze_extra_allowable_bit_widths
    : option (list nat) (* defaults to [8 :: nil] *);
    modinv_fuel : option nat
  }.

Declare Reduction cbv_RawCurveParameters
  := cbv [sz
            bitwidth
            s
            c
            carry_chains
            a24
            coef_div_modulus
            goldilocks
            montgomery
            mul_code
            square_code
            upper_bound_of_exponent
            allowable_bit_widths
            freeze_extra_allowable_bit_widths
            modinv_fuel].

(*
Ltac extra_prove_mul_eq := idtac.
Ltac extra_prove_square_eq := idtac.
 *)
