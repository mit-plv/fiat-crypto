Require Export Coq.QArith.QArith_base.
Require Export Coq.ZArith.BinInt.
Require Export Coq.Lists.List.
Require Export Crypto.Util.ZUtil.Notations.
Require Crypto.Util.Tuple.

Local Set Primitive Projections.
Coercion QArith_base.inject_Z : Z >-> Q.
Coercion Z.of_nat : nat >-> Z.

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
    base : Q;
    bitwidth : Z;
    s : Z;
    c : list limb;
    carry_chains
    : option (list (list nat)) (* defaults to [seq 0 (pred sz) :: (0 :: 1 :: nil) :: nil] *);
    a24 : option Z;
    coef_div_modulus : option nat;

    goldilocks : option bool; (* defaults to true iff the prime ([s-c]) is of the form [2²ᵏ - 2ᵏ - 1] *)
    karatsuba : option bool; (* defaults to false, currently unused *)
    montgomery : bool;
    freeze : option bool; (* defaults to true iff [s = 2^(base * sz)] *)
    ladderstep : bool;

    mul_code : option (Z^sz -> Z^sz -> Z^sz);
    square_code : option (Z^sz -> Z^sz);
    upper_bound_of_exponent_tight
    : option (Z -> Z) (* defaults to [fun exp => 2^exp + 2^(exp-3)] for non-montgomery, [fun exp => 2^exp - 1] for montgomery *);
    upper_bound_of_exponent_loose
    : option (Z -> Z) (* defaults to [3 * upper_bound_of_exponent_tight] for non-montgomery, [fun exp => 2^exp - 1] for montgomery *);
    allowable_bit_widths
    : option (list nat) (* defaults to [bitwidth :: 2*bitwidth :: nil] *);
    freeze_extra_allowable_bit_widths
    : option (list nat) (* defaults to [8 :: nil] *);
    modinv_fuel : option nat
  }.

Declare Reduction cbv_RawCurveParameters
  := cbv [sz
            base
            bitwidth
            s
            c
            carry_chains
            a24
            coef_div_modulus
            goldilocks
            karatsuba
            montgomery
            freeze
            ladderstep
            mul_code
            square_code
            upper_bound_of_exponent_tight
            upper_bound_of_exponent_loose
            allowable_bit_widths
            freeze_extra_allowable_bit_widths
            modinv_fuel].

(*
Ltac extra_prove_mul_eq := idtac.
Ltac extra_prove_square_eq := idtac.
 *)
