Require Export Coq.ZArith.BinInt.
Require Export Coq.Lists.List.
Require Export Crypto.Util.ZUtil.Notations.
Require Crypto.Util.Tuple.

Module Export Notations.
  Export ListNotations.

  Open Scope list_scope.
  Open Scope Z_scope.

  Notation limb := (Z * Z)%type.
  Infix "^" := Tuple.tuple : type_scope.
End Notations.

(* These definitions will need to be passed as Ltac arguments (or
   cleverly inferred) when things are eventually automated *)
Module Type CurveParameters.
  Parameter sz : nat.
  Parameter bitwidth : Z.
  Parameter s : Z.
  Parameter c : list limb.
  Parameter carry_chain1
    : option (list nat). (* defaults to [seq 0 (pred sz)] *)
  Parameter carry_chain2
    : option (list nat). (* defaults to [0 :: 1 :: nil] *)
  Parameter a24 : Z.
  Parameter coef_div_modulus : nat.

  Parameter mul_code : option (Z^sz -> Z^sz -> Z^sz).
  Parameter square_code : option (Z^sz -> Z^sz).
  Parameter upper_bound_of_exponent
    : option (Z -> Z). (* defaults to [fun exp => 2^exp + 2^(exp-3)] *)
  Parameter allowable_bit_widths
    : option (list nat). (* defaults to [bitwidth :: 2*bitwidth :: nil] *)
  Parameter freeze_extra_allowable_bit_widths
    : option (list nat). (* defaults to [8 :: nil] *)
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End CurveParameters.

Module FillCurveParameters (P : CurveParameters).
  Local Notation defaulted opt_v default
    := (match opt_v with
        | Some v => v
        | None => default
        end).
  Notation compute v
    := (ltac:(let v' := v in let v' := (eval vm_compute in v') in exact v'))
         (only parsing).
  Definition sz := P.sz.
  Definition bitwidth := P.bitwidth.
  Definition s := P.s.
  Definition c := P.c.
  Definition carry_chain1 := defaulted P.carry_chain1 (seq 0 (pred sz)).
  Definition carry_chain2 := defaulted P.carry_chain2 (0 :: 1 :: nil)%nat.
  Definition a24 := P.a24.
  Definition coef_div_modulus := P.coef_div_modulus.

  Ltac default_mul :=
    lazymatch (eval hnf in P.mul_code) with
    | None => reflexivity
    | Some ?mul_code
      => instantiate (1:=mul_code)
    end.
  Ltac default_square :=
    lazymatch (eval hnf in P.square_code) with
    | None => reflexivity
    | Some ?square_code
      => instantiate (1:=square_code)
    end.

  Definition upper_bound_of_exponent
    := defaulted P.upper_bound_of_exponent (fun exp => (2^exp + 2^(exp-3))%Z).
  Definition allowable_bit_widths
    := defaulted P.allowable_bit_widths (Z.to_nat bitwidth :: 2*Z.to_nat bitwidth :: nil)%nat.
  Definition freeze_allowable_bit_widths
    := defaulted P.freeze_extra_allowable_bit_widths [8]%nat ++ allowable_bit_widths.

  (* hack around https://coq.inria.fr/bugs/show_bug.cgi?id=5764 *)
  Ltac do_unfold v' :=
    let P_sz := P.sz in
    let P_bitwidth := P.bitwidth in
    let P_s := P.s in
    let P_c := P.c in
    let P_carry_chain1 := P.carry_chain1 in
    let P_carry_chain2 := P.carry_chain2 in
    let P_a24 := P.a24 in
    let P_coef_div_modulus := P.coef_div_modulus in
    let P_mul_code := P.mul_code in
    let P_square_code := P.square_code in
    let P_upper_bound_of_exponent := P.upper_bound_of_exponent in
    let P_allowable_bit_widths := P.allowable_bit_widths in
    let P_freeze_extra_allowable_bit_widths := P.freeze_extra_allowable_bit_widths in
    let v' := (eval cbv [id
                           List.app
                           sz bitwidth s c carry_chain1 carry_chain2 a24 coef_div_modulus
                           P_sz P_bitwidth P_s P_c P_carry_chain1 P_carry_chain2 P_a24 P_coef_div_modulus
                           P_mul_code P_square_code
                           upper_bound_of_exponent allowable_bit_widths freeze_allowable_bit_widths
                           P_upper_bound_of_exponent P_allowable_bit_widths P_freeze_extra_allowable_bit_widths
                           pred seq]
                in v') in
    v'.
  Notation unfold v
    := (ltac:(let v' := v in
              let v' := do_unfold v' in
              exact v'))
         (only parsing).
  Ltac extra_prove_mul_eq := P.extra_prove_mul_eq.
  Ltac extra_prove_square_eq := P.extra_prove_square_eq.
End FillCurveParameters.
