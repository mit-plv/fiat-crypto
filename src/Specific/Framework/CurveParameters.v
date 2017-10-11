Require Export Coq.ZArith.BinInt.
Require Export Coq.Lists.List.
Require Export Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.TagList.
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
  Parameter carry_chains
    : option (list (list nat)). (* defaults to [seq 0 (pred sz) :: (0 :: 1 :: nil) :: nil] *)
  Parameter a24 : option Z.
  Parameter coef_div_modulus : option nat.

  Parameter goldilocks : bool.

  Parameter mul_code : option (Z^sz -> Z^sz -> Z^sz).
  Parameter square_code : option (Z^sz -> Z^sz).
  Parameter upper_bound_of_exponent
    : option (Z -> Z). (* defaults to [fun exp => 2^exp + 2^(exp-3)] *)
  Parameter allowable_bit_widths
    : option (list nat). (* defaults to [bitwidth :: 2*bitwidth :: nil] *)
  Parameter freeze_extra_allowable_bit_widths
    : option (list nat). (* defaults to [8 :: nil] *)
  Parameter modinv_fuel : option nat.
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End CurveParameters.

Module TAG.
  Inductive tags := sz | bitwidth | s | c | carry_chains | a24 | coef_div_modulus | goldilocks | upper_bound_of_exponent | allowable_bit_widths | freeze_allowable_bit_widths | modinv_fuel.
End TAG.

Module FillCurveParameters (P : CurveParameters).
  Local Notation defaulted opt_v default
    := (match opt_v with
        | Some v => v
        | None => default
        end).
  Ltac do_compute v :=
    let v' := (eval vm_compute in v) in v'.
  Notation compute v
    := (ltac:(let v' := do_compute v in exact v'))
         (only parsing).
  Definition sz := P.sz.
  Definition bitwidth := P.bitwidth.
  Definition s := P.s.
  Definition c := P.c.
  Definition carry_chains := defaulted P.carry_chains [seq 0 (pred sz); [0; 1]]%nat.
  Definition a24 := defaulted P.a24 0.
  Definition coef_div_modulus := defaulted P.coef_div_modulus 0%nat.

  Definition goldilocks := P.goldilocks.

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
    := defaulted P.upper_bound_of_exponent
                 (fun exp => (2^exp + 2^(exp-3))%Z).
  Local Notation list_8_if_not_exists ls :=
    (if existsb (Nat.eqb 8) ls
     then nil
     else [8]%nat)
      (only parsing).
  Definition allowable_bit_widths
    := defaulted
         P.allowable_bit_widths
         (Z.to_nat bitwidth :: 2*Z.to_nat bitwidth :: nil)%nat.
  Definition freeze_allowable_bit_widths
    := defaulted
         P.freeze_extra_allowable_bit_widths
         (list_8_if_not_exists allowable_bit_widths)
         ++ allowable_bit_widths.
  Definition modinv_fuel := defaulted P.modinv_fuel 10%nat.

  (* hack around https://coq.inria.fr/bugs/show_bug.cgi?id=5764 *)
  Ltac do_unfold v' :=
    let P_sz := P.sz in
    let P_bitwidth := P.bitwidth in
    let P_s := P.s in
    let P_c := P.c in
    let P_carry_chains := P.carry_chains in
    let P_a24 := P.a24 in
    let P_coef_div_modulus := P.coef_div_modulus in
    let P_goldilocks := P.goldilocks in
    let P_mul_code := P.mul_code in
    let P_square_code := P.square_code in
    let P_upper_bound_of_exponent := P.upper_bound_of_exponent in
    let P_allowable_bit_widths := P.allowable_bit_widths in
    let P_freeze_extra_allowable_bit_widths := P.freeze_extra_allowable_bit_widths in
    let P_modinv_fuel := P.modinv_fuel in
    let v' := (eval cbv [id
                           List.app
                           sz bitwidth s c carry_chains a24 coef_div_modulus goldilocks modinv_fuel
                           P_sz P_bitwidth P_s P_c P_carry_chains P_a24 P_coef_div_modulus P_goldilocks P_modinv_fuel
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

  Local Notation P_sz := sz.
  Local Notation P_bitwidth := bitwidth.
  Local Notation P_s := s.
  Local Notation P_c := c.
  Local Notation P_carry_chains := carry_chains.
  Local Notation P_a24 := a24.
  Local Notation P_coef_div_modulus := coef_div_modulus.
  Local Notation P_goldilocks := goldilocks.
  Local Notation P_upper_bound_of_exponent := upper_bound_of_exponent.
  Local Notation P_allowable_bit_widths := allowable_bit_widths.
  Local Notation P_freeze_allowable_bit_widths := freeze_allowable_bit_widths.
  Local Notation P_modinv_fuel := modinv_fuel.

  Ltac pose_sz sz :=
    cache_term_with_type_by
      nat
      ltac:(let v := do_compute P_sz in exact v)
             sz.
  Ltac pose_bitwidth bitwidth :=
    cache_term_with_type_by
      Z
      ltac:(let v := do_compute P_bitwidth in exact v)
             bitwidth.
  Ltac pose_s s := (* don't want to compute, e.g., [2^255] *)
    cache_term_with_type_by
      Z
      ltac:(let v := do_unfold P_s in exact v)
             s.
  Ltac pose_c c :=
    cache_term_with_type_by
      (list limb)
      ltac:(let v := do_compute P_c in exact v)
             c.
  Ltac pose_carry_chains carry_chains :=
    let v := do_compute P_carry_chains in
    cache_term v carry_chains.

  Ltac pose_a24 a24 :=
    let v := do_compute P_a24 in
    cache_term v a24.
  Ltac pose_coef_div_modulus coef_div_modulus :=
    cache_term_with_type_by
      nat
      ltac:(let v := do_compute P_coef_div_modulus in exact v)
             coef_div_modulus.
  Ltac pose_goldilocks goldilocks :=
    cache_term_with_type_by
      bool
      ltac:(let v := do_compute P_goldilocks in exact v)
             goldilocks.

  Ltac pose_modinv_fuel modinv_fuel :=
    cache_term_with_type_by
      nat
      ltac:(let v := do_compute P_modinv_fuel in exact v)
             modinv_fuel.

  Ltac pose_upper_bound_of_exponent upper_bound_of_exponent :=
    cache_term_with_type_by
      (Z -> Z)
      ltac:(let v := do_unfold P_upper_bound_of_exponent in exact v)
             upper_bound_of_exponent.

  (* Everything below this line autogenerated by remake_packages.py *)
  Ltac add_sz pkg :=
    let sz := fresh "sz" in
    let sz := pose_sz sz in
    Tag.update pkg TAG.sz sz.

  Ltac add_bitwidth pkg :=
    let bitwidth := fresh "bitwidth" in
    let bitwidth := pose_bitwidth bitwidth in
    Tag.update pkg TAG.bitwidth bitwidth.

  Ltac add_s pkg :=
    let s := fresh "s" in
    let s := pose_s s in
    Tag.update pkg TAG.s s.

  Ltac add_c pkg :=
    let c := fresh "c" in
    let c := pose_c c in
    Tag.update pkg TAG.c c.

  Ltac add_carry_chains pkg :=
    let carry_chains := fresh "carry_chains" in
    let carry_chains := pose_carry_chains carry_chains in
    Tag.update pkg TAG.carry_chains carry_chains.

  Ltac add_a24 pkg :=
    let a24 := fresh "a24" in
    let a24 := pose_a24 a24 in
    Tag.update pkg TAG.a24 a24.

  Ltac add_coef_div_modulus pkg :=
    let coef_div_modulus := fresh "coef_div_modulus" in
    let coef_div_modulus := pose_coef_div_modulus coef_div_modulus in
    Tag.update pkg TAG.coef_div_modulus coef_div_modulus.

  Ltac add_goldilocks pkg :=
    let goldilocks := fresh "goldilocks" in
    let goldilocks := pose_goldilocks goldilocks in
    Tag.update pkg TAG.goldilocks goldilocks.

  Ltac add_modinv_fuel pkg :=
    let modinv_fuel := fresh "modinv_fuel" in
    let modinv_fuel := pose_modinv_fuel modinv_fuel in
    Tag.update pkg TAG.modinv_fuel modinv_fuel.

  Ltac add_upper_bound_of_exponent pkg :=
    let upper_bound_of_exponent := fresh "upper_bound_of_exponent" in
    let upper_bound_of_exponent := pose_upper_bound_of_exponent upper_bound_of_exponent in
    Tag.update pkg TAG.upper_bound_of_exponent upper_bound_of_exponent.

  Ltac add_CurveParameters_package pkg :=
    let pkg := add_sz pkg in
    let pkg := add_bitwidth pkg in
    let pkg := add_s pkg in
    let pkg := add_c pkg in
    let pkg := add_carry_chains pkg in
    let pkg := add_a24 pkg in
    let pkg := add_coef_div_modulus pkg in
    let pkg := add_goldilocks pkg in
    let pkg := add_modinv_fuel pkg in
    let pkg := add_upper_bound_of_exponent pkg in
    Tag.strip_local pkg.
End FillCurveParameters.