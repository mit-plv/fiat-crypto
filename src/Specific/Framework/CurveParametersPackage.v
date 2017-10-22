(* This file is autogenerated from CurveParameters.v by remake_packages.py *)
Require Export Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.Packages.
Require Import Crypto.Util.TagList.

Ltac if_goldilocks pkg tac_true tac_false arg :=
  let goldilocks := Tag.get pkg TAG.goldilocks in
  let goldilocks := (eval vm_compute in (goldilocks : bool)) in
  lazymatch goldilocks with
  | true => tac_true arg
  | false => tac_false arg
  end.

Ltac if_montgomery pkg tac_true tac_false arg :=
  let montgomery := Tag.get pkg TAG.montgomery in
  let montgomery := (eval vm_compute in (montgomery : bool)) in
  lazymatch montgomery with
  | true => tac_true arg
  | false => tac_false arg
  end.

Ltac if_freeze pkg tac_true tac_false arg :=
  let freeze := Tag.get pkg TAG.freeze in
  let freeze := (eval vm_compute in (freeze : bool)) in
  lazymatch freeze with
  | true => tac_true arg
  | false => tac_false arg
  end.

Ltac if_ladderstep pkg tac_true tac_false arg :=
  let ladderstep := Tag.get pkg TAG.ladderstep in
  let ladderstep := (eval vm_compute in (ladderstep : bool)) in
  lazymatch ladderstep with
  | true => tac_true arg
  | false => tac_false arg
  end.


Module MakeCurveParametersPackage (PKG : PrePackage).
  Module Import MakeCurveParametersPackageInternal := MakePackageBase PKG.

  Ltac get_base _ := get TAG.base.
  Notation base := (ltac:(let v := get_base () in exact v)) (only parsing).
  Ltac get_sz _ := get TAG.sz.
  Notation sz := (ltac:(let v := get_sz () in exact v)) (only parsing).
  Ltac get_bitwidth _ := get TAG.bitwidth.
  Notation bitwidth := (ltac:(let v := get_bitwidth () in exact v)) (only parsing).
  Ltac get_s _ := get TAG.s.
  Notation s := (ltac:(let v := get_s () in exact v)) (only parsing).
  Ltac get_c _ := get TAG.c.
  Notation c := (ltac:(let v := get_c () in exact v)) (only parsing).
  Ltac get_carry_chains _ := get TAG.carry_chains.
  Notation carry_chains := (ltac:(let v := get_carry_chains () in exact v)) (only parsing).
  Ltac get_a24 _ := get TAG.a24.
  Notation a24 := (ltac:(let v := get_a24 () in exact v)) (only parsing).
  Ltac get_coef_div_modulus _ := get TAG.coef_div_modulus.
  Notation coef_div_modulus := (ltac:(let v := get_coef_div_modulus () in exact v)) (only parsing).
  Ltac get_goldilocks _ := get TAG.goldilocks.
  Notation goldilocks := (ltac:(let v := get_goldilocks () in exact v)) (only parsing).
  Ltac get_montgomery _ := get TAG.montgomery.
  Notation montgomery := (ltac:(let v := get_montgomery () in exact v)) (only parsing).
  Ltac get_freeze _ := get TAG.freeze.
  Notation freeze := (ltac:(let v := get_freeze () in exact v)) (only parsing).
  Ltac get_ladderstep _ := get TAG.ladderstep.
  Notation ladderstep := (ltac:(let v := get_ladderstep () in exact v)) (only parsing).
  Ltac get_allowable_bit_widths _ := get TAG.allowable_bit_widths.
  Notation allowable_bit_widths := (ltac:(let v := get_allowable_bit_widths () in exact v)) (only parsing).
  Ltac get_freeze_allowable_bit_widths _ := get TAG.freeze_allowable_bit_widths.
  Notation freeze_allowable_bit_widths := (ltac:(let v := get_freeze_allowable_bit_widths () in exact v)) (only parsing).
  Ltac get_upper_bound_of_exponent_tight _ := get TAG.upper_bound_of_exponent_tight.
  Notation upper_bound_of_exponent_tight := (ltac:(let v := get_upper_bound_of_exponent_tight () in exact v)) (only parsing).
  Ltac get_upper_bound_of_exponent_loose _ := get TAG.upper_bound_of_exponent_loose.
  Notation upper_bound_of_exponent_loose := (ltac:(let v := get_upper_bound_of_exponent_loose () in exact v)) (only parsing).
  Ltac get_modinv_fuel _ := get TAG.modinv_fuel.
  Notation modinv_fuel := (ltac:(let v := get_modinv_fuel () in exact v)) (only parsing).
  Ltac get_mul_code _ := get TAG.mul_code.
  Notation mul_code := (ltac:(let v := get_mul_code () in exact v)) (only parsing).
  Ltac get_square_code _ := get TAG.square_code.
  Notation square_code := (ltac:(let v := get_square_code () in exact v)) (only parsing).
End MakeCurveParametersPackage.
