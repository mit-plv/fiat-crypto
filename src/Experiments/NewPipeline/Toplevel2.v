Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Crypto.Util.Strings.String.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.HexString.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Algebra.Ring Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.SubsetoidRing.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Tactics.GetGoal.
Require Import Crypto.Arithmetic.BarrettReduction.Generalized.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Experiments.NewPipeline.Arithmetic.
Require Crypto.Experiments.NewPipeline.Language.
Require Crypto.Experiments.NewPipeline.UnderLets.
Require Crypto.Experiments.NewPipeline.AbstractInterpretation.
Require Crypto.Experiments.NewPipeline.AbstractInterpretationProofs.
Require Crypto.Experiments.NewPipeline.Rewriter.
Require Crypto.Experiments.NewPipeline.MiscCompilerPasses.
Require Crypto.Experiments.NewPipeline.CStringification.
Require Export Crypto.Experiments.NewPipeline.Toplevel1.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import Associational Positional.

Import
  Crypto.Experiments.NewPipeline.Language
  Crypto.Experiments.NewPipeline.UnderLets
  Crypto.Experiments.NewPipeline.AbstractInterpretation
  Crypto.Experiments.NewPipeline.AbstractInterpretationProofs
  Crypto.Experiments.NewPipeline.Rewriter
  Crypto.Experiments.NewPipeline.MiscCompilerPasses
  Crypto.Experiments.NewPipeline.CStringification.

Import
  Language.Compilers
  UnderLets.Compilers
  AbstractInterpretation.Compilers
  AbstractInterpretationProofs.Compilers
  Rewriter.Compilers
  MiscCompilerPasses.Compilers
  CStringification.Compilers.

Import Compilers.defaults.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Notation "x" := (expr.Var x) (only printing, at level 9) : expr_scope.

Import UnsaturatedSolinas.

Module X25519_64.
  Definition n := 5%nat.
  Definition s := 2^255.
  Definition c := [(1, 19)].
  Definition machine_wordsize := 64.
  Local Notation tight_bounds := (tight_bounds n s c).
  Local Notation loose_bounds := (loose_bounds n s c).
  Local Notation prime_bound := (prime_bound s c).

  Derive base_51_relax
         SuchThat (rrelax_correctT n s c machine_wordsize base_51_relax)
         As base_51_relax_correct.
  Proof. Time solve_rrelax machine_wordsize. Time Qed.
  Derive base_51_carry_mul
         SuchThat (rcarry_mul_correctT n s c machine_wordsize base_51_carry_mul)
         As base_51_carry_mul_correct.
  Proof. Time solve_rcarry_mul machine_wordsize. Time Qed.
  Derive base_51_carry
         SuchThat (rcarry_correctT n s c machine_wordsize base_51_carry)
         As base_51_carry_correct.
  Proof. Time solve_rcarry machine_wordsize. Time Qed.
  Derive base_51_add
         SuchThat (radd_correctT n s c machine_wordsize base_51_add)
         As base_51_add_correct.
  Proof. Time solve_radd machine_wordsize. Time Qed.
  Derive base_51_sub
         SuchThat (rsub_correctT n s c machine_wordsize base_51_sub)
         As base_51_sub_correct.
  Proof. Time solve_rsub machine_wordsize. Time Qed.
  Derive base_51_opp
         SuchThat (ropp_correctT n s c machine_wordsize base_51_opp)
         As base_51_opp_correct.
  Proof. Time solve_ropp machine_wordsize. Time Qed.
  Derive base_51_to_bytes
         SuchThat (rto_bytes_correctT n s c machine_wordsize base_51_to_bytes)
         As base_51_to_bytes_correct.
  Proof. Time solve_rto_bytes machine_wordsize. Time Qed.
  Derive base_51_from_bytes
         SuchThat (rfrom_bytes_correctT n s c machine_wordsize base_51_from_bytes)
         As base_51_from_bytes_correct.
  Proof. Time solve_rfrom_bytes machine_wordsize. Time Qed.
  Derive base_51_encode
         SuchThat (rencode_correctT n s c machine_wordsize base_51_encode)
         As base_51_encode_correct.
  Proof. Time solve_rencode machine_wordsize. Time Qed.
  Derive base_51_zero
         SuchThat (rzero_correctT n s c machine_wordsize base_51_zero)
         As base_51_zero_correct.
  Proof. Time solve_rzero machine_wordsize. Time Qed.
  Derive base_51_one
         SuchThat (rone_correctT n s c machine_wordsize base_51_one)
         As base_51_one_correct.
  Proof. Time solve_rone machine_wordsize. Time Qed.
  Lemma base_51_curve_good
    : check_args n s c machine_wordsize (Success tt) = Success tt.
  Proof. vm_compute; reflexivity. Qed.

  Definition base_51_good : GoodT n s c machine_wordsize
    := Good n s c machine_wordsize
            base_51_curve_good
            base_51_carry_mul_correct
            base_51_carry_correct
            base_51_relax_correct
            base_51_add_correct
            base_51_sub_correct
            base_51_opp_correct
            base_51_zero_correct
            base_51_one_correct
            base_51_encode_correct
            base_51_to_bytes_correct
            base_51_from_bytes_correct.

  Print Assumptions base_51_good.
  Import PrintingNotations.
  Set Printing Width 80.
  Open Scope string_scope.
  Local Notation prime_bytes_bounds := (prime_bytes_bounds n s c).
  Print base_51_to_bytes.
  Print base_51_carry_mul.
(*base_51_carry_mul =
fun var : type -> Type =>
(λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
 expr_let x1 := (uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                ((uint64)(x[[1]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19) +₁₂₈
                 ((uint64)(x[[2]]) *₁₂₈ ((uint64)(x0[[3]]) *₆₄ 19) +₁₂₈
                  ((uint64)(x[[3]]) *₁₂₈ ((uint64)(x0[[2]]) *₆₄ 19) +₁₂₈
                   (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[1]]) *₆₄ 19)))) in
 expr_let x2 := (uint64)(x1 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ ((uint64)(x0[[3]]) *₆₄ 19) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[2]]) *₆₄ 19))))) in
 expr_let x3 := (uint64)(x2 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[2]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[3]]) *₆₄ 19))))) in
 expr_let x4 := (uint64)(x3 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[3]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[2]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19))))) in
 expr_let x5 := (uint64)(x4 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[4]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[3]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ (uint64)(x0[[2]]) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ (uint64)(x0[[0]]))))) in
 expr_let x6 := ((uint64)(x1) & 2251799813685247) +₆₄ (uint64)(x5 >> 51) *₆₄ 19 in
 expr_let x7 := (uint64)(x6 >> 51) +₆₄ ((uint64)(x2) & 2251799813685247) in
 expr_let x8 := ((uint64)(x6) & 2251799813685247) in
 expr_let x9 := ((uint64)(x7) & 2251799813685247) in
 expr_let x10 := (uint64)(x7 >> 51) +₆₄ ((uint64)(x3) & 2251799813685247) in
 expr_let x11 := ((uint64)(x4) & 2251799813685247) in
 expr_let x12 := ((uint64)(x5) & 2251799813685247) in
 [x8; x9; x10; x11; x12])%expr
     : Expr
         (type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)
  Print base_51_sub.
  (*
base_51_sub =
fun var : type -> Type =>
(λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
 expr_let x1 := (4503599627370458 +₆₄ (uint64)(x[[0]])) -₆₄ (uint64)(x0[[0]]) in
 expr_let x2 := (4503599627370494 +₆₄ (uint64)(x[[1]])) -₆₄ (uint64)(x0[[1]]) in
 expr_let x3 := (4503599627370494 +₆₄ (uint64)(x[[2]])) -₆₄ (uint64)(x0[[2]]) in
 expr_let x4 := (4503599627370494 +₆₄ (uint64)(x[[3]])) -₆₄ (uint64)(x0[[3]]) in
 expr_let x5 := (4503599627370494 +₆₄ (uint64)(x[[4]])) -₆₄ (uint64)(x0[[4]]) in
 [x1; x2; x3; x4; x5])%expr
     : Expr
         (type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)

  Compute ToString.C.ToFunctionString
          true true "" "fecarry_mul" [] base_51_carry_mul
          None (Some loose_bounds, (Some loose_bounds, tt)).
  (*
void fecarry_mul(uint64_t[5] x1, uint64_t[5] x2, uint64_t[5] x3) {
  uint128_t x4 = (((uint128_t)(x1[0]) * (x2[0])) + (((uint128_t)(x1[1]) * ((x2[4]) * 0x13)) + (((uint128_t)(x1[2]) * ((x2[3]) * 0x13)) + (((uint128_t)(x1[3]) * ((x2[2]) * 0x13)) + ((uint128_t)(x1[4]) * ((x2[1]) * 0x13))))));
  uint128_t x5 = ((uint64_t)(x4 >> 51) + (((uint128_t)(x1[0]) * (x2[1])) + (((uint128_t)(x1[1]) * (x2[0])) + (((uint128_t)(x1[2]) * ((x2[4]) * 0x13)) + (((uint128_t)(x1[3]) * ((x2[3]) * 0x13)) + ((uint128_t)(x1[4]) * ((x2[2]) * 0x13)))))));
  uint128_t x6 = ((uint64_t)(x5 >> 51) + (((uint128_t)(x1[0]) * (x2[2])) + (((uint128_t)(x1[1]) * (x2[1])) + (((uint128_t)(x1[2]) * (x2[0])) + (((uint128_t)(x1[3]) * ((x2[4]) * 0x13)) + ((uint128_t)(x1[4]) * ((x2[3]) * 0x13)))))));
  uint128_t x7 = ((uint64_t)(x6 >> 51) + (((uint128_t)(x1[0]) * (x2[3])) + (((uint128_t)(x1[1]) * (x2[2])) + (((uint128_t)(x1[2]) * (x2[1])) + (((uint128_t)(x1[3]) * (x2[0])) + ((uint128_t)(x1[4]) * ((x2[4]) * 0x13)))))));
  uint128_t x8 = ((uint64_t)(x7 >> 51) + (((uint128_t)(x1[0]) * (x2[4])) + (((uint128_t)(x1[1]) * (x2[3])) + (((uint128_t)(x1[2]) * (x2[2])) + (((uint128_t)(x1[3]) * (x2[1])) + ((uint128_t)(x1[4]) * (x2[0])))))));
  uint64_t x9 = ((uint64_t)(x4 & 0x7ffffffffffffUL) + ((uint64_t)(x8 >> 51) * 0x13));
  uint64_t x10 = ((x9 >> 51) + (uint64_t)(x5 & 0x7ffffffffffffUL));
  x3[0] = (x9 & 0x7ffffffffffffUL);
  x3[1] = (x10 & 0x7ffffffffffffUL);
  x3[2] = ((x10 >> 51) + (uint64_t)(x6 & 0x7ffffffffffffUL));
  x3[3] = (uint64_t)(x7 & 0x7ffffffffffffUL);
  x3[4] = (uint64_t)(x8 & 0x7ffffffffffffUL);
}
   *)
  Compute ToString.C.ToFunctionString
          true true "" "fesub" [] base_51_sub
          None (Some tight_bounds, (Some tight_bounds, tt)).
(*
void fesub(uint64_t[5] x1, uint64_t[5] x2, uint64_t[5] x3) {
  x3[0] = ((0xfffffffffffdaUL + (x1[0])) - (x2[0]));
  x3[1] = ((0xffffffffffffeUL + (x1[1])) - (x2[1]));
  x3[2] = ((0xffffffffffffeUL + (x1[2])) - (x2[2]));
  x3[3] = ((0xffffffffffffeUL + (x1[3])) - (x2[3]));
  x3[4] = ((0xffffffffffffeUL + (x1[4])) - (x2[4]));
}
*)
End X25519_64.

Module P224_64.
  Definition s := 2^224.
  Definition c :=  [(2^96, 1); (1,-1)].
  Definition machine_wordsize := 128.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.
  Set Printing Depth 100000.

  Local Notation "'mul128' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint128, _)%core) @ (#Z_mul_split @ #(ident.Literal (t:=base.type.Z) 340282366920938463463374607431768211456) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'add128' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint128, bool)%core) @ (#Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) 340282366920938463463374607431768211456) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adc128' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint128, bool)%core) @ (#Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) 340282366920938463463374607431768211456) @ c @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'sub128' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint128, bool)%core) @ (#Z_sub_get_borrow @ #(ident.Literal (t:=base.type.Z) 340282366920938463463374607431768211456) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'sbb128' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint128, bool)%core) @ (#Z_sub_with_get_borrow @ #(ident.Literal (t:=base.type.Z) 340282366920938463463374607431768211456) @ c @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'mul64' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint64, _)%core) @ (#Z_mul_split @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'add64' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adc64' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ c @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adx64' '(' c ',' x ',' y ')'" :=
    (#(Z_cast bool) @ (#Z_add_with_carry @ c @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'sub64' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_sub_get_borrow @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'sbb64' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_sub_with_get_borrow @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ c @ x @ y))%expr (at level 50) : expr_scope.
  Set Printing Width 1000000.
  Print mulmod.
End P224_64.

Module P192_64.
  Definition s := 2^192.
  Definition c :=  [(2^64, 1); (1,1)].
  Definition machine_wordsize := 64.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.
  Set Printing Depth 100000.

  Local Notation "'mul64' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint64, _)%core) @ (#Z_mul_split @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'add64' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adc64' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ c @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adx64' '(' c ',' x ',' y ')'" :=
    (#(Z_cast bool) @ (#Z_add_with_carry @ c @ x @ y))%expr (at level 50) : expr_scope.

  Print mulmod.
(*
mulmod = fun var : type -> Type => λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
         expr_let x1 := mul64 ((uint64)(x[[2]]), (uint64)(x0[[2]])) in
         expr_let x2 := mul64 ((uint64)(x[[2]]), (uint64)(x0[[1]])) in
         expr_let x3 := mul64 ((uint64)(x[[2]]), (uint64)(x0[[0]])) in
         expr_let x4 := mul64 ((uint64)(x[[1]]), (uint64)(x0[[2]])) in
         expr_let x5 := mul64 ((uint64)(x[[1]]), (uint64)(x0[[1]])) in
         expr_let x6 := mul64 ((uint64)(x[[1]]), (uint64)(x0[[0]])) in
         expr_let x7 := mul64 ((uint64)(x[[0]]), (uint64)(x0[[2]])) in
         expr_let x8 := mul64 ((uint64)(x[[0]]), (uint64)(x0[[1]])) in
         expr_let x9 := mul64 ((uint64)(x[[0]]), (uint64)(x0[[0]])) in
         expr_let x10 := add64 (x1₂, x9₂) in
         expr_let x11 := adc64 (x10₂, 0, x8₂) in
         expr_let x12 := add64 (x1₁, x10₁) in
         expr_let x13 := adc64 (x12₂, 0, x11₁) in
         expr_let x14 := add64 (x2₂, x12₁) in
         expr_let x15 := adc64 (x14₂, 0, x13₁) in
         expr_let x16 := add64 (x4₂, x14₁) in
         expr_let x17 := adc64 (x16₂, x1₂, x15₁) in
         expr_let x18 := add64 (x2₁, x16₁) in
         expr_let x19 := adc64 (x18₂, x1₁, x17₁) in
         expr_let x20 := add64 (x1₂, x9₁) in
         expr_let x21 := adc64 (x20₂, x3₂, x18₁) in
         expr_let x22 := adc64 (x21₂, x2₂, x19₁) in
         expr_let x23 := add64 (x2₁, x20₁) in
         expr_let x24 := adc64 (x23₂, x4₁, x21₁) in
         expr_let x25 := adc64 (x24₂, x4₂, x22₁) in
         expr_let x26 := add64 (x3₂, x23₁) in
         expr_let x27 := adc64 (x26₂, x5₂, x24₁) in
         expr_let x28 := adc64 (x27₂, x3₁, x25₁) in
         expr_let x29 := add64 (x4₁, x26₁) in
         expr_let x30 := adc64 (x29₂, x7₂, x27₁) in
         expr_let x31 := adc64 (x30₂, x5₁, x28₁) in
         expr_let x32 := add64 (x5₂, x29₁) in
         expr_let x33 := adc64 (x32₂, x6₁, x30₁) in
         expr_let x34 := adc64 (x33₂, x6₂, x31₁) in
         expr_let x35 := add64 (x7₂, x32₁) in
         expr_let x36 := adc64 (x35₂, x8₁, x33₁) in
         expr_let x37 := adc64 (x36₂, x7₁, x34₁) in
         [x35₁; x36₁; x37₁]
     : Expr (type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)

End P192_64.

Module PreFancy.
  Section with_wordmax.
    Context (log2wordmax : Z) (log2wordmax_pos : 1 < log2wordmax) (log2wordmax_even : log2wordmax mod 2 = 0).
    Let wordmax := 2 ^ log2wordmax.
    Lemma wordmax_gt_2 : 2 < wordmax.
    Proof.
      apply Z.le_lt_trans with (m:=2 ^ 1); [ reflexivity | ].
      apply Z.pow_lt_mono_r; omega.
    Qed.

    Lemma wordmax_even : wordmax mod 2 = 0.
    Proof.
      replace 2 with (2 ^ 1) by reflexivity.
      subst wordmax. apply Z.mod_same_pow; omega.
    Qed.

    Let half_bits := log2wordmax / 2.

    Lemma half_bits_nonneg : 0 <= half_bits.
    Proof. subst half_bits; Z.zero_bounds. Qed.

    Let wordmax_half_bits := 2 ^ half_bits.

    Lemma wordmax_half_bits_pos : 0 < wordmax_half_bits.
    Proof. subst wordmax_half_bits half_bits. Z.zero_bounds. Qed.

    Lemma half_bits_squared : (wordmax_half_bits - 1) * (wordmax_half_bits - 1) <= wordmax - 1.
    Proof.
      pose proof wordmax_half_bits_pos.
      subst wordmax_half_bits.
      transitivity (2 ^ (half_bits + half_bits) - 2 * 2 ^ half_bits + 1).
      { rewrite Z.pow_add_r by (subst half_bits; Z.zero_bounds).
        autorewrite with push_Zmul; omega. }
      { transitivity (wordmax - 2 * 2 ^ half_bits + 1); [ | lia].
        subst wordmax.
        apply Z.add_le_mono_r.
        apply Z.sub_le_mono_r.
        apply Z.pow_le_mono_r; [ omega | ].
        rewrite Z.add_diag; subst half_bits.
        apply BinInt.Z.mul_div_le; omega. }
    Qed.

    Lemma wordmax_half_bits_le_wordmax : wordmax_half_bits <= wordmax.
    Proof.
      subst wordmax half_bits wordmax_half_bits.
      apply Z.pow_le_mono_r; [lia|].
      apply Z.div_le_upper_bound; lia.
    Qed.

    Lemma ones_half_bits : wordmax_half_bits - 1 = Z.ones half_bits.
    Proof.
      subst wordmax_half_bits. cbv [Z.ones].
      rewrite Z.shiftl_mul_pow2, <-Z.sub_1_r by auto using half_bits_nonneg.
      lia.
    Qed.

    Lemma wordmax_half_bits_squared : wordmax_half_bits * wordmax_half_bits = wordmax.
    Proof.
      subst wordmax half_bits wordmax_half_bits.
      rewrite <-Z.pow_add_r by Z.zero_bounds.
      rewrite Z.add_diag, Z.mul_div_eq by omega.
      f_equal; lia.
    Qed.

(*
    Section interp.
      Context {interp_cast : zrange -> Z -> Z}.
      Local Notation interp_scalar := (interp_scalar (interp_cast:=interp_cast)).
      Local Notation interp_cast2 := (interp_cast2 (interp_cast:=interp_cast)).
      Local Notation low x := (Z.land x (wordmax_half_bits - 1)).
      Local Notation high x := (x >> half_bits).
      Local Notation shift x imm := ((x << imm) mod wordmax).

      Definition interp_ident {s d} (idc : ident s d) : type.interp s -> type.interp d :=
        match idc with
        | add imm => fun x => Z.add_get_carry_full wordmax (fst x) (shift (snd x) imm)
        | addc imm => fun x => Z.add_with_get_carry_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm)
        | sub imm => fun x => Z.sub_get_borrow_full wordmax (fst x) (shift (snd x) imm)
        | subb imm => fun x => Z.sub_with_get_borrow_full wordmax (fst (fst x)) (snd (fst x)) (shift (snd x) imm)
        | mulll => fun x => low (fst x) * low (snd x)
        | mullh => fun x => low (fst x) * high (snd x)
        | mulhl => fun x => high (fst x) * low (snd x)
        | mulhh => fun x => high (fst x) * high (snd x)
        | rshi n => fun x => Z.rshi wordmax (fst x) (snd x) n
        | selc => fun x => Z.zselect (fst (fst x)) (snd (fst x)) (snd x)
        | selm => fun x => Z.zselect (Z.cc_m wordmax (fst (fst x))) (snd (fst x)) (snd x)
        | sell => fun x => Z.zselect (Z.land (fst (fst x)) 1) (snd (fst x)) (snd x)
        | addm => fun x => Z.add_modulo (fst (fst x)) (snd (fst x)) (snd x)
        end.

      Fixpoint interp {t} (e : @expr type.interp ident t) : type.interp t :=
        match e with
        | Scalar t s => interp_scalar s
        | LetInAppIdentZ s d r idc x f =>
          interp (f (interp_cast r (interp_ident idc (interp_scalar x))))
        | LetInAppIdentZZ s d r idc x f =>
          interp (f (interp_cast2 r (interp_ident idc (interp_scalar x))))
        end.
    End interp.

    Section proofs.
      Context (dummy_arrow : forall s d, type.interp (s -> d)%ctype) (consts : list Z)
              (consts_ok : forall x, In x consts -> 0 <= x <= wordmax - 1).
      Context {interp_cast : zrange -> Z -> Z} {interp_cast_correct : forall r x, lower r <= x <= upper r -> interp_cast r x = x}.
      Local Notation interp_scalar := (interp_scalar (interp_cast:=interp_cast)).
      Local Notation interp_cast2 := (interp_cast2 (interp_cast:=interp_cast)).

      Local Notation word_range := (r[0~>wordmax-1])%zrange.
      Local Notation half_word_range := (r[0~>wordmax_half_bits-1])%zrange.
      Local Notation flag_range := (r[0~>1])%zrange.

      Definition in_word_range (r : zrange) := is_tighter_than_bool r word_range = true.
      Definition in_flag_range (r : zrange) := is_tighter_than_bool r flag_range = true.

      Fixpoint get_range_var (t : type) : type.interp t -> range_type t :=
        match t with
        | type.type_primitive type.Z =>
          fun x => {| lower := x; upper := x |}
        | type.prod a b =>
          fun x => (get_range_var a (fst x), get_range_var b (snd x))
        | _ => fun _ => tt
        end.

      Fixpoint get_range {t} (x : @scalar type.interp t) : range_type t :=
        match x with
        | Var t v => get_range_var t v
        | TT => tt
        | Nil _ => tt
        | Pair _ _ x y => (get_range x, get_range y)
        | Cast r _ => r
        | Cast2 r _ => r
        | Fst _ _ p => fst (get_range p)
        | Snd _ _ p => snd (get_range p)
        | Shiftr n x => ZRange.map (fun y => Z.shiftr y n) (get_range x)
        | Shiftl n x => ZRange.map (fun y => Z.shiftl y n) (get_range x)
        | Land n x => r[0~>n]%zrange
        | CC_m n x => ZRange.map (Z.cc_m n) (get_range x)
        | Primitive type.Z x => {| lower := x; upper := x |}
        | Primitive p x => tt
        end.

      Fixpoint has_range {t} : range_type t -> type.interp t -> Prop :=
        match t with
        | type.type_primitive type.Z =>
          fun r x =>
            lower r <= x <= upper r
        | type.prod a b =>
          fun r x =>
            has_range (fst r) (fst x) /\ has_range (snd r) (snd x)
        | _ => fun _ _ => True
        end.

      Inductive ok_scalar : forall {t}, @scalar type.interp t -> Prop :=
      | sc_ok_var : forall t v, ok_scalar (Var t v)
      | sc_ok_unit : ok_scalar TT
      | sc_ok_nil : forall t, ok_scalar (Nil t)
      | sc_ok_pair : forall A B x y,
          @ok_scalar A x ->
          @ok_scalar B y ->
          ok_scalar (Pair x y)
      | sc_ok_cast : forall r (x : scalar type.Z),
          ok_scalar x ->
          is_tighter_than_bool (get_range x) r = true ->
          ok_scalar (Cast r x)
      | sc_ok_cast2 : forall r (x : scalar (type.prod type.Z type.Z)),
          ok_scalar x ->
          is_tighter_than_bool (fst (get_range x)) (fst r) = true ->
          is_tighter_than_bool (snd (get_range x)) (snd r) = true ->
          ok_scalar (Cast2 r x)
      | sc_ok_fst :
          forall A B p, @ok_scalar (A * B) p -> ok_scalar (Fst p)
      | sc_ok_snd :
          forall A B p, @ok_scalar (A * B) p -> ok_scalar (Snd p)
      | sc_ok_shiftr :
          forall n x, 0 <= n -> ok_scalar x -> ok_scalar (Shiftr n x)
      | sc_ok_shiftl :
          forall n x, 0 <= n -> 0 <= lower (@get_range type.Z x) -> ok_scalar x -> ok_scalar (Shiftl n x)
      | sc_ok_land :
          forall n x, 0 <= n -> 0 <= lower (@get_range type.Z x) -> ok_scalar x -> ok_scalar (Land n x)
      | sc_ok_cc_m :
          forall x, ok_scalar x -> ok_scalar (CC_m wordmax x)
      | sc_ok_prim : forall p x, ok_scalar (@Primitive _ p x)
      .

      Inductive is_halved : scalar type.Z -> Prop :=
      | is_halved_lower :
          forall x : scalar type.Z,
            in_word_range (get_range x) ->
            is_halved (Cast half_word_range (Land (wordmax_half_bits - 1) x))
      | is_halved_upper :
          forall x : scalar type.Z,
            in_word_range (get_range x) ->
            is_halved (Cast half_word_range (Shiftr half_bits x))
      | is_halved_constant :
          forall y z,
            constant_to_scalar consts z = Some y ->
            is_halved y ->
            is_halved (Primitive (t:=type.Z) z)
      .

      Inductive ok_ident : forall s d, scalar s -> range_type d -> ident.ident s d -> Prop :=
      | ok_add :
          forall x y : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair x y)
                     (word_range, flag_range)
                     (ident.Z.add_get_carry_concrete wordmax)
      | ok_addc :
          forall (c x y : scalar type.Z) outr,
            in_flag_range (get_range c) ->
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            lower outr = 0 ->
            (0 <= upper (get_range c) + upper (get_range x) + upper (get_range y) <= upper outr \/ outr = word_range) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair (Pair c x) y)
                     (outr, flag_range)
                     (ident.Z.add_with_get_carry_concrete wordmax)
      | ok_sub :
          forall x y : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair x y)
                     (word_range, flag_range)
                     (ident.Z.sub_get_borrow_concrete wordmax)
      | ok_subb :
          forall b x y : scalar type.Z,
            in_flag_range (get_range b) ->
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            ok_ident _
                     (type.prod type.Z type.Z)
                     (Pair (Pair b x) y)
                     (word_range, flag_range)
                     (ident.Z.sub_with_get_borrow_concrete wordmax)
      | ok_rshi :
          forall (x : scalar (type.prod type.Z type.Z)) n outr,
            in_word_range (fst (get_range x)) ->
            in_word_range (snd (get_range x)) ->
            (* note : using [outr] rather than [word_range] allows for cases where the result has been put in a smaller word size. *)
            lower outr = 0 ->
            0 <= n ->
            ((0 <= (upper (snd (get_range x)) + upper (fst (get_range x)) * wordmax) / 2^n <= upper outr)
              \/ outr = word_range) ->
            ok_ident (type.prod type.Z type.Z) type.Z x outr (ident.Z.rshi_concrete wordmax n)
      | ok_selc :
          forall (x : scalar (type.prod type.Z type.Z)) (y z : scalar type.Z),
            in_flag_range (snd (get_range x)) ->
            in_word_range (get_range y) ->
            in_word_range (get_range z) ->
            ok_ident _
                     type.Z
                     (Pair (Pair (Cast flag_range (Snd x)) y) z)
                     word_range
                     ident.Z.zselect
      | ok_selm :
          forall x y z : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            in_word_range (get_range z) ->
            ok_ident _
                     type.Z
                     (Pair (Pair (Cast flag_range (CC_m wordmax x)) y) z)
                     word_range
                     ident.Z.zselect
      | ok_sell :
          forall x y z : scalar type.Z,
            in_word_range (get_range x) ->
            in_word_range (get_range y) ->
            in_word_range (get_range z) ->
            ok_ident _
                     type.Z
                     (Pair (Pair (Cast flag_range (Land 1 x)) y) z)
                     word_range
                     ident.Z.zselect
      | ok_addm :
          forall (x : scalar (type.prod (type.prod type.Z type.Z) type.Z)),
            in_word_range (fst (fst (get_range x))) ->
            in_word_range (snd (fst (get_range x))) ->
            in_word_range (snd (get_range x)) ->
            upper (fst (fst (get_range x))) + upper (snd (fst (get_range x))) - lower (snd (get_range x)) < wordmax ->
            ok_ident _
                     type.Z
                     x
                     word_range
                     ident.Z.add_modulo
      | ok_mul :
          forall x y : scalar type.Z,
            is_halved x ->
            is_halved y ->
            ok_ident (type.prod type.Z type.Z)
                     type.Z
                     (Pair x y)
                     word_range
                     ident.Z.mul
      .

      Inductive ok_expr : forall {t}, @expr type.interp ident.ident t -> Prop :=
      | ok_of_scalar : forall t s, ok_scalar s -> @ok_expr t (Scalar s)
      | ok_letin_z : forall s d r idc x f,
          ok_ident _ type.Z x r idc ->
          (r <=? word_range)%zrange = true ->
          ok_scalar x ->
          (forall y, has_range (t:=type.Z) r y -> ok_expr (f y)) ->
          ok_expr (@LetInAppIdentZ _ _ s d r idc x f)
      | ok_letin_zz : forall s d r idc x f,
          ok_ident _ (type.prod type.Z type.Z) x (r, flag_range) idc ->
          (r <=? word_range)%zrange = true ->
          ok_scalar x ->
          (forall y, has_range (t:=type.Z * type.Z) (r, flag_range) y -> ok_expr (f y)) ->
          ok_expr (@LetInAppIdentZZ _ _ s d (r, flag_range) idc x f)
      .

      Ltac invert H :=
        inversion H; subst;
        repeat match goal with
               | H : existT _ _ _ = existT _ _ _ |- _ => apply (Eqdep_dec.inj_pair2_eq_dec _ type.type_eq_dec) in H; subst
               end.

      Lemma has_range_get_range_var {t} (v : type.interp t) :
        has_range (get_range_var _ v) v.
      Proof.
        induction t; cbn [get_range_var has_range fst snd]; auto.
        destruct p; auto; cbn [upper lower]; omega.
      Qed.

      Lemma has_range_loosen r1 r2 (x : Z) :
        @has_range type.Z r1 x ->
        is_tighter_than_bool r1 r2 = true ->
        @has_range type.Z r2 x.
      Proof.
        cbv [is_tighter_than_bool has_range]; intros;
          match goal with H : _ && _ = true |- _ => rewrite andb_true_iff in H; destruct H end;
          Z.ltb_to_lt; omega.
      Qed.

      Lemma interp_cast_noop x r :
        @has_range type.Z r x ->
        interp_cast r x = x.
      Proof. cbv [has_range]; intros; auto. Qed.

      Lemma interp_cast2_noop x r :
        @has_range (type.prod type.Z type.Z) r x ->
        interp_cast2 r x = x.
      Proof.
        cbv [has_range interp_cast2]; intros.
        rewrite !interp_cast_correct by tauto.
        destruct x; reflexivity.
      Qed.

      Lemma has_range_shiftr n (x : scalar type.Z) :
        0 <= n ->
        has_range (get_range x) (interp_scalar x) ->
        @has_range type.Z (ZRange.map (fun y : Z => y >> n) (get_range x)) (interp_scalar x >> n).
      Proof. cbv [has_range]; intros; cbn. auto using Z.shiftr_le with omega. Qed.
      Hint Resolve has_range_shiftr : has_range.

      Lemma has_range_shiftl n r x :
        0 <= n -> 0 <= lower r ->
        @has_range type.Z r x ->
        @has_range type.Z (ZRange.map (fun y : Z => y << n) r) (x << n).
      Proof. cbv [has_range]; intros; cbn. auto using Z.shiftl_le_mono with omega. Qed.
      Hint Resolve has_range_shiftl : has_range.

      Lemma has_range_land n (x : scalar type.Z) :
        0 <= n -> 0 <= lower (get_range x) ->
        has_range (get_range x) (interp_scalar x) ->
        @has_range type.Z (r[0~>n])%zrange (Z.land (interp_scalar x) n).
      Proof.
        cbv [has_range]; intros; cbn.
        split; [ apply Z.land_nonneg | apply Z.land_upper_bound_r ]; omega.
      Qed.
      Hint Resolve has_range_land : has_range.

      Lemma has_range_interp_scalar {t} (x : scalar t) :
        ok_scalar x ->
        has_range (get_range x) (interp_scalar x).
      Proof.
        induction 1; cbn [interp_scalar get_range];
          auto with has_range;
          try solve [try inversion IHok_scalar; cbn [has_range];
                     auto using has_range_get_range_var]; [ | | | ].
        { rewrite interp_cast_noop by eauto using has_range_loosen.
          eapply has_range_loosen; eauto. }
        { inversion IHok_scalar.
          rewrite interp_cast2_noop;
            cbn [has_range]; split; eapply has_range_loosen; eauto. }
        { cbn. cbv [has_range] in *.
          pose proof wordmax_gt_2.
          rewrite !Z.cc_m_eq by omega.
          split; apply Z.div_le_mono; Z.zero_bounds; omega. }
        { destruct p; cbn [has_range upper lower]; auto; omega. }
      Qed.
      Hint Resolve has_range_interp_scalar : has_range.

      Lemma has_word_range_interp_scalar (x : scalar type.Z) :
        ok_scalar x ->
        in_word_range (get_range x) ->
        @has_range type.Z word_range (interp_scalar x).
      Proof. eauto using has_range_loosen, has_range_interp_scalar. Qed.

      Lemma in_word_range_nonneg r : in_word_range r -> 0 <= lower r.
      Proof.
        cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff; intuition.
      Qed.

      Lemma in_word_range_upper_nonneg r x : @has_range type.Z r x -> in_word_range r -> 0 <= upper r.
      Proof.
        cbv [in_word_range is_tighter_than_bool]; cbn.
        rewrite andb_true_iff; intuition.
        Z.ltb_to_lt. omega.
      Qed.

      Lemma has_word_range_shiftl n r x :
        0 <= n -> upper r * 2 ^ n <= wordmax - 1 ->
        @has_range type.Z r x ->
        in_word_range r ->
        @has_range type.Z word_range (x << n).
      Proof.
        intros.
        eapply has_range_loosen;
          [ apply has_range_shiftl; eauto using in_word_range_nonneg with has_range; omega | ].
        cbv [is_tighter_than_bool]. cbn.
        apply andb_true_iff; split; apply Z.leb_le;
          [ apply Z.shiftl_nonneg; solve [auto using in_word_range_nonneg] | ].
        rewrite Z.shiftl_mul_pow2 by omega.
        auto.
      Qed.

      Lemma has_range_rshi r n x y :
        0 <= n ->
        0 <= x ->
        0 <= y ->
        lower r = 0 ->
        (0 <= (y + x * wordmax) / 2^n <= upper r \/ r = word_range) ->
        @has_range type.Z r (Z.rshi wordmax x y n).
      Proof.
        pose proof wordmax_gt_2.
        intros. cbv [has_range].
        rewrite Z.rshi_correct by omega.
        match goal with |- context [?x mod ?m] =>
                        pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
        split; [lia|].
        intuition.
        { destruct (Z_lt_dec (upper r) wordmax); [ | lia].
          rewrite Z.mod_small by (split; Z.zero_bounds; omega).
          omega. }
        { subst r. cbn [upper]. omega. }
      Qed.

      Lemma in_word_range_spec r :
        (0 <= lower r /\ upper r <= wordmax - 1)
        <-> in_word_range r.
      Proof.
        intros; cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff.
        intuition; apply Z.leb_le; cbn [upper lower]; try omega.
      Qed.

      Ltac destruct_scalar :=
        match goal with
        | x : scalar (type.prod (type.prod _ _) _) |- _ =>
          match goal with |- context [interp_scalar x] =>
            destruct (interp_scalar x) as [ [? ?] ?];
            destruct (get_range x) as [ [? ?] ?]
          end
        | x : scalar (type.prod _ _) |- _ =>
          match goal with |- context [interp_scalar x] =>
            destruct (interp_scalar x) as [? ?]; destruct (get_range x) as [? ?]
          end
        end.

      Ltac extract_ok_scalar' level x :=
        match goal with
        | H : ok_scalar (Pair (Pair (?f (?g x)) _) _) |- _ =>
          match (eval compute in (4 <=? level)) with
          | true => invert H; extract_ok_scalar' 3 x
          | _ => fail
          end
        | H : ok_scalar (Pair (?f (?g x)) _) |- _ =>
          match (eval compute in (3 <=? level)) with
          | true => invert H; extract_ok_scalar' 2 x
          | _ => fail
          end
        | H : ok_scalar (Pair _ (?f (?g x))) |- _ =>
          match (eval compute in (3 <=? level)) with
          | true => invert H; extract_ok_scalar' 2 x
          | _ => fail
          end
        | H : ok_scalar (?f (?g x)) |- _ =>
          match (eval compute in (2 <=? level)) with
          | true => invert H; extract_ok_scalar' 1 x
          | _ => fail
          end
        | H : ok_scalar (Pair (Pair x _) _) |- _ =>
          match (eval compute in (2 <=? level)) with
          | true => invert H; extract_ok_scalar' 1 x
          | _ => fail
          end
        | H : ok_scalar (Pair (Pair _ x) _) |- _ =>
          match (eval compute in (2 <=? level)) with
          | true => invert H; extract_ok_scalar' 1 x
          | _ => fail
          end
        | H : ok_scalar (?g x) |- _ => invert H
        | H : ok_scalar (Pair x _) |- _ => invert H
        | H : ok_scalar (Pair _ x) |- _ => invert H
        end.

      Ltac extract_ok_scalar :=
        match goal with |- ok_scalar ?x => extract_ok_scalar' 4 x; assumption end.

      Lemma has_half_word_range_shiftr r x :
        in_word_range r ->
        @has_range type.Z r x ->
        @has_range type.Z half_word_range (x >> half_bits).
      Proof.
        cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff.
        cbn [has_range upper lower]; intros; intuition; Z.ltb_to_lt.
        { apply Z.shiftr_nonneg. omega. }
        { pose proof half_bits_nonneg.
          pose proof half_bits_squared.
          assert (x >> half_bits < wordmax_half_bits); [|omega].
          rewrite Z.shiftr_div_pow2 by auto.
          apply Z.div_lt_upper_bound; Z.zero_bounds.
          subst wordmax_half_bits half_bits.
          rewrite <-Z.pow_add_r by omega.
          rewrite Z.add_diag, Z.mul_div_eq, log2wordmax_even by omega.
          autorewrite with zsimplify_fast. subst wordmax. omega. }
      Qed.

      Lemma has_half_word_range_land r x :
        in_word_range r ->
        @has_range type.Z r x ->
        @has_range type.Z half_word_range (x &' (wordmax_half_bits - 1)).
      Proof.
        pose proof wordmax_half_bits_pos.
        cbv [in_word_range is_tighter_than_bool].
        rewrite andb_true_iff.
        cbn [has_range upper lower]; intros; intuition; Z.ltb_to_lt.
        { apply Z.land_nonneg; omega. }
        { apply Z.land_upper_bound_r; omega. }
      Qed.

      Section constant_to_scalar.
        Lemma constant_to_scalar_single_correct s x z :
            0 <= x <= wordmax - 1 ->
            constant_to_scalar_single x z = Some s -> interp_scalar s = z.
        Proof.
          cbv [constant_to_scalar_single].
          break_match; try discriminate; intros; Z.ltb_to_lt; subst;
            try match goal with H : Some _ = Some _ |- _ => inversion H; subst end;
            cbn [interp_scalar]; apply interp_cast_noop.
          { apply has_half_word_range_shiftr with (r:=r[x~>x]%zrange);
            cbv [in_word_range is_tighter_than_bool upper lower has_range]; try omega.
            apply andb_true_iff; split; apply Z.leb_le; omega. }
          { apply has_half_word_range_land with (r:=r[x~>x]%zrange);
            cbv [in_word_range is_tighter_than_bool upper lower has_range]; try omega.
            apply andb_true_iff; split; apply Z.leb_le; omega. }
        Qed.

        Lemma constant_to_scalar_correct s z :
          constant_to_scalar consts z = Some s -> interp_scalar s = z.
        Proof.
          cbv [constant_to_scalar].
          apply fold_right_invariant; try discriminate.
          intros until 2; break_match; eauto using constant_to_scalar_single_correct.
        Qed.

        Lemma constant_to_scalar_single_cases x y z :
          @constant_to_scalar_single type.interp x z = Some y ->
          (y = Cast half_word_range (Land (wordmax_half_bits - 1) (Primitive (t:=type.Z) x)))
          \/ (y = Cast half_word_range (Shiftr half_bits (Primitive (t:=type.Z) x))).
        Proof.
          cbv [constant_to_scalar_single].
          break_match; try discriminate; intros; Z.ltb_to_lt; subst;
            try match goal with H : Some _ = Some _ |- _ => inversion H; subst end;
            tauto.
        Qed.

        Lemma constant_to_scalar_cases y z :
          @constant_to_scalar type.interp consts z = Some y ->
          (exists x,
              @has_range type.Z word_range x
              /\ y = Cast half_word_range (Land (wordmax_half_bits - 1) (Primitive x)))
          \/ (exists x,
                 @has_range type.Z word_range x
                 /\ y = Cast half_word_range (Shiftr half_bits (Primitive x))).
        Proof.
          cbv [constant_to_scalar].
          apply fold_right_invariant; try discriminate.
          intros until 2; break_match; eauto; intros.
          match goal with H : constant_to_scalar_single _ _ = _ |- _ =>
                          destruct (constant_to_scalar_single_cases _ _ _ H); subst end.
          { left; eexists; split; eauto.
            apply consts_ok; auto. }
          { right; eexists; split; eauto.
            apply consts_ok; auto. }
        Qed.

        Lemma ok_scalar_constant_to_scalar y z : constant_to_scalar consts z = Some y -> ok_scalar y.
        Proof.
          pose proof wordmax_half_bits_pos. pose proof half_bits_nonneg.
          let H := fresh in
          intro H; apply constant_to_scalar_cases in H; destruct H as [ [? ?] | [? ?] ]; intuition; subst;
            cbn [has_range lower upper] in *; repeat constructor; cbn [lower get_range]; try apply Z.leb_refl; try omega.
          assert (in_word_range r[x~>x]) by (apply in_word_range_spec; cbn [lower upper]; omega).
          pose proof (has_half_word_range_shiftr r[x~>x] x ltac:(assumption) ltac:(cbv [has_range lower upper]; omega)).
          cbn [has_range ZRange.map is_tighter_than_bool lower upper] in *.
          apply andb_true_iff; cbn [lower upper]; split; apply Z.leb_le; omega.
        Qed.
      End constant_to_scalar.
      Hint Resolve ok_scalar_constant_to_scalar.

      Lemma is_halved_has_range x :
        ok_scalar x ->
        is_halved x ->
        @has_range type.Z half_word_range (interp_scalar x).
      Proof.
        intro; pose proof (has_range_interp_scalar x ltac:(assumption)).
        induction 1; cbn [interp_scalar] in *; intros; try assumption; [ ].
        rewrite <-(constant_to_scalar_correct y z) by assumption.
        eauto using has_range_interp_scalar.
      Qed.

      Lemma ident_interp_has_range s d x r idc:
        ok_scalar x ->
        ok_ident s d x r idc ->
        has_range r (ident.interp idc (interp_scalar x)).
      Proof.
        intro.
        pose proof (has_range_interp_scalar x ltac:(assumption)).
        pose proof wordmax_gt_2.
        induction 1; cbn [ident.interp ident.gen_interp]; intros; try destruct_scalar;
          repeat match goal with
                 | H : _ && _ = true |- _ => rewrite andb_true_iff in H; destruct H; Z.ltb_to_lt
                 |  H : _ /\ _ |- _ => destruct H
                 | H : is_halved _ |- _ => apply is_halved_has_range in H; [ | extract_ok_scalar ]
                 | _ => progress subst
                 | _ => progress (cbv [in_word_range in_flag_range is_tighter_than_bool] in * )
                 | _ => progress (cbn [interp_scalar get_range has_range upper lower fst snd] in * )
                 end.
        {
          autorewrite with to_div_mod.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
          rewrite Z.div_between_0_if by omega.
          split; break_match; lia. }
        {
          autorewrite with to_div_mod.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
          rewrite Z.div_between_0_if by omega.
          match goal with H : _ \/ _ |- _ => destruct H; subst end.
          { split; break_match; try lia.
            destruct (Z_lt_dec (upper outr) wordmax).
            { match goal with |- _ <= ?y mod _ <= ?u =>
                              assert (y <= u) by nia end.
              rewrite Z.mod_small by omega. omega. }
            { match goal with|- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
              omega. } }
          { split; break_match; cbn; lia. } }
        {
          autorewrite with to_div_mod.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
          rewrite Z.div_sub_small by omega.
          split; break_match; lia. }
        {
          autorewrite with to_div_mod.
          match goal with |- context [?a - ?b - ?c] => replace (a - b - c) with (a - (b + c)) by ring end.
          match goal with |- context[?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
          rewrite Z.div_sub_small by omega.
          split; break_match; lia. }
        { apply has_range_rshi; try nia; [ ].
          match goal with H : context [upper ?ra + upper ?rb * wordmax] |- context [?a + ?b * wordmax] =>
                          assert ((a + b * wordmax) / 2^n <= (upper ra + upper rb * wordmax) / 2^n) by (apply Z.div_le_mono; Z.zero_bounds; nia)
          end.
          match goal with H : _ \/ ?P |- _ \/ ?P => destruct H; [left|tauto] end.
          split; Z.zero_bounds; nia. }
        { rewrite Z.zselect_correct. break_match; omega. }
        { cbn [interp_scalar fst snd get_range] in *.
          rewrite Z.zselect_correct. break_match; omega. }
        { cbn [interp_scalar fst snd get_range] in *.
          rewrite Z.zselect_correct. break_match; omega. }
        { rewrite Z.add_modulo_correct.
          break_match; Z.ltb_to_lt; omega. }
        { cbn [interp_scalar has_range fst snd get_range upper lower] in *.
          pose proof half_bits_squared. nia. }
      Qed.

      Lemma has_flag_range_cc_m r x :
        @has_range type.Z r x ->
        in_word_range r ->
        @has_range type.Z flag_range (Z.cc_m wordmax x).
      Proof.
        cbv [has_range in_word_range is_tighter_than_bool].
        cbn [upper lower]; rewrite andb_true_iff; intros.
        match goal with H : _ /\ _ |- _ => destruct H; Z.ltb_to_lt end.
        pose proof wordmax_gt_2. pose proof wordmax_even.
        pose proof (Z.cc_m_small wordmax x). omega.
      Qed.

      Lemma has_flag_range_cc_m' (x : scalar type.Z) :
        ok_scalar x ->
        in_word_range (get_range x) ->
        @has_range type.Z flag_range (Z.cc_m wordmax (interp_scalar x)).
      Proof. eauto using has_flag_range_cc_m with has_range. Qed.

      Lemma has_flag_range_land r x :
        @has_range type.Z r x ->
        in_word_range r ->
        @has_range type.Z flag_range (Z.land x 1).
      Proof.
        cbv [has_range in_word_range is_tighter_than_bool].
        cbn [upper lower]; rewrite andb_true_iff; intuition; Z.ltb_to_lt.
        { apply Z.land_nonneg. left; omega. }
        { apply Z.land_upper_bound_r; omega. }
      Qed.

      Lemma has_flag_range_land' (x : scalar type.Z) :
        ok_scalar x ->
        in_word_range (get_range x) ->
        @has_range type.Z flag_range (Z.land (interp_scalar x) 1).
      Proof. eauto using has_flag_range_land with has_range. Qed.

      Ltac rewrite_cast_noop_in_mul :=
        repeat match goal with
               | _ => rewrite interp_cast_noop with (r:=half_word_range) in *
                   by (eapply has_range_loosen; auto using has_range_land, has_range_interp_scalar)
               | _ => rewrite interp_cast_noop with (r:=half_word_range) in *
                   by (eapply has_range_loosen; try apply has_range_shiftr; auto using has_range_interp_scalar;
                       cbn [ZRange.map get_range] in *; auto)
               | _ => rewrite interp_cast_noop by assumption
               end.

      Lemma is_halved_cases x :
        is_halved x ->
        ok_scalar x ->
        (exists y,
            invert_lower consts x = Some y
            /\ invert_upper consts x = None
            /\ interp_scalar y &' (wordmax_half_bits - 1) = interp_scalar x)
        \/ (exists y,
               invert_lower consts x = None
               /\ invert_upper consts x = Some y
               /\ interp_scalar y >> half_bits = interp_scalar x).
      Proof.
        induction 1; intros; cbn; rewrite ?Z.eqb_refl; cbn.
        { left. eexists; repeat split; auto.
          rewrite interp_cast_noop; [ reflexivity | ].
          apply has_half_word_range_land with (r:=get_range x); auto.
          apply has_range_interp_scalar; extract_ok_scalar. }
        { right. eexists; repeat split; auto.
          rewrite interp_cast_noop; [ reflexivity | ].
          apply has_half_word_range_shiftr with (r:=get_range x); auto.
          apply has_range_interp_scalar; extract_ok_scalar. }
        { match goal with H : constant_to_scalar _ _ = Some _ |- _ =>
                          rewrite H;
                            let P := fresh in
                            destruct (constant_to_scalar_cases _ _ H) as [ [? [? ?] ] | [? [? ?] ] ];
                              subst; cbn; rewrite ?Z.eqb_refl; cbn
          end.
          { left; eexists; repeat split; auto.
            erewrite <-constant_to_scalar_correct by eassumption.
            subst. cbn.
            rewrite interp_cast_noop; [ reflexivity | ].
            eapply has_half_word_range_land with (r:=word_range); auto.
            cbv [in_word_range is_tighter_than_bool].
            rewrite !Z.leb_refl; reflexivity. }
          { right; eexists; repeat split; auto.
            erewrite <-constant_to_scalar_correct by eassumption.
            subst. cbn.
            rewrite interp_cast_noop; [ reflexivity | ].
            eapply has_half_word_range_shiftr with (r:=word_range); auto.
            cbv [in_word_range is_tighter_than_bool].
            rewrite !Z.leb_refl; reflexivity. } }
      Qed.

      Lemma halved_mul_range x y :
        ok_scalar (Pair x y) ->
        is_halved x ->
        is_halved y ->
        0 <= interp_scalar x * interp_scalar y < wordmax.
      Proof.
        intro Hok; invert Hok. intros.
        repeat match goal with H : _ |- _ => apply is_halved_has_range in H; [|assumption] end.
        cbv [has_range lower upper] in *.
        pose proof half_bits_squared. nia.
      Qed.

      Lemma of_straightline_ident_mul_correct r t x y g :
        is_halved x ->
        is_halved y ->
        ok_scalar (Pair x y) ->
        (word_range <=? r)%zrange = true ->
        @has_range type.Z word_range (ident.interp ident.Z.mul (interp_scalar (Pair x y))) ->
        @interp interp_cast _ (of_straightline_ident dummy_arrow consts ident.Z.mul t r (Pair x y) g) =
        @interp interp_cast _ (g (ident.interp ident.Z.mul (interp_scalar (Pair x y)))).
      Proof.
        intros Hx Hy Hok ? ?; invert Hok; cbn [interp_scalar of_straightline_ident];
        destruct (is_halved_cases x Hx ltac:(assumption)) as [ [? [Pxlow [Pxhigh Pxi] ] ] | [? [Pxlow [Pxhigh Pxi] ] ] ];
          rewrite ?Pxlow, ?Pxhigh;
          destruct (is_halved_cases y Hy ltac:(assumption)) as [ [? [Pylow [Pyhigh Pyi] ] ] | [? [Pylow [Pyhigh Pyi] ] ] ];
          rewrite ?Pylow, ?Pyhigh;
          cbn; rewrite Pxi, Pyi; assert (0 <= interp_scalar x * interp_scalar y < wordmax) by (auto using halved_mul_range);
            rewrite interp_cast_noop by (cbv [is_tighter_than_bool] in *; cbn [has_range upper lower] in *; rewrite andb_true_iff in *; intuition; Z.ltb_to_lt; lia); reflexivity.
      Qed.

      Lemma has_word_range_mod_small x:
        @has_range type.Z word_range x ->
        x mod wordmax = x.
      Proof.
        cbv [has_range upper lower].
        intros. apply Z.mod_small; omega.
      Qed.

      Lemma half_word_range_le_word_range r :
        upper r = wordmax_half_bits - 1 ->
        lower r = 0 ->
        (r <=? word_range)%zrange = true.
      Proof.
        pose proof wordmax_half_bits_le_wordmax.
        destruct r; cbv [is_tighter_than_bool ZRange.lower ZRange.upper].
        intros; subst.
        apply andb_true_iff; split; Z.ltb_to_lt; lia.
      Qed.

      Lemma and_shiftl_half_bits_eq x :
        (x &' (wordmax_half_bits - 1)) << half_bits = x << half_bits mod wordmax.
      Proof.
        rewrite ones_half_bits.
        rewrite Z.land_ones, !Z.shiftl_mul_pow2 by auto using half_bits_nonneg.
        rewrite <-wordmax_half_bits_squared.
        subst wordmax_half_bits.
        rewrite Z.mul_mod_distr_r_full.
        reflexivity.
      Qed.

      Lemma in_word_range_word_range : in_word_range word_range.
      Proof.
        cbv [in_word_range is_tighter_than_bool].
        rewrite !Z.leb_refl; reflexivity.
      Qed.

      Lemma invert_shift_correct (s : scalar type.Z) x imm :
        ok_scalar s ->
        invert_shift consts s = Some (x, imm) ->
        interp_scalar s = (interp_scalar x << imm) mod wordmax.
      Proof.
        intros Hok ?; invert Hok;
          try match goal with H : ok_scalar ?x, H' : context[Cast _ ?x] |- _ =>
                          invert H end;
          try match goal with H : ok_scalar ?x, H' : context[Shiftl _ ?x] |- _ =>
                          invert H end;
          try match goal with H : ok_scalar ?x, H' : context[Shiftl _ (Cast _ ?x)] |- _ =>
                          invert H end;
          try (cbn [invert_shift invert_upper invert_upper'] in *; discriminate);
          repeat match goal with
                 | _ => progress (cbn [invert_shift invert_lower invert_lower' invert_upper invert_upper' interp_scalar fst snd] in * )
                 | _ => rewrite interp_cast_noop by eauto using has_half_word_range_land, has_half_word_range_shiftr, in_word_range_word_range, has_range_loosen
                 | H : ok_scalar (Shiftr _ _) |- _ => apply has_range_interp_scalar in H
                 | H : ok_scalar (Shiftl _ _) |- _ => apply has_range_interp_scalar in H
                 | H : ok_scalar (Land _ _) |- _ => apply has_range_interp_scalar in H
                 | H : context [if ?x then _ else _] |- _ =>
                   let Heq := fresh in case_eq x; intro Heq; rewrite Heq in H
                 | H : context [match @constant_to_scalar ?v ?consts ?x with _ => _ end] |- _ =>
                   let Heq := fresh in
                   case_eq (@constant_to_scalar v consts x); intros until 0; intro Heq; rewrite Heq in *; [|discriminate];
                     destruct (constant_to_scalar_cases _ _ Heq) as [ [? [? ?] ] | [? [? ?] ] ]; subst;
                       pose proof (ok_scalar_constant_to_scalar _ _ Heq)
                 | H : constant_to_scalar _ _ = Some _ |- _ => erewrite <-(constant_to_scalar_correct _ _ H)
                 | H : _ |- _ => rewrite andb_true_iff in H; destruct H; Z.ltb_to_lt
                 | H : Some _ = Some _ |- _ => progress (invert H)
                 | _ => rewrite has_word_range_mod_small by eauto using has_range_loosen, half_word_range_le_word_range
                 | _ => rewrite has_word_range_mod_small by
                       (eapply has_range_loosen with (r1:=half_word_range);
                        [ eapply has_half_word_range_shiftr with (r:=word_range) | ];
                        eauto using in_word_range_word_range, half_word_range_le_word_range)
                 | _ => rewrite and_shiftl_half_bits_eq
                 | _ => progress subst
                 | _ => reflexivity
                 | _ => discriminate
                 end.
      Qed.

      Local Ltac solve_commutative_replace :=
        match goal with
               | |- @eq (_ * _) ?x ?y =>
                 replace x with (fst x, snd x) by (destruct x; reflexivity);
                 replace y with (fst y, snd y) by (destruct y; reflexivity)
        end; autorewrite with to_div_mod; solve [repeat (f_equal; try ring)].

      Fixpoint is_tighter_than_bool_range_type t : range_type t -> range_type t -> bool :=
        match t with
        | type.type_primitive type.Z => (fun r1 r2 => (r1 <=? r2)%zrange)
        | type.prod a b => fun r1 r2 =>
                             (is_tighter_than_bool_range_type a (fst r1) (fst r2))
                               && (is_tighter_than_bool_range_type b (snd r1) (snd r2))
        | _ => fun _ _ => true
        end.

      Definition range_ok {t} : range_type t -> Prop :=
        match t with
        | type.type_primitive type.Z => fun r => in_word_range r
        | type.prod type.Z type.Z => fun r => in_word_range (fst r) /\ snd r = flag_range
        | _ => fun _ => False
        end.

      Lemma of_straightline_ident_correct s d t x r r' (idc : ident.ident s d) g :
        ok_ident s d x r idc ->
        range_ok r' ->
        is_tighter_than_bool_range_type d r r' = true ->
        ok_scalar x ->
        @interp interp_cast _ (of_straightline_ident dummy_arrow consts idc t r' x g) =
        @interp interp_cast _ (g (ident.interp idc (interp_scalar x))).
      Proof.
        intros.
        pose proof wordmax_half_bits_pos.
        pose proof (ident_interp_has_range _ _ x r idc ltac:(assumption) ltac:(assumption)).
        match goal with H : ok_ident _ _ _ _ _ |- _ => induction H end;
          try solve [auto using of_straightline_ident_mul_correct];
          cbv [is_tighter_than_bool_range_type is_tighter_than_bool range_ok] in *;
          cbn [of_straightline_ident ident.interp ident.gen_interp
                                     invert_selm invert_sell] in *;
            intros; rewrite ?Z.eqb_refl; cbn [andb];
            try match goal with |- context [invert_shift] => break_match end;
            cbn [interp interp_ident]; try destruct_scalar;
          repeat match goal with
                   | _ => progress (cbn [fst snd interp_scalar] in * )
                   | _ => progress break_match; [ ]
                   | _ => progress autorewrite with zsimplify_fast
                   | _ => progress Z.ltb_to_lt
                   | H : _ /\ _ |- _ => destruct H
                   | _ => rewrite andb_true_iff in *
                   | _ => rewrite interp_cast_noop with (r:=flag_range) in *
                       by (apply has_flag_range_cc_m'; auto; extract_ok_scalar)
                   | _ => rewrite interp_cast_noop with (r:=flag_range) in *
                       by (apply has_flag_range_land'; auto; extract_ok_scalar)
                   | H : _ = (_,_) |- _ => progress (inversion H; subst)
                   | H : invert_shift _ _ = Some _ |- _ =>
                     apply invert_shift_correct in H; [|extract_ok_scalar];
                       rewrite <-H
                   | H : has_range ?r  (?f ?x ?y) |- context [?f ?y ?x] =>
                     replace (f y x) with (f x y) by solve_commutative_replace
                   | _ => rewrite has_word_range_mod_small
                       by (eapply has_range_loosen;
                           [apply has_range_interp_scalar; extract_ok_scalar|];
                           assumption)
                   | _ => rewrite interp_cast_noop by (cbn [has_range fst snd] in *; split; lia)
                   | _ => rewrite interp_cast2_noop by (cbn [has_range fst snd] in *; split; lia)
                   | _ => reflexivity
                 end.
      Qed.

      Lemma of_straightline_correct {t} (e : expr t) :
        ok_expr e ->
        @interp interp_cast _ (of_straightline dummy_arrow consts e)
        = Straightline.expr.interp (interp_ident:=@ident.interp) (interp_cast:=interp_cast) e.
      Proof.
        induction 1; cbn [of_straightline]; intros;
          repeat match goal with
                 | _ => progress cbn [Straightline.expr.interp]
                 | _ => erewrite of_straightline_ident_correct
                     by (cbv [range_ok is_tighter_than_bool_range_type];
                         eauto using in_word_range_word_range;
                         try apply andb_true_iff; auto)
                 | _ => rewrite interp_cast_noop by eauto using has_range_loosen, ident_interp_has_range
                 | _ => rewrite interp_cast2_noop by eauto using has_range_loosen, ident_interp_has_range
                 | H : forall y, has_range _ y -> interp _ = _ |- _ => rewrite H by eauto using has_range_loosen, ident_interp_has_range
                 | _ => reflexivity
        end.
      Qed.
    End proofs.

   Section no_interp_cast.
      Context (dummy_arrow : forall s d, type.interp (s -> d)%ctype) (consts : list Z)
              (consts_ok : forall x, In x consts -> 0 <= x <= wordmax - 1).

      Local Arguments interp _ {_} _.
      Local Arguments interp_scalar _ {_} _.

      Local Ltac tighter_than_to_le :=
        repeat match goal with
               | _ => progress (cbv [is_tighter_than_bool] in * )
               | _ => rewrite andb_true_iff in *
               | H : _ /\ _ |- _ => destruct H
               end; Z.ltb_to_lt.

      Lemma replace_interp_cast_scalar {t} (x : scalar t) interp_cast interp_cast'
        (interp_cast_correct : forall r x, lower r <= x <= upper r -> interp_cast r x = x)
        (interp_cast'_correct : forall r x, lower r <= x <= upper r -> interp_cast' r x = x) :
        ok_scalar x ->
        interp_scalar interp_cast x = interp_scalar interp_cast' x.
      Proof.
        induction 1; cbn [interp_scalar Straightline.expr.interp_scalar];
          repeat match goal with
                 | _ => progress (cbv [has_range interp_cast2] in * )
                 | _ => progress tighter_than_to_le
                 | H : ok_scalar _ |- _ => apply (has_range_interp_scalar (interp_cast_correct:=interp_cast_correct)) in H
                 | _ => rewrite <-IHok_scalar
                 | _ => rewrite interp_cast_correct by omega
                 | _ => rewrite interp_cast'_correct by omega
                 | _ => congruence
                 end.
      Qed.

      Lemma replace_interp_cast {t} (e : expr t) interp_cast interp_cast'
        (interp_cast_correct : forall r x, lower r <= x <= upper r -> interp_cast r x = x)
        (interp_cast'_correct : forall r x, lower r <= x <= upper r -> interp_cast' r x = x) :
        ok_expr consts e ->
        interp interp_cast (of_straightline dummy_arrow consts e) =
        interp interp_cast' (of_straightline dummy_arrow consts e).
      Proof.
        induction 1; intros; cbn [of_straightline interp].
        { apply replace_interp_cast_scalar; auto. }
        { erewrite !of_straightline_ident_correct by (eauto; cbv [range_ok]; apply in_word_range_word_range).
          rewrite replace_interp_cast_scalar with (interp_cast'0:=interp_cast') by auto.
          eauto using ident_interp_has_range. }
        { erewrite !of_straightline_ident_correct by
              (eauto; try solve [cbv [range_ok]; split; auto using in_word_range_word_range];
               cbv [is_tighter_than_bool_range_type]; apply andb_true_iff; split; auto).
          rewrite replace_interp_cast_scalar with (interp_cast'0:=interp_cast') by auto.
          eauto using ident_interp_has_range. }
      Qed.
    End no_interp_cast.
*)
  End with_wordmax.
(*
  Definition of_Expr {s d} (log2wordmax : Z) (consts : list Z) (e : Expr (s -> d))
             (var : type -> Type) (x : var s) dummy_arrow : @Straightline.expr.expr var ident d :=
    @of_straightline log2wordmax var dummy_arrow consts _ (Straightline.of_Expr e var x dummy_arrow).
*)
  Definition interp_cast_mod w r x := if (lower r =? 0)
                                      then if (upper r =? 2^w - 1)
                                           then x mod (2^w)
                                           else if (upper r =? 1)
                                                then x mod 2
                                                else x
                                      else x.

  Lemma interp_cast_mod_correct w r x :
    lower r <= x <= upper r ->
    interp_cast_mod w r x = x.
  Proof.
    cbv [interp_cast_mod].
    intros; break_match; rewrite ?andb_true_iff in *; intuition; Z.ltb_to_lt;
      apply Z.mod_small; omega.
  Qed.
(*
  Lemma of_Expr_correct {s d} (log2wordmax : Z) (consts : list Z) (e : Expr (s -> d))
        (e' : (type.interp s -> Uncurried.expr.expr d))
        (x : type.interp s) dummy_arrow :
    e type.interp = Abs e' ->
    1 < log2wordmax ->
    log2wordmax mod 2 = 0 ->
    Straightline.expr.ok_expr (e' x) ->
    (forall x0 : Z, In x0 consts -> 0 <= x0 <= 2 ^ log2wordmax - 1) ->
    ok_expr log2wordmax consts
            (of_uncurried (dummy_arrow:=dummy_arrow) (depth (fun _ : type => unit) (fun _ : type => tt) (e _)) (e' x)) ->
    (depth type.interp (@DefaultValue.type.default) (e' x) <= depth (fun _ : type => unit) (fun _ : type => tt) (e _))%nat ->
    @interp log2wordmax (interp_cast_mod log2wordmax) _ (of_Expr log2wordmax consts e type.interp x dummy_arrow) = @Uncurried.expr.interp _ (@ident.interp) _ (e type.interp) x.
  Proof.
    intro He'; intros; cbv [of_Expr Straightline.of_Expr].
    rewrite He'; cbn [invert_Abs expr.interp].
    assert (forall r z, lower r <= z <= upper r -> ident.cast ident.cast_outside_of_range r z = z) as interp_cast_correct.
    { cbv [ident.cast]; intros; break_match; rewrite ?andb_true_iff, ?andb_false_iff in *; intuition; Z.ltb_to_lt; omega. }
    erewrite replace_interp_cast with (interp_cast':=ident.cast ident.cast_outside_of_range) by auto using interp_cast_mod_correct.
    rewrite of_straightline_correct by auto.
    erewrite Straightline.expr.of_uncurried_correct by eassumption.
    reflexivity.
  Qed.
*)
  Notation LetInAppIdentZ S D r eidc x f
    := (expr.LetIn
          (A:=type.base (base.type.type_base base.type.Z))
          (B:=type.base D)
          (expr.App
             (s:=type.base (base.type.type_base base.type.Z))
             (d:=type.base (base.type.type_base base.type.Z))
             (expr.Ident (ident.Z_cast r))
             (expr.App
                (s:=type.base S)
                (d:=type.base (base.type.type_base base.type.Z))
                eidc
                x))
          f).
  Notation LetInAppIdentZZ S D r eidc x f
    := (expr.LetIn
          (A:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
          (B:=type.base D)
          (expr.App
             (s:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
             (d:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
             (expr.Ident (ident.Z_cast2 r))
             (expr.App
                (s:=type.base S)
                (d:=type.base (base.type.prod (base.type.type_base base.type.Z) (base.type.type_base base.type.Z)))
                eidc
                x))
          f).
  Module Notations.
    Import PrintingNotations.
    (*Import Straightline.expr.*)

    Local Open Scope expr_scope.
    Local Notation "'tZ'" := (base.type.type_base base.type.Z).
    Notation "'RegZero'" := (expr.Ident (ident.Literal 0)).
    Notation "$ x" := (#(ident.Z_cast uint256) @ (#ident.fst @ (#(ident.Z_cast2 (uint256,bool)%core) @ (expr.Var x)))) (at level 10, format "$ x").
    Notation "$ x" := (#(ident.Z_cast uint128) @ (#ident.fst @ (#(ident.Z_cast2 (uint128,bool)%core) @ (expr.Var x)))) (at level 10, format "$ x").
    Notation "$ x ₁" := (#(ident.Z_cast uint256) @ (#ident.fst @ (expr.Var x))) (at level 10, format "$ x ₁").
    Notation "$ x ₂" := (#(ident.Z_cast uint256) @ (#ident.snd @ (expr.Var x))) (at level 10, format "$ x ₂").
    Notation "$ x" := (#(ident.Z_cast uint256) @ (expr.Var x)) (at level 10, format "$ x").
    Notation "$ x" := (#(ident.Z_cast uint128) @ (expr.Var x)) (at level 10, format "$ x").
    Notation "$ x" := (#(ident.Z_cast bool) @ (expr.Var x)) (at level 10, format "$ x").
    Notation "carry{ $ x }" := (#(ident.Z_cast bool) @ (#ident.snd @ (#(ident.Z_cast2 (uint256, bool)%core) @ (expr.Var x))))
                                 (at level 10, format "carry{ $ x }").
    Notation "Lower{ x }" := (#(ident.Z_cast uint128) @ (#(ident.Z_land 340282366920938463463374607431768211455) @ x))
                               (at level 10, format "Lower{ x }").
    Notation "f @( y , x1 , x2 ); g "
      := (LetInAppIdentZZ _ _ (uint256, bool)%core f (x1, x2) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ); '//' g ").
    Notation "f @( y , x1 , x2 , x3 ); g "
      := (LetInAppIdentZZ _ _ (uint256, bool)%core f (#ident.pair @ (#ident.pair @ x1 @ x2) @ x3) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ,  x3 ); '//' g ").
    Notation "f @( y , x1 , x2 , x3 ); '#128' g "
      := (LetInAppIdentZZ _ _ (uint128, bool)%core f (#ident.pair @ (#ident.pair @ x1 @ x2) @ x3) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ,  x3 );  '#128' '//' g ").
    Notation "f @( y , x1 , x2 ); g "
      := (LetInAppIdentZ _ _ uint256 f (#ident.pair @ x1 @ x2) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ); '//' g ").
    Notation "f @( y , x1 , x2 , x3 ); g "
      := (LetInAppIdentZ _ _ uint256 f (#ident.pair @ (#ident.pair @ x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "f @( y ,  x1 ,  x2 ,  x3 ); '//' g ").
    (* special cases for when the ident constructor takes a constant argument *)
    Notation "add@( y , x1 , x2 , n ); g"
      := (LetInAppIdentZZ _ _ (uint256, bool) (#(ident.fancy_add 256 n)) (#ident.pair @ x1 x2) (fun y => g))
           (at level 10, g at level 200, format "add@( y ,  x1 ,  x2 ,  n ); '//' g").
    Notation "addc@( y , x1 , x2 , x3 , n ); g"
      := (LetInAppIdentZZ _ _ (uint256, bool) (#(ident.fancy_addc 256 n)) (#ident.pair @ (#ident.pair @ x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "addc@( y ,  x1 ,  x2 ,  x3 ,  n ); '//' g").
    Notation "addc@( y , x1 , x2 , x3 , n ); '#128' g"
      := (LetInAppIdentZZ _ _ (uint128, bool) (#(ident.fancy_addc 256 n)) (#ident.pair @ (#ident.pair @ x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "addc@( y ,  x1 ,  x2 ,  x3 ,  n );  '#128' '//' g").
    Notation "sub@( y , x1 , x2 , n ); g"
      := (LetInAppIdentZZ _ _ (uint256, bool) (#(ident.fancy_sub 256 n)) (#ident.pair @ x1 x2) (fun y => g))
           (at level 10, g at level 200, format "sub@( y ,  x1 ,  x2 ,  n ); '//' g").
    Notation "subb@( y , x1 , x2 , x3 , n ); g"
      := (LetInAppIdentZZ _ _ (uint256, bool) (#(ident.fancy_subb 256 n)) (#ident.pair @ (#ident.pair @ x1 x2) x3) (fun y => g))
           (at level 10, g at level 200, format "subb@( y ,  x1 ,  x2 ,  x3 ,  n ); '//' g").
    Notation "rshi@( y , x1 , x2 , n ); g"
      := (LetInAppIdentZ _ _ _ (#(ident.fancy_rshi 256 n)) (#ident.pair @ x1 x2) (fun y => g))
           (at level 10, g at level 200, format "rshi@( y ,  x1 ,  x2 , n ); '//' g ").
    (*Notation "'ret' $ x" := (Scalar (expr.Var x)) (at level 10, format "'ret'  $ x").*)
    Notation "( x , y )" := (#ident.pair @ x @ y) (at level 10, left associativity).
  End Notations.
(*
  Module Tactics.
    Ltac ok_expr_step' :=
      match goal with
      | _ => assumption
      | |- _ <= _ <= _ \/ @eq zrange _ _ =>
        right; lazy; try split; congruence
      | |- _ <= _ <= _ \/ @eq zrange _ _ =>
        left; lazy; try split; congruence
      | |- context [PreFancy.ok_ident] => constructor
      | |- context [PreFancy.ok_scalar] => constructor; try omega
      | |- context [PreFancy.is_halved] => eapply PreFancy.is_halved_constant; [lazy; reflexivity | ]
      | |- context [PreFancy.is_halved] => constructor
      | |- context [PreFancy.in_word_range] => lazy; reflexivity
      | |- context [PreFancy.in_flag_range] => lazy; reflexivity
      | |- context [PreFancy.get_range] =>
        cbn [PreFancy.get_range lower upper fst snd ZRange.map]
      | x : type.interp (type.prod _ _) |- _ => destruct x
      | |- (_ <=? _)%zrange = true =>
        match goal with
        | |- context [PreFancy.get_range_var] =>
          cbv [is_tighter_than_bool PreFancy.has_range fst snd upper lower] in *; cbn;
          apply andb_true_iff; split; apply Z.leb_le
        | _ => lazy
        end; omega || reflexivity
      | |- @eq zrange _ _ => lazy; reflexivity
      | |- _ <= _ => omega
      | |- _ <= _ <= _ => omega
      end; intros.

    Ltac ok_expr_step :=
      match goal with
      | |- context [PreFancy.ok_expr] => constructor; cbn [fst snd]; repeat ok_expr_step'
      end; intros; cbn [Nat.max].
  End Tactics.
 *)
  Notation interp w := (@expr.interp base.type ident.ident base.interp (@ident.gen_interp (PreFancy.interp_cast_mod w))).
  Notation Interp w := (@expr.Interp base.type ident.ident base.interp (@ident.gen_interp (PreFancy.interp_cast_mod w))).
End PreFancy.

Module Fancy.
  (*Import Straightline.expr.*)

  Module CC.
    Inductive code : Type :=
    | C : code
    | M : code
    | L : code
    | Z : code
    .

    Record state :=
      { cc_c : bool; cc_m : bool; cc_l : bool; cc_z : bool }.

    Definition code_dec (x y : code) : {x = y} + {x <> y}.
    Proof. destruct x, y; try apply (left eq_refl); right; congruence. Defined.

    Definition update (to_write : list code) (result : BinInt.Z) (cc_spec : code -> BinInt.Z -> bool) (old_state : state)
      : state :=
      {|
        cc_c := if (In_dec code_dec C to_write)
                then cc_spec C result
                else old_state.(cc_c);
        cc_m := if (In_dec code_dec M to_write)
                then cc_spec M result
                else old_state.(cc_m);
        cc_l := if (In_dec code_dec L to_write)
                then cc_spec L result
                else old_state.(cc_l);
        cc_z := if (In_dec code_dec Z to_write)
                then cc_spec Z result
                else old_state.(cc_z)
      |}.

  End CC.

  Record instruction :=
    {
      num_source_regs : nat;
      writes_conditions : list CC.code;
      spec : tuple Z num_source_regs -> CC.state -> Z
    }.

  Section expr.
    Context {name : Type} (name_eqb : name -> name -> bool) (wordmax : Z) (cc_spec : CC.code -> Z -> bool).

    Inductive expr :=
    | Ret : name -> expr
    | Instr (i : instruction)
            (rd : name) (* destination register *)
            (args : tuple name i.(num_source_regs)) (* source registers *)
            (cont : expr) (* next line *)
      : expr
    .

    Fixpoint interp (e : expr) (cc : CC.state) (ctx : name -> Z) : Z :=
      match e with
      | Ret n => ctx n
      | Instr i rd args cont =>
        let result := i.(spec) (Tuple.map ctx args) cc in
        let new_cc := CC.update i.(writes_conditions) result cc_spec cc in
        let new_ctx := (fun n : name => if name_eqb n rd then result mod wordmax else ctx n) in
        interp cont new_cc new_ctx
      end.
  End expr.

  Section ISA.
    Import CC.

    (* For the C flag, we have to consider cases with a negative result (like the one returned by an underflowing borrow).
       In these cases, we want to set the C flag to true. *)
    Definition cc_spec (x : CC.code) (result : BinInt.Z) : bool :=
      match x with
      | CC.C => if result <? 0 then true else Z.testbit result 256
      | CC.M => Z.testbit result 255
      | CC.L => Z.testbit result 0
      | CC.Z => result =? 0
      end.

    Local Definition lower128 x := (Z.land x (Z.ones 128)).
    Local Definition upper128 x := (Z.shiftr x 128).
    Local Notation "x '[C]'" := (if x.(cc_c) then 1 else 0) (at level 20).
    Local Notation "x '[M]'" := (if x.(cc_m) then 1 else 0) (at level 20).
    Local Notation "x '[L]'" := (if x.(cc_l) then 1 else 0) (at level 20).
    Local Notation "x '[Z]'" := (if x.(cc_z) then 1 else 0) (at level 20).
    Local Notation "'int'" := (BinInt.Z).
    Local Notation "x << y" := ((x << y) mod (2^256)) : Z_scope. (* truncating left shift *)


    (* Note: In the specification document, argument order gets a bit
    confusing. Like here, r0 is always the first argument "source 0"
    and r1 the second. But the specification of MUL128LU is:
            (R[RS1][127:0] * R[RS0][255:128])

    while the specification of SUB is:
          (R[RS0] - shift(R[RS1], imm))

    In the SUB case, r0 is really treated the first argument, but in
    MUL128LU the order seems to be reversed; rather than low-high, we
    take the high part of the first argument r0 and the low parts of
    r1. This is also true for MUL128UL. *)

    Definition ADD (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 + (r1 << imm))
      |}.

    Definition ADDC (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 + (r1 << imm) + cc[C])
      |}.

    Definition SUB (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 - (r1 << imm))
      |}.

    Definition SUBC (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [C; M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   r0 - (r1 << imm) - cc[C])
      |}.


    Definition MUL128LL : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (lower128 r0) * (lower128 r1))
      |}.

    Definition MUL128LU : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (lower128 r1) * (upper128 r0)) (* see note *)
      |}.

    Definition MUL128UL : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (upper128 r1) * (lower128 r0)) (* see note *)
      |}.

    Definition MUL128UU : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (upper128 r0) * (upper128 r1))
      |}.

    (* Note : Unlike the other operations, the output of RSHI is
    truncated in the specification. This is not strictly necessary,
    since the interpretation function truncates the output
    anyway. However, it is useful to make the definition line up
    exactly with Z.rshi. *)
    Definition RSHI (imm : int) : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1) cc =>
                   (((2^256 * r0) + r1) >> imm) mod (2^256))
      |}.

    Definition SELC : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [];
        spec := (fun '(r0, r1) cc =>
                   if cc[C] =? 1 then r0 else r1)
      |}.

    Definition SELM : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [];
        spec := (fun '(r0, r1) cc =>
                   if cc[M] =? 1 then r0 else r1)
      |}.

    Definition SELL : instruction :=
      {|
        num_source_regs := 2;
        writes_conditions := [];
        spec := (fun '(r0, r1) cc =>
                   if cc[L] =? 1 then r0 else r1)
      |}.

    (* TODO : treat the MOD register specially, like CC *)
    Definition ADDM : instruction :=
      {|
        num_source_regs := 3;
        writes_conditions := [M; L; Z];
        spec := (fun '(r0, r1, MOD) cc =>
                   let ra := r0 + r1 in
                   if ra >=? MOD
                   then ra - MOD
                   else ra)
      |}.

  End ISA.

  Module Registers.
    Inductive register : Type :=
    | r0 : register
    | r1 : register
    | r2 : register
    | r3 : register
    | r4 : register
    | r5 : register
    | r6 : register
    | r7 : register
    | r8 : register
    | r9 : register
    | r10 : register
    | r11 : register
    | r12 : register
    | r13 : register
    | r14 : register
    | r15 : register
    | r16 : register
    | r17 : register
    | r18 : register
    | r19 : register
    | r20 : register
    | r21 : register
    | r22 : register
    | r23 : register
    | r24 : register
    | r25 : register
    | r26 : register
    | r27 : register
    | r28 : register
    | r29 : register
    | r30 : register
    | RegZero : register (* r31 *)
    | RegMod : register
    .

    Definition reg_dec (x y : register) : {x = y} + {x <> y}.
    Proof. destruct x, y; try (apply left; congruence); right; congruence. Defined.
    Definition reg_eqb x y := if reg_dec x y then true else false.

    Lemma reg_eqb_neq x y : x <> y -> reg_eqb x y = false.
    Proof. cbv [reg_eqb]; break_match; congruence. Qed.
    Lemma reg_eqb_refl x : reg_eqb x x = true.
    Proof. cbv [reg_eqb]; break_match; congruence. Qed.
  End Registers.

  Section of_prefancy.
    Local Notation cexpr := (@Compilers.expr.expr base.type ident.ident).
    Context (name : Type) (name_succ : name -> name) (error : name) (consts : Z -> option name).

    Fixpoint base_var (t : base.type) : Type :=
      match t with
      | base.type.Z => name
      | base.type.prod a b => base_var a * base_var b
      | _ => unit
      end.
    Fixpoint var (t : type.type base.type) : Type :=
      match t with
      | type.base t => base_var t
      | type.arrow s d => var s -> var d
      end.
    Fixpoint base_error {t} : base_var t
      := match t with
         | base.type.Z => error
         | base.type.prod A B => (@base_error A, @base_error B)
         | _ => tt
         end.
    Fixpoint make_error {t} : var t
      := match t with
         | type.base _ => base_error
         | type.arrow s d => fun _ => @make_error d
         end.

    Fixpoint of_prefancy_scalar {t} (s : @cexpr var t) : var t
      := match s in expr.expr t return var t with
         | Compilers.expr.Var t v => v
         | expr.App s d f x => @of_prefancy_scalar _ f (@of_prefancy_scalar _ x)
         | expr.Ident t idc
           => match idc in ident.ident t return var t with
              | ident.Literal base.type.Z v => match consts v with
                                               | Some n => n
                                               | None => error
                                               end
              | ident.pair A B => fun a b => (a, b)%core
              | ident.fst A B => fun v => fst v
              | ident.snd A B => fun v => snd v
              | ident.Z_cast _ => fun v => v
              | ident.Z_cast2 _ => fun v => v
              | _ => make_error
              end
         | expr.Abs s d f => make_error
         | expr.LetIn A B x f => make_error
         end%expr_pat%etype.

    (* Note : some argument orders are reversed for MUL128LU, MUL128UL, SELC, SELM, and SELL *)
    Local Notation tZ := base.type.Z.
    Definition of_prefancy_ident {s d : base.type} (idc : ident.ident (s -> d))
      : @cexpr var s -> option {i : instruction & tuple name i.(num_source_regs) } :=
      match idc in ident.ident t return match t return Type with
                                        | type.arrow (type.base s) (type.base d)
                                          => @cexpr var s
                                        | _ => unit
                                        end
                                        -> option {i : instruction & tuple name i.(num_source_regs) }
      with
      | ident.fancy_add log2wordmax imm
        => fun args : @cexpr var (tZ * tZ) =>
             if Z.eqb log2wordmax 256
             then Some (existT _ (ADD imm) (of_prefancy_scalar args))
             else None
      | ident.fancy_addc log2wordmax imm
        => fun args : @cexpr var (tZ * tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ (ADDC imm) (of_prefancy_scalar ((#ident.snd @ (#ident.fst @ args)), (#ident.snd @ args))))
             else None
      | ident.fancy_sub log2wordmax imm
        => fun args : @cexpr var (tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ (SUB imm) (of_prefancy_scalar args))
             else None
      | ident.fancy_subb log2wordmax imm
        => fun args : @cexpr var (tZ * tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ (SUBC imm) (of_prefancy_scalar ((#ident.snd @ (#ident.fst @ args)), (#ident.snd @ args))))
             else None
      | ident.fancy_mulll log2wordmax
        => fun args : @cexpr var (tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ MUL128LL (of_prefancy_scalar args))
             else None
      | ident.fancy_mullh log2wordmax
        => fun args : @cexpr var (tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ MUL128LU (of_prefancy_scalar ((#ident.snd @ args), (#ident.fst @ args))))
             else None
      | ident.fancy_mulhl log2wordmax
        => fun args : @cexpr var (tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ MUL128UL (of_prefancy_scalar ((#ident.snd @ args), (#ident.fst @ args))))
             else None
      | ident.fancy_mulhh log2wordmax
        => fun args : @cexpr var (tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ MUL128UU (of_prefancy_scalar args))
             else None
      | ident.fancy_rshi log2wordmax imm
        => fun args : @cexpr var (tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ (RSHI imm) (of_prefancy_scalar args))
             else None
      | ident.fancy_selc
        => fun args : @cexpr var (tZ * tZ * tZ) => Some (existT _ SELC (of_prefancy_scalar ((#ident.snd @ args), (#ident.snd @ (#ident.fst @ args)))))
      | ident.fancy_selm log2wordmax
        => fun args : @cexpr var (tZ * tZ * tZ)  =>
             if Z.eqb log2wordmax 256
             then Some (existT _ SELM (of_prefancy_scalar ((#ident.snd @ args), (#ident.snd @ (#ident.fst @ args)))))
             else None
      | ident.fancy_sell
        => fun args : @cexpr var (tZ * tZ * tZ) => Some (existT _ SELL (of_prefancy_scalar ((#ident.snd @ args), (#ident.snd @ (#ident.fst @ args)))))
      | ident.fancy_addm
        => fun args : @cexpr var (tZ * tZ * tZ) => Some (existT _ ADDM (of_prefancy_scalar args))
      | _ => fun _ => None
      end.

    Local Notation "x <- y ; f" := (match y with Some x => f | None => Ret error end).
    Definition of_prefancy_step
               (of_prefancy : forall (next_name : name) {t} (e : @cexpr var t), @expr name)
               (next_name : name) {t} (e : @cexpr var t) : @expr name
      := let default _ := (e' <- type.try_transport base.try_make_transport_cps (@cexpr var) t tZ e;
                             Ret (of_prefancy_scalar e')) in
         match e with
         | PreFancy.LetInAppIdentZ s d r eidc x f
           => idc <- invert_expr.invert_Ident eidc;
                instr_args <- @of_prefancy_ident s tZ idc x;
                let i : instruction := projT1 instr_args in
                let args : tuple name i.(num_source_regs) := projT2 instr_args in
                Instr i next_name args (@of_prefancy (name_succ next_name) _ (f next_name))
         | PreFancy.LetInAppIdentZZ s d r eidc x f
           => idc <- invert_expr.invert_Ident eidc;
                instr_args <- @of_prefancy_ident s (tZ * tZ) idc x;
                let i : instruction := projT1 instr_args in
                let args : tuple name i.(num_source_regs) := projT2 instr_args in
                Instr i next_name args (@of_prefancy (name_succ next_name) _ (f (next_name, error))) (* we pass the error code as the carry register, because it cannot be read from directly. *)
         | _  => default tt
         end.
    Fixpoint of_prefancy (next_name : name) {t} (e : @cexpr var t) : @expr name
      := @of_prefancy_step of_prefancy next_name t e.
  End of_prefancy.

  Section allocate_registers.
    Context (reg name : Type) (name_eqb : name -> name -> bool) (error : reg).
    Fixpoint allocate (e : @expr name) (reg_list : list reg) (name_to_reg : name -> reg) : @expr reg :=
      match e with
      | Ret n => Ret (name_to_reg n)
      | Instr i rd args cont =>
        match reg_list with
        | r :: reg_list' => Instr i r (Tuple.map name_to_reg args) (allocate cont reg_list' (fun n => if name_eqb n rd then r else name_to_reg n))
        | nil => Ret error
        end
      end.
  End allocate_registers.

  Definition test_prog : @expr positive :=
    Instr (ADD (128)) 3%positive (1, 2)%positive
          (Instr (ADDC 0) 4%positive (3,1)%positive
                 (Ret 4%positive)).

  Definition x1 := 2^256 - 1.
  Definition x2 := 2^128 - 1.
  Definition wordmax := 2^256.
  Definition expected :=
    let r3' := (x1 + (x2 << 128)) in
    let r3 := r3' mod wordmax in
    let c := r3' / wordmax in
    let r4' := (r3 + x1 + c) in
    r4' mod wordmax.
  Definition actual :=
    interp Pos.eqb
           (2^256) cc_spec test_prog {|CC.cc_c:=false; CC.cc_m:=false; CC.cc_l:=false; CC.cc_z:=false|}
           (fun n => if n =? 1%positive
                     then x1
                     else if n =? 2%positive
                          then x2
                          else 0).
  Lemma test_prog_ok : expected = actual.
  Proof. reflexivity. Qed.

  Definition of_Expr {t} next_name (consts : Z -> option positive) (consts_list : list Z)
             (e : expr.Expr t)
             (x : type.for_each_lhs_of_arrow (var positive) t)
    : positive -> @expr positive :=
    fun error =>
      @of_prefancy positive Pos.succ error consts next_name _ (invert_expr.smart_App_curried (e _) x).

End Fancy.

Module Prod.
  Import Fancy. Import Registers.

  Definition Mul256 (out src1 src2 tmp : register) (cont : Fancy.expr) : Fancy.expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UL tmp (src1, src2)
                 (Instr (ADD 128) out (out, tmp)
                        (Instr MUL128LU tmp (src1, src2)
                               (Instr (ADD 128) out (out, tmp) cont)))).
  Definition Mul256x256 (out outHigh src1 src2 tmp : register) (cont : Fancy.expr) : Fancy.expr :=
    Instr MUL128LL out (src1, src2)
          (Instr MUL128UU outHigh (src1, src2)
                 (Instr MUL128UL tmp (src1, src2)
                        (Instr (ADD 128) out (out, tmp)
                               (Instr (ADDC (-128)) outHigh (outHigh, tmp)
                                      (Instr MUL128LU tmp (src1, src2)
                                             (Instr (ADD 128) out (out, tmp)
                                                    (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont))))))).

  Definition MontRed256 lo hi y t1 t2 scratch RegPInv : @Fancy.expr register :=
    Mul256 y lo RegPInv t1
           (Mul256x256 t1 t2 y RegMod scratch
                       (Instr (ADD 0) lo (lo, t1)
                              (Instr (ADDC 0) hi (hi, t2)
                                     (Instr SELC y (RegMod, RegZero)
                                            (Instr (SUB 0) lo (hi, y)
                                                   (Instr ADDM lo (lo, RegZero, RegMod)
                                                          (Ret lo))))))).

  (* Barrett reduction -- this is only the "reduce" part, excluding the initial multiplication. *)
  Definition MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 : @Fancy.expr register :=
    let q1Bottom256 := scratchp1 in
    let muSelect := scratchp2 in
    let q2 := scratchp3 in
    let q2High := scratchp4 in
    let q2High2 := scratchp5 in
    let q3 := scratchp1 in
    let r2 := scratchp2 in
    let r2High := scratchp3 in
    let maybeM := scratchp1 in
    Instr SELM muSelect (RegMuLow, RegZero)
          (Instr (RSHI 255) q1Bottom256 (xHigh, x)
                 (Mul256x256 q2 q2High q1Bottom256 RegMuLow scratchp5
                             (Instr (RSHI 255) q2High2 (RegZero, xHigh)
                                    (Instr (ADD 0) q2High (q2High, q1Bottom256)
                                           (Instr (ADDC 0) q2High2 (q2High2, RegZero)
                                                  (Instr (ADD 0) q2High (q2High, muSelect)
                                                         (Instr (ADDC 0) q2High2 (q2High2, RegZero)
                                                                (Instr (RSHI 1) q3 (q2High2, q2High)
                                                                       (Mul256x256 r2 r2High RegMod q3 scratchp4
                                                                                   (Instr (SUB 0) muSelect (x, r2)
                                                                                          (Instr (SUBC 0) xHigh (xHigh, r2High)
                                                                                                 (Instr SELL maybeM (RegMod, RegZero)
                                                                                                        (Instr (SUB 0) q3 (muSelect, maybeM)
                                                                                                               (Instr ADDM x (q3, RegZero, RegMod)
                                                                                                                      (Ret x))))))))))))))).
End Prod.

Module ProdEquiv.
  Import Fancy. Import Registers.

  Definition interp256 := Fancy.interp reg_eqb (2^256) cc_spec.
  Lemma interp_step i rd args cont cc ctx :
    interp256 (Instr i rd args cont) cc ctx =
      let result := spec i (Tuple.map ctx args) cc in
      let new_cc := CC.update (writes_conditions i) result cc_spec cc in
      let new_ctx := fun n => if reg_eqb n rd then result mod wordmax else ctx n in interp256 cont new_cc new_ctx.
  Proof. reflexivity. Qed.

  (* TODO : move *)
  Lemma tuple_map_ext {A B} (f g : A -> B) n (t : tuple A n) :
    (forall x : A, f x = g x) ->
    Tuple.map f t = Tuple.map g t.
  Proof.
    destruct n; [reflexivity|]; cbn in *.
    induction n; cbn in *; intro H; auto; [ ].
    rewrite IHn by assumption.
    rewrite H; reflexivity.
  Qed.

  Lemma interp_state_equiv e :
    forall cc ctx cc' ctx',
    cc = cc' -> (forall r, ctx r = ctx' r) ->
    interp256 e cc ctx = interp256 e cc' ctx'.
  Proof.
    induction e; intros; subst; cbn; [solve[auto]|].
    apply IHe; rewrite tuple_map_ext with (g:=ctx') by auto;
      [reflexivity|].
    intros; break_match; auto.
  Qed.
  Lemma cc_overwrite_full x1 x2 l1 cc :
    CC.update [CC.C; CC.M; CC.L; CC.Z] x2 cc_spec (CC.update l1 x1 cc_spec cc) = CC.update [CC.C; CC.M; CC.L; CC.Z] x2 cc_spec cc.
  Proof.
    cbv [CC.update]. cbn [CC.cc_c CC.cc_m CC.cc_l CC.cc_z].
    break_match; try match goal with H : ~ In _ _ |- _ => cbv [In] in H; tauto end.
    reflexivity.
  Qed.

  Lemma tuple_map_ext_In {A B} (f g : A -> B) n (t : tuple A n) :
    (forall x, In x (to_list n t) -> f x = g x) ->
    Tuple.map f t = Tuple.map g t.
  Proof.
    destruct n; [reflexivity|]; cbn in *.
    induction n; cbn in *; intro H; auto; [ ].
    destruct t.
    rewrite IHn by auto using in_cons.
    rewrite H; auto using in_eq.
  Qed.

  Definition value_unused r e : Prop :=
    forall x cc ctx, interp256 e cc ctx = interp256 e cc (fun r' => if reg_eqb r' r then x else ctx r').

  Lemma value_unused_skip r i rd args cont (Hcont: value_unused r cont) :
    r <> rd ->
    (~ In r (Tuple.to_list _ args)) ->
    value_unused r (Instr i rd args cont).
  Proof.
    cbv [value_unused] in *; intros.
    rewrite !interp_step; cbv zeta.
    rewrite Hcont with (x:=x).
    match goal with |- ?lhs = ?rhs =>
                    match lhs with context [Tuple.map ?f ?t] =>
                                   match rhs with context [Tuple.map ?g ?t] =>
                                                  rewrite (tuple_map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
                                   end end end.
    apply interp_state_equiv; [ congruence | ].
    { intros; cbv [reg_eqb] in *; break_match; congruence. }
  Qed.

  Lemma value_unused_overwrite r i args cont :
    (~ In r (Tuple.to_list _ args)) ->
    value_unused r (Instr i r args cont).
  Proof.
    cbv [value_unused]; intros; rewrite !interp_step; cbv zeta.
    match goal with |- ?lhs = ?rhs =>
                    match lhs with context [Tuple.map ?f ?t] =>
                                   match rhs with context [Tuple.map ?g ?t] =>
                                                  rewrite (tuple_map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
                                   end end end.
    apply interp_state_equiv; [ congruence | ].
    { intros; cbv [reg_eqb] in *; break_match; congruence. }
  Qed.

  Lemma value_unused_ret r r' :
    r <> r' ->
    value_unused r (Ret r').
  Proof.
    cbv - [reg_dec]; intros.
    break_match; congruence.
  Qed.

  Ltac remember_results :=
    repeat match goal with |- context [(spec ?i ?args ?flags) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (spec i args flags) as x eqn:Heqx;
                    remember (x mod w) as y
           end.

  Ltac do_interp_step :=
    rewrite interp_step; cbn - [interp spec];
    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
    remember_results.

  Lemma interp_Mul256 out src1 src2 tmp tmp2 cont cc ctx:
    out <> src1 ->
    out <> src2 ->
    out <> tmp ->
    out <> tmp2 ->
    src1 <> src2 ->
    src1 <> tmp ->
    src1 <> tmp2 ->
    src2 <> tmp ->
    src2 <> tmp2 ->
    tmp <> tmp2 ->
    value_unused tmp cont ->
    value_unused tmp2 cont ->
    interp256 (Prod.Mul256 out src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128LU tmp (src1, src2)
              (Instr MUL128UL tmp2 (src1, src2)
                     (Instr MUL128LL out (src1, src2)
                                 (Instr (ADD 128) out (out, tmp2)
                                        (Instr (ADD 128) out (out, tmp) cont))))) cc ctx.
  Proof.
    intros; cbv [Prod.Mul256].
    repeat (do_interp_step; cbn [spec MUL128LL MUL128UL MUL128LU ADD] in * ).

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv.
    { rewrite !cc_overwrite_full.
      f_equal. subst. lia. }
    { intros; cbv [reg_eqb].
      repeat (break_match_step ltac:(fun _ => idtac); try congruence); reflexivity. }
  Qed.

  Lemma interp_Mul256x256 out outHigh src1 src2 tmp tmp2 cont cc ctx:
    out <> src1 ->
    out <> outHigh ->
    out <> src2 ->
    out <> tmp ->
    out <> tmp2 ->
    outHigh <> src1 ->
    outHigh <> src2 ->
    outHigh <> tmp ->
    outHigh <> tmp2 ->
    src1 <> src2 ->
    src1 <> tmp ->
    src1 <> tmp2 ->
    src2 <> tmp ->
    src2 <> tmp2 ->
    tmp <> tmp2 ->
    value_unused tmp cont ->
    value_unused tmp2 cont ->
    interp256 (Prod.Mul256x256 out outHigh src1 src2 tmp cont) cc ctx =
    interp256 (
        Instr MUL128LL out (src1, src2)
              (Instr MUL128LU tmp (src1, src2)
                     (Instr MUL128UL tmp2 (src1, src2)
                            (Instr MUL128UU outHigh (src1, src2)
                                   (Instr (ADD 128) out (out, tmp2)
                                          (Instr (ADDC (-128)) outHigh (outHigh, tmp2)
                                                 (Instr (ADD 128) out (out, tmp)
                                                        (Instr (ADDC (-128)) outHigh (outHigh, tmp) cont)))))))) cc ctx.
  Proof.
    intros; cbv [Prod.Mul256x256].
    repeat (do_interp_step; cbn [spec MUL128LL MUL128UL MUL128LU MUL128UU ADD ADDC] in * ).

    match goal with H : value_unused tmp _ |- _ => erewrite H end.
    match goal with H : value_unused tmp2 _ |- _ => erewrite H end.
    apply interp_state_equiv.
    { rewrite !cc_overwrite_full.
      f_equal.
      subst. cbn - [Z.add Z.modulo Z.testbit Z.mul Z.shiftl Fancy.lower128 Fancy.upper128].
      lia. }
    { intros; cbv [reg_eqb].
      repeat (break_match_step ltac:(fun _ => idtac); try congruence); try reflexivity; [ ].
      subst. cbn - [Z.add Z.modulo Z.testbit Z.mul Z.shiftl Fancy.lower128 Fancy.upper128].
      lia. }
  Qed.

  Lemma mulll_comm rd x y cont cc ctx :
    ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128LL rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128LL rd (y, x) cont) cc ctx.
  Proof. rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma mulhh_comm rd x y cont cc ctx :
    ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128UU rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128UU rd (y, x) cont) cc ctx.
  Proof. rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma mullh_mulhl rd x y cont cc ctx :
    ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128LU rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr Fancy.MUL128UL rd (y, x) cont) cc ctx.
  Proof. rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.mul_comm. reflexivity. Qed.

  Lemma add_comm rd x y cont cc ctx :
    0 <= ctx x < 2^256 ->
    0 <= ctx y < 2^256 ->
    ProdEquiv.interp256 (Fancy.Instr (Fancy.ADD 0) rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr (Fancy.ADD 0) rd (y, x) cont) cc ctx.
  Proof.
    intros; rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite Z.add_comm.
    rewrite !(Z.mod_small (ctx _)) by (cbn in *; omega). reflexivity.
  Qed.

  Lemma addc_comm rd x y cont cc ctx :
    0 <= ctx x < 2^256 ->
    0 <= ctx y < 2^256 ->
    ProdEquiv.interp256 (Fancy.Instr (Fancy.ADDC 0) rd (x, y) cont) cc ctx = ProdEquiv.interp256 (Fancy.Instr (Fancy.ADDC 0) rd (y, x) cont) cc ctx.
  Proof.
    intros; rewrite !ProdEquiv.interp_step. cbn - [Fancy.interp]. rewrite (Z.add_comm (ctx x)).
    rewrite !(Z.mod_small (ctx _)) by (cbn in *; omega). reflexivity.
  Qed.

  (* Tactics to help prove that something in Fancy is line-by-line equivalent to something in PreFancy *)
  Ltac push_value_unused :=
    repeat match goal with
           | |- ~ In _ _ => cbn; intuition; congruence
           | _ => apply ProdEquiv.value_unused_overwrite
           | _ => apply ProdEquiv.value_unused_skip; [ | congruence | ]
           | _ => apply ProdEquiv.value_unused_ret; congruence
           end.

  Ltac remember_single_result :=
    match goal with |- context [(Fancy.spec ?i ?args ?cc) mod ?w] =>
                    let x := fresh "x" in
                    let y := fresh "y" in
                    let Heqx := fresh "Heqx" in
                    remember (Fancy.spec i args cc) as x eqn:Heqx;
                    remember (x mod w) as y
    end.
  Ltac step_both_sides :=
    match goal with |- ProdEquiv.interp256 (Fancy.Instr ?i ?rd1 ?args1 _) _ ?ctx1 = ProdEquiv.interp256 (Fancy.Instr ?i ?rd2 ?args2 _) _ ?ctx2 =>
                    rewrite (ProdEquiv.interp_step i rd1 args1); rewrite (ProdEquiv.interp_step i rd2 args2);
                    cbn - [Fancy.interp Fancy.spec];
                    repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence;
                    remember_single_result;
                    lazymatch goal with
                    | |- context [Fancy.spec i _ _] =>
                      let Heqa1 := fresh in
                      let Heqa2 := fresh in
                      remember (Tuple.map (n:=i.(Fancy.num_source_regs)) ctx1 args1) eqn:Heqa1;
                      remember (Tuple.map (n:=i.(Fancy.num_source_regs)) ctx2 args2) eqn:Heqa2;
                      cbn in Heqa1; cbn in Heqa2;
                      repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl in Heqa1 by congruence;
                      repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl in Heqa2 by congruence;
                      let a1 := match type of Heqa1 with _ = ?a1 => a1 end in
                      let a2 := match type of Heqa2 with _ = ?a2 => a2 end in
                      (fail 1 "arguments to " i " do not match; LHS has " a1 " and RHS has " a2)
                    | _ => idtac
                    end
    end.
End ProdEquiv.

(* Lemmas to help prove that a fancy and prefancy expression have the
same meaning -- should be replaced eventually with a proof of fancy
passes in general. *)

Module Fancy_PreFancy_Equiv.
  Import Fancy.Registers.

  Lemma interp_cast_mod_eq w u x: u = 2^w - 1 -> ident.cast (PreFancy.interp_cast_mod w) r[0 ~> u] x = x mod 2^w.
  Proof.
    cbv [ident.cast PreFancy.interp_cast_mod upper lower]; intros; subst.
    rewrite !Z.eqb_refl.
    break_innermost_match; Bool.split_andb; Z.ltb_to_lt; Z.rewrite_mod_small; reflexivity.
  Qed.
  Lemma interp_cast_mod_flag w x: ident.cast (PreFancy.interp_cast_mod w) r[0 ~> 1] x = x mod 2.
  Proof.
    cbv [ident.cast PreFancy.interp_cast_mod upper lower].
    break_match; Bool.split_andb; Z.ltb_to_lt; Z.rewrite_mod_small; subst; try omega.
    f_equal; omega.
  Qed.

  Lemma interp_equivZ {s} w u (Hu : u = 2^w-1) i rd regs e cc ctx idc args f :
    (Fancy.spec i (Tuple.map ctx regs) cc
     = ident.gen_interp (PreFancy.interp_cast_mod w) (t:=type.arrow _ base.type.Z) idc (PreFancy.interp w args)) ->
    ( let r := Fancy.spec i (Tuple.map ctx regs) cc in
      Fancy.interp reg_eqb (2 ^ w) Fancy.cc_spec e
                 (Fancy.CC.update (Fancy.writes_conditions i) r Fancy.cc_spec cc)
                 (fun n : register => if reg_eqb n rd then r mod 2 ^ w else ctx n) =
    @PreFancy.interp w base.type.Z (f (r mod 2 ^ w))) ->
    Fancy.interp reg_eqb (2^w) Fancy.cc_spec (Fancy.Instr i rd regs e) cc ctx
    = @PreFancy.interp w base.type.Z
                      (@PreFancy.LetInAppIdentZ s _ (r[0~>2^w-1])%zrange (#idc) args f).
  Proof.
    cbv zeta; intros spec_eq next_eq.
    cbn [Fancy.interp PreFancy.interp].
    cbv [Let_In].
    rewrite next_eq.
    cbn in *.
    rewrite <-spec_eq.
    rewrite interp_cast_mod_eq by omega.
    reflexivity.
  Qed.

  Lemma interp_equivZZ {s} w (Hw : 2 < 2 ^ w) u (Hu : u = 2^w - 1) i rd regs e cc ctx idc args f :
    ((Fancy.spec i (Tuple.map ctx regs) cc) mod 2 ^ w
     = fst (ident.gen_interp (PreFancy.interp_cast_mod w) (t:=type.arrow _ (base.type.Z*base.type.Z)) idc (PreFancy.interp w args))) ->
    ((if Fancy.cc_spec Fancy.CC.C(Fancy.spec i (Tuple.map ctx regs) cc) then 1 else 0)
     = snd (ident.gen_interp (PreFancy.interp_cast_mod w) (t:=type.arrow _ (base.type.Z*base.type.Z)) idc (PreFancy.interp w args)) mod 2) ->
    ( let r := Fancy.spec i (Tuple.map ctx regs) cc in
      Fancy.interp reg_eqb (2 ^ w) Fancy.cc_spec e
                 (Fancy.CC.update (Fancy.writes_conditions i) r Fancy.cc_spec cc)
                 (fun n : register => if reg_eqb n rd then r mod 2 ^ w else ctx n) =
     @PreFancy.interp w base.type.Z
                     (f (r mod 2 ^ w, if (Fancy.cc_spec Fancy.CC.C r) then 1 else 0))) ->
    Fancy.interp reg_eqb (2^w) Fancy.cc_spec (Fancy.Instr i rd regs e) cc ctx
    = @PreFancy.interp w base.type.Z
                      (@PreFancy.LetInAppIdentZZ s _ (r[0~>u], r[0~>1])%zrange (#idc) args f).
  Proof.
    cbv zeta; intros spec_eq1 spec_eq2 next_eq.
    cbn [Fancy.interp PreFancy.interp].
    cbv [Let_In].
    cbn [ident.gen_interp]; Prod.eta_expand.
    rewrite next_eq.
    rewrite interp_cast_mod_eq by omega.
    rewrite interp_cast_mod_flag by omega.
    cbn -[Fancy.cc_spec] in *.
    rewrite <-spec_eq1, <-spec_eq2.
    rewrite Z.mod_mod by omega.
    reflexivity.
  Qed.
End Fancy_PreFancy_Equiv.

Module Barrett256.

  Definition M := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition machine_wordsize := 256.

  Derive barrett_red256
         SuchThat (BarrettReduction.rbarrett_red_correctT M machine_wordsize barrett_red256)
         As barrett_red256_correct.
  Proof. Time solve_rbarrett_red machine_wordsize. Time Qed.

  Definition muLow := Eval lazy in (2 ^ (2 * machine_wordsize) / M) mod (2^machine_wordsize).
  (*
  Definition barrett_red256_prefancy' := PreFancy.of_Expr machine_wordsize [M; muLow] barrett_red256.

  Derive barrett_red256_prefancy
         SuchThat (barrett_red256_prefancy = barrett_red256_prefancy' type.interp)
         As barrett_red256_prefancy_eq.
  Proof. lazy - [type.interp]; reflexivity. Qed.
   *)

  Lemma barrett_reduce_correct_specialized :
    forall (xLow xHigh : Z),
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      BarrettReduction.barrett_reduce machine_wordsize M muLow 2 2 xLow xHigh = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof.
    intros.
    apply BarrettReduction.barrett_reduce_correct; cbv [machine_wordsize M muLow] in *;
      try omega;
      try match goal with
          | |- context [weight] => intros; cbv [weight]; autorewrite with zsimplify; auto using Z.pow_mul_r with omega
          end; lazy; try split; congruence.
  Qed.

  (*
  (* Note: If this is not factored out, then for some reason Qed takes forever in barrett_red256_correct_full. *)
  Lemma barrett_red256_correct_proj2 :
    forall xy : type.interp base.interp (base.type.prod base.type.Z base.type.Z),
      ZRange.type.option.is_bounded_by
        (t:=base.type.prod base.type.Z base.type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
      type.app_curried (t:=type.arrow (base.type.prod base.type.Z base.type.Z) base.type.Z) (expr.Interp (@ident.interp) barrett_red256) xy = type.app_curried (t:=type.arrow (base.type.prod base.type.Z base.type.Z) base.type.Z) (fun xy => BarrettReduction.barrett_reduce machine_wordsize M muLow 2 2 (fst xy) (snd xy)) xy.
  Proof. intros; destruct (barrett_red256_correct xy); assumption. Qed.
  Lemma barrett_red256_correct_proj2' :
    forall x y : Z,
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        (x, y) = true ->
       expr.Interp (@ident.interp) barrett_red256 (x, y) = BarrettReduction.barrett_reduce machine_wordsize M muLow 2 2 x y.
  Proof. intros; rewrite barrett_red256_correct_proj2 by assumption; unfold app_curried; exact eq_refl. Qed.
   *)
  Strategy -100 [type.app_curried].
  Local Arguments is_bounded_by_bool / .
  Lemma barrett_red256_correct_full  :
    forall (xLow xHigh : Z),
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      PreFancy.Interp 256 barrett_red256 xLow xHigh = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof.
    intros.
    rewrite <-barrett_reduce_correct_specialized by assumption.
    destruct (proj1 barrett_red256_correct (xLow, (xHigh, tt)) (xLow, (xHigh, tt))) as [H1 H2].
    { repeat split. }
    { cbn -[Z.pow].
      rewrite !andb_true_iff.
      assert (M < 2^machine_wordsize) by (vm_compute; reflexivity).
      repeat apply conj; Z.ltb_to_lt; trivial; omega. }
    { etransitivity; [ eapply H2 | ]. (* need Strategy -100 [type.app_curried]. for this to be fast *)
      generalize BarrettReduction.barrett_reduce; vm_compute; reflexivity. }
  Qed.

  (*
  Import PreFancy.Tactics. (* for ok_expr_step *)
  Lemma barrett_red256_prefancy_correct :
    forall xLow xHigh dummy_arrow,
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      @PreFancy.interp machine_wordsize (PreFancy.interp_cast_mod machine_wordsize) type.Z (barrett_red256_prefancy (xLow, xHigh) dummy_arrow) = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof.
    intros. rewrite barrett_red256_prefancy_eq; cbv [barrett_red256_prefancy'].
    erewrite PreFancy.of_Expr_correct.
    { apply barrett_red256_correct_full; try assumption; reflexivity. }
    { reflexivity. }
    { lazy; reflexivity. }
    { lazy; reflexivity. }
    { repeat constructor. }
    { cbv [In M muLow]; intros; intuition; subst; cbv; congruence. }
    { let r := (eval compute in (2 ^ machine_wordsize)) in
      replace (2^machine_wordsize) with r in * by reflexivity.
      cbv [M muLow machine_wordsize] in *.
      assert (lower r[0~>1] = 0) by reflexivity.
      repeat (ok_expr_step; [ ]).
      ok_expr_step.
      lazy; congruence.
      constructor.
      constructor. }
    { lazy. omega. }
  Qed.
   *)
  Definition barrett_red256_fancy' (xLow xHigh RegMuLow RegMod RegZero error : positive) :=
    Fancy.of_Expr 3%positive
                  (fun z => if z =? muLow then Some RegMuLow else if z =? M then Some RegMod else if z =? 0 then Some RegZero else None)
                  [M; muLow]
                  barrett_red256
                  (xLow, (xHigh, tt))
                  error.
  Derive barrett_red256_fancy
         SuchThat (forall xLow xHigh RegMuLow RegMod RegZero,
                      barrett_red256_fancy xLow xHigh RegMuLow RegMod RegZero = barrett_red256_fancy' xLow xHigh RegMuLow RegMod RegZero)
         As barrett_red256_fancy_eq.
  Proof.
    intros.
    lazy - [Fancy.ADD Fancy.ADDC Fancy.SUB Fancy.SUBC
                      Fancy.MUL128LL Fancy.MUL128LU Fancy.MUL128UL Fancy.MUL128UU
                      Fancy.RSHI Fancy.SELC Fancy.SELM Fancy.SELL Fancy.ADDM].
    reflexivity.
  Qed.

  Import Fancy.Registers.

  Definition barrett_red256_alloc' xLow xHigh RegMuLow :=
    fun errorP errorR =>
    Fancy.allocate register
                   positive Pos.eqb
                   errorR
                   (barrett_red256_fancy 1000%positive 1001%positive 1002%positive 1003%positive 1004%positive errorP)
                   [r2;r3;r4;r5;r6;r7;r8;r9;r10;r5;r11;r6;r12;r13;r14;r15;r16;r17;r18;r19;r20;r21;r22;r23;r24;r25;r26;r27;r28;r29]
                   (fun n => if n =? 1000 then xLow
                             else if n =? 1001 then xHigh
                                  else if n =? 1002 then RegMuLow
                                       else if n =? 1003 then RegMod
                                            else if n =? 1004 then RegZero
                                                 else errorR).
  Derive barrett_red256_alloc
         SuchThat (barrett_red256_alloc = barrett_red256_alloc')
         As barrett_red256_alloc_eq.
  Proof.
    intros.
    cbv [barrett_red256_alloc' barrett_red256_fancy].
    cbn. subst barrett_red256_alloc.
    reflexivity.
  Qed.

  Set Printing Depth 1000.
  Import ProdEquiv.

  Local Ltac solve_bounds :=
    match goal with
    | H : ?a = ?b mod ?c |- 0 <= ?a < ?c => rewrite H; apply Z.mod_pos_bound; omega
    | _ => assumption
    end.

  Lemma barrett_red256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg,
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] ->
      0 <= start_context x < 2^machine_wordsize ->
      0 <= start_context xHigh < 2^machine_wordsize ->
      0 <= start_context RegMuLow < 2^machine_wordsize ->
      ProdEquiv.interp256 (barrett_red256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context x
                                    else if reg_eqb r r1
                                         then start_context xHigh
                                         else if reg_eqb r r30
                                              then start_context RegMuLow
                                              else start_context r)
    = ProdEquiv.interp256 (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context.
  Proof.
    intros.
    let r := eval compute in (2^machine_wordsize) in
        replace (2^machine_wordsize) with r in * by reflexivity.
    cbv [Prod.MulMod barrett_red256_alloc].

    (* Extract proofs that no registers are equal to each other *)
    repeat match goal with
           | H : NoDup _ |- _ => inversion H; subst; clear H
           | H : ~ In _ _ |- _ => cbv [In] in H
           | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H
           | H : ~ False |- _ => clear H
           end.

    step_both_sides.

    (* TODO: To prove equivalence between these two, we need to either relocate the RSHI instructions so they're in the same places or use instruction commutativity to push them down. *)

  Admitted.

  Import Fancy_PreFancy_Equiv.

  Definition interp_equivZZ_256 {s} :=
    @interp_equivZZ s 256 ltac:(cbv; congruence) 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).
  Definition interp_equivZ_256 {s} :=
    @interp_equivZ s 256 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).

  Local Ltac simplify_op_equiv start_ctx :=
    cbn - [Fancy.spec (*PreFancy.interp_ident*) ident.gen_interp Fancy.cc_spec Z.shiftl];
    repeat match goal with H : start_ctx _ = _ |- _ => rewrite H end;
    cbv - [
      Z.rshi Z.cc_m Fancy.CC.cc_m
        Z.add_with_get_carry_full Z.add_get_carry_full
        Z.sub_get_borrow_full Z.sub_with_get_borrow_full
        Z.le Z.lt Z.ltb Z.leb Z.geb Z.eqb Z.land Z.shiftr Z.shiftl
        Z.add Z.mul Z.div Z.sub Z.modulo Z.testbit Z.pow Z.ones
        fst snd]; cbn [fst snd];
    try (replace (2 ^ (256 / 2) - 1) with (Z.ones 128) by reflexivity; rewrite !Z.land_ones by omega);
    autorewrite with to_div_mod; rewrite ?Z.mod_mod, <-?Z.testbit_spec' by omega;
    let r := (eval compute in (2 ^ 256)) in
    replace (2^256) with r in * by reflexivity;
    repeat match goal with
           | H : 0 <= ?x < ?m |- context [?x mod ?m] => rewrite (Z.mod_small x m) by apply H
           | |- context [?x <? 0] => rewrite (proj2 (Z.ltb_ge x 0)) by (break_match; Z.zero_bounds)
           | _ => rewrite Z.mod_small with (b:=2) by (break_match; omega)
           | |- context [ (if Z.testbit ?a ?n then 1 else 0) + ?b + ?c] =>
             replace ((if Z.testbit a n then 1 else 0) + b + c) with (b + c + (if Z.testbit a n then 1 else 0)) by ring
           end.

  Local Ltac solve_nonneg ctx :=
    match goal with x := (Fancy.spec _ _ _) |- _ => subst x end;
    simplify_op_equiv ctx; Z.zero_bounds.

  Local Ltac generalize_result :=
    let v := fresh "v" in intro v; generalize v; clear v; intro v.

  Local Ltac generalize_result_nonneg ctx :=
    let v := fresh "v" in
    let v_nonneg := fresh "v_nonneg" in
    intro v; assert (0 <= v) as v_nonneg; [solve_nonneg ctx |generalize v v_nonneg; clear v v_nonneg; intros v v_nonneg].

  Local Ltac step_abs :=
    match goal with
    | [ |- context G[expr.interp ?ident_interp (expr.Abs ?f) ?x] ]
      => let G' := context G[expr.interp ident_interp (f x)] in
         change G'; cbv beta
    end.
  Local Ltac step ctx :=
    repeat step_abs;
    match goal with
    | |- Fancy.interp _ _ _ (Fancy.Instr (Fancy.ADD _) _ _ (Fancy.Instr (Fancy.ADDC _) _ _ _)) _ _ = _ =>
      apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result_nonneg ctx]
    | [ |- _ = expr.interp _ (PreFancy.LetInAppIdentZ _ _ _ _ _ _) ]
      => apply interp_equivZ_256; [simplify_op_equiv ctx | generalize_result]
    | [ |- _ = expr.interp _ (PreFancy.LetInAppIdentZZ _ _ _ _ _ _) ]
      => apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result]
    end.

  (* TODO: move this lemma to ZUtil *)
  Lemma testbit_neg_eq_if x n :
    0 <= n ->
    - (2 ^ n) <= x  < 2 ^ n ->
    Z.b2z (if x <? 0 then true else Z.testbit x n) = - (x / 2 ^ n) mod 2.
  Proof.
    intros. break_match; Z.ltb_to_lt.
    { autorewrite with zsimplify. reflexivity. }
    { autorewrite with zsimplify.
      rewrite Z.bits_above_pow2 by omega.
      reflexivity. }
  Qed.

  Lemma prod_barrett_red256_correct :
    forall (cc_start_state : Fancy.CC.state) (* starting carry flags *)
           (start_context : register -> Z)   (* starting register values *)
           (x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 extra_reg : register), (* registers to use in computation *)
      NoDup [x; xHigh; RegMuLow; scratchp1; scratchp2; scratchp3; scratchp4; scratchp5; extra_reg; RegMod; RegZero] -> (* registers are unique *)
             0 <= start_context x < 2^machine_wordsize ->
             0 <= start_context xHigh < M ->
             start_context RegMuLow = muLow ->
             start_context RegMod = M ->
             start_context RegZero = 0 ->
             cc_start_state.(Fancy.CC.cc_m) = (Z.cc_m (2^256) (start_context xHigh) =? 1) ->
             let X := start_context x + 2^machine_wordsize * start_context xHigh in
             ProdEquiv.interp256 (Prod.MulMod x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5) cc_start_state start_context = X mod M.
  Proof.
    intros. subst X.
    assert (0 <= start_context xHigh < 2^machine_wordsize) by (cbv [M] in *; cbn; omega).
    let r := (eval compute in (2 ^ machine_wordsize)) in
    replace (2^machine_wordsize) with r in * by reflexivity.
    cbv [M muLow] in *.

    rewrite <-barrett_red256_correct_full by auto.
    rewrite <-barrett_red256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (auto; cbn; auto with omega).
    cbv [ProdEquiv.interp256].
    let r := (eval compute in (2 ^ 256)) in
    replace (2^256) with r in * by reflexivity.
    cbv [barrett_red256_alloc barrett_red256 expr.Interp].

    step start_context.
    { match goal with H : Fancy.CC.cc_m _ = _ |- _ => rewrite H end.
      match goal with |- context [Z.cc_m ?s ?x] =>
                      pose proof (Z.cc_m_small s x ltac:(reflexivity) ltac:(reflexivity) ltac:(omega));
                        let H := fresh in
                        assert (Z.cc_m s x = 1 \/ Z.cc_m s x = 0) as H by omega;
                          destruct H as [H | H]; rewrite H in *
      end; repeat (change (0 =? 1) with false || change (?x =? ?x) with true || cbv beta iota);
        break_innermost_match; Z.ltb_to_lt; try congruence. }
    apply interp_equivZ_256; [ simplify_op_equiv start_context | ]. (* apply manually instead of using [step] to allow a custom bounds proof *)
    { rewrite Z.rshi_correct by omega.
      autorewrite with zsimplify_fast.
      rewrite Z.shiftr_div_pow2 by omega.
      break_innermost_match; Z.ltb_to_lt; try omega.
      do 2 f_equal; omega. }

    (* Special case to remember the bound for the output of RSHI *)
    let v := fresh "v" in
    let v_bound := fresh "v_bound" in
    intro v; assert (0 <= v <= 1) as v_bound; [ |generalize v v_bound; clear v v_bound; intros v v_bound].
    { solve_nonneg start_context. autorewrite with zsimplify_fast.
      rewrite Z.shiftr_div_pow2 by omega.
      rewrite Z.mod_small by admit.
      split; [Z.zero_bounds|].
      apply Z.lt_succ_r.
      apply Z.div_lt_upper_bound; try lia; admit. }
(*
    step start_context.
    { rewrite Z.rshi_correct by omega.
      rewrite Z.shiftr_div_pow2 by omega.
      repeat (f_equal; try ring). }
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context;
      [ rewrite Z.mod_small with (b:=2) by (rewrite Z.mod_small by omega; omega); (* Here we make use of the bound of RSHI *)
        reflexivity
      | rewrite Z.mod_small with (b:=2) by (rewrite Z.mod_small by omega; omega); (* Here we make use of the bound of RSHI *)
        reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context.
    { rewrite Z.rshi_correct by omega.
      rewrite Z.shiftr_div_pow2 by omega.
      repeat (f_equal; try ring). }

    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].

    step start_context.
    { reflexivity. }
    { autorewrite with zsimplify_fast.
      match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
      rewrite <-testbit_neg_eq_if with (n:=256) by (cbn; omega).
      reflexivity. }
    step start_context.
    { reflexivity. }
    { autorewrite with zsimplify_fast.
      rewrite Z.mod_small with (a:=(if (if _ <? 0 then true else _) then _ else _)) (b:=2) by (break_innermost_match; omega).
      match goal with |- context [?a - ?b - ?c] => replace (a - b - c) with (a - (b + c)) by ring end.
      match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
      rewrite <-testbit_neg_eq_if with (n:=256) by (break_innermost_match; cbn; omega).
      reflexivity. }
    step start_context.
    { rewrite Z.bit0_eqb.
      match goal with |- context [(?x mod ?m) &' 1] =>
                      replace (x mod m) with (x &' Z.ones 256) by (rewrite Z.land_ones by omega; reflexivity) end.
      rewrite <-Z.land_assoc.
      rewrite Z.land_ones with (n:=1) by omega.
      cbn.
      match goal with |- context [?x mod 2] =>
                      let H := fresh in
                      assert (x mod 2 = 0 \/ x mod 2 = 1) as H
                          by (pose proof (Z.mod_pos_bound x 2 ltac:(omega)); omega);
                        destruct H as [H | H]; rewrite H
      end; reflexivity. }
    step start_context.
    { reflexivity. }
    { autorewrite with zsimplify_fast.
      repeat match goal with |- context [?x mod ?m] => unique pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
      rewrite <-testbit_neg_eq_if with (n:=256) by (cbn; omega).
      reflexivity. }
    step start_context; [ break_innermost_match; Z.ltb_to_lt; omega | ].
    reflexivity.
*)
  Admitted.

  Import PrintingNotations.
  Set Printing Width 1000.
  Open Scope expr_scope.
  Print barrett_red256.
  (*
barrett_red256 =  fun var : type -> Type => λ x : var (type.type_primitive type.Z * type.type_primitive type.Z)%ctype,
                expr_let x0 := SELM (x₂, 0, 26959946667150639793205513449348445388433292963828203772348655992835) in
                expr_let x1 := RSHI (0, x₂, 255) in
                expr_let x2 := RSHI (x₂, x₁, 255) in
                expr_let x3 := 79228162514264337589248983038 *₂₅₆ (uint128)(x2 >> 128) in
                expr_let x4 := 79228162514264337589248983038 *₂₅₆ ((uint128)(x2) & 340282366920938463463374607431768211455) in
                expr_let x5 := 340282366841710300930663525764514709507 *₂₅₆ (uint128)(x2 >> 128) in
                expr_let x6 := 340282366841710300930663525764514709507 *₂₅₆ ((uint128)(x2) & 340282366920938463463374607431768211455) in
                expr_let x7 := ADD_256 ((uint256)(((uint128)(x5) & 340282366920938463463374607431768211455) << 128), x6) in
                expr_let x8 := ADDC_256 (x7₂, (uint128)(x5 >> 128), x3) in
                expr_let x9 := ADD_256 ((uint256)(((uint128)(x4) & 340282366920938463463374607431768211455) << 128), x7₁) in
                expr_let x10 := ADDC_256 (x9₂, (uint128)(x4 >> 128), x8₁) in
                expr_let x11 := ADD_256 (x2, x10₁) in
                expr_let x12 := ADDC_128 (x11₂, 0, x1) in
                expr_let x13 := ADD_256 (x0, x11₁) in
                expr_let x14 := ADDC_128 (x13₂, 0, x12₁) in
                expr_let x15 := RSHI (x14₁, x13₁, 1) in
                expr_let x16 := 340282366841710300967557013911933812736 *₂₅₆ (uint128)(x15 >> 128) in
                expr_let x17 := 79228162514264337593543950335 *₂₅₆ (uint128)(x15 >> 128) in
                expr_let x18 := 340282366841710300967557013911933812736 *₂₅₆ ((uint128)(x15) & 340282366920938463463374607431768211455) in
                expr_let x19 := 79228162514264337593543950335 *₂₅₆ ((uint128)(x15) & 340282366920938463463374607431768211455) in
                expr_let x20 := ADD_256 ((uint256)(((uint128)(x18) & 340282366920938463463374607431768211455) << 128), x19) in
                expr_let x21 := ADDC_256 (x20₂, (uint128)(x18 >> 128), x16) in
                expr_let x22 := ADD_256 ((uint256)(((uint128)(x17) & 340282366920938463463374607431768211455) << 128), x20₁) in
                expr_let x23 := ADDC_256 (x22₂, (uint128)(x17 >> 128), x21₁) in
                expr_let x24 := SUB_256 (x₁, x22₁) in
                expr_let x25 := SUBB_256 (x24₂, x₂, x23₁) in
                expr_let x26 := SELL (x25₁, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951) in
                expr_let x27 := SUB_256 (x24₁, x26) in
                ADDM (x27₁, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951)
     : Expr (type.uncurry (type.type_primitive type.Z -> type.type_primitive type.Z -> type.type_primitive type.Z))
  *)

  Import PreFancy.
  Import PreFancy.Notations.
  (*
Local Notation "'RegMod'" := (Straightline.expr.Primitive (t:=type.Z) 115792089210356248762697446949407573530086143415290314195533631308867097853951).
  Local Notation "'RegMuLow'" := (Straightline.expr.Primitive (t:=type.Z) 26959946667150639793205513449348445388433292963828203772348655992835).
   *)
  (*
  Print barrett_red256_prefancy.
*)
  (*
    selm@(y, $x₂, RegZero, RegMuLow);
    rshi@(y0, RegZero, $x₂,255);
    rshi@(y1, $x₂, $x₁,255);
    mulhh@(y2, RegMuLow, $y1);
    mulhl@(y3, RegMuLow, $y1);
    mullh@(y4, RegMuLow, $y1);
    mulll@(y5, RegMuLow, $y1);
    add@(y6, $y5, $y4, 128);
    addc@(y7, carry{$y6}, $y2, $y4, -128);
    add@(y8, $y6, $y3, 128);
    addc@(y9, carry{$y8}, $y7, $y3, -128);
    add@(y10, $y1, $y9, 0);
    addc@(y11, carry{$y10}, RegZero, $y0, 0); #128
    add@(y12, $y, $y10, 0);
    addc@(y13, carry{$y12}, RegZero, $y11, 0); #128
    rshi@(y14, $y13, $y12,1);
    mulhh@(y15, RegMod, $y14);
    mullh@(y16, RegMod, $y14);
    mulhl@(y17, RegMod, $y14);
    mulll@(y18, RegMod, $y14);
    add@(y19, $y18, $y17, 128);
    addc@(y20, carry{$y19}, $y15, $y17, -128);
    add@(y21, $y19, $y16, 128);
    addc@(y22, carry{$y21}, $y20, $y16, -128);
    sub@(y23, $x₁, $y21, 0);
    subb@(y24, carry{$y23}, $x₂, $y22, 0);
    sell@(y25, $y24, RegZero, RegMod);
    sub@(y26, $y23, $y25, 0);
    addm@(y27, $y26, RegZero, RegMod);
    ret $y27
  *)
End Barrett256.

Module Montgomery256.

  Definition N := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition N':= (115792089210356248768974548684794254293921932838497980611635986753331132366849).
  Definition R := Eval lazy in (2^256).
  Definition R' := 115792089183396302114378112356516095823261736990586219612555396166510339686400.
  Definition machine_wordsize := 256.

  Derive montred256
         SuchThat (MontgomeryReduction.rmontred_correctT N R N' machine_wordsize montred256)
         As montred256_correct.
  Proof. Time solve_rmontred machine_wordsize. Time Qed.

  (*
  Definition montred256_prefancy' := PreFancy.of_Expr machine_wordsize [N;N'] montred256.

  Derive montred256_prefancy
         SuchThat (montred256_prefancy = montred256_prefancy' type.interp)
         As montred256_prefancy_eq.
  Proof. lazy - [type.interp]; reflexivity. Qed.
*)

  Lemma montred'_correct_specialized R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2 (lo, hi) = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    apply MontgomeryReduction.montred'_correct with (T:=lo + R * hi) (R':=R');
      try match goal with
            | |- context[R'] => assumption
            | |- context [lo] =>
              try assumption; progress autorewrite with zsimplify cancel_pair; reflexivity
          end; lazy; try split; congruence.
  Qed.

  (*
  (* Note: If this is not factored out, then for some reason Qed takes forever in montred256_correct_full. *)
  Lemma montred256_correct_proj2 :
    forall xy : type.interp (type.prod type.Z type.Z),
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
       expr.Interp (@ident.interp) montred256 xy = app_curried (t:=type.arrow (type.prod type.Z type.Z) type.Z) (MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2) xy.
  Proof. intros; destruct (montred256_correct xy); assumption. Qed.
  Lemma montred256_correct_proj2' :
    forall xy : type.interp (type.prod type.Z type.Z),
      ZRange.type.option.is_bounded_by
        (t:=type.prod type.Z type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        xy = true ->
       expr.Interp (@ident.interp) montred256 xy = MontgomeryReduction.montred' N R N' (Z.log2 R) 2 2 xy.
  Proof. intros; rewrite montred256_correct_proj2 by assumption; unfold app_curried; exact eq_refl. Qed.
   *)
  Local Arguments is_bounded_by_bool / .
  Lemma montred256_correct_full  R' (R'_correct : Z.equiv_modulo N (R * R') 1) :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      PreFancy.Interp 256 montred256 (lo, hi) = ((lo + R * hi) * R') mod N.
  Proof.
    intros.
    rewrite <-montred'_correct_specialized by assumption.
    destruct (proj1 montred256_correct ((lo, hi), tt) ((lo, hi), tt)) as [H2 H3].
    { repeat split. }
    { cbn -[Z.pow].
      rewrite !andb_true_iff.
      repeat apply conj; Z.ltb_to_lt; trivial; cbv [R N machine_wordsize] in *; lia. }
    { etransitivity; [ eapply H3 | ]. (* need Strategy -100 [type.app_curried]. for this to be fast *)
      generalize MontgomeryReduction.montred'; vm_compute; reflexivity. }
  Qed.

  (*
  (* TODO : maybe move these ok_expr tactics somewhere else *)
  Ltac ok_expr_step' :=
    match goal with
    | _ => assumption
    | |- _ <= _ <= _ \/ @eq zrange _ _ =>
      right; lazy; try split; congruence
    | |- _ <= _ <= _ \/ @eq zrange _ _ =>
      left; lazy; try split; congruence
    | |- lower r[0~>_]%zrange = 0 => reflexivity
    | |- context [PreFancy.ok_ident] => constructor
    | |- context [PreFancy.ok_scalar] => constructor; try omega
    | |- context [PreFancy.is_halved] => eapply PreFancy.is_halved_constant; [lazy; reflexivity | ]
    | |- context [PreFancy.is_halved] => constructor
    | |- context [PreFancy.in_word_range] => lazy; reflexivity
    | |- context [PreFancy.in_flag_range] => lazy; reflexivity
    | |- context [PreFancy.get_range] =>
      cbn [PreFancy.get_range lower upper fst snd ZRange.map]
    | x : type.interp (type.prod _ _) |- _ => destruct x
    | |- (_ <=? _)%zrange = true =>
      match goal with
      | |- context [PreFancy.get_range_var] =>
        cbv [is_tighter_than_bool PreFancy.has_range fst snd upper lower R N] in *; cbn;
        apply andb_true_iff; split; apply Z.leb_le
      | _ => lazy
      end; omega || reflexivity
    | |- @eq zrange _ _ => lazy; reflexivity
    | |- _ <= _ => cbv [machine_wordsize]; omega
    | |- _ <= _ <= _ => cbv [machine_wordsize]; omega
    end; intros.

  (* TODO : maybe move these ok_expr tactics somewhere else *)
  Ltac ok_expr_step :=
    match goal with
    | |- context [PreFancy.ok_expr] => constructor; cbn [fst snd]; repeat ok_expr_step'
    end; intros; cbn [Nat.max].*)

  (*
  Lemma montred256_prefancy_correct :
    forall (lo hi : Z),
      0 <= lo < R -> 0 <= hi < R -> 0 <= lo + R * hi < R * N ->
      @PreFancy.interp machine_wordsize base.type.Z (montred256 _ @ (##lo,##hi)) = ((lo + R * hi) * R') mod N.
  Proof.
    intros.

    rewrite montred256_prefancy_eq; cbv [montred256_prefancy'].
    erewrite PreFancy.of_Expr_correct.
    { apply montred256_correct_full; try assumption; reflexivity. }
    { reflexivity. }
    { lazy; reflexivity. }
    { lazy; reflexivity. }
    { repeat constructor. }
    { cbv [In N N']; intros; intuition; subst; cbv; congruence. }
    { assert (340282366920938463463374607431768211455 * 2 ^ 128 <= 2 ^ machine_wordsize - 1) as shiftl_128_ok by (lazy; congruence).
      repeat (ok_expr_step; [ ]).
      ok_expr_step.
      lazy; congruence.
      constructor.
      constructor. }
    { lazy. omega. }
   Qed.
*)

  Definition montred256_fancy' (lo hi RegMod RegPInv RegZero error : positive) :=
    Fancy.of_Expr 3%positive
                  (fun z => if z =? N then Some RegMod else if z =? N' then Some RegPInv else if z =? 0 then Some RegZero else None)
                  [N;N']
                  montred256
                  ((lo, hi)%positive, tt)
                  error.
  Derive montred256_fancy
         SuchThat (forall RegMod RegPInv RegZero,
                      montred256_fancy RegMod RegPInv RegZero = montred256_fancy' RegMod RegPInv RegZero)
         As montred256_fancy_eq.
  Proof.
    intros.
    lazy - [Fancy.ADD Fancy.ADDC Fancy.SUB
                      Fancy.MUL128LL Fancy.MUL128LU Fancy.MUL128UL Fancy.MUL128UU
                      Fancy.RSHI Fancy.SELC Fancy.SELM Fancy.SELL Fancy.ADDM].
    reflexivity.
  Qed.

  Import Fancy.Registers.

  Definition montred256_alloc' lo hi RegPInv :=
    fun errorP errorR =>
    Fancy.allocate register
                   positive Pos.eqb
                   errorR
                   (montred256_fancy 1000%positive 1001%positive 1002%positive 1003%positive 1004%positive errorP)
                   [r2;r3;r4;r5;r6;r7;r8;r9;r10;r11;r12;r13;r14;r15;r16;r17;r18;r19;r20]
                   (fun n => if n =? 1000 then lo
                             else if n =? 1001 then hi
                                  else if n =? 1002 then RegMod
                                       else if n =? 1003 then RegPInv
                                            else if n =? 1004 then RegZero
                                                 else errorR).
  Derive montred256_alloc
         SuchThat (montred256_alloc = montred256_alloc')
         As montred256_alloc_eq.
  Proof.
    intros.
    cbv [montred256_alloc' montred256_fancy].
    cbn. subst montred256_alloc.
    reflexivity.
  Qed.

  Import ProdEquiv.

  Local Ltac solve_bounds :=
    match goal with
    | H : ?a = ?b mod ?c |- 0 <= ?a < ?c => rewrite H; apply Z.mod_pos_bound; omega
    | _ => assumption
    end.

  Lemma montred256_alloc_equivalent errorP errorR cc_start_state start_context :
    forall lo hi y t1 t2 scratch RegPInv extra_reg,
      NoDup [lo; hi; y; t1; t2; scratch; RegPInv; extra_reg; RegMod; RegZero] ->
      0 <= start_context lo < R ->
      0 <= start_context hi < R ->
      0 <= start_context RegPInv < R ->
      ProdEquiv.interp256 (montred256_alloc r0 r1 r30 errorP errorR) cc_start_state
                          (fun r => if reg_eqb r r0
                                    then start_context lo
                                    else if reg_eqb r r1
                                         then start_context hi
                                         else if reg_eqb r r30
                                              then start_context RegPInv
                                              else start_context r)
    = ProdEquiv.interp256 (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context.
  Proof.
    intros. cbv [R] in *.
    cbv [Prod.MontRed256 montred256_alloc].

    (* Extract proofs that no registers are equal to each other *)
    repeat match goal with
           | H : NoDup _ |- _ => inversion H; subst; clear H
           | H : ~ In _ _ |- _ => cbv [In] in H
           | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H; destruct H
           | H : ~ False |- _ => clear H
           end.

    rewrite ProdEquiv.interp_Mul256 with (tmp2:=extra_reg) by (congruence || push_value_unused).

    rewrite mullh_mulhl. step_both_sides.
    rewrite mullh_mulhl. step_both_sides.
    (*
    step_both_sides.
    step_both_sides.

    rewrite ProdEquiv.interp_Mul256x256 with (tmp2:=extra_reg) by (congruence || push_value_unused).

    rewrite mulll_comm. step_both_sides.
    step_both_sides.
    step_both_sides.
    rewrite mulhh_comm. step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.


    rewrite add_comm by (cbn; solve_bounds). step_both_sides.
    rewrite addc_comm by (cbn; solve_bounds). step_both_sides.
    step_both_sides.
    step_both_sides.
    step_both_sides.

    cbn; repeat progress rewrite ?reg_eqb_neq, ?reg_eqb_refl by congruence.
    reflexivity.*)
  Admitted.

  Import Fancy_PreFancy_Equiv.

  Definition interp_equivZZ_256 {s} :=
    @interp_equivZZ s 256 ltac:(cbv; congruence) 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).
  Definition interp_equivZ_256 {s} :=
    @interp_equivZ s 256 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(reflexivity).

  Local Ltac simplify_op_equiv start_ctx :=
    cbn - [Fancy.spec ident.gen_interp Fancy.cc_spec];
    repeat match goal with H : start_ctx _ = _ |- _ => rewrite H end;
    cbv - [
      Z.add_with_get_carry_full
        Z.add_get_carry_full Z.sub_get_borrow_full
        Z.le Z.ltb Z.leb Z.geb Z.eqb Z.land Z.shiftr Z.shiftl
        Z.add Z.mul Z.div Z.sub Z.modulo Z.testbit Z.pow Z.ones
        fst snd]; cbn [fst snd];
    try (replace (2 ^ (256 / 2) - 1) with (Z.ones 128) by reflexivity; rewrite !Z.land_ones by omega);
    autorewrite with to_div_mod; rewrite ?Z.mod_mod, <-?Z.testbit_spec' by omega;
    repeat match goal with
           | H : 0 <= ?x < ?m |- context [?x mod ?m] => rewrite (Z.mod_small x m) by apply H
           | |- context [?x <? 0] => rewrite (proj2 (Z.ltb_ge x 0)) by (break_match; Z.zero_bounds)
           | _ => rewrite Z.mod_small with (b:=2) by (break_match; omega)
           | |- context [ (if Z.testbit ?a ?n then 1 else 0) + ?b + ?c] =>
             replace ((if Z.testbit a n then 1 else 0) + b + c) with (b + c + (if Z.testbit a n then 1 else 0)) by ring
           end.

  Local Ltac solve_nonneg ctx :=
    match goal with x := (Fancy.spec _ _ _) |- _ => subst x end;
    simplify_op_equiv ctx; Z.zero_bounds.

  Local Ltac generalize_result :=
    let v := fresh "v" in intro v; generalize v; clear v; intro v.

  Local Ltac generalize_result_nonneg ctx :=
    let v := fresh "v" in
    let v_nonneg := fresh "v_nonneg" in
    intro v; assert (0 <= v) as v_nonneg; [solve_nonneg ctx |generalize v v_nonneg; clear v v_nonneg; intros v v_nonneg].

  Local Ltac step_abs :=
    match goal with
    | [ |- context G[expr.interp ?ident_interp (expr.Abs ?f) ?x] ]
      => let G' := context G[expr.interp ident_interp (f x)] in
         change G'; cbv beta
    end.
  Local Ltac step ctx :=
    repeat step_abs;
    match goal with
    | |- Fancy.interp _ _ _ (Fancy.Instr (Fancy.ADD _) _ _ (Fancy.Instr (Fancy.ADDC _) _ _ _)) _ _ = _ =>
      apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result_nonneg ctx]
    | [ |- _ = expr.interp _ (PreFancy.LetInAppIdentZ _ _ _ _ _ _) ]
      => apply interp_equivZ_256; [simplify_op_equiv ctx | generalize_result]
    | [ |- _ = expr.interp _ (PreFancy.LetInAppIdentZZ _ _ _ _ _ _) ]
      => apply interp_equivZZ_256; [ simplify_op_equiv ctx | simplify_op_equiv ctx | generalize_result]
    end.

  (* TODO: move this lemma to ZUtil *)
  Lemma testbit_neg_eq_if x y n :
    0 <= n ->
    0 <= x < 2 ^ n ->
    0 <= y < 2 ^ n ->
    Z.b2z (if (x - y) <? 0 then true else Z.testbit (x - y) n) = - ((x - y) / 2 ^ n) mod 2.
  Proof.
    intros. rewrite Z.sub_pos_bound_div_eq by omega.
    break_innermost_match; Z.ltb_to_lt; try lia; try reflexivity; [ ].
    rewrite Z.testbit_eqb, Z.div_between_0_if by omega.
    break_innermost_match; Z.ltb_to_lt; try lia; reflexivity.
  Qed.

  Local Ltac break_ifs :=
    repeat (break_innermost_match_step; Z.ltb_to_lt; try (exfalso; omega); []).

  Lemma prod_montred256_correct :
    forall (cc_start_state : Fancy.CC.state) (* starting carry flags can be anything *)
           (start_context : register -> Z)   (* starting register values *)
           (lo hi y t1 t2 scratch RegPInv extra_reg : register), (* registers to use in computation *)
      NoDup [lo; hi; y; t1; t2; scratch; RegPInv; extra_reg; RegMod; RegZero] -> (* registers must be distinct *)
      start_context RegPInv = N' ->  (* RegPInv needs to hold the inverse of the modulus *)
      start_context RegMod = N ->    (* RegMod needs to hold the modulus *)
      start_context RegZero = 0 ->   (* RegZero needs to hold zero *)
      (0 <= start_context lo < R) -> (* low half of the input is in bounds (R=2^256) *)
      (0 <= start_context hi < R) -> (* high half of the input is in bounds (R=2^256) *)
      let x := (start_context lo) + R * (start_context hi) in (* x is the input (split into two registers) *)
      (0 <= x < R * N) -> (* input precondition *)
      (ProdEquiv.interp256 (Prod.MontRed256 lo hi y t1 t2 scratch RegPInv) cc_start_state start_context = (x * R') mod N).
  Proof.
    intros. subst x. cbv [N R N'] in *.
    rewrite <-montred256_correct_full by (auto; vm_compute; reflexivity).
    rewrite <-montred256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (cbv [R]; auto with omega).
    cbv [ProdEquiv.interp256].
    cbv [montred256_alloc montred256 expr.Interp].

    step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | ].
    (*step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | break_ifs; reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].

    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ reflexivity | reflexivity | ].
    step start_context; [ break_innermost_match; Z.ltb_to_lt; omega | ].
    step start_context; [ reflexivity | | ].
    {
      let r := eval cbv in (2^256) in replace (2^256) with r by reflexivity.
      rewrite !Z.shiftl_0_r, !Z.mod_mod by omega.
      apply testbit_neg_eq_if;
        let r := eval cbv in (2^256) in replace (2^256) with r by reflexivity;
        auto using Z.mod_pos_bound with omega. }
    step start_context; [ break_innermost_match; Z.ltb_to_lt; omega | ].
    reflexivity.
     *)
  Admitted.

  Import PrintingNotations.
  Set Printing Width 10000.

  Print montred256.
(*
montred256 = fun var : type -> Type => (λ x : var (type.type_primitive type.Z * type.type_primitive type.Z)%ctype,
    expr_let x0 := 79228162514264337593543950337 *₂₅₆ (uint128)(x₁ >> 128) in
    expr_let x1 := 340282366841710300986003757985643364352 *₂₅₆ ((uint128)(x₁) & 340282366920938463463374607431768211455) in
    expr_let x2 := 79228162514264337593543950337 *₂₅₆ ((uint128)(x₁) & 340282366920938463463374607431768211455) in
    expr_let x3 := ADD_256 ((uint256)(((uint128)(x1) & 340282366920938463463374607431768211455) << 128), x2) in
    expr_let x4 := ADD_256 ((uint256)(((uint128)(x0) & 340282366920938463463374607431768211455) << 128), x3₁) in
    expr_let x5 := 79228162514264337593543950335 *₂₅₆ ((uint128)(x4₁) & 340282366920938463463374607431768211455) in
    expr_let x6 := 79228162514264337593543950335 *₂₅₆ (uint128)(x4₁ >> 128) in
    expr_let x7 := 340282366841710300967557013911933812736 *₂₅₆ ((uint128)(x4₁) & 340282366920938463463374607431768211455) in
    expr_let x8 := 340282366841710300967557013911933812736 *₂₅₆ (uint128)(x4₁ >> 128) in
    expr_let x9 := ADD_256 ((uint256)(((uint128)(x7) & 340282366920938463463374607431768211455) << 128), x5) in
    expr_let x10 := ADDC_256 (x9₂, (uint128)(x7 >> 128), x8) in
    expr_let x11 := ADD_256 ((uint256)(((uint128)(x6) & 340282366920938463463374607431768211455) << 128), x9₁) in
    expr_let x12 := ADDC_256 (x11₂, (uint128)(x6 >> 128), x10₁) in
    expr_let x13 := ADD_256 (x11₁, x₁) in
    expr_let x14 := ADDC_256 (x13₂, x12₁, x₂) in
    expr_let x15 := SELC (x14₂, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951) in
    expr_let x16 := SUB_256 (x14₁, x15) in
    ADDM (x16₁, 0, 115792089210356248762697446949407573530086143415290314195533631308867097853951))%expr
     : Expr (type.uncurry (type.type_primitive type.Z * type.type_primitive type.Z -> type.type_primitive type.Z))
*)

  Import PreFancy.
  Import PreFancy.Notations.
  Local Notation "'RegMod'" := (expr.Ident (ident.Literal 115792089210356248762697446949407573530086143415290314195533631308867097853951)).
  Local Notation "'RegPInv'" := (expr.Ident (ident.Literal 115792089210356248768974548684794254293921932838497980611635986753331132366849)).
  Local Open Scope expr_scope.
  Local Notation mulhl := (#(fancy_mulhl 256)).
  Local Notation mulhh := (#(fancy_mulhh 256)).
  Local Notation mulll := (#(fancy_mulll 256)).
  Local Notation mullh := (#(fancy_mullh 256)).
  Local Notation selc := (#(fancy_selc)).
  Local Notation addm := (#(fancy_addm)).
  Notation add n := (#(fancy_add 256 n)).
  Notation addc n := (#(fancy_addc 256 n)).

  Print montred256.
  (*
montred256 =
fun var : type -> Type =>
λ x : var (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype),
mulhl@(x0, x₁, RegPInv);
mullh@(x1, x₁, RegPInv);
mulll@(x2, x₁, RegPInv);
(add 128)@(x3, x2, Lower{x1});
(add 128)@(x4, x3₁, Lower{x0});
mulll@(x5, RegMod, x4₁);
mullh@(x6, RegMod, x4₁);
mulhl@(x7, RegMod, x4₁);
mulhh@(x8, RegMod, x4₁);
(add 128)@(x9, x5, Lower{x7});
(addc (-128))@(x10, carry{$x9}, x8, x7);
(add 128)@(x11, x9₁, Lower{x6});
(addc (-128))@(x12, carry{$x11}, x10₁, x6);
(add 0)@(x13, x11₁, x₁);
(addc 0)@(x14, carry{$x13}, x12₁, x₂);
selc@(x15, (carry{$x14}, RegZero), RegMod);
#(fancy_sub 256 0)@(x16, x14₁, x15);
addm@(x17, (x16₁, RegZero), RegMod);
x17
     : Expr
         (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype ->
          type.base (base.type.type_base base.type.Z))%ptype
  *)

End Montgomery256.

Local Notation "i rd x y ; cont" := (Fancy.Instr i rd (x, y) cont) (at level 40, cont at level 200, format "i  rd  x  y ; '//' cont").
Local Notation "i rd x y z ; cont" := (Fancy.Instr i rd (x, y, z) cont) (at level 40, cont at level 200, format "i  rd  x  y  z ; '//' cont").

Import Fancy.Registers.
Import Fancy.

Import Barrett256 Montgomery256.

(*** Montgomery Reduction ***)

(* Status: Code in final form is proven correct modulo admits in compiler portions. *)

(* Montgomery Code : *)
Eval cbv beta iota delta [Prod.MontRed256 Prod.Mul256 Prod.Mul256x256] in Prod.MontRed256.
(*
     = fun lo hi y t1 t2 scratch RegPInv : register =>
       MUL128LL y lo RegPInv;
       MUL128UL t1 lo RegPInv;
       ADD 128 y y t1;
       MUL128LU t1 lo RegPInv;
       ADD 128 y y t1;
       MUL128LL t1 y RegMod;
       MUL128UU t2 y RegMod;
       MUL128UL scratch y RegMod;
       ADD 128 t1 t1 scratch;
       ADDC (-128) t2 t2 scratch;
       MUL128LU scratch y RegMod;
       ADD 128 t1 t1 scratch;
       ADDC (-128) t2 t2 scratch;
       ADD 0 lo lo t1;
       ADDC 0 hi hi t2;
       SELC y RegMod RegZero;
       SUB 0 lo hi y;
       ADDM lo lo RegZero RegMod;
       Ret lo
 *)

(* Uncomment to see proof statement and remaining admitted statements,
or search for "prod_montred256_correct" to see comments on the proof
preconditions. *)
(*
Check Montgomery256.prod_montred256_correct.
Print Assumptions Montgomery256.prod_montred256_correct.
*)

(*** Barrett Reduction ***)

(* Status: Code is proven correct modulo admits in compiler
portions. However, unlike for Montgomery, this code is not proven
equivalent to the register-allocated and efficiently-scheduled
reference (Prod.MulMod). This proof is currently admitted and would
require either fiddling with code generation to make instructions come
out in the right order or reasoning about which instructions
commute. *)

(* Barrett reference code: *)
Eval cbv beta iota delta [Prod.MulMod Prod.Mul256x256] in Prod.MulMod.
(*
     = fun x xHigh RegMuLow scratchp1 scratchp2 scratchp3 scratchp4 scratchp5 : register =>
       let q1Bottom256 := scratchp1 in
       let muSelect := scratchp2 in
       let q2 := scratchp3 in
       let q2High := scratchp4 in
       let q2High2 := scratchp5 in
       let q3 := scratchp1 in
       let r2 := scratchp2 in
       let r2High := scratchp3 in
       let maybeM := scratchp1 in
       SELM muSelect RegMuLow RegZero;
       RSHI 255 q1Bottom256 xHigh x;
       MUL128LL q2 q1Bottom256 RegMuLow;
       MUL128UU q2High q1Bottom256 RegMuLow;
       MUL128UL scratchp5 q1Bottom256 RegMuLow;
       ADD 128 q2 q2 scratchp5;
       ADDC (-128) q2High q2High scratchp5;
       MUL128LU scratchp5 q1Bottom256 RegMuLow;
       ADD 128 q2 q2 scratchp5;
       ADDC (-128) q2High q2High scratchp5;
       RSHI 255 q2High2 RegZero xHigh;
       ADD 0 q2High q2High q1Bottom256;
       ADDC 0 q2High2 q2High2 RegZero;
       ADD 0 q2High q2High muSelect;
       ADDC 0 q2High2 q2High2 RegZero;
       RSHI 1 q3 q2High2 q2High;
       MUL128LL r2 RegMod q3;
       MUL128UU r2High RegMod q3;
       MUL128UL scratchp4 RegMod q3;
       ADD 128 r2 r2 scratchp4;
       ADDC (-128) r2High r2High scratchp4;
       MUL128LU scratchp4 RegMod q3;
       ADD 128 r2 r2 scratchp4;
       ADDC (-128) r2High r2High scratchp4;
       SUB 0 muSelect x r2;
       SUBC 0 xHigh xHigh r2High;
       SELL maybeM RegMod RegZero;
       SUB 0 q3 muSelect maybeM;
       ADDM x q3 RegZero RegMod;
       Ret x
 *)

(* Barrett generated code (equivalence with reference admitted) *)
Eval cbv beta iota delta [barrett_red256_alloc] in barrett_red256_alloc.
(*
     = fun (xLow xHigh RegMuLow : register) (_ : positive) (_ : register) =>
       SELM r2 RegMuLow RegZero;
       RSHI 255 r3 RegZero xHigh;
       RSHI 255 r4 xHigh xLow;
       MUL128UU r5 RegMuLow r4;
       MUL128UL r6 r4 RegMuLow;
       MUL128LU r7 r4 RegMuLow;
       MUL128LL r8 RegMuLow r4;
       ADD 128 r9 r8 r7;
       ADDC (-128) r10 r5 r7;
       ADD 128 r5 r9 r6;
       ADDC (-128) r11 r10 r6;
       ADD 0 r6 r4 r11;
       ADDC 0 r12 RegZero r3;
       ADD 0 r13 r2 r6;
       ADDC 0 r14 RegZero r12;
       RSHI 1 r15 r14 r13;
       MUL128UU r16 RegMod r15;
       MUL128LU r17 r15 RegMod;
       MUL128UL r18 r15 RegMod;
       MUL128LL r19 RegMod r15;
       ADD 128 r20 r19 r18;
       ADDC (-128) r21 r16 r18;
       ADD 128 r22 r20 r17;
       ADDC (-128) r23 r21 r17;
       SUB 0 r24 xLow r22;
       SUBC 0 r25 xHigh r23;
       SELL r26 RegMod RegZero;
       SUB 0 r27 r24 r26;
       ADDM r28 r27 RegZero RegMod;
       Ret r28
 *)

(* Uncomment to see proof statement and remaining admitted statements. *)
(*
Check prod_barrett_red256_correct.
Print Assumptions prod_barrett_red256_correct.
(* The equivalence with generated code is admitted as barrett_red256_alloc_equivalent. *)
*)
