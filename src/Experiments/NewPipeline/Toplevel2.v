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
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
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
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Experiments.NewPipeline.Arithmetic.
Require Crypto.Experiments.NewPipeline.Language.
Require Crypto.Experiments.NewPipeline.UnderLets.
Require Crypto.Experiments.NewPipeline.AbstractInterpretation.
Require Crypto.Experiments.NewPipeline.AbstractInterpretationProofs.
Require Crypto.Experiments.NewPipeline.Rewriter.
Require Crypto.Experiments.NewPipeline.MiscCompilerPasses.
Require Crypto.Experiments.NewPipeline.CStringification.
Require Export Crypto.Experiments.NewPipeline.PushButtonSynthesis.
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
(* Notation "x" := (expr.Var x) (only printing, at level 9) : expr_scope. *)

Import UnsaturatedSolinas.

(* TODO: Figure out what examples should go here *)
(*
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
 *)

(** TODO: Figure out if this belongs here *)
Module PrintingNotations.
  Export ident.
  (*Global Set Printing Width 100000.*)
  Open Scope zrange_scope.
  Notation "'uint256'"
    := (r[0 ~> 115792089237316195423570985008687907853269984665640564039457584007913129639935]%zrange) : zrange_scope.
  Notation "'uint128'"
    := (r[0 ~> 340282366920938463463374607431768211455]%zrange) : zrange_scope.
  Notation "'uint64'"
    := (r[0 ~> 18446744073709551615]) : zrange_scope.
  Notation "'uint32'"
    := (r[0 ~> 4294967295]) : zrange_scope.
  Notation "'bool'"
    := (r[0 ~> 1]%zrange) : zrange_scope.
  Notation "( range )( ls [[ n ]] )"
    := ((#(ident.Z_cast range) @ (ls [[ n ]]))%expr)
         (format "( range )( ls [[ n ]] )") : expr_scope.
  (*Notation "( range )( v )" := (ident.Z_cast range @@ v)%expr : expr_scope.*)
  Notation "x *₂₅₆ y"
    := (#(ident.Z_cast uint256) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x *₁₂₈ y"
    := (#(ident.Z_cast uint128) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x *₆₄ y"
    := (#(ident.Z_cast uint64) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x *₃₂ y"
    := (#(ident.Z_cast uint32) @ (#ident.Z_mul @ x @ y))%expr (at level 40) : expr_scope.
  Notation "x +₂₅₆ y"
    := (#(ident.Z_cast uint256) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x +₁₂₈ y"
    := (#(ident.Z_cast uint128) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x +₆₄ y"
    := (#(ident.Z_cast uint64) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x +₃₂ y"
    := (#(ident.Z_cast uint32) @ (#ident.Z_add @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x -₁₂₈ y"
    := (#(ident.Z_cast uint128) @ (#ident.Z_sub @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x -₆₄ y"
    := (#(ident.Z_cast uint64) @ (#ident.Z_sub @ x @ y))%expr (at level 50) : expr_scope.
  Notation "x -₃₂ y"
    := (#(ident.Z_cast uint32) @ (#ident.Z_sub @ x @ y))%expr (at level 50) : expr_scope.
  Notation "( out_t )( v >> count )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_shiftr @ v @ count))%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "( out_t )( v << count )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_shiftl @ v @ count))%expr)
         (format "( out_t )( v  <<  count )") : expr_scope.
  Notation "( range )( v )"
    := ((#(ident.Z_cast range) @ $v)%expr)
         (format "( range )( v )") : expr_scope.
  Notation "( mask & ( out_t )( v ) )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_land @ #(ident.Literal (t:=base.type.Z) mask) @ v))%expr)
         (format "( mask  &  ( out_t )( v ) )")
       : expr_scope.
  Notation "( ( out_t )( v ) & mask )"
    := ((#(ident.Z_cast out_t) @ (#ident.Z_land @ v @ #(ident.Literal (t:=base.type.Z) mask)))%expr)
         (format "( ( out_t )( v )  &  mask )")
       : expr_scope.

  Notation "x" := (#(ident.Z_cast _) @ $x)%expr (only printing, at level 9) : expr_scope.
  Notation "x" := (#(ident.Z_cast2 _) @ $x)%expr (only printing, at level 9) : expr_scope.
  Notation "v ₁" := (#ident.fst @ $v)%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (#ident.snd @ $v)%expr (at level 10, format "v ₂") : expr_scope.
  Notation "v ₁" := (#(ident.Z_cast _) @ (#ident.fst @ $v))%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (#(ident.Z_cast _) @ (#ident.snd @ $v))%expr (at level 10, format "v ₂") : expr_scope.
  Notation "v ₁" := (#(ident.Z_cast _) @ (#ident.fst @ (#(ident.Z_cast2 _) @ $v)))%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (#(ident.Z_cast _) @ (#ident.snd @ (#(ident.Z_cast2 _) @ $v)))%expr (at level 10, format "v ₂") : expr_scope.
  Notation "x" := (#(ident.Literal x%Z))%expr (only printing) : expr_scope.

  (*Notation "ls [[ n ]]" := (List.nth_default_concrete _ n @@ ls)%expr : expr_scope.
  Notation "( range )( v )" := (ident.Z_cast range @@ v)%expr : expr_scope.
  Notation "x *₁₂₈ y"
    := (ident.Z_cast uint128 @@ (ident.Z.mul (x, y)))%expr (at level 40) : expr_scope.
  Notation "( out_t )( v >> count )"
    := (ident.Z_cast out_t (ident.Z.shiftr count @@ v)%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "( out_t )( v >> count )"
    := (ident.Z_cast out_t (ident.Z.shiftr count @@ v)%expr)
         (format "( out_t )( v  >>  count )") : expr_scope.
  Notation "v ₁" := (ident.fst @@ v)%expr (at level 10, format "v ₁") : expr_scope.
  Notation "v ₂" := (ident.snd @@ v)%expr (at level 10, format "v ₂") : expr_scope.*)
  (*
  Notation "'ℤ'"
    := BoundsAnalysis.type.Z : zrange_scope.
  Notation "ls [[ n ]]" := (List.nth n @@ ls)%nexpr : nexpr_scope.
  Notation "x *₆₄₋₆₄₋₁₂₈ y"
    := (mul uint64 uint64 uint128 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₆₄₋₆₄₋₆₄ y"
    := (mul uint64 uint64 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₃₂₋₃₂ y"
    := (mul uint32 uint32 uint32 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₁₂₈₋₁₂₈ y"
    := (mul uint32 uint128 uint128 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₆₄₋₆₄ y"
    := (mul uint32 uint64 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x *₃₂₋₃₂₋₆₄ y"
    := (mul uint32 uint32 uint64 @@ (x, y))%nexpr (at level 40) : nexpr_scope.
  Notation "x +₁₂₈ y"
    := (add uint128 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₆₄₋₁₂₈₋₁₂₈ y"
    := (add uint64 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₃₂₋₆₄₋₆₄ y"
    := (add uint32 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₆₄ y"
    := (add uint64 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x +₃₂ y"
    := (add uint32 uint32 uint32 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₁₂₈ y"
    := (sub uint128 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₆₄₋₁₂₈₋₁₂₈ y"
    := (sub uint64 uint128 uint128 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₃₂₋₆₄₋₆₄ y"
    := (sub uint32 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₆₄ y"
    := (sub uint64 uint64 uint64 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x -₃₂ y"
    := (sub uint32 uint32 uint32 @@ (x, y))%nexpr (at level 50) : nexpr_scope.
  Notation "x" := ({| BoundsAnalysis.type.value := x |}) (only printing) : nexpr_scope.
  Notation "( out_t )( v >> count )"
    := ((shiftr _ out_t count @@ v)%nexpr)
         (format "( out_t )( v  >>  count )")
       : nexpr_scope.
  Notation "( out_t )( v << count )"
    := ((shiftl _ out_t count @@ v)%nexpr)
         (format "( out_t )( v  <<  count )")
       : nexpr_scope.
  Notation "( ( out_t ) v & mask )"
    := ((land _ out_t mask @@ v)%nexpr)
         (format "( ( out_t ) v  &  mask )")
       : nexpr_scope.
*)
  (* TODO: come up with a better notation for arithmetic with carries
  that still distinguishes it from arithmetic without carries? *)
  Local Notation "'TwoPow256'" := 115792089237316195423570985008687907853269984665640564039457584007913129639936 (only parsing).
  Notation "'ADD_256' ( x ,  y )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y))%expr : expr_scope.
  Notation "'ADD_128' ( x ,  y )" := (#(ident.Z_cast2 (uint128, bool)%core) @ (#ident.Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y))%expr : expr_scope.
  Notation "'ADDC_256' ( x ,  y ,  z )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y @ z))%expr : expr_scope.
  Notation "'ADDC_128' ( x ,  y ,  z )" := (#(ident.Z_cast2 (uint128, bool)%core) @ (#ident.Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y @ z))%expr : expr_scope.
  Notation "'SUB_256' ( x ,  y )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_sub_get_borrow @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y))%expr : expr_scope.
  Notation "'SUBB_256' ( x ,  y , z )" := (#(ident.Z_cast2 (uint256, bool)%core) @ (#ident.Z_sub_with_get_borrow @ #(ident.Literal (t:=base.type.Z) TwoPow256) @ x @ y @ z))%expr : expr_scope.
  Notation "'ADDM' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (#ident.Z_add_modulo @ x @ y @ z))%expr : expr_scope.
  Notation "'RSHI' ( x ,  y ,  z )" := (#(ident.Z_cast _) @ (#ident.Z_rshi @ _ @ x @ y @ z))%expr : expr_scope.
  Notation "'SELC' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (ident.Z_zselect @ x @ y @ z))%expr : expr_scope.
  Notation "'SELM' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (ident.Z_zselect @ (#(Z_cast bool) @ (#Z_cc_m @ _) @ x) @ y @ z))%expr : expr_scope.
  Notation "'SELL' ( x ,  y ,  z )" := (#(ident.Z_cast uint256) @ (#ident.Z_zselect @ (#(Z_cast bool) @ (#Z_land @ #(ident.Literal (t:=base.type.Z 1)) @ x)) @ y @ z))%expr : expr_scope.
End PrintingNotations.

Module Fancy.

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
        let new_ctx := (fun n => if name_eqb n rd then result mod wordmax else ctx n) in
        interp cont new_cc new_ctx
      end.
  End expr.

  Section ISA.
    Import CC.

    Definition cc_spec (x : CC.code) (result : BinInt.Z) : bool :=
      match x with
      | CC.C => Z.testbit result 256 (* carry bit *)
      | CC.M => Z.testbit result 255 (* most significant bit *)
      | CC.L => Z.testbit result 0   (* least significant bit *)
      | CC.Z => result =? 0          (* whether equal to zero *)
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
    Local Notation LetInAppIdentZ S D r eidc x f
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
    Local Notation LetInAppIdentZZ S D r eidc x f
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
              | ident.Z_cast r => fun v => v
              | ident.Z_cast2 (r1, r2) => fun v => v
              | ident.Z_land => fun x y => x
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
      := let default _ := (e' <- type.try_transport (@base.try_make_transport_cps) (@cexpr var) t tZ e;
                             Ret (of_prefancy_scalar e')) in
         match e with
         | LetInAppIdentZ s d r eidc x f
           => idc <- invert_expr.invert_Ident eidc;
                instr_args <- @of_prefancy_ident s tZ idc x;
                let i : instruction := projT1 instr_args in
                let args : tuple name i.(num_source_regs) := projT2 instr_args in
                Instr i next_name args (@of_prefancy (name_succ next_name) _ (f next_name))
         | LetInAppIdentZZ s d r eidc x f
           => idc <- invert_expr.invert_Ident eidc;
                instr_args <- @of_prefancy_ident s (tZ * tZ) idc x;
                let i : instruction := projT1 instr_args in
                let args : tuple name i.(num_source_regs) := projT2 instr_args in
                Instr i next_name args (@of_prefancy (name_succ next_name) _ (f (next_name, next_name))) (* the second argument is for the carry, and it will not be read from directly. *)
         | _  => default tt
         end.
    Fixpoint of_prefancy (next_name : name) {t} (e : @cexpr var t) : @expr name
      := @of_prefancy_step of_prefancy next_name t e.

    Section Proofs.
      Context (name_eqb : name -> name -> bool).
      Context (name_lt : name -> name -> Prop)
              (name_lt_trans : forall n1 n2 n3,
                  name_lt n1 n2 -> name_lt n2 n3 -> name_lt n1 n3)
              (name_lt_irr : forall n, ~ name_lt n n)
              (name_lt_succ : forall n, name_lt n (name_succ n))
              (name_eqb_eq : forall n1 n2, name_eqb n1 n2 = true -> n1 = n2)
              (name_eqb_neq : forall n1 n2, name_eqb n1 n2 = false -> n1 <> n2).
      Local Notation wordmax := (2^256).
      Local Notation interp := (interp name_eqb wordmax cc_spec).
      Local Notation uint256 := r[0~>wordmax-1]%zrange.
      Local Notation uint128 := r[0~>(2 ^ (Z.log2 wordmax / 2) - 1)]%zrange.
      Definition cast_oor (r : zrange) (v : Z) := v mod (upper r + 1).
      Local Notation "'existZ' x" := (existT _ (type.base (base.type.type_base tZ)) x) (at level 200).
      Local Notation "'existZZ' x" := (existT _ (type.base (base.type.type_base tZ * base.type.type_base tZ)%etype) x) (at level 200).
      Local Notation cinterp := (expr.interp (@ident.gen_interp cast_oor)).
      Definition interp_if_Z {t} (e : cexpr t) : option Z :=
        option_map (expr.interp (@ident.gen_interp cast_oor) (t:=tZ))
                   (type.try_transport
                      (@base.try_make_transport_cps)
                      _ _ tZ e).

      Lemma interp_if_Z_Some {t} e r :
        @interp_if_Z t e = Some r ->
        exists e',
          (type.try_transport
             (@base.try_make_transport_cps) _ _ tZ e) = Some e' /\
          expr.interp (@ident.gen_interp cast_oor) (t:=tZ) e' = r.
      Proof.
        clear. cbv [interp_if_Z option_map].
        break_match; inversion 1; intros.
        subst; eexists. tauto.
      Qed.

      Inductive valid_scalar
        : @cexpr var (base.type.type_base tZ) -> Prop :=
      | valid_scalar_literal :
          forall v n,
            consts v = Some n ->
            valid_scalar (expr.Ident (@ident.Literal base.type.Z v))
      | valid_scalar_Var :
          forall v,
            valid_scalar (expr.App (expr.Ident (ident.Z_cast uint256)) (expr.Var v))
      | valid_scalar_fst :
          forall v r2,
            valid_scalar
              (expr.App (expr.Ident (ident.Z_cast uint256))
                        (expr.App (expr.Ident (@ident.fst (base.type.type_base tZ)
                                                          (base.type.type_base tZ)))
                                  (expr.App (expr.Ident (ident.Z_cast2 (uint256, r2))) (expr.Var v))))
      .
      Inductive valid_carry
        :  @cexpr var (base.type.type_base tZ) -> Prop :=
      | valid_carry_0 : consts 0 <> None -> valid_carry (expr.Ident (@ident.Literal base.type.Z 0))
      | valid_carry_1 : consts 1 <> None -> valid_carry (expr.Ident (@ident.Literal base.type.Z 1))
      | valid_carry_snd :
          forall v r2,
            valid_carry
              (expr.App (expr.Ident (ident.Z_cast r[0~>1]))
                        (expr.App (expr.Ident (@ident.snd (base.type.type_base tZ)
                                                          (base.type.type_base tZ)))
                                  (expr.App (expr.Ident (ident.Z_cast2 (r2, r[0~>1]))) (expr.Var v))))
      .

      Fixpoint interp_base (ctx : name -> Z) (cctx : name -> bool) {t}
        : base_var t -> base.interp t :=
        match t as t0 return base_var t0 -> base.interp t0 with
        | base.type.type_base tZ => fun n => ctx n
        | (base.type.type_base tZ * base.type.type_base tZ)%etype =>
          fun v => (ctx (fst v), Z.b2z (cctx (snd v)))
        | (a * b)%etype =>
          fun _ => DefaultValue.type.base.default
        | _ => fun _ : unit =>
                 DefaultValue.type.base.default
        end.

      Definition new_write {d} : var d -> name :=
        match d with
        | type.base (base.type.type_base tZ) => fun r => r
        | type.base (base.type.type_base tZ * base.type.type_base tZ)%etype => fst
        | _ => fun _ => error
        end.
      Definition new_cc_to_name (old_cc_to_name : CC.code -> name) (i : instruction)
                 {d} (new_r : var d) (x : CC.code) : name :=
        if (in_dec CC.code_dec x (writes_conditions i))
        then new_write new_r
        else old_cc_to_name x.

      Inductive valid_ident
        : forall {s d},
          (CC.code -> name) -> (* last variables that wrote to each flag *)
          (var d -> CC.code -> name) -> (* new last variables that wrote to each flag *)
          ident.ident (s->d) -> @cexpr var s -> Prop :=
      | valid_fancy_add :
          forall r imm x y,
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r (ADD imm)) (ident.fancy_add 256 imm) (x, y)%expr_pat
      | valid_fancy_addc :
          forall r imm c x y,
            (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.C) ->
            valid_carry c ->
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r (ADDC imm)) (ident.fancy_addc 256 imm) (c, x, y)%expr_pat
      | valid_fancy_sub :
          forall r imm x y,
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r (SUB imm)) (ident.fancy_sub 256 imm) (x, y)%expr_pat
      | valid_fancy_subb :
          forall r imm c x y,
            (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.C) ->
            valid_carry c ->
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r (SUBC imm)) (ident.fancy_subb 256 imm) (c, x, y)%expr_pat
      | valid_fancy_mulll :
          forall r x y,
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r MUL128LL) (ident.fancy_mulll 256) (x, y)%expr_pat
      | valid_fancy_mullh :
          forall r x y,
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r MUL128LU) (ident.fancy_mullh 256) (x, y)%expr_pat
      | valid_fancy_mulhl :
          forall r x y,
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r MUL128UL) (ident.fancy_mulhl 256) (x, y)%expr_pat
      | valid_fancy_mulhh :
          forall r x y,
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r MUL128UU) (ident.fancy_mulhh 256) (x, y)%expr_pat
      | valid_fancy_rshi :
          forall r imm x y,
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r (RSHI imm)) (ident.fancy_rshi 256 imm) (x, y)%expr_pat
      | valid_fancy_selc :
          forall r c x y,
            (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.C) ->
            valid_carry c ->
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r SELC) ident.fancy_selc (c, x, y)%expr_pat
      | valid_fancy_selm :
          forall r c x y,
            (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.M) ->
            valid_scalar c ->
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r SELM) (ident.fancy_selm 256) (c, x, y)%expr_pat
      | valid_fancy_sell :
          forall r c x y,
            (of_prefancy_scalar (t:= base.type.type_base tZ) c = r CC.L) ->
            valid_scalar c ->
            valid_scalar x ->
            valid_scalar y ->
            valid_ident r (new_cc_to_name r SELL) ident.fancy_sell (c, x, y)%expr_pat
      | valid_fancy_addm :
          forall r x y m,
            valid_scalar x ->
            valid_scalar y ->
            valid_scalar m ->
            valid_ident r (new_cc_to_name r ADDM) ident.fancy_addm (x, y, m)%expr_pat
      .

      Inductive valid_expr
        : forall t,
          (CC.code -> name) -> (* the last variables that wrote to each flag *)
          @cexpr var t -> Prop :=
      | valid_LetInZ_loosen :
          forall s d idc r rf x f u ia,
            valid_ident r rf idc x ->
            0 < u < wordmax ->
            (forall x, valid_expr _ (rf x) (f x)) ->
            of_prefancy_ident idc x = Some ia ->
            (forall cc ctx,
                (forall n v, consts v = Some n -> ctx n = v) ->
                (forall n, ctx n mod wordmax = ctx n) ->
                let args := Tuple.map ctx (projT2 ia) in
                spec (projT1 ia) args cc mod wordmax = spec (projT1 ia) args cc mod (u+1)) ->
            valid_expr _ r (LetInAppIdentZ s d r[0~>u] (expr.Ident idc) x f)
      | valid_LetInZ :
          forall s d idc r rf x f,
            valid_ident r rf idc x ->
            (forall x, valid_expr _ (rf x) (f x)) ->
            valid_expr _ r (LetInAppIdentZ s d uint256 (expr.Ident idc) x f)
      | valid_LetInZZ :
          forall s d idc r rf x f,
            valid_ident r rf idc x ->
            (forall x : var (type.base (base.type.type_base tZ * base.type.type_base tZ)%etype),
                fst x = snd x ->
                valid_expr _ (rf x) (f x)) ->
            valid_expr _ r (LetInAppIdentZZ s d (uint256, r[0~>1]) (expr.Ident idc) x f)
      | valid_Ret :
          forall r x,
            valid_scalar x ->
            valid_expr _ r x
      .

      Lemma cast_oor_id v u : 0 <= v <= u -> cast_oor r[0 ~> u] v = v.
      Proof. intros; cbv [cast_oor upper]. apply Z.mod_small; omega. Qed.
      Lemma cast_oor_mod v u : 0 <= u -> cast_oor r[0 ~> u] v mod (u+1) = v mod (u+1).
      Proof. intros; cbv [cast_oor upper]. apply Z.mod_mod; omega. Qed.

      Lemma wordmax_nonneg : 0 <= wordmax.
      Proof. cbv; congruence. Qed.

      Lemma of_prefancy_scalar_correct'
            (e1 : @cexpr var (type.base (base.type.type_base tZ)))
            (e2 : cexpr (type.base (base.type.type_base tZ)))
            G (ctx : name -> Z) (cctx : name -> bool) :
        valid_scalar e1 ->
        LanguageWf.Compilers.expr.wf G e1 e2 ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall v1 v2, In (existZ (v1, v2)) G -> ctx v1 = v2) -> (* implied by above *)
        (forall n, ctx n mod wordmax = ctx n) ->
        (forall v1 v2, In (existZZ (v1, v2)) G -> ctx (fst v1) = fst v2) ->
        (forall v1 v2, In (existZZ (v1, v2)) G -> Z.b2z (cctx (snd v1)) = snd v2) ->
        ctx (of_prefancy_scalar e1) = cinterp e2.
      Proof.
        inversion 1; inversion 1;
          cbv [interp_if_Z option_map];
          cbn [of_prefancy_scalar interp_base]; intros.
        all: repeat first [
                      progress subst
                    | exfalso; assumption
                    | progress inversion_sigma
                    | progress inversion_option
                    | progress Prod.inversion_prod
                    | progress LanguageInversion.Compilers.expr.inversion_expr
                    | progress LanguageInversion.Compilers.expr.invert_subst
                    | progress LanguageWf.Compilers.expr.inversion_wf_one_constr
                    | progress LanguageInversion.Compilers.expr.invert_match
                    | progress destruct_head'_sig
                    | progress destruct_head'_and
                    | progress destruct_head'_or
                    | progress Z.ltb_to_lt
                    | progress cbv [id]
                    | progress cbn [fst snd upper lower fst snd eq_rect projT1 projT2 expr.interp ident.interp ident.gen_interp interp_base] in *
                    | progress HProp.eliminate_hprop_eq
                    | progress break_innermost_match_hyps
                    | progress break_innermost_match
                    | match goal with H : context [_ = cinterp _] |- context [cinterp _] =>
                                      rewrite <-H by eauto; try reflexivity end
                    | solve [eauto using (f_equal2 pair), cast_oor_id, wordmax_nonneg]
                    | rewrite LanguageWf.Compilers.ident.cast_out_of_bounds_simple_0_mod
                    | rewrite Z.mod_mod by lia
                    | rewrite cast_oor_mod by (cbv; congruence)
                    | lia
                    | match goal with
                        H : context[ ?x mod _ = ?x ] |- _ => rewrite H end
                    | match goal with
                      | H : context [In _ _ -> _ = _] |- _ => erewrite H by eauto end
                    | match goal with
                      | H : forall v1 v2, In _ _ -> ?ctx v1 = v2 |- ?x = ?x mod ?m =>
                        replace m with wordmax by ring; erewrite <-(H _ x)  by eauto; solve [eauto]
                      end
                    | match goal with
                      | H : forall v1 v2, In _ _ -> ?ctx (fst v1) = fst v2,
                        H' : In (existZZ (_,(?x,?y))) _ |- ?x = ?x mod ?m =>
                      replace m with wordmax by ring;
                      specialize (H _ _ H'); cbn [fst] in H; rewrite <-H; solve [eauto] end
                    ].
      Qed.

      Lemma of_prefancy_scalar_correct
            (e1 : @cexpr var (type.base (base.type.type_base tZ)))
            (e2 : cexpr (type.base (base.type.type_base tZ)))
            G (ctx : name -> Z) cc :
        valid_scalar e1 ->
        LanguageWf.Compilers.expr.wf G e1 e2 ->
        (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cc v1 = v2) ->
        (forall n, ctx n mod wordmax = ctx n) ->
        ctx (of_prefancy_scalar e1) = cinterp e2.
      Proof.
        intros; match goal with H : context [interp_base _ _ _ = _] |- _ =>
                                pose proof (H (base.type.type_base base.type.Z));
                                  pose proof (H (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype); cbn [interp_base] in *
                end.
        eapply of_prefancy_scalar_correct'; eauto;
          match goal with
          | H : forall _ _, In _ _ -> (_, _) = _ |- _ =>
            let v1 := fresh "v" in
            let v2 := fresh "v" in
            intros v1 v2 ?; rewrite <-(H v1 v2) by auto
          end; reflexivity.
      Qed.

      Lemma of_prefancy_ident_Some {s d} idc r rf x:
        @valid_ident (type.base s) (type.base d) r rf idc x ->
        of_prefancy_ident idc x <> None.
      Proof.
        induction s; inversion 1; intros;
          repeat first [
                   progress subst
                 | progress inversion_sigma
                 | progress cbn [eq_rect projT1 projT2 of_prefancy_ident invert_expr.invert_Ident option_map] in *
                 | progress Z.ltb_to_lt
                 | progress break_innermost_match
                 | progress LanguageInversion.Compilers.type.inversion_type
                 | progress LanguageInversion.Compilers.expr.inversion_expr
                 | congruence
                 ].
      Qed.

      Ltac name_eqb_to_eq :=
        repeat match goal with
               | H : name_eqb _ _ = true |- _ => apply name_eqb_eq in H
               | H : name_eqb _ _ = false |- _ => apply name_eqb_neq in H
               end.
      Ltac inversion_of_prefancy_ident :=
          match goal with
          | H : of_prefancy_ident _ _ = None |- _ =>
            eapply of_prefancy_ident_Some in H;
            [ contradiction | eassumption]
          end.

      Local Ltac hammer :=
        repeat first [
                      progress subst
                    | progress inversion_sigma
                    | progress inversion_option
                    | progress inversion_of_prefancy_ident
                    | progress Prod.inversion_prod
                    | progress cbv [id]
                    | progress cbn [eq_rect projT1 projT2 expr.interp ident.interp ident.gen_interp interp_base interp invert_expr.invert_Ident interp_if_Z option_map] in *
                    | progress LanguageInversion.Compilers.type_beq_to_eq
                    | progress name_eqb_to_eq
                    | progress LanguageInversion.Compilers.rewrite_type_transport_correct
                    | progress HProp.eliminate_hprop_eq
                    | progress break_innermost_match_hyps
                    | progress break_innermost_match
                    | progress LanguageInversion.Compilers.type.inversion_type
                    | progress LanguageInversion.Compilers.expr.inversion_expr
                    | solve [auto]
                    | contradiction
               ].
      Ltac prove_Ret :=
        repeat match goal with
               | H : valid_scalar (expr.LetIn _ _) |- _ =>
                 inversion H
               | _ => progress cbn [id of_prefancy of_prefancy_step of_prefancy_scalar]
               | _ => progress hammer
               | H : valid_scalar (expr.Ident _) |- _ =>
                 inversion H; clear H
               | |- _ = cinterp ?f (cinterp ?x) =>
                 transitivity
                   (cinterp (f @ x)%expr);
                 [ | reflexivity ];
                 erewrite <-of_prefancy_scalar_correct by (try reflexivity; eassumption)
               end.

      Lemma cast_mod u v :
        0 <= u ->
        ident.cast cast_oor r[0~>u] v = v mod (u + 1).
      Proof.
        intros.
        rewrite LanguageWf.Compilers.ident.cast_out_of_bounds_simple_0_mod by auto using cast_oor_id.
        cbv [cast_oor upper]. apply Z.mod_mod. omega.
      Qed.

      Lemma cc_spec_c v :
        Z.b2z (cc_spec CC.C v) = (v / wordmax) mod 2.
      Proof. cbv [cc_spec]; apply Z.testbit_spec'. omega. Qed.

      Lemma cc_m_zselect x z nz :
        x mod wordmax = x ->
        (if (if cc_spec CC.M x then 1 else 0) =? 1 then nz else z) =
        Z.zselect (x >> 255) z nz.
      Proof.
        intro Hx_small.
        transitivity (if (Z.b2z (cc_spec CC.M x) =? 1) then nz else z); [ reflexivity | ].
        cbv [cc_spec Z.zselect].
        rewrite Z.testbit_spec', Z.shiftr_div_pow2 by omega. rewrite <-Hx_small.
        rewrite Div.Z.div_between_0_if by (try replace (2 * (2 ^ 255)) with wordmax by reflexivity;
                                           auto with zarith).
        break_innermost_match; Z.ltb_to_lt; try rewrite Z.mod_small in * by omega; congruence.
      Qed.

      Lemma cc_l_zselect x z nz :
        (if (if cc_spec CC.L x then 1 else 0) =? 1 then nz else z) = Z.zselect (x &' 1) z nz.
      Proof.
        transitivity (if (Z.b2z (cc_spec CC.L x) =? 1) then nz else z); [ reflexivity | ].
        transitivity (Z.zselect (x &' Z.ones 1) z nz); [ | reflexivity ].
        cbv [cc_spec Z.zselect]. rewrite Z.testbit_spec', Z.land_ones by omega.
        autorewrite with zsimplify_fast. rewrite Zmod_even.
        break_innermost_match; Z.ltb_to_lt; congruence.
      Qed.

      Lemma b2z_range b : 0<= Z.b2z b < 2.
      Proof. cbv [Z.b2z]. break_match; lia. Qed.


      Lemma of_prefancy_scalar_carry
            (c : @cexpr var (type.base (base.type.type_base tZ)))
            (e : cexpr (type.base (base.type.type_base tZ)))
            G (ctx : name -> Z) cctx :
        valid_carry c ->
        LanguageWf.Compilers.expr.wf G c e ->
        (forall n0, consts 0 = Some n0 -> cctx n0 = false) ->
        (forall n1, consts 1 = Some n1 -> cctx n1 = true) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        Z.b2z (cctx (of_prefancy_scalar c)) = cinterp e.
      Proof.
        inversion 1; inversion 1; intros; hammer; cbn;
        repeat match goal with
               | H : context [ _ = false] |- Z.b2z _ = 0 => rewrite H; reflexivity
               | H : context [ _ = true] |- Z.b2z _ = 1 => rewrite H; reflexivity
               | _ => progress LanguageWf.Compilers.expr.inversion_wf_one_constr
               | _ => progress cbn [fst snd]
               | _ => progress destruct_head'_sig
               | _ => progress destruct_head'_and
               | _ => progress hammer
               | _ => progress LanguageInversion.Compilers.expr.invert_subst
               | _ => rewrite cast_mod by (cbv; congruence)
               | _ => rewrite Z.mod_mod by omega
               | _ => rewrite Z.mod_small by apply b2z_range
               | H : (forall _ _ _, In _ _ -> interp_base _ _ _ = _),
                     H' : In (existZZ (?v, _)) _ |- context [cctx (snd ?v)] =>
                 specialize (H _ _ _ H'); cbn in H
               end.
      Qed.

      Ltac simplify_ident :=
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbn [fst snd of_prefancy_ident] in *
                 | _ => progress LanguageWf.Compilers.expr.inversion_wf_one_constr
                 | H : { _ | _ } |- _ => destruct H
                 | H : _ /\ _ |- _ => destruct H
                 | H : upper _ = _ |- _ => rewrite H
                 | _ => rewrite cc_spec_c by auto
                 | _ => rewrite cast_mod by (cbv; congruence)
                 | H : _ |- _ =>
                   apply LanguageInversion.Compilers.expr.invert_Ident_Some in H
                 | H : _ |- _ =>
                   apply LanguageInversion.Compilers.expr.invert_App_Some in H
                 | H : ?P, H' : ?P |- _ => clear H'
                 | _ => progress hammer
                 end.

      (* TODO: zero flag is a little tricky, since the value
        depends both on the stored variable and the carry if there
        is one. For now, since Barrett doesn't use it, we're just
        pretending it doesn't exist. *)
      Definition cc_good cc cctx ctx r :=
          CC.cc_c cc = cctx (r CC.C) /\
          CC.cc_m cc = cc_spec CC.M (ctx (r CC.M)) /\
          CC.cc_l cc = cc_spec CC.L (ctx (r CC.L)) /\
          (forall n0 : name, consts 0 = Some n0 -> cctx n0 = false) /\
          (forall n1 : name, consts 1 = Some n1 -> cctx n1 = true).

      Lemma of_prefancy_identZ_loosen_correct {s} idc:
        forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f u,
          @valid_ident (type.base s) (type_base tZ) r rf idc x ->
          LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
          LanguageWf.Compilers.expr.wf G #(ident.Z_cast r[0~>u]) f ->
          0 < u < wordmax ->
          cc_good cc cctx ctx r ->
          (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
          (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
          (forall n, ctx n mod wordmax = ctx n) ->
          of_prefancy_ident idc x = Some i ->
          (spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod (u+1)) ->
          spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = (cinterp f (cinterp x2)).
      Proof.
        Time
          inversion 1; inversion 1; cbn [of_prefancy_ident]; hammer; (simplify_ident; [ ]). (* TODO : suuuuuper slow *)
        all:
          rewrite cast_mod by omega;
          match goal with
                   | H : context [spec _ _ _ mod _ = _] |- ?x mod wordmax = _ mod ?m =>
                     replace (x mod wordmax) with (x mod m) by auto
          end.
        all:  cbn - [Z.shiftl wordmax]; cbv [cc_good] in *; destruct_head'_and;
            repeat match goal with
                   | H : CC.cc_c _ = _ |- _ => rewrite H
                   | H : CC.cc_m _ = _ |- _ => rewrite H
                   | H : CC.cc_l _ = _ |- _ => rewrite H
                   | H : CC.cc_z _ = _ |- _ => rewrite H
                   | H: of_prefancy_scalar _ = ?r ?c |- _ => rewrite <-H
                   | _ => progress rewrite ?cc_m_zselect, ?cc_l_zselect by auto
                   | _ => progress rewrite ?Z.add_modulo_correct, ?Z.geb_leb by auto
                   | |- context [cinterp ?x] =>
                     erewrite of_prefancy_scalar_correct with (e2:=x) by eauto
                   | |- context [cinterp ?x] =>
                     erewrite <-of_prefancy_scalar_carry with (e:=x) by eauto
                   | |- context [if _ (of_prefancy_scalar _) then _ else _ ] =>
                     cbv [Z.zselect Z.b2z];
                       break_innermost_match; Z.ltb_to_lt; try reflexivity;
                         congruence
                   end; try reflexivity.

        { (* RSHI case *)
          cbv [Z.rshi].
          rewrite Z.land_ones, Z.shiftl_mul_pow2 by (cbv; congruence).
          change (2 ^ Z.log2 wordmax) with wordmax.
          break_innermost_match; try congruence; [ ]. autorewrite with zsimplify_fast.
          repeat (f_equal; try ring). }
      Qed.
      Lemma of_prefancy_identZ_correct {s} idc:
        forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
          @valid_ident (type.base s) (type_base tZ) r rf idc x ->
          LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
          LanguageWf.Compilers.expr.wf G #(ident.Z_cast uint256) f ->
          cc_good cc cctx ctx r ->
          (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
          (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
          (forall n, ctx n mod wordmax = ctx n) ->
          of_prefancy_ident idc x = Some i ->
          spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = (cinterp f (cinterp x2)).
      Proof.
        intros; eapply of_prefancy_identZ_loosen_correct; try eassumption; [ | ].
        { cbn; omega. } { intros; f_equal; ring. }
      Qed.
      Lemma of_prefancy_identZZ_correct' {s} idc:
        forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
          @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
          LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
          LanguageWf.Compilers.expr.wf G #(ident.Z_cast2 (uint256, r[0~>1])) f ->
          cc_good cc cctx ctx r ->
          (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
          (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
          (forall n, ctx n mod wordmax = ctx n) ->
          of_prefancy_ident idc x = Some i ->
          spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = fst (cinterp f (cinterp x2)) /\
          Z.b2z (cc_spec CC.C (spec (projT1 i) (Tuple.map ctx (projT2 i)) cc)) = snd (cinterp f (cinterp x2)).
      Proof.
        inversion 1; inversion 1; cbn [of_prefancy_ident]; intros; hammer; (simplify_ident; [ ]);
          cbn - [Z.div Z.modulo]; cbv [Z.sub_with_borrow Z.add_with_carry];
            cbv [cc_good] in *; destruct_head'_and; autorewrite with zsimplify_fast.
        all: repeat match goal with
                 | H : CC.cc_c _ = _ |- _ => rewrite H
                 | H: of_prefancy_scalar _ = ?r ?c |- _ => rewrite <-H
                 | H : LanguageWf.Compilers.expr.wf _ ?x ?e |- context [cinterp ?e] =>
                   erewrite <-of_prefancy_scalar_correct with (e1:=x) (e2:=e) by eauto
                 | H : LanguageWf.Compilers.expr.wf _ ?x ?e2 |- context [cinterp ?e2] =>
                   erewrite <-of_prefancy_scalar_carry with (c:=x) (e:=e2) by eauto
                    end.
        all: match goal with |- context [(?x << ?n) mod ?m] =>
                             pose proof (Z.mod_pos_bound (x << n) m ltac:(omega)) end.
        all:repeat match goal with
                 | |- context [if _ (of_prefancy_scalar _) then _ else _ ] =>
                   cbv [Z.zselect Z.b2z]; break_innermost_match; Z.ltb_to_lt; try congruence; [ | ]
                 | _ => rewrite Z.add_opp_r
                 | _ => rewrite Div.Z.div_sub_small by auto with zarith
                 | H : forall n, ?ctx n mod wordmax = ?ctx n |- context [?ctx ?m - _] => rewrite <-(H m)
                 |  |- ((?x - ?y - ?c) / _) mod _ = - ((- ?c + ?x - ?y) / _) mod _ =>
                    replace (-c + x - y) with (x - (y + c)) by ring; replace (x - y - c) with (x - (y + c)) by ring
                 | _ => split
                 | _ => try apply (f_equal2 Z.modulo); try apply (f_equal2 Z.div); ring
                 | _ => break_innermost_match; reflexivity
                 end.
      Qed.
      Lemma of_prefancy_identZZ_correct {s} idc:
        forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
          @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
          LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
          LanguageWf.Compilers.expr.wf G #(ident.Z_cast2 (uint256, r[0~>1])) f ->
          cc_good cc cctx ctx r ->
          (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
          (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
          (forall n, ctx n mod wordmax = ctx n) ->
          of_prefancy_ident idc x = Some i ->
          spec (projT1 i) (Tuple.map ctx (projT2 i)) cc mod wordmax = fst (cinterp f (cinterp x2)).
      Proof. apply of_prefancy_identZZ_correct'. Qed.
      Lemma of_prefancy_identZZ_correct_carry {s} idc:
        forall (x : @cexpr var _) i ctx G cc cctx x2 r rf f,
          @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
          LanguageWf.Compilers.expr.wf G (#idc @ x)%expr_pat x2 ->
          LanguageWf.Compilers.expr.wf G #(ident.Z_cast2 (uint256, r[0~>1])) f ->
          cc_good cc cctx ctx r ->
          (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
          (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
          (forall n, ctx n mod wordmax = ctx n) ->
          of_prefancy_ident idc x = Some i ->
          Z.b2z (cc_spec CC.C (spec (projT1 i) (Tuple.map ctx (projT2 i)) cc)) = snd (cinterp f (cinterp x2)).
      Proof. apply of_prefancy_identZZ_correct'. Qed.

      Lemma identZZ_writes {s} idc r rf x:
        @valid_ident (type.base s) (type_base (tZ * tZ)) r rf idc x ->
        forall i, of_prefancy_ident idc x = Some i ->
                    In CC.C (writes_conditions (projT1 i)).
      Proof.
        inversion 1;
          repeat match goal with
                 | _ => progress intros
                 | _ => progress cbn [of_prefancy_ident writes_conditions ADD ADDC SUB SUBC In] in *
                 | _ => progress hammer; Z.ltb_to_lt
                 | _ => congruence
                 end.
      Qed.

      (* Common side conditions for cases in of_prefancy_correct *)
      Local Ltac side_cond :=
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [In fst snd] in *
               | H : _ \/ _ |- _ => destruct H
               | [H : forall _ _, In _ ?l -> _, H' : In _ ?l |- _] =>
                 let H'' := fresh in
                 pose proof H'; apply H in H''; clear H
               | H : name_lt ?n ?n |- _ =>
                 specialize (name_lt_irr n); contradiction
               | _ => progress hammer
               | _ => solve [eauto]
               end.

      Lemma interp_base_helper G next_name ctx cctx :
        (forall n v2, In (existZ (n, v2)) G -> name_lt n next_name) ->
        (forall n v2, In (existZZ (n, v2)) G -> name_lt (fst n) next_name) ->
        (forall n v2, In (existZZ (n, v2)) G -> fst n = snd n) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
        (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G ->
                         t = base.type.type_base tZ
                         \/ t = (base.type.type_base tZ * base.type.type_base tZ)%etype) ->
        forall t v1 v2 x xc,
          In (existT (fun t : type => (var t * type.interp base.interp t)%type) (type.base t) (v1, v2)%zrange)
             ((existZ (next_name, x)%zrange) :: G) ->
          interp_base (fun n : name => if name_eqb n next_name then x else ctx n)
                      (fun n : name => if name_eqb n next_name then xc else cctx n) v1 = v2.
      Proof.
        intros.
        repeat match goal with
               | H: In _ (_ :: _) |- _ => cbn [In] in H; destruct H; [ solve [side_cond] | ]
               | H : (forall t _ _, In _ ?G -> (t = _ \/ t = _)), H' : In _ ?G |- _ =>
                 destruct (H _ _ _ H'); subst t
               | H : forall _ _ _, In _ ?G -> interp_base _ _ _ = _, H' : In _ G |- _ => specialize (H _ _ _ H')
        end; side_cond.
      Qed.

      Lemma name_eqb_refl n : name_eqb n n = true.
      Proof. case_eq (name_eqb n n); intros; name_eqb_to_eq; auto. Qed.

      Lemma valid_ident_new_cc_to_name s d r rf idc x y n :
        @valid_ident (type.base s) (type.base d) r rf idc x ->
        of_prefancy_ident idc x = Some y ->
        rf n = new_cc_to_name r (projT1 y) n.
      Proof. inversion 1; intros; hammer; simplify_ident. Qed.

      Lemma new_cc_to_name_Z_cases r i n x :
        new_cc_to_name (d:=base.type.type_base tZ) r i n x
        = if in_dec CC.code_dec x (writes_conditions i)
          then n else r x.
      Proof. reflexivity. Qed.
      Lemma new_cc_to_name_ZZ_cases r i n x :
        new_cc_to_name (d:=base.type.type_base tZ * base.type.type_base tZ) r i n x
        = if in_dec CC.code_dec x (writes_conditions i)
          then fst n else r x.
      Proof. reflexivity. Qed.

      Lemma cc_good_helper cc cctx ctx r i x next_name :
        (forall c, name_lt (r c) next_name) ->
        (forall n v, consts v = Some n -> name_lt n next_name) ->
        cc_good cc cctx ctx r ->
        cc_good (CC.update (writes_conditions i) x cc_spec cc)
                (fun n : name =>
                   if name_eqb n next_name
                   then CC.cc_c (CC.update (writes_conditions i) x cc_spec cc)
                   else cctx n)
                (fun n : name => if name_eqb n next_name then x mod wordmax else ctx n)
                (new_cc_to_name (d:=base.type.type_base tZ) r i next_name).
      Proof.
        cbv [cc_good]; intros; destruct_head'_and.
        rewrite !new_cc_to_name_Z_cases.
        cbv [CC.update CC.cc_c CC.cc_m CC.cc_l CC.cc_z].
        repeat match goal with
               | _ => split; intros
               | _ => progress hammer
               | H : forall c, name_lt (r c) (r ?c2) |- _ => specialize (H c2)
               | H : (forall n v, consts v = Some n -> name_lt _ _),
                     H' : consts _ = Some _ |- _ => specialize (H _ _ H')
               | H : name_lt ?n ?n |- _ => apply name_lt_irr in H; contradiction
               | _ => cbv [cc_spec]; rewrite Z.mod_pow2_bits_low by omega
               | _ => congruence
               end.
      Qed.

      Lemma of_prefancy_correct
            {t} (e1 : @cexpr var t) (e2 : @cexpr _ t) r :
        valid_expr _ r e1 ->
        forall G,
        LanguageWf.Compilers.expr.wf G e1 e2 ->
        forall ctx cc cctx,
          cc_good cc cctx ctx r ->
          (forall n v, consts v = Some n -> In (existZ (n, v)) G) ->
          (forall n v2, In (existZZ (n, v2)) G -> fst n = snd n) ->
          (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G -> interp_base ctx cctx v1 = v2) ->
          (forall t v1 v2, In (existT _ (type.base t) (v1, v2)) G ->
                           t = base.type.type_base tZ
                           \/ t = (base.type.type_base tZ * base.type.type_base tZ)%etype) ->
          (forall n, ctx n mod wordmax = ctx n) ->
          forall next_name result,
            (forall c : CC.code, name_lt (r c) next_name) ->
            (forall n v2, In (existZ (n, v2)) G -> name_lt n next_name) ->
            (forall n v2, In (existZZ (n, v2)) G -> name_lt (fst n) next_name) ->
            (interp_if_Z e2 = Some result) ->
            interp (@of_prefancy next_name t e1) cc ctx = result.
      Proof.
        induction 1; inversion 1; cbv [interp_if_Z];
          cbn [of_prefancy of_prefancy_step]; intros;
            match goal with H : context [interp_base _ _ _ = _] |- _ =>
                            pose proof (H (base.type.type_base base.type.Z)) end;
            try solve [prove_Ret]; [ | | ]; hammer;
              match goal with
              | H : context [interp (of_prefancy _ _) _ _ = _]
                |- interp _ ?cc' ?ctx' = _ =>
                match goal with
                | _ : context [LetInAppIdentZ _ _ _ _ _ _] |-  _=>
                  erewrite H with
                      (G := (existZ (next_name, ctx' next_name)) :: G)
                      (e2 := _ (ctx' next_name))
                      (cctx := (fun n => if name_eqb n next_name then CC.cc_c cc' else cctx n))
                | _ : context [LetInAppIdentZZ _ _ _ _ _ _] |-  _=>
                  erewrite H with
                      (G := (existZZ ((next_name, next_name), (ctx' next_name, Z.b2z (CC.cc_c cc')))) :: G)
                      (e2 := _ (ctx' next_name, Z.b2z (CC.cc_c cc')))
                      (cctx := (fun n => if name_eqb n next_name then CC.cc_c cc' else cctx n))
                end
              end;
              repeat match goal with
                     | _ => progress intros
                     | _ => rewrite name_eqb_refl in *
                     | _ => rewrite Z.testbit_spec' in *
                     | _ =>  erewrite valid_ident_new_cc_to_name by eassumption
                     | _ => rewrite new_cc_to_name_Z_cases
                     | _ => rewrite new_cc_to_name_ZZ_cases
                     | _ => solve [intros; eapply interp_base_helper; side_cond]
                     | _ => solve [intros; apply cc_good_helper; eauto]
                     | _ => reflexivity
                     | _ => solve [eauto using Z.mod_small, b2z_range]
                     | _ => progress autorewrite with zsimplify_fast
                     | _ => progress side_cond
                     end; [ | | ].
        { cbn - [cc_spec]; cbv [id]; cbn - [cc_spec].
          inversion wf_x; hammer.
          erewrite of_prefancy_identZ_loosen_correct by eauto.
          reflexivity. }
        { cbn - [cc_spec]; cbv [id]; cbn - [cc_spec].
          inversion wf_x; hammer.
          erewrite of_prefancy_identZ_correct by eassumption.
          reflexivity. }
        { cbn - [cc_spec]; cbv [id]; cbn - [cc_spec].
          match goal with H : _ |- _ => pose proof H; eapply identZZ_writes in H; [ | eassumption] end.
          inversion wf_x; hammer.
          erewrite of_prefancy_identZZ_correct by eassumption.
          erewrite of_prefancy_identZZ_correct_carry by eassumption.
          rewrite <-surjective_pairing. reflexivity. }
      Qed.
    End Proofs.
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

  Definition of_Expr {t} next_name (consts : Z -> option positive)
             (e : expr.Expr t)
             (x : type.for_each_lhs_of_arrow (var positive) t)
    : positive -> @expr positive :=
    fun error =>
      @of_prefancy positive Pos.succ error consts next_name _ (invert_expr.smart_App_curried (e _) x).

  Section Proofs.

    Section with_name.
        Context (name : Type) (name_eqb : name -> name -> bool)
                (name_succ : name -> name) (error : name)
                (consts : Z -> option name) (wordmax : Z)
                (cc_spec : CC.code -> Z -> bool).


        Context (reg : Type) (error_reg : reg) (reg_eqb : reg -> reg -> bool).
        Context (reg_eqb_refl : forall r, reg_eqb r r = true).

        Inductive error_free : @expr reg -> Prop :=
        | error_free_Ret : forall r, r <> error_reg -> error_free (Ret r)
        | error_free_Instr : forall i rd args cont,
            error_free cont ->
            error_free (Instr i rd args cont)
        .

        Lemma allocate_correct e :
          forall cc ctx reg_list name_to_reg,
            error_free (allocate reg name name_eqb error_reg e reg_list name_to_reg) ->
            interp reg_eqb wordmax cc_spec (allocate reg name name_eqb error_reg e reg_list name_to_reg) cc ctx
            = interp name_eqb wordmax cc_spec e cc (fun n : name => ctx (name_to_reg n)).
        Proof.
          induction e; destruct reg_list; inversion 1; intros;
            try reflexivity; try congruence; [ ].
          cbn. rewrite IHe by auto.
          rewrite Tuple.map_map.
          (*
           Need to prove that contexts are equivalent and swapping contexts is OK
          *)
        (*
             TODO : either prove this lemma or devise a good way to
             prove case-by-case that the output of allocate is
             equivalent to the input.
         *)
        Admitted.
    End with_name.

    Fixpoint var_pairs {t var1 var2}
      : type.for_each_lhs_of_arrow var1 t
        -> type.for_each_lhs_of_arrow var2 t
        -> list {t : Compilers.type base.type.type & (var1 t * var2 t)%type } :=
      match t as t0 return
            (type.for_each_lhs_of_arrow var1 t0
             -> type.for_each_lhs_of_arrow var2 t0 -> _) with
      | type.base _ => fun _ _ => nil
      | (s -> d)%ptype =>
        fun x1 x2 =>
          existT _ _ (fst x1, fst x2) :: var_pairs (snd x1) (snd x2)
      end.

    Local Notation existZ := (existT _  (type.base (base.type.type_base base.type.Z))).
    Local Notation existZZ := (existT _  (type.base (base.type.type_base base.type.Z * base.type.type_base base.type.Z)%etype)).

    Fixpoint make_ctx (var_list : list (positive * Z)) : positive -> Z :=
      match var_list with
      | [] => fun _ => 0
      | (n, v) :: l' => fun m => if (m =? n)%positive then v else make_ctx l' m
      end.

    Definition make_pairs :
      list (positive * Z) -> list {t : Compilers.type base.type.type & (var positive t * @type.interp base.type base.interp t)%type } := map (fun x => existZ x).

    Fixpoint make_consts (consts_list : list (positive * Z)) : Z -> option positive :=
      match consts_list with
      | [] => fun _ => None
      | (n, v) :: l' => fun x => if x =? v then Some n else make_consts l' x
      end.

    Local Ltac ez :=
      repeat match goal with
             | _ => progress intros
             | _ => progress subst
             | H : _ \/ _ |- _ => destruct H
             | H : _ |- _ => rewrite Pos.eqb_eq in H
             | H : _ |- _ => rewrite Pos.eqb_neq in H
             | _ => progress break_innermost_match
             | _ => progress break_match_hyps
             | _ => progress inversion_sigma
             | _ => progress inversion_option
             | _ => progress Prod.inversion_prod
             | _ => progress HProp.eliminate_hprop_eq
             | _ => progress Z.ltb_to_lt
             | _ => reflexivity
             | _ => congruence
             | _ => solve [eauto]
             end.


    Lemma make_consts_ok consts_list n v :
      make_consts consts_list v = Some n ->
      In (existZ (n, v)%zrange) (make_pairs consts_list).
    Proof.
      cbv [make_pairs]; induction consts_list as [|[ ? ? ] ?]; cbn; ez.
    Qed.

    Lemma make_pairs_ok consts_list:
      forall v1 v2,
        In (existZ (v1, v2)%zrange) (make_pairs consts_list) ->
        In (v1, v2) consts_list.
    Proof.
      cbv [make_pairs]. induction consts_list as [| [ n v ] ? ]; cbn; [ tauto | ]. ez.
    Qed.
    Lemma make_ctx_ok consts_list:
      (forall n v1 v2, In (n, v1) consts_list ->
                       In (n, v2) consts_list -> v1 = v2) ->
      forall n v,
        In (n, v) consts_list ->
      make_ctx consts_list n = v.
    Proof.
      induction consts_list as [| [ n v ] ? ]; cbn; [ tauto | ].
      repeat match goal with
             | _ => progress cbn [eq_rect fst snd] in *
             | _ => progress ez
             end.
    Qed.

    Lemma make_ctx_cases consts_list n :
      make_ctx consts_list n = 0 \/
      In (n, make_ctx consts_list n) consts_list.
    Proof. induction consts_list; cbn; ez. Qed.

    Lemma only_integers consts_list t v1 v2 :
      In (existT (fun t : type => (var positive t * type.interp base.interp t)%type) (type.base t)
                 (v1, v2)%zrange) (make_pairs consts_list) ->
      t = base.type.type_base base.type.Z.
    Proof.
      induction consts_list; cbn; [ tauto | ].
      destruct 1; congruence || tauto.
    Qed.

    Lemma no_pairs consts_list v1 v2 :
      In (existZZ (v1, v2)%zrange) (make_pairs consts_list) -> False.
    Proof. intro H; apply only_integers in H. congruence. Qed.


    Definition make_cc last_wrote ctx carry_flag : CC.state :=
      {| CC.cc_c := carry_flag;
         CC.cc_m := cc_spec CC.M (ctx (last_wrote CC.M));
         CC.cc_l := cc_spec CC.L (ctx (last_wrote CC.L));
         CC.cc_z := cc_spec CC.Z (ctx (last_wrote CC.Z)
                                  + (if (last_wrote CC.C =? last_wrote CC.Z)%positive
                                     then wordmax * Z.b2z carry_flag else 0));
      |}.


    Hint Resolve Pos.lt_trans Pos.lt_irrefl Pos.lt_succ_diag_r Pos.eqb_refl.
    Hint Resolve in_or_app.
    Hint Resolve make_consts_ok make_pairs_ok make_ctx_ok no_pairs.
    (* TODO : probably not all of these preconditions are necessary -- prune them sometime *)
    Lemma of_Expr_correct next_name consts_list arg_list error
          (carry_flag : bool)
          (last_wrote : CC.code -> positive) (* variables which last wrote to each flag; put RegZero if flag empty *)
          t (e : Expr t)
          (x1 : type.for_each_lhs_of_arrow (var positive) t)
          (x2 : type.for_each_lhs_of_arrow _ t) result :
      let e1 := (invert_expr.smart_App_curried (e _) x1) in
      let e2 := (invert_expr.smart_App_curried (e _) x2) in
      let ctx := make_ctx (consts_list ++ arg_list) in
      let consts := make_consts consts_list in
      let cc := make_cc last_wrote ctx carry_flag in
      let G := make_pairs consts_list ++ make_pairs arg_list in
      (forall c, last_wrote c < next_name)%positive ->
      (forall n v, In (n, v) (consts_list ++ arg_list) -> (n < next_name)%positive) ->
      (In (last_wrote CC.C, Z.b2z carry_flag) consts_list) ->
      (forall n v1 v2, In (n, v1) (consts_list ++ arg_list) ->
                       In (n, v2) (consts_list ++ arg_list) -> v1 = v2) (* no duplicate names *) ->
      (forall v1 v2, In (v1, v2) consts_list -> v2 mod 2 ^ 256 = v2) ->
      (forall v1 v2, In (v1, v2) arg_list -> v2 mod 2 ^ 256 = v2) ->
      (LanguageWf.Compilers.expr.wf G e1 e2) ->
      valid_expr _ error consts _ last_wrote e1 ->
      interp_if_Z e2 = Some result ->
      interp Pos.eqb wordmax cc_spec (of_Expr next_name consts e x1 error) cc ctx = result.
    Proof.
      cbv [of_Expr]; intros.
      eapply of_prefancy_correct with (name_lt := Pos.lt)
                                      (cctx := fun n => if (n =? last_wrote CC.C)%positive
                                                        then carry_flag
                                                        else match make_consts consts_list 1 with
                                                             | Some n1 => (n =? n1)%positive
                                                             | _ => false
                                                             end);
        cbv [id]; eauto;
        try apply Pos.eqb_neq; intros;
          try solve [apply make_ctx_ok; auto; apply make_pairs_ok;
                     cbv [make_pairs]; rewrite map_app; auto ];
          repeat match goal with
                 | H : _ |- _ => apply in_app_or in H; destruct H
                 | H : In _ (make_pairs _) |- context [ _ = base.type.type_base _] => apply only_integers in H
                 | H : In _ (make_pairs _) |- context [interp_base] =>
                   pose proof (only_integers _ _ _ _ H); subst; cbn [interp_base]
                 | _ => solve [eauto]
                 | _ => solve [exfalso; eauto]
                 end.
      (* TODO : clean this up *)
      { cbv [cc_good make_cc]; repeat split; intros;
          [ rewrite Pos.eqb_refl; reflexivity | | ];
          break_innermost_match; try rewrite Pos.eqb_eq in *; subst; try reflexivity;
            repeat match goal with
                   | H : make_consts _ _ = Some _ |- _ =>
                     apply make_consts_ok, make_pairs_ok in H
                   | _ => apply Pos.eqb_neq; intro; subst
                   | _ => inversion_option; congruence
                   end;
            match goal with
            | H : In (?n, ?x) consts_list, H': In (?n, ?y) consts_list,
                                               H'' : forall n x y, In (n,x) _ -> In (n,y) _ -> x = y |- _ =>
              assert (x = y) by (eapply H''; eauto)
            end; destruct carry_flag; cbn [Z.b2z] in *; congruence. }
      { match goal with |- context [make_ctx ?l ?n] =>
                        let H := fresh in
                        destruct (make_ctx_cases l n) as [H | H];
                          [ rewrite H | apply in_app_or in H; destruct H ]
        end; eauto. }
    Qed.

    Section expression_equivalence.
      Context {name1 name2}
              (name1_eqb : name1 -> name1 -> bool)
              (name2_eqb : name2 -> name2 -> bool)
              (name1_eqb_eq : forall n m, name1_eqb n m = true -> n = m)
              (name1_eqb_neq : forall n m, name1_eqb n m = false -> n <> m)
              (name2_eqb_eq : forall n m, name2_eqb n m = true -> n = m)
              (name2_eqb_neq : forall n m, name2_eqb n m = false -> n <> m).

      (* name1 should only map to a single name2; several name1s might map to the same name2 *)
      Inductive in_step : (name1 -> name2) -> expr -> expr -> Prop :=
      | in_step_ret :
          forall M n1 n2, M n1 = n2 -> in_step M (Ret n1) (Ret n2)
      | in_step_instr :
          forall i M rd1 rd2 args1 args2 e1 e2,
            in_step M e1 e2 ->
            Tuple.map M args1 = args2 -> (* args correspond with old assignments *)
            M rd1 = rd2 -> (* destination register corresponds with new assignment *)
            in_step M (Instr i rd1 args1 e1) (Instr i rd2 args2 e2)
      .

      Lemma interp_eq M e1 e2 (HM : forall n n', M n = M n' -> n = n') :
        in_step M e1 e2 ->
        forall cc ctx1 ctx2,
          (forall n1, ctx1 n1 = ctx2 (M n1)) ->
          interp name1_eqb wordmax cc_spec e1 cc ctx1 =
          interp name2_eqb wordmax cc_spec e2 cc ctx2.
      Proof.
        induction 1; intros; cbn [interp]; [ congruence | ].
        replace (Tuple.map ctx1 args1) with (Tuple.map ctx2 args2)
          by (subst args2; rewrite Tuple.map_map; apply Tuple.map_ext_In; intros;
              match goal with | H : context [ctx1 _ = ctx2 _] |- _ => rewrite H end;
              f_equal; eauto using eq_sym).
        apply IHin_step; intros; eauto.
        break_innermost_match;
          repeat match goal with
                 | _ => progress subst
                 | H : _ = true  |- _ => apply name1_eqb_eq in H
                 | H : _ = false |- _ => apply name1_eqb_neq in H
                 | H : _ = true  |- _ => apply name2_eqb_eq in H
                 | H : _ = false |- _ => apply name2_eqb_neq in H
                 | H : M _ = M _ |- _ => apply HM in H
                 end; congruence.
      Qed.
    End expression_equivalence.
  End Proofs.
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

  Lemma interp_state_equiv e :
    forall cc ctx cc' ctx',
    cc = cc' -> (forall r, ctx r = ctx' r) ->
    interp256 e cc ctx = interp256 e cc' ctx'.
  Proof.
    induction e; intros; subst; cbn; [solve[auto]|].
    apply IHe; rewrite Tuple.map_ext with (g:=ctx') by auto;
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
                                                  rewrite (Tuple.map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
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
                                                  rewrite (Tuple.map_ext_In f g) by (intros; cbv [reg_eqb]; break_match; congruence)
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

Module Barrett256.
  Import LanguageWf.Compilers.

  Definition M := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition machine_wordsize := 256.

  Derive barrett_red256
         SuchThat (BarrettReduction.rbarrett_red_correctT M machine_wordsize barrett_red256)
         As barrett_red256_correct.
  Proof. Time solve_rbarrett_red_nocache machine_wordsize. Time Qed.

  Definition muLow := Eval lazy in (2 ^ (2 * machine_wordsize) / M) mod (2^machine_wordsize).

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

  Eval simpl in (type.for_each_lhs_of_arrow (type.interp base.interp)
    (type.base (base.type.type_base base.type.Z) ->
     type.base (base.type.type_base base.type.Z) ->
     type.base (base.type.type_base base.type.Z))%ptype).

  (* Note: If this is not factored out, then for some reason Qed takes forever in barrett_red256_correct_full. *)
  Lemma barrett_red256_correct_proj2 :
    forall x y,
      ZRange.type.option.is_bounded_by
        (t:=base.type.prod base.type.Z base.type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        (x, y) = true ->
      type.app_curried
          (expr.Interp (@ident.gen_interp ident.cast_outside_of_range)
             barrett_red256) (x, (y, tt)) =
        BarrettReduction.barrett_reduce machine_wordsize M
             ((2 ^ (2 * machine_wordsize) / M)
              mod 2 ^ machine_wordsize) 2 2 x y.
  Proof.
    intros.
    destruct ((proj1 barrett_red256_correct) (x, (y, tt)) (x, (y, tt))).
    { cbn; tauto. }
    { cbn in *. rewrite andb_true_r. auto. }
    { auto. }
  Qed.
  Lemma barrett_red256_correct_proj2' :
    forall x y,
      ZRange.type.option.is_bounded_by
        (t:=base.type.prod base.type.Z base.type.Z)
        (Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange, Some r[0 ~> 2 ^ machine_wordsize - 1]%zrange)
        (x, y) = true ->
      expr.Interp (@ident.interp) barrett_red256 x y =
        BarrettReduction.barrett_reduce machine_wordsize M
             ((2 ^ (2 * machine_wordsize) / M)
              mod 2 ^ machine_wordsize) 2 2 x y.
  Proof.
    intros.
    erewrite <-barrett_red256_correct_proj2 by assumption.
    unfold type.app_curried. exact eq_refl.
  Qed.
  Strategy -100 [type.app_curried].
  Local Arguments is_bounded_by_bool / .
  Lemma barrett_red256_correct_full  :
    forall (xLow xHigh : Z),
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      expr.Interp (@ident.interp) barrett_red256 xLow xHigh = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
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

  Definition barrett_red256_fancy' (xLow xHigh RegMuLow RegMod RegZero error : positive) :=
    Fancy.of_Expr 6%positive
                  (Fancy.make_consts [(RegMuLow, muLow); (RegMod, M); (RegZero, 0)])
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
  Ltac step := repeat match goal with
                      | _ => progress cbn [fst snd]
                      | |- LanguageWf.Compilers.expr.wf _ _ _ =>
                        econstructor; try solve [econstructor]; [ ]
                      | |- LanguageWf.Compilers.expr.wf _ _ _ =>
                        solve [econstructor]
                      | |- In _ _ => auto 50 using in_eq, in_cons
                      end.

  (* TODO(jgross)
     There's probably a more general statement to make here about the
     correctness of smart_App_curried, but I'm not sure what it is. *)
  Lemma interp_smart_App_curried_2 :
    forall s1 s2 d (e : Compilers.expr (s1 -> s2 -> type.base d))
           (x1 : @type.interp base.type base.interp s1)
           (x2 : @type.interp base.type base.interp s2),
      interp (invert_expr.smart_App_curried e (x1, (x2, tt))) = interp e x1 x2.
  Admitted.

  Lemma loosen_rshi_subgoal (ctx : positive -> Z) (n z: positive) cc :
    ctx z = 0 ->
    ctx n mod 2^256 = ctx n ->
    Fancy.spec (Fancy.RSHI 255) (Tuple.map (n:=2) ctx (z, n)) cc mod 2 ^ 256 =
    Fancy.spec (Fancy.RSHI 255) (Tuple.map (n:=2) ctx (z, n)) cc mod (1+1).
  Proof.
    intros Hz Hn. cbn [Tuple.map Tuple.map' fst snd]. rewrite Hz, <-Hn.
    replace (1+1) with 2 by omega. assert (2 < 2^256) by (cbn; omega).
    cbn [Fancy.spec Fancy.RSHI]. autorewrite with zsimplify_fast.
    rewrite Z.shiftr_div_pow2 by omega.
    match goal with |- context [(?x / ?d) mod _] =>
                    assert (0 <= x / d < 2);
                      [ | rewrite !(Z.mod_small (x / d)) by omega; reflexivity ]
    end.
    split; [ solve [Z.zero_bounds] | ].
    apply Z.div_lt_upper_bound; [ cbn; omega | ].
    eapply Z.lt_le_trans; [ apply Z.mod_pos_bound; cbn; omega | ].
    cbn; omega.
  Qed.

  (* This expression should have NO ands in it -- search for "&'" should return nothing *)
  Print barrett_red256.

  (* TODO: don't rely on the C, M, and L flags *)
  Lemma barrett_red256_fancy_correct :
    forall xLow xHigh error,
      0 <= xLow < 2 ^ machine_wordsize ->
      0 <= xHigh < M ->
      let RegZero := 1%positive in
      let RegMod := 2%positive in
      let RegMuLow := 3%positive in
      let RegxHigh := 4%positive in
      let RegxLow := 5%positive in
      let consts_list := [(RegMuLow, muLow); (RegMod, M); (RegZero, 0)] in
      let arg_list := [(RegxHigh, xHigh); (RegxLow, xLow)] in
      let ctx := Fancy.make_ctx (consts_list ++ arg_list) in
      let carry_flag := false in (* TODO: don't rely on this value, given it's unused *)
      let last_wrote := (fun x : Fancy.CC.code =>
                           match x with
                           | Fancy.CC.C => RegZero
                           | _ => RegxHigh (* xHigh needs to have written M; others unused *)
                           end) in
      let cc := Fancy.make_cc last_wrote ctx carry_flag in
      Fancy.interp Pos.eqb Fancy.wordmax Fancy.cc_spec (barrett_red256_fancy RegxLow RegxHigh RegMuLow RegMod RegZero error) cc ctx = (xLow + 2 ^ machine_wordsize * xHigh) mod M.
  Proof.
    intros.
    rewrite barrett_red256_fancy_eq.
    cbv [barrett_red256_fancy'].
    rewrite <-barrett_red256_correct_full by auto.
    eapply Fancy.of_Expr_correct with (x2 := (xLow, (xHigh, tt))).
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      intuition; Prod.inversion_prod; subst; cbv. break_innermost_match; congruence. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      intuition; Prod.inversion_prod; subst; cbv; congruence. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow. tauto. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      intuition; Prod.inversion_prod; subst; cbv; congruence. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      match goal with |- context [_ mod ?m] => change m with (2 ^ machine_wordsize) end.
      assert (M < 2 ^ machine_wordsize) by (cbv; congruence).
      assert (0 <= muLow < 2 ^ machine_wordsize) by (split; cbv; congruence).
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; omega. }
    { cbn; intros; subst RegZero RegMod RegMuLow RegxHigh RegxLow.
      match goal with |- context [_ mod ?m] => change m with (2 ^ machine_wordsize) end.
      assert (M < 2 ^ machine_wordsize) by (cbv; congruence).
      assert (0 <= muLow < 2 ^ machine_wordsize) by (split; cbv; congruence).
      intuition; Prod.inversion_prod; subst; apply Z.mod_small; omega. }
    { cbn.
      repeat match goal with
             | _ => apply expr.WfLetIn
             | _ => progress step
             | _ => econstructor
             end. }
    { cbn. cbv [muLow M].
      Ltac sub :=
        repeat match goal with
               | _ => progress intros
               | |- context [Fancy.valid_ident] => econstructor
               | |- context[Fancy.valid_scalar] => econstructor
               | |- context [Fancy.valid_carry] => econstructor
               | _ => reflexivity
               | |- _ <> None => cbn; congruence
               | |- Fancy.of_prefancy_scalar _ _ _ _ = _ => cbn; solve [eauto]
               end.

      admit.
      (* TODO: this code is currently broken because there are unexpected redundant ands in the code *)
      (*
      repeat (econstructor; [ solve [sub] | intros ]).
      econstructor.
      (* For the too-tight RSHI cast, we have to loosen the bounds *)
      eapply Fancy.valid_LetInZ_loosen; try solve [sub];
        [ cbn; omega | | intros; apply loosen_rshi_subgoal; solve [eauto] ].
      repeat (econstructor; [ solve [sub] | intros ]).
      econstructor.
      { sub. admit.
      (* TODO: this is the too-tight RSHI cast *) }
      repeat (econstructor; [ solve [sub] | intros ]).
      econstructor. sub. *)

    }
    { cbn - [barrett_red256].
      cbv [id].
      cbv [expr.Interp].
      replace (@ident.gen_interp Fancy.cast_oor) with (@ident.interp) by admit. (* TODO(jgross): need to be able to say that I can switch out cast_outside_of_range because bounds checking works *)
      rewrite <-interp_smart_App_curried_2.
      reflexivity. }
  Admitted.

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

    erewrite <-barrett_red256_fancy_correct with (error:=100000%positive) by eauto.
    rewrite <-barrett_red256_alloc_equivalent with (errorR := RegZero) (errorP := 1%positive) (extra_reg:=extra_reg)
      by (auto; cbn; auto with omega).
    cbv [ProdEquiv.interp256].
    let r := (eval compute in (2 ^ 256)) in
    replace (2^256) with r in * by reflexivity.

    cbn - [Fancy.interp Pos.eqb].
    cbv [Fancy.make_cc].
    match goal with |- _ = Fancy.interp _ _ _ _ ?cc _ =>
                    let x := fresh in
                    set cc as x; cbv [Pos.eqb] in x; subst x
    end.
    assert (Fancy.CC.cc_m cc_start_state = Fancy.cc_spec Fancy.CC.M (start_context xHigh)) as M_equal.
    { match goal with H : Fancy.CC.cc_m _ = _ |- _ => rewrite H end.
      cbv [Fancy.cc_spec]. rewrite Z.cc_m_eq, Z.testbit_eqb by omega.
      rewrite Z.mod_small by (split; [ solve [Z.zero_bounds] | apply Z.div_lt_upper_bound; cbn; omega ]).
      reflexivity. }
    rewrite <-M_equal.

    (* strategy to fix flags :
       1) replace state on both sides with a state reflecting dead flags updated to 0; prove that each side ignores those flags and interps remain equal
       2) prove that the M flags are the same and rewrite; now same flags are on both sides
     *)

    let dead_flags := constr:([Fancy.CC.C; Fancy.CC.L; Fancy.CC.Z]) in
    match goal with
    | H : Fancy.CC.cc_m _ = _
      |- _ = Fancy.interp _ _ _ _ ?cc _ =>
      let x := fresh in
      let Hx := fresh in
      remember (Fancy.CC.update dead_flags 0 Fancy.cc_spec cc) as x eqn:Hx;
        cbv [Fancy.CC.update] in Hx; cbn in Hx;
          match goal with
            |- ?lhs = ?rhs =>
            match (eval pattern cc in rhs) with
              ?f _ => transitivity (f x); subst x
            end
          end
    end.

    Focus 2. {
      (* here's where we need to prove the interps are equal even if I change the dead flags *)


    cbv [barrett_red256_alloc barrett_red256_fancy].

    (*
    step start_context.
    { match goal with H : Fancy.CC.cc_m _ = _ |- _ => rewrite H end.
      match goal with |- context [Z.cc_m ?s ?x] =>
                      pose proof (Z.cc_m_small s x ltac:(reflexivity) ltac:(omega));
                        let H := fresh in
                        assert (Z.cc_m s x = 1 \/ Z.cc_m s x = 0) as H by omega;
                          destruct H as [H | H]; rewrite H in *
      end; repeat (change (0 =? 1) with false || change (?x =? ?x) with true || cbv beta iota);
        break_innermost_match; Z.ltb_to_lt; try congruence.
      all: repeat match goal with
                  | [ H : context[ident.cast] |- _ ]
                    => rewrite ident.cast_in_bounds in H
                      by (cbv [is_bounded_by_bool]; rewrite Bool.andb_true_iff; split; Z.ltb_to_lt; cbn [upper lower]; lia)
                  end.
      all: congruence. }
    apply interp_equivZ_256; [ simplify_op_equiv start_context | ]. (* apply manually instead of using [step] to allow a custom bounds proof *)
    all: rewrite ?ident.cast_in_bounds
      by (cbv [is_bounded_by_bool]; rewrite Bool.andb_true_iff; split; Z.ltb_to_lt; cbn [upper lower]; lia).
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
      *)
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
      rewrite <-Z.testbit_neg_eq_if with (n:=256) by (cbn; omega).
      reflexivity. }
    step start_context.
    { reflexivity. }
    { autorewrite with zsimplify_fast.
      rewrite Z.mod_small with (a:=(if (if _ <? 0 then true else _) then _ else _)) (b:=2) by (break_innermost_match; omega).
      match goal with |- context [?a - ?b - ?c] => replace (a - b - c) with (a - (b + c)) by ring end.
      match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(omega)) end.
      rewrite <-Z.testbit_neg_eq_if with (n:=256) by (break_innermost_match; cbn; omega).
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
      rewrite <-Z.testbit_neg_eq_if with (n:=256) by (cbn; omega).
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

End Barrett256.

(* TODO : once Barrett is updated & working, fix Montgomery to match *)
(*
Module Montgomery256.

  Definition N := Eval lazy in (2^256-2^224+2^192+2^96-1).
  Definition N':= (115792089210356248768974548684794254293921932838497980611635986753331132366849).
  Definition R := Eval lazy in (2^256).
  Definition R' := 115792089183396302114378112356516095823261736990586219612555396166510339686400.
  Definition machine_wordsize := 256.

  Derive montred256
         SuchThat (MontgomeryReduction.rmontred_correctT N R N' machine_wordsize montred256)
         As montred256_correct.
  Proof. Time solve_rmontred_nocache machine_wordsize. Time Qed.

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
    @interp_equivZ s 256 115792089237316195423570985008687907853269984665640564039457584007913129639935 ltac:(lia) ltac:(reflexivity).

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

  Local Ltac break_ifs :=
    repeat (break_innermost_match_step; Z.ltb_to_lt; try (exfalso; omega); []).

  Local Opaque PreFancy.interp_cast_mod.

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

    (*step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | ].
    step start_context; [ break_ifs; reflexivity | ].*)
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
      apply Z.testbit_neg_eq_if;
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
*)
