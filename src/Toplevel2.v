(* TODO: prune all these dependencies *)
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
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.Show.
Require Import Crypto.Arithmetic.
Require Crypto.Language.
Require Crypto.UnderLets.
Require Crypto.AbstractInterpretation.
Require Crypto.AbstractInterpretationProofs.
Require Crypto.Rewriter.
Require Crypto.MiscCompilerPasses.
Require Crypto.CStringification.
Require Export Crypto.PushButtonSynthesis.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import Associational Positional.

Import
  Crypto.Language
  Crypto.UnderLets
  Crypto.AbstractInterpretation
  Crypto.AbstractInterpretationProofs
  Crypto.Rewriter
  Crypto.MiscCompilerPasses
  Crypto.CStringification.

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


(* TODO : update these summaries and move them to other files *)

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
