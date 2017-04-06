Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.InputSyntax.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Equality.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.

Ltac base_reify_op op op_head extra ::=
     lazymatch op_head with
     | @Z.add => constr:(reify_op op op_head 2 (Add TZ TZ TZ))
     | @Z.mul => constr:(reify_op op op_head 2 (Mul TZ TZ TZ))
     | @Z.sub => constr:(reify_op op op_head 2 (Sub TZ TZ TZ))
     | @Z.shiftl => constr:(reify_op op op_head 2 (Shl TZ TZ TZ))
     | @Z.shiftr => constr:(reify_op op op_head 2 (Shr TZ TZ TZ))
     | @Z.land => constr:(reify_op op op_head 2 (Land TZ TZ TZ))
     | @Z.lor => constr:(reify_op op op_head 2 (Lor TZ TZ TZ))
     | @Z.opp => constr:(reify_op op op_head 1 (Opp TZ TZ))
     end.
Ltac base_reify_type T ::=
     lazymatch T with
     | Z => TZ
     end.
Ltac Reify' e := Reflection.Reify.Reify' base_type interp_base_type op e.
Ltac Reify e :=
  let v := Reflection.Reify.Reify base_type interp_base_type op make_const e in
  constr:(ExprEta v).
Ltac prove_ExprEta_Compile_correct :=
  fun _
  => intros;
     rewrite ?InterpExprEta;
     prove_compile_correct_using ltac:(fun _ => apply make_const_correct) ().

Ltac Reify_rhs :=
  Reflection.Reify.Reify_rhs_gen Reify prove_ExprEta_Compile_correct interp_op ltac:(fun tac => tac ()).

Ltac prereify_context_variables :=
  Reflection.Reify.prereify_context_variables interp_base_type.
Ltac reify_context_variable :=
  Reflection.Reify.reify_context_variable base_type interp_base_type op.
Ltac lazy_reify_context_variable :=
  Reflection.Reify.lazy_reify_context_variable base_type interp_base_type op.
Ltac reify_context_variables :=
  Reflection.Reify.reify_context_variables base_type interp_base_type op.
