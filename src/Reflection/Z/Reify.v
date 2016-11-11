Require Import Coq.ZArith.ZArith.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Reflection.InputSyntax.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.LinearizeInterp.

Ltac base_reify_op op op_head extra ::=
     lazymatch op_head with
     | @Z.add => constr:(reify_op op op_head 2 Add)
     | @Z.mul => constr:(reify_op op op_head 2 Mul)
     | @Z.sub => constr:(reify_op op op_head 2 Sub)
     | @Z.shiftl => constr:(reify_op op op_head 2 Shl)
     | @Z.shiftr => constr:(reify_op op op_head 2 Shr)
     | @Z.land => constr:(reify_op op op_head 2 Land)
     | @Z.lor => constr:(reify_op op op_head 2 Lor)
     | @ModularBaseSystemListZOperations.neg => constr:(reify_op op op_head 2 Neg)
     | @ModularBaseSystemListZOperations.cmovne => constr:(reify_op op op_head 4 Cmovne)
     | @ModularBaseSystemListZOperations.cmovl => constr:(reify_op op op_head 4 Cmovle)
     end.
Ltac base_reify_type T ::=
     lazymatch T with
     | Z => TZ
     end.
Ltac Reify' e := Reflection.Reify.Reify' base_type interp_base_type op e.
Ltac Reify e :=
  let v := Reflection.Reify.Reify base_type interp_base_type op e in
  constr:((*Inline _*) ((*CSE _*) (InlineConst (Linearize v)))).
Ltac prove_InlineConst_Linearize_Compile_correct :=
  fun _
  => lazymatch goal with
     | [ |- Syntax.interp_type_gen_rel_pointwise _ (@Syntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op ?t (InlineConst (Linearize _))) _ ]
       => etransitivity;
          [ apply (@Interp_InlineConst base_type_code interp_base_type op interp_op t);
            reflect_Wf base_type_eq_semidec_is_dec op_beq_bl
          | etransitivity;
            [ apply (@Interp_Linearize base_type_code interp_base_type op interp_op t)
            | prove_compile_correct () ] ]
     end.
Ltac Reify_rhs :=
  Reflection.Reify.Reify_rhs_gen Reify prove_InlineConst_Linearize_Compile_correct interp_op ltac:(fun tac => tac ()).
