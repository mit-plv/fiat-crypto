Require Import Coq.ZArith.ZArith.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
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
     | @Z.add => constr:(reify_op op op_head 2 (Add TZ))
     | @Z.mul => constr:(reify_op op op_head 2 (Mul TZ))
     | @Z.sub => constr:(reify_op op op_head 2 (Sub TZ))
     | @Z.shiftl => constr:(reify_op op op_head 2 (Shl TZ))
     | @Z.shiftr => constr:(reify_op op op_head 2 (Shr TZ))
     | @Z.land => constr:(reify_op op op_head 2 (Land TZ))
     | @Z.lor => constr:(reify_op op op_head 2 (Lor TZ))
     | @ModularBaseSystemListZOperations.cmovne => constr:(reify_op op op_head 4 (Cmovne TZ))
     | @ModularBaseSystemListZOperations.cmovl => constr:(reify_op op op_head 4 (Cmovle TZ))
     | @ModularBaseSystemListZOperations.neg
       => lazymatch extra with
          | @ModularBaseSystemListZOperations.neg ?int_width _
            => constr:(reify_op op op_head 1 (Neg TZ int_width))
          | _ => fail 100 "Anomaly: In Reflection.Z.base_reify_op: head is neg but body is wrong:" extra
          end
     end.
Ltac base_reify_type T ::=
     lazymatch T with
     | Z => TZ
     end.
Ltac Reify' e := Reflection.Reify.Reify' base_type interp_base_type op e.
Ltac Reify e :=
  let v := Reflection.Reify.Reify base_type interp_base_type op make_const e in
  constr:(ExprEta ((*Inline _*) ((*CSE _*) (InlineConst is_const (Linearize v))))).
Ltac prove_ExprEta_InlineConst_Linearize_Compile_correct :=
  fun _
  => intros;
     rewrite ?InterpExprEta;
     lazymatch goal with
     | [ |- ?R (@Syntax.Interp ?base_type_code ?interp_base_type ?op ?interp_op ?t (InlineConst ?is_const (Linearize _)) ?x) _ ]
       => etransitivity;
          [ apply (@InterpInlineConst base_type_code interp_base_type op interp_op is_const t);
            reflect_Wf base_type_eq_semidec_is_dec op_beq_bl
          | etransitivity;
            [ apply (@InterpLinearize base_type_code interp_base_type op interp_op t)
            | prove_compile_correct_using ltac:(fun _ => apply make_const_correct) () ] ]
     end.
Ltac Reify_rhs :=
  Reflection.Reify.Reify_rhs_gen Reify prove_ExprEta_InlineConst_Linearize_Compile_correct interp_op ltac:(fun tac => tac ()).
