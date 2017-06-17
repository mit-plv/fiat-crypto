Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.InputSyntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.WfReflective.
Require Import Crypto.Compilers.Reify.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.IdfunWithAlt.
Require Import Crypto.Util.Tactics.DebugPrint.

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
     | @Z.opp => constr:(reify_op op op_head 1 (Opp TZ TZ))
     | @Z.zselect => constr:(reify_op op op_head 3 (Zselect TZ TZ TZ TZ))
     | @Z.add_with_carry => constr:(reify_op op op_head 3 (AddWithCarry TZ TZ TZ TZ))
     | @Z.sub_with_borrow => constr:(reify_op op op_head 3 (SubWithBorrow TZ TZ TZ TZ))
     | @id_with_alt
       => lazymatch extra with
          | @id_with_alt Z _ _
            => constr:(reify_op op op_head 2 (IdWithAlt TZ TZ TZ))
          | @id_with_alt ?T _ _
            => let c := uconstr:(@id_with_alt) in
               let uZ := uconstr:(Z) in
               constr_run_tac_fail ltac:(fun _ => idtac "Error: In Reflection.Z.base_reify_op: can only reify" c "applied to" uZ "not" T)
          | _ => constr_run_tac_fail ltac:(fun _ => idtac "Anomaly: In Reflection.Z.base_reify_op: head is id_with_alt but body is wrong:" extra)
          end
     | @Z.mul_split_at_bitwidth
       => lazymatch extra with
          | @Z.mul_split_at_bitwidth ?bit_width _ _
            => constr:(reify_op op op_head 2 (MulSplit bit_width TZ TZ TZ TZ))
          | _ => constr_run_tac_fail ltac:(fun _ => idtac "Anomaly: In Reflection.Z.base_reify_op: head is Z.mul_split_with_bitwidth but body is wrong:" extra)
          end
     | @Z.add_with_get_carry
       => lazymatch extra with
          | @Z.add_with_get_carry ?bit_width _ _ _
            => constr:(reify_op op op_head 3 (AddWithGetCarry bit_width TZ TZ TZ TZ TZ))
          | _ => constr_run_tac_fail ltac:(fun _ => idtac "Anomaly: In Reflection.Z.base_reify_op: head is Z.add_with_get_carry but body is wrong:" extra)
          end
     | @Z.sub_with_get_borrow
       => lazymatch extra with
          | @Z.sub_with_get_borrow ?bit_width _ _ _
            => constr:(reify_op op op_head 3 (SubWithGetBorrow bit_width TZ TZ TZ TZ TZ))
          | _ => constr_run_tac_fail ltac:(fun _ => idtac "Anomaly: In Reflection.Z.base_reify_op: head is Z.sub_with_get_borrow but body is wrong:" extra)
          end
     end.
Ltac base_reify_type T ::=
     lazymatch T with
     | Z => TZ
     end.
Ltac Reify' e :=
  let e := (eval cbv beta delta [Z.add_get_carry Z.sub_get_borrow] in e) in
  Compilers.Reify.Reify' base_type interp_base_type op e.
Ltac Reify e :=
  let e := (eval cbv beta delta [Z.add_get_carry Z.sub_get_borrow] in e) in
  let v := Compilers.Reify.Reify base_type interp_base_type op make_const e in
  constr:(ExprEta v).
Ltac prove_ExprEta_Compile_correct :=
  fun _
  => intros;
     rewrite ?InterpExprEta;
     prove_compile_correct_using ltac:(fun _ => apply make_const_correct) ().

Ltac Reify_rhs :=
 Compilers.Reify.Reify_rhs_gen Reify prove_ExprEta_Compile_correct interp_op ltac:(fun tac => tac ()).

Ltac prereify_context_variables :=
 Compilers.Reify.prereify_context_variables interp_base_type.
Ltac reify_context_variable :=
 Compilers.Reify.reify_context_variable base_type interp_base_type op.
Ltac lazy_reify_context_variable :=
 Compilers.Reify.lazy_reify_context_variable base_type interp_base_type op.
Ltac reify_context_variables :=
 Compilers.Reify.reify_context_variables base_type interp_base_type op.
