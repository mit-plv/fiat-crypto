Require Import Coq.ZArith.ZArith.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.Linearize.

Ltac base_reify_op op op_head ::=
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
  constr:((*Inline _*) ((*CSE _*) ((*InlineConst*) (Linearize v)))).
