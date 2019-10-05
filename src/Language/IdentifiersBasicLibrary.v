Require Import Crypto.Language.Pre.
Require Import Crypto.Language.Language.

Module Compilers.
  Import Language.Compilers.
  Module Basic.
    Module GoalType.
      Local Set Primitive Projections.

      Class ExprReifyInfoT {exprInfo : Classes.ExprInfoT} :=
        {
          all_base_and_interp : list (Classes.base * Type)
          ; all_ident_and_interp : GallinaAndReifiedIdentList.t
        }.

      Record package :=
        {
          exprInfo : Classes.ExprInfoT
          ; exprExtraInfo : @Classes.ExprExtraInfoT exprInfo
          ; exprReifyInfo : @ExprReifyInfoT exprInfo
          ; ident_is_var_like : forall t (idc : Classes.ident t), Datatypes.bool
        }.
    End GoalType.
  End Basic.
End Compilers.
