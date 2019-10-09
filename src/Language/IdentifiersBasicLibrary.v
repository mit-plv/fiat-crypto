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

      Definition package_with_args (scraped_data : ScrapedData.t) (var_like_idents : GallinaIdentList.t) (base : Type) (ident : type.type (base.type base) -> Type)
        := package.

      Definition base_elim_with_args (scraped_data : ScrapedData.t) := Type.
      Definition ident_elim_with_args (scraped_data : ScrapedData.t) (base : Type) := Type.
    End GoalType.
  End Basic.
End Compilers.
