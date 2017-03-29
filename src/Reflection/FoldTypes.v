Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.SmartMap.

Section language.
  Context {base_type_code} {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Section generic_type.
    Context {A}
            (process : base_type_code -> A)
            (fold : A -> A -> A).

    Section with_var.
      Context {var : base_type_code -> Type}
              (init : A)
              (dummy : forall t, var t).

      Fixpoint fold_flat_type (t : flat_type base_type_code) : A
        := match t with
           | Tbase T => process T
           | Unit => init
           | Prod A B => fold (fold_flat_type A) (fold_flat_type B)
           end.

      Fixpoint type_foldf {t} (e : @exprf base_type_code op var t) : A
        := match e with
           | TT => init
           | Var t v => process t
           | Op t tR opc args
             => fold (@type_foldf t args) (fold_flat_type tR)
           | LetIn tx ex tC eC
             => fold (@type_foldf tx ex)
                     (@type_foldf tC (eC (SmartValf _ dummy _)))
           | Pair tx ex ty ey
             => fold (@type_foldf tx ex) (@type_foldf ty ey)
           end.

      Definition type_fold {t} (e : @expr base_type_code op var t) : A
        := fold (fold_flat_type (domain t)) (type_foldf (invert_Abs e (SmartValf _ dummy _))).
    End with_var.

    Definition TypeFold (init : A) {t} (e : Expr base_type_code op t) : A
      := type_fold init (fun _ => tt) (e (fun _ => unit)).
  End generic_type.
End language.
