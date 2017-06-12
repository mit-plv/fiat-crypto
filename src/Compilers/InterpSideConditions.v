Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Notations.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          (interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d)
          (interped_op_side_conditions : forall s d, op s d -> interp_flat_type interp_base_type s -> pointed_Prop).

  Local Notation exprf := (@exprf base_type_code op interp_base_type).
  Local Notation expr := (@expr base_type_code op interp_base_type).
  Local Notation Expr := (@Expr base_type_code op).

  Fixpoint interpf_side_conditions_gen {t} (e : exprf t) : pointed_Prop * interp_flat_type interp_base_type t
    := match e with
       | TT => (trivial, tt)
       | Var t v => (trivial, v)
       | Op t1 tR opc args
         => let '(args_cond, argsv) := @interpf_side_conditions_gen _ args in
            (args_cond /\ interped_op_side_conditions _ _ opc argsv, interp_op _ _ opc argsv)
       | LetIn tx ex tC eC
         => let '(x_cond, xv) := @interpf_side_conditions_gen _ ex in
            let '(c_cond, cv) := @interpf_side_conditions_gen _ (eC xv) in
            (x_cond /\ c_cond, cv)
       | Pair tx ex ty ey
         => let '(x_cond, xv) := @interpf_side_conditions_gen _ ex in
            let '(y_cond, yv) := @interpf_side_conditions_gen _ ey in
            (x_cond /\ y_cond, (xv, yv))
       end%pointed_prop.
  Definition interpf_side_conditions {t} e : pointed_Prop
    := fst (@interpf_side_conditions_gen t e).
  Definition interp_side_conditions {t} (e : expr t) : interp_flat_type interp_base_type (domain t) -> pointed_Prop
    := fun x => interpf_side_conditions (invert_Abs e x).
  Definition InterpSideConditions {t} (e : Expr t) : interp_flat_type interp_base_type (domain t) -> pointed_Prop
    := interp_side_conditions (e _).
End language.
