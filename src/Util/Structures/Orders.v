Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.

Module Type UsualEqLt := UsualEq <+ HasLt.
Module Type UsualEqLe := UsualEq <+ HasLe.
Module Type UsualEqLtLe := UsualEq <+ HasLt <+ HasLe.

Module Type EqLeBool := Typ <+ HasEqb <+ HasLeb.
Module Type EqLtBool := Typ <+ HasEqb <+ HasLtb.
Module Type EqLeBool' := EqLeBool <+ EqbNotation <+ LebNotation.
Module Type EqLtBool' := EqLtBool <+ EqbNotation <+ LtbNotation.
Module Type EqLtLeBool := Typ <+ HasEqb <+ HasLtb <+ HasLeb.
Module Type EqLtLeBool' := EqLtLeBool <+ EqbNotation <+ LtbNotation <+ LebNotation.

Module Type TotalEqLeBool := EqLeBool <+ LebIsTotal.
Module Type TotalEqLtLeBool := EqLtLeBool <+ LebIsTotal.
Module Type TotalEqLeBool' := EqLeBool' <+ LebIsTotal.
Module Type TotalEqLtLeBool' := EqLtLeBool' <+ LebIsTotal.

Local Coercion is_true : bool >-> Sortclass.

Module Type IsStrOrderBool (Import E:EqLtBool').
#[global]
  Declare Instance ltb_strorder : StrictOrder ltb.
#[global]
  Declare Instance ltb_compat : Proper (eqb==>eqb==>eq) ltb.
End IsStrOrderBool.

Module StrOrderBool := EqLtBool <+ IsStrOrderBool.
Module StrOrderBool' := EqLtBool' <+ IsStrOrderBool.

Module Type LebIsLtbEqb (Import E:EqLtLeBool').
  Axiom leb_ltbeqb : forall x y, ((x <=? y) = ((x <? y) || (x =? y)))%bool.
End LebIsLtbEqb.
