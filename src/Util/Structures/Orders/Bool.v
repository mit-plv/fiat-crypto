Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.Bool.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.DestructHead.

Local Set Implicit Arguments.
Local Coercion is_true : bool >-> Sortclass.

Module BoolHasLeb.
  Definition leb := implb.
End BoolHasLeb.

Module BoolHasLtb.
  Definition ltb x y := match x, y with false, true => true | _, _ => false end.
End BoolHasLtb.

Module BoolHasLe.
  Definition le : relation bool := BoolHasLeb.leb.
End BoolHasLe.

Module BoolHasLt.
  Definition lt : relation bool := BoolHasLtb.ltb.
End BoolHasLt.

Local Ltac t :=
  repeat first [ intro
               | progress cbv in *
               | progress subst
               | progress congruence
               | progress destruct_head'_bool
               | progress destruct_head'_or
               | solve [ eauto ]
               | exactly_once constructor ].

Module BoolIsStrOrder.
  Global Instance lt_strorder : StrictOrder BoolHasLt.lt | 1.
  Proof. t. Qed.
  Global Instance lt_compat : Proper (eq==>eq==>iff) BoolHasLt.lt | 1.
  Proof. t. Qed.
End BoolIsStrOrder.

Module BoolLeIsLtEq.
  Local Infix "<=" := BoolHasLe.le.
  Local Infix "<" := BoolHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof. t. Qed.
End BoolLeIsLtEq.

Module BoolHasCmp.
  Definition compare (x y : bool) :=
    match x, y with
    | false, true => Lt
    | true, true | false, false => Eq
    | true, false => Gt
    end.
End BoolHasCmp.

Module BoolCmpNotation := Nop <+ CmpNotation BoolTyp BoolHasCmp.

Module BoolCmpSpec.
  Local Infix "<" := BoolHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) (BoolHasCmp.compare x y).
  Proof. t. Qed.
End BoolCmpSpec.

Module BoolLtIsTotal.
  Local Infix "<" := BoolHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof. t. Qed.
End BoolLtIsTotal.

Module BoolLebNotation := Nop <+ LebNotation BoolTyp BoolHasLeb.
Module BoolLtbNotation := Nop <+ LtbNotation BoolTyp BoolHasLtb.

Module BoolLebSpec.
  Lemma leb_le : forall x y, BoolHasLeb.leb x y = true <-> BoolHasLe.le x y.
  Proof. t. Qed.
End BoolLebSpec.

Module BoolLtbSpec.
  Lemma ltb_lt : forall x y, BoolHasLtb.ltb x y = true <-> BoolHasLt.lt x y.
  Proof. t. Qed.
End BoolLtbSpec.

Module BoolLebIsTotal.
  Local Infix "<=?" := BoolHasLeb.leb (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof. t. Qed.
End BoolLebIsTotal.

Module BoolLebIsTransitive.
  Lemma leb_trans : Transitive BoolHasLeb.leb.
  Proof. t. Qed.
End BoolLebIsTransitive.

Module BoolUsualIsStrOrder.
  Global Instance lt_strorder : StrictOrder BoolHasLt.lt | 1 := _.
  Global Instance lt_compat : Proper (eq==>eq==>iff) BoolHasLt.lt | 1 := _.
End BoolUsualIsStrOrder.

Module BoolUsualLeIsLtEq.
  Local Infix "<=" := BoolHasLe.le.
  Local Infix "<" := BoolHasLt.lt.
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof. t. Qed.
End BoolUsualLeIsLtEq.

Module BoolUsualCmpSpec.
  Local Infix "<" := BoolHasLt.lt.
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) (BoolHasCmp.compare x y).
  Proof. t. Qed.
End BoolUsualCmpSpec.

Module BoolUsualLtIsTotal.
  Local Infix "<" := BoolHasLt.lt.
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof. t. Qed.
End BoolUsualLtIsTotal.

Module BoolEqLt <: EqLt := BoolEq <+ BoolHasLt.
Module BoolEqLe <: EqLe := BoolEq <+ BoolHasLe.
Module BoolEqLtLe <: EqLtLe := BoolEq <+ BoolHasLt <+ BoolHasLe.
Module BoolEqLt' <: EqLt' := BoolEq <+ BoolHasLt <+ EqLtNotation.
Module BoolEqLe' <: EqLe' := BoolEq <+ BoolHasLe <+ EqLeNotation.
Module BoolEqLtLe' <: EqLtLe' := BoolEq <+ BoolHasLt <+ BoolHasLe <+ EqLtLeNotation.
Module BoolStrOrder <: StrOrder := BoolEqualityType <+ BoolHasLt <+ BoolIsStrOrder.
Module BoolStrOrder' <: StrOrder' := BoolStrOrder <+ EqLtNotation.
Module BoolHasCompare := BoolHasCmp <+ BoolCmpSpec.
Module BoolDecStrOrder <: DecStrOrder := BoolStrOrder <+ BoolHasCompare.
Module BoolDecStrOrder' <: DecStrOrder' := BoolDecStrOrder <+ EqLtNotation <+ CmpNotation.
Module BoolOrderedType <: OrderedType := BoolDecStrOrder <+ BoolHasEqDec.
Module BoolOrderedType' <: OrderedType' := BoolOrderedType <+ EqLtNotation <+ CmpNotation.
Module BoolOrderedTypeFull <: OrderedTypeFull := BoolOrderedType <+ BoolHasLe <+ BoolLeIsLtEq.
Module BoolOrderedTypeFull' <: OrderedTypeFull' := BoolOrderedTypeFull <+ EqLtLeNotation <+ CmpNotation.

Module BoolUsualEqLt <: UsualEqLt := BoolUsualEq <+ BoolHasLt.
Module BoolUsualEqLe <: UsualEqLe := BoolUsualEq <+ BoolHasLe.
Module BoolUsualEqLtLe <: UsualEqLtLe := BoolUsualEq <+ BoolHasLt <+ BoolHasLe.

Module BoolUsualStrOrder <: UsualStrOrder := BoolUsualEqualityType <+ BoolHasLt <+ BoolUsualIsStrOrder.

Module BoolUsualHasCompare := BoolHasCmp <+ BoolUsualCmpSpec.

Module BoolUsualDecStrOrder <: UsualDecStrOrder := BoolUsualStrOrder <+ BoolUsualHasCompare.
Module BoolUsualOrderedType <: UsualOrderedType := BoolUsualDecStrOrder <+ BoolUsualHasEqDec.
Module BoolUsualOrderedTypeFull <: UsualOrderedTypeFull := BoolUsualOrderedType <+ BoolHasLe <+ BoolUsualLeIsLtEq.

Module BoolUsualStrOrder' <: UsualStrOrder' := BoolUsualStrOrder <+ LtNotation.
Module BoolUsualDecStrOrder' <: UsualDecStrOrder' := BoolUsualDecStrOrder <+ LtNotation.
Module BoolUsualOrderedType' <: UsualOrderedType' := BoolUsualOrderedType <+ LtNotation.
Module BoolUsualOrderedTypeFull' <: UsualOrderedTypeFull' := BoolUsualOrderedTypeFull <+ LtLeNotation.

Module BoolTotalOrder <: TotalOrder := BoolStrOrder <+ BoolHasLe <+ BoolLeIsLtEq <+ BoolLtIsTotal.
Module BoolUsualTotalOrder <: UsualTotalOrder
:= BoolUsualStrOrder <+ BoolHasLe <+ BoolUsualLeIsLtEq <+ BoolUsualLtIsTotal.

Module BoolTotalOrder' <: TotalOrder' := BoolTotalOrder <+ EqLtLeNotation.
Module BoolUsualTotalOrder' <: UsualTotalOrder' := BoolUsualTotalOrder <+ LtLeNotation.

Module BoolLeBool <: LeBool := BoolTyp <+ BoolHasLeb.
Module BoolLtBool <: LtBool := BoolTyp <+ BoolHasLtb.
Module BoolLeBool' <: LeBool' := BoolLeBool <+ LebNotation.
Module BoolLtBool' <: LtBool' := BoolLtBool <+ LtbNotation.

Module BoolTotalLeBool <: TotalLeBool := BoolLeBool <+ BoolLebIsTotal.
Module BoolTotalLeBool' <: TotalLeBool' := BoolLeBool' <+ BoolLebIsTotal.

Module BoolTotalTransitiveLeBool <: TotalTransitiveLeBool := BoolTotalLeBool <+ BoolLebIsTransitive.
Module BoolTotalTransitiveLeBool' <: TotalTransitiveLeBool' := BoolTotalLeBool' <+ BoolLebIsTransitive.

Module BoolHasBoolOrdFuns := BoolTyp <+ BoolHasEqb <+ BoolHasLtb <+ BoolHasLeb.

Module BoolHasBoolOrdFuns' := BoolHasBoolOrdFuns <+ BoolEqbNotation <+ BoolLtbNotation <+ BoolLebNotation.

Module BoolBoolOrdSpecs := BoolEqbSpec <+ BoolLtbSpec <+ BoolLebSpec.

Module BoolOrderFunctions := BoolHasCompare <+ BoolHasBoolOrdFuns <+ BoolBoolOrdSpecs.
Module BoolOrderFunctions' := BoolHasCompare <+ BoolCmpNotation <+ BoolHasBoolOrdFuns' <+ BoolBoolOrdSpecs.
