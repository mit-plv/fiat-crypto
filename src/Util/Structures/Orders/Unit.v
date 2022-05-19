Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.Unit.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Unit.
Require Import Crypto.Util.Tactics.DestructHead.

Local Set Implicit Arguments.

Module UnitHasLeb.
  Definition leb (x y : unit) := true.
End UnitHasLeb.

Module UnitHasLtb.
  Definition ltb (x y : unit) := false.
End UnitHasLtb.

Module UnitHasLe.
  Definition le : relation unit := fun _ _ => True.
End UnitHasLe.

Module UnitHasLt.
  Definition lt : relation unit := fun _ _ => False.
End UnitHasLt.

Local Ltac t :=
  repeat first [ intro
               | progress cbv in *
               | progress subst
               | exfalso; assumption
               | congruence
               | progress destruct_head'_unit
               | progress destruct_head'_or
               | solve [ eauto ]
               | exactly_once constructor ].

Module UnitIsStrOrder.
  Global Instance lt_strorder : StrictOrder UnitHasLt.lt | 1.
  Proof. t. Qed.
  Global Instance lt_compat : Proper (eq==>eq==>iff) UnitHasLt.lt | 1.
  Proof. t. Qed.
End UnitIsStrOrder.

Module UnitIsStrOrderOrig.
  Lemma lt_trans : forall x y z, UnitHasLt.lt x y -> UnitHasLt.lt y z -> UnitHasLt.lt x z.
  Proof. t. Qed.
  Lemma lt_not_eq : forall x y, UnitHasLt.lt x y -> ~ eq x y.
  Proof. t. Qed.
End UnitIsStrOrderOrig.

Module UnitHasCompareOrig.
  Definition compare : forall x y, OrderedType.Compare UnitHasLt.lt eq x y.
  Proof.
    constructor; destruct_head'_unit; reflexivity.
  Defined.
End UnitHasCompareOrig.

Module UnitLeIsLtEq.
  Local Infix "<=" := UnitHasLe.le.
  Local Infix "<" := UnitHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof. t. Qed.
End UnitLeIsLtEq.

Module UnitHasCmp.
  Definition compare (x y : unit) : comparison := Eq.
End UnitHasCmp.

Module UnitCmpNotation := Nop <+ CmpNotation UnitTyp UnitHasCmp.

Module UnitCmpSpec.
  Local Infix "<" := UnitHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) Eq.
  Proof. t. Qed.
End UnitCmpSpec.

Module UnitLtIsTotal.
  Local Infix "<" := UnitHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof. t. Qed.
End UnitLtIsTotal.

Module UnitLebNotation := Nop <+ LebNotation UnitTyp UnitHasLeb.
Module UnitLtbNotation := Nop <+ LtbNotation UnitTyp UnitHasLtb.

Module UnitLebSpec.
  Lemma leb_le : forall x y, UnitHasLeb.leb x y = true <-> UnitHasLe.le x y.
  Proof. t. Qed.
End UnitLebSpec.

Module UnitLtbSpec.
  Lemma ltb_lt : forall x y, UnitHasLtb.ltb x y = true <-> UnitHasLt.lt x y.
  Proof. t. Qed.
End UnitLtbSpec.

Module UnitLebIsTotal.
  Local Infix "<=?" := UnitHasLeb.leb (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof. t. Qed.
End UnitLebIsTotal.

Module UnitLebIsTransitive.
  Local Coercion is_true : bool >-> Sortclass.
  Lemma leb_trans : Transitive UnitHasLeb.leb.
  Proof. t. Qed.
End UnitLebIsTransitive.

Module UnitUsualIsStrOrder.
  Global Instance lt_strorder : StrictOrder UnitHasLt.lt | 1 := _.
  Global Instance lt_compat : Proper (eq==>eq==>iff) UnitHasLt.lt | 1 := _.
End UnitUsualIsStrOrder.

Module UnitUsualLeIsLtEq.
  Local Infix "<=" := UnitHasLe.le.
  Local Infix "<" := UnitHasLt.lt.
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof. t. Qed.
End UnitUsualLeIsLtEq.

Module UnitUsualCmpSpec.
  Local Infix "<" := UnitHasLt.lt.
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) Eq.
  Proof. t. Qed.
End UnitUsualCmpSpec.

Module UnitUsualLtIsTotal.
  Local Infix "<" := UnitHasLt.lt.
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof. t. Qed.
End UnitUsualLtIsTotal.

Local Coercion is_true : bool >-> Sortclass.

Module UnitIsStrOrderBool.
  Global Instance ltb_strorder : StrictOrder UnitHasLtb.ltb | 10.
  Proof. t. Qed.
  Global Instance ltb_compat : Proper (UnitHasEqb.eqb==>UnitHasEqb.eqb==>eq) UnitHasLtb.ltb | 10.
  Proof. t. Qed.
End UnitIsStrOrderBool.

Module UnitLebIsLtbEqb.
  Lemma leb_ltbeqb : forall x y, (UnitHasLeb.leb x y = (UnitHasLtb.ltb x y || UnitHasEqb.eqb x y))%bool.
  Proof. t. Qed.
End UnitLebIsLtbEqb.

Module UnitEqLt <: EqLt := UnitEq <+ UnitHasLt.
Module UnitEqLe <: EqLe := UnitEq <+ UnitHasLe.
Module UnitEqLtLe <: EqLtLe := UnitEq <+ UnitHasLt <+ UnitHasLe.
Module UnitEqLt' <: EqLt' := UnitEq <+ UnitHasLt <+ EqLtNotation.
Module UnitEqLe' <: EqLe' := UnitEq <+ UnitHasLe <+ EqLeNotation.
Module UnitEqLtLe' <: EqLtLe' := UnitEq <+ UnitHasLt <+ UnitHasLe <+ EqLtLeNotation.
Module UnitStrOrder <: StrOrder := UnitEqualityType <+ UnitHasLt <+ UnitIsStrOrder.
Module UnitStrOrder' <: StrOrder' := UnitStrOrder <+ EqLtNotation.
Module UnitHasCompare := UnitHasCmp <+ UnitCmpSpec.
Module UnitDecStrOrder <: DecStrOrder := UnitStrOrder <+ UnitHasCompare.
Module UnitDecStrOrder' <: DecStrOrder' := UnitDecStrOrder <+ EqLtNotation <+ CmpNotation.
Module UnitOrderedType <: OrderedType := UnitDecStrOrder <+ UnitHasEqDec.
Module UnitOrderedType' <: OrderedType' := UnitOrderedType <+ EqLtNotation <+ CmpNotation.
Module UnitOrderedTypeFull <: OrderedTypeFull := UnitOrderedType <+ UnitHasLe <+ UnitLeIsLtEq.
Module UnitOrderedTypeFull' <: OrderedTypeFull' := UnitOrderedTypeFull <+ EqLtLeNotation <+ CmpNotation.

Module UnitUsualEqLt <: UsualEqLt := UnitUsualEq <+ UnitHasLt.
Module UnitUsualEqLe <: UsualEqLe := UnitUsualEq <+ UnitHasLe.
Module UnitUsualEqLtLe <: UsualEqLtLe := UnitUsualEq <+ UnitHasLt <+ UnitHasLe.

Module UnitUsualStrOrder <: UsualStrOrder := UnitUsualEqualityType <+ UnitHasLt <+ UnitUsualIsStrOrder.

Module UnitUsualHasCompare := UnitHasCmp <+ UnitUsualCmpSpec.

Module UnitUsualDecStrOrder <: UsualDecStrOrder := UnitUsualStrOrder <+ UnitUsualHasCompare.
Module UnitUsualOrderedType <: UsualOrderedType := UnitUsualDecStrOrder <+ UnitUsualHasEqDec.
Module UnitUsualOrderedTypeFull <: UsualOrderedTypeFull := UnitUsualOrderedType <+ UnitHasLe <+ UnitUsualLeIsLtEq.

Module UnitUsualStrOrder' <: UsualStrOrder' := UnitUsualStrOrder <+ LtNotation.
Module UnitUsualDecStrOrder' <: UsualDecStrOrder' := UnitUsualDecStrOrder <+ LtNotation.
Module UnitUsualOrderedType' <: UsualOrderedType' := UnitUsualOrderedType <+ LtNotation.
Module UnitUsualOrderedTypeFull' <: UsualOrderedTypeFull' := UnitUsualOrderedTypeFull <+ LtLeNotation.

Module UnitTotalOrder <: TotalOrder := UnitStrOrder <+ UnitHasLe <+ UnitLeIsLtEq <+ UnitLtIsTotal.
Module UnitUsualTotalOrder <: UsualTotalOrder
:= UnitUsualStrOrder <+ UnitHasLe <+ UnitUsualLeIsLtEq <+ UnitUsualLtIsTotal.

Module UnitTotalOrder' <: TotalOrder' := UnitTotalOrder <+ EqLtLeNotation.
Module UnitUsualTotalOrder' <: UsualTotalOrder' := UnitUsualTotalOrder <+ LtLeNotation.

Module UnitOrderedTypeOrig <: OrderedTypeOrig := OT_of_New UnitOrderedType.
Module UnitMiniOrderedType <: MiniOrderedType := UnitOrderedTypeOrig.
Module UnitUsualOrderedTypeOrig <: UsualOrderedTypeOrig := UnitOrderedTypeOrig.
Module UnitUsualMiniOrderedType <: UsualMiniOrderedType := UnitOrderedTypeOrig.

Module UnitLeBool <: LeBool := UnitTyp <+ UnitHasLeb.
Module UnitLtBool <: LtBool := UnitTyp <+ UnitHasLtb.
Module UnitLeBool' <: LeBool' := UnitLeBool <+ LebNotation.
Module UnitLtBool' <: LtBool' := UnitLtBool <+ LtbNotation.
Module UnitEqLeBool <: EqLeBool := UnitTyp <+ UnitHasEqb <+ UnitHasLeb.
Module UnitEqLtBool <: EqLtBool := UnitTyp <+ UnitHasEqb <+ UnitHasLtb.
Module UnitEqLeBool' <: EqLeBool' := UnitEqLeBool <+ EqbNotation <+ LebNotation.
Module UnitEqLtBool' <: EqLtBool' := UnitEqLtBool <+ EqbNotation <+ LtbNotation.
Module UnitEqLtLeBool <: EqLtLeBool := UnitTyp <+ UnitHasEqb <+ UnitHasLtb <+ UnitHasLeb.
Module UnitEqLtLeBool' <: EqLtLeBool' := UnitEqLtLeBool <+ EqbNotation <+ LtbNotation <+ LebNotation.

Module UnitTotalLeBool <: TotalLeBool := UnitLeBool <+ UnitLebIsTotal.
Module UnitTotalLeBool' <: TotalLeBool' := UnitLeBool' <+ UnitLebIsTotal.
Module UnitTotalEqLeBool <: TotalEqLeBool := UnitEqLeBool <+ UnitLebIsTotal.
Module UnitTotalEqLeBool' <: TotalEqLeBool' := UnitEqLeBool' <+ UnitLebIsTotal.
Module UnitTotalEqLtLeBool <: TotalEqLtLeBool := UnitEqLtLeBool <+ UnitLebIsTotal.
Module UnitTotalEqLtLeBool' <: TotalEqLtLeBool' := UnitEqLtLeBool' <+ UnitLebIsTotal.

Module UnitTotalTransitiveLeBool <: TotalTransitiveLeBool := UnitTotalLeBool <+ UnitLebIsTransitive.
Module UnitTotalTransitiveLeBool' <: TotalTransitiveLeBool' := UnitTotalLeBool' <+ UnitLebIsTransitive.
Module UnitTotalTransitiveEqLeBool <: TotalTransitiveEqLeBool := UnitTotalEqLeBool <+ UnitLebIsTransitive.
Module UnitTotalTransitiveEqLeBool' <: TotalTransitiveEqLeBool' := UnitTotalEqLeBool' <+ UnitLebIsTransitive.
Module UnitTotalTransitiveEqLtLeBool <: TotalTransitiveEqLtLeBool := UnitTotalEqLtLeBool <+ UnitLebIsTransitive.
Module UnitTotalTransitiveEqLtLeBool' <: TotalTransitiveEqLtLeBool' := UnitTotalEqLtLeBool' <+ UnitLebIsTransitive.

Module UnitStrOrderBool <: StrOrderBool := UnitEqbType <+ UnitHasLtb <+ UnitIsStrOrderBool.
Module UnitStrOrderBool' <: StrOrderBool' := UnitStrOrderBool <+ EqLtBoolNotation.

Module UnitTotalOrderBool <: TotalOrderBool := UnitStrOrderBool <+ UnitHasLeb <+ UnitLebIsLtbEqb <+ UnitLebIsTotal.
Module UnitTotalOrderBool' <: TotalOrderBool' := UnitTotalOrderBool <+ EqLtLeBoolNotation.

Module UnitHasBoolOrdFuns := UnitHasEqb <+ UnitHasLtb <+ UnitHasLeb.

Module UnitHasBoolOrdFuns' := UnitHasBoolOrdFuns <+ UnitEqbNotation <+ UnitLtbNotation <+ UnitLebNotation.

Module UnitBoolOrdSpecs := UnitEqbSpec <+ UnitLtbSpec <+ UnitLebSpec.

Module UnitOrderFunctions := UnitHasCompare <+ UnitHasBoolOrdFuns <+ UnitBoolOrdSpecs.
Module UnitOrderFunctions' := UnitHasCompare <+ UnitCmpNotation <+ UnitHasBoolOrdFuns' <+ UnitBoolOrdSpecs.
