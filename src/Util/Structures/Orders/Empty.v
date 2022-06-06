Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.Empty.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Tactics.DestructHead.

Local Set Implicit Arguments.

Module EmptyHasLeb.
  Definition leb (x y : Empty_set) := true.
End EmptyHasLeb.

Module EmptyHasLtb.
  Definition ltb (x y : Empty_set) := false.
End EmptyHasLtb.

Module EmptyHasLe.
  Definition le : relation Empty_set := fun _ _ => True.
End EmptyHasLe.

Module EmptyHasLt.
  Definition lt : relation Empty_set := fun _ _ => False.
End EmptyHasLt.

Local Ltac t :=
  repeat first [ intro
               | progress cbv in *
               | progress subst
               | exfalso; assumption
               | congruence
               | progress destruct_head'_Empty_set
               | progress destruct_head'_or
               | solve [ eauto ]
               | exactly_once constructor ].

Module EmptyIsStrOrder.
  Global Instance lt_strorder : StrictOrder EmptyHasLt.lt | 1.
  Proof. t. Qed.
  Global Instance lt_compat : Proper (eq==>eq==>iff) EmptyHasLt.lt | 1.
  Proof. t. Qed.
End EmptyIsStrOrder.

Module EmptyLeIsLtEq.
  Local Infix "<=" := EmptyHasLe.le.
  Local Infix "<" := EmptyHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof. t. Qed.
End EmptyLeIsLtEq.

Module EmptyHasCmp.
  Definition compare (x y : Empty_set) : comparison := Eq.
End EmptyHasCmp.

Module EmptyCmpNotation := Nop <+ CmpNotation EmptyTyp EmptyHasCmp.

Module EmptyCmpSpec.
  Local Infix "<" := EmptyHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) Eq.
  Proof. t. Qed.
End EmptyCmpSpec.

Module EmptyLtIsTotal.
  Local Infix "<" := EmptyHasLt.lt.
  Local Infix "==" := eq (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof. t. Qed.
End EmptyLtIsTotal.

Module EmptyLebNotation := Nop <+ LebNotation EmptyTyp EmptyHasLeb.
Module EmptyLtbNotation := Nop <+ LtbNotation EmptyTyp EmptyHasLtb.

Module EmptyLebSpec.
  Lemma leb_le : forall x y, EmptyHasLeb.leb x y = true <-> EmptyHasLe.le x y.
  Proof. t. Qed.
End EmptyLebSpec.

Module EmptyLtbSpec.
  Lemma ltb_lt : forall x y, EmptyHasLtb.ltb x y = true <-> EmptyHasLt.lt x y.
  Proof. t. Qed.
End EmptyLtbSpec.

Module EmptyLebIsTotal.
  Local Infix "<=?" := EmptyHasLeb.leb (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof. t. Qed.
End EmptyLebIsTotal.

Module EmptyLebIsTransitive.
  Local Coercion is_true : bool >-> Sortclass.
  Lemma leb_trans : Transitive EmptyHasLeb.leb.
  Proof. t. Qed.
End EmptyLebIsTransitive.

Module EmptyUsualIsStrOrder.
  Global Instance lt_strorder : StrictOrder EmptyHasLt.lt | 1 := _.
  Global Instance lt_compat : Proper (eq==>eq==>iff) EmptyHasLt.lt | 1 := _.
End EmptyUsualIsStrOrder.

Module EmptyIsStrOrderOrig.
  Lemma lt_trans : forall x y z, EmptyHasLt.lt x y -> EmptyHasLt.lt y z -> EmptyHasLt.lt x z.
  Proof. t. Qed.
  Lemma lt_not_eq : forall x y, EmptyHasLt.lt x y -> ~ eq x y.
  Proof. t. Qed.
End EmptyIsStrOrderOrig.

Module EmptyHasCompareOrig.
  Definition compare : forall x y, OrderedType.Compare EmptyHasLt.lt eq x y.
  Proof. intros []. Defined.
End EmptyHasCompareOrig.

Module EmptyUsualLeIsLtEq.
  Local Infix "<=" := EmptyHasLe.le.
  Local Infix "<" := EmptyHasLt.lt.
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof. t. Qed.
End EmptyUsualLeIsLtEq.

Module EmptyUsualCmpSpec.
  Local Infix "<" := EmptyHasLt.lt.
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) Eq.
  Proof. t. Qed.
End EmptyUsualCmpSpec.

Module EmptyUsualLtIsTotal.
  Local Infix "<" := EmptyHasLt.lt.
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof. t. Qed.
End EmptyUsualLtIsTotal.

Local Coercion is_true : bool >-> Sortclass.

Module EmptyIsStrOrderBool.
  Global Instance ltb_strorder : StrictOrder EmptyHasLtb.ltb | 10.
  Proof. t. Qed.
  Global Instance ltb_compat : Proper (EmptyHasEqb.eqb==>EmptyHasEqb.eqb==>eq) EmptyHasLtb.ltb | 10.
  Proof. t. Qed.
End EmptyIsStrOrderBool.

Module EmptyLebIsLtbEqb.
  Lemma leb_ltbeqb : forall x y, (EmptyHasLeb.leb x y = (EmptyHasLtb.ltb x y || EmptyHasEqb.eqb x y))%bool.
  Proof. t. Qed.
End EmptyLebIsLtbEqb.

Module EmptyEqLt <: EqLt := EmptyEq <+ EmptyHasLt.
Module EmptyEqLe <: EqLe := EmptyEq <+ EmptyHasLe.
Module EmptyEqLtLe <: EqLtLe := EmptyEq <+ EmptyHasLt <+ EmptyHasLe.
Module EmptyEqLt' <: EqLt' := EmptyEq <+ EmptyHasLt <+ EqLtNotation.
Module EmptyEqLe' <: EqLe' := EmptyEq <+ EmptyHasLe <+ EqLeNotation.
Module EmptyEqLtLe' <: EqLtLe' := EmptyEq <+ EmptyHasLt <+ EmptyHasLe <+ EqLtLeNotation.
Module EmptyStrOrder <: StrOrder := EmptyEqualityType <+ EmptyHasLt <+ EmptyIsStrOrder.
Module EmptyStrOrder' <: StrOrder' := EmptyStrOrder <+ EqLtNotation.
Module EmptyHasCompare := EmptyHasCmp <+ EmptyCmpSpec.
Module EmptyDecStrOrder <: DecStrOrder := EmptyStrOrder <+ EmptyHasCompare.
Module EmptyDecStrOrder' <: DecStrOrder' := EmptyDecStrOrder <+ EqLtNotation <+ CmpNotation.
Module EmptyOrderedType <: OrderedType := EmptyDecStrOrder <+ EmptyHasEqDec.
Module EmptyOrderedType' <: OrderedType' := EmptyOrderedType <+ EqLtNotation <+ CmpNotation.
Module EmptyOrderedTypeFull <: OrderedTypeFull := EmptyOrderedType <+ EmptyHasLe <+ EmptyLeIsLtEq.
Module EmptyOrderedTypeFull' <: OrderedTypeFull' := EmptyOrderedTypeFull <+ EqLtLeNotation <+ CmpNotation.

Module EmptyUsualEqLt <: UsualEqLt := EmptyUsualEq <+ EmptyHasLt.
Module EmptyUsualEqLe <: UsualEqLe := EmptyUsualEq <+ EmptyHasLe.
Module EmptyUsualEqLtLe <: UsualEqLtLe := EmptyUsualEq <+ EmptyHasLt <+ EmptyHasLe.

Module EmptyUsualStrOrder <: UsualStrOrder := EmptyUsualEqualityType <+ EmptyHasLt <+ EmptyUsualIsStrOrder.

Module EmptyUsualHasCompare := EmptyHasCmp <+ EmptyUsualCmpSpec.

Module EmptyUsualDecStrOrder <: UsualDecStrOrder := EmptyUsualStrOrder <+ EmptyUsualHasCompare.
Module EmptyUsualOrderedType <: UsualOrderedType := EmptyUsualDecStrOrder <+ EmptyUsualHasEqDec.
Module EmptyUsualOrderedTypeFull <: UsualOrderedTypeFull := EmptyUsualOrderedType <+ EmptyHasLe <+ EmptyUsualLeIsLtEq.

Module EmptyUsualStrOrder' <: UsualStrOrder' := EmptyUsualStrOrder <+ LtNotation.
Module EmptyUsualDecStrOrder' <: UsualDecStrOrder' := EmptyUsualDecStrOrder <+ LtNotation.
Module EmptyUsualOrderedType' <: UsualOrderedType' := EmptyUsualOrderedType <+ LtNotation.
Module EmptyUsualOrderedTypeFull' <: UsualOrderedTypeFull' := EmptyUsualOrderedTypeFull <+ LtLeNotation.

Module EmptyTotalOrder <: TotalOrder := EmptyStrOrder <+ EmptyHasLe <+ EmptyLeIsLtEq <+ EmptyLtIsTotal.
Module EmptyUsualTotalOrder <: UsualTotalOrder
:= EmptyUsualStrOrder <+ EmptyHasLe <+ EmptyUsualLeIsLtEq <+ EmptyUsualLtIsTotal.

Module EmptyTotalOrder' <: TotalOrder' := EmptyTotalOrder <+ EqLtLeNotation.
Module EmptyUsualTotalOrder' <: UsualTotalOrder' := EmptyUsualTotalOrder <+ LtLeNotation.

Module EmptyOrderedTypeOrig <: OrderedTypeOrig := OT_of_New EmptyOrderedType.
Module EmptyMiniOrderedType <: MiniOrderedType := EmptyOrderedTypeOrig.
Module EmptyUsualOrderedTypeOrig <: UsualOrderedTypeOrig := EmptyOrderedTypeOrig.
Module EmptyUsualMiniOrderedType <: UsualMiniOrderedType := EmptyOrderedTypeOrig.

Module EmptyLeBool <: LeBool := EmptyTyp <+ EmptyHasLeb.
Module EmptyLtBool <: LtBool := EmptyTyp <+ EmptyHasLtb.
Module EmptyLeBool' <: LeBool' := EmptyLeBool <+ LebNotation.
Module EmptyLtBool' <: LtBool' := EmptyLtBool <+ LtbNotation.
Module EmptyEqLeBool <: EqLeBool := EmptyTyp <+ EmptyHasEqb <+ EmptyHasLeb.
Module EmptyEqLtBool <: EqLtBool := EmptyTyp <+ EmptyHasEqb <+ EmptyHasLtb.
Module EmptyEqLeBool' <: EqLeBool' := EmptyEqLeBool <+ EqbNotation <+ LebNotation.
Module EmptyEqLtBool' <: EqLtBool' := EmptyEqLtBool <+ EqbNotation <+ LtbNotation.
Module EmptyEqLtLeBool <: EqLtLeBool := EmptyTyp <+ EmptyHasEqb <+ EmptyHasLtb <+ EmptyHasLeb.
Module EmptyEqLtLeBool' <: EqLtLeBool' := EmptyEqLtLeBool <+ EqbNotation <+ LtbNotation <+ LebNotation.

Module EmptyTotalLeBool <: TotalLeBool := EmptyLeBool <+ EmptyLebIsTotal.
Module EmptyTotalLeBool' <: TotalLeBool' := EmptyLeBool' <+ EmptyLebIsTotal.
Module EmptyTotalEqLeBool <: TotalEqLeBool := EmptyEqLeBool <+ EmptyLebIsTotal.
Module EmptyTotalEqLeBool' <: TotalEqLeBool' := EmptyEqLeBool' <+ EmptyLebIsTotal.
Module EmptyTotalEqLtLeBool <: TotalEqLtLeBool := EmptyEqLtLeBool <+ EmptyLebIsTotal.
Module EmptyTotalEqLtLeBool' <: TotalEqLtLeBool' := EmptyEqLtLeBool' <+ EmptyLebIsTotal.

Module EmptyTotalTransitiveLeBool <: TotalTransitiveLeBool := EmptyTotalLeBool <+ EmptyLebIsTransitive.
Module EmptyTotalTransitiveLeBool' <: TotalTransitiveLeBool' := EmptyTotalLeBool' <+ EmptyLebIsTransitive.
Module EmptyTotalTransitiveEqLeBool <: TotalTransitiveEqLeBool := EmptyTotalEqLeBool <+ EmptyLebIsTransitive.
Module EmptyTotalTransitiveEqLeBool' <: TotalTransitiveEqLeBool' := EmptyTotalEqLeBool' <+ EmptyLebIsTransitive.
Module EmptyTotalTransitiveEqLtLeBool <: TotalTransitiveEqLtLeBool := EmptyTotalEqLtLeBool <+ EmptyLebIsTransitive.
Module EmptyTotalTransitiveEqLtLeBool' <: TotalTransitiveEqLtLeBool' := EmptyTotalEqLtLeBool' <+ EmptyLebIsTransitive.

Module EmptyStrOrderBool <: StrOrderBool := EmptyEqbType <+ EmptyHasLtb <+ EmptyIsStrOrderBool.
Module EmptyStrOrderBool' <: StrOrderBool' := EmptyStrOrderBool <+ EqLtBoolNotation.

Module EmptyTotalOrderBool <: TotalOrderBool := EmptyStrOrderBool <+ EmptyHasLeb <+ EmptyLebIsLtbEqb <+ EmptyLebIsTotal.
Module EmptyTotalOrderBool' <: TotalOrderBool' := EmptyTotalOrderBool <+ EqLtLeBoolNotation.

Module EmptyHasBoolOrdFuns := EmptyHasEqb <+ EmptyHasLtb <+ EmptyHasLeb.

Module EmptyHasBoolOrdFuns' := EmptyHasBoolOrdFuns <+ EmptyEqbNotation <+ EmptyLtbNotation <+ EmptyLebNotation.

Module EmptyBoolOrdSpecs := EmptyEqbSpec <+ EmptyLtbSpec <+ EmptyLebSpec.

Module EmptyOrderFunctions := EmptyHasCompare <+ EmptyHasBoolOrdFuns <+ EmptyBoolOrdSpecs.
Module EmptyOrderFunctions' := EmptyHasCompare <+ EmptyCmpNotation <+ EmptyHasBoolOrdFuns' <+ EmptyBoolOrdSpecs.
