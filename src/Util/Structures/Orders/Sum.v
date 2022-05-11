Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.Sum.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Tactics.DestructHead.

Local Set Implicit Arguments.

Module SumHasLt (E1 : EqLt) (E2 : EqLt).
  Definition lt := sum_le E1.lt E2.lt.
End SumHasLt.

Module SumHasLe (E1 : EqLe) (E2 : EqLe).
  Definition le := sum_le E1.le E2.le.
End SumHasLe.

Module SumIsStrOrder (E1 : StrOrder) (E2 : StrOrder).
  Global Instance lt_strorder : StrictOrder (sum_le E1.lt E2.lt) | 1 := _.
  Global Instance lt_compat : Proper (sumwise E1.eq E2.eq==>sumwise E1.eq E2.eq==>iff) (sum_le E1.lt E2.lt) | 1 := _.
End SumIsStrOrder.

Module SumLeIsLtEq (E1 : EqLtLe') (E2 : EqLtLe') (E1s : LeIsLtEq E1) (E2s : LeIsLtEq E2).
  Local Infix "<=" := (sum_le E1.le E2.le).
  Local Infix "<" := (sum_le E1.lt E2.lt).
  Local Infix "==" := (sumwise E1.eq E2.eq) (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof.
    pose proof E1s.le_lteq.
    pose proof E2s.le_lteq.
    intros [x|x] [y|y]; cbn; firstorder eauto.
  Qed.
End SumLeIsLtEq.

Module SumHasCmp (E1 : Typ) (E2 : Typ) (E1c : HasCmp E1) (E2c : HasCmp E2).
  Definition compare := Sum.compare E1c.compare E2c.compare.
End SumHasCmp.

Module SumCmpNotation (E1 : Typ) (E2 : Typ) (E1c : HasCmp E1) (E2c : HasCmp E2).
  Module Import _SumCmpNotation.
    Module T := SumTyp E1 E2.
    Module C := SumHasCmp E1 E2 E1c E2c.
  End _SumCmpNotation.
  Include CmpNotation T C.
End SumCmpNotation.

Module SumCmpSpec (E1 : EqLt) (E2 : EqLt) (E1c : HasCompare E1) (E2c : HasCompare E2).
  Local Infix "<" := (sum_le E1.lt E2.lt).
  Local Infix "==" := (sumwise E1.eq E2.eq) (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) (Sum.compare E1c.compare E2c.compare x y).
  Proof.
    intros [x|x] [y|y]; cbn; auto using E1c.compare_spec, E2c.compare_spec.
  Qed.
End SumCmpSpec.

Module SumLtIsTotal (E1 : EqLt) (E2 : EqLt) (E1s : LtIsTotal E1) (E2s : LtIsTotal E2).
  Local Infix "<" := (sum_le E1.lt E2.lt).
  Local Infix "==" := (sumwise E1.eq E2.eq) (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof.
    pose proof E1s.lt_total; pose proof E2s.lt_total.
    intros [x|x] [y|y]; cbn; firstorder auto.
  Qed.
End SumLtIsTotal.

Module SumHasLeb (E1 : Typ) (E2 : Typ) (E1s : HasLeb E1) (E2s : HasLeb E2).
  Definition leb := sum_leb E1s.leb E2s.leb.
End SumHasLeb.

Module SumHasLtb (E1 : Typ) (E2 : Typ) (E1s : HasLtb E1) (E2s : HasLtb E2).
  Definition ltb := sum_leb E1s.ltb E2s.ltb.
End SumHasLtb.

Module SumLebNotation (E1 : Typ) (E2 : Typ) (E1s : HasLeb E1) (E2s : HasLeb E2).
  Module Import _SumLebNotation.
    Module T := SumTyp E1 E2.
    Module E := SumHasLeb E1 E2 E1s E2s.
  End _SumLebNotation.
  Include LebNotation T E.
End SumLebNotation.

Module SumLtbNotation (E1 : Typ) (E2 : Typ) (E1s : HasLtb E1) (E2s : HasLtb E2).
  Module Import _SumLtbNotation.
    Module T := SumTyp E1 E2.
    Module E := SumHasLtb E1 E2 E1s E2s.
  End _SumLtbNotation.
  Include LtbNotation T E.
End SumLtbNotation.

Module SumLebSpec (E1 : Typ) (E2 : Typ) (E1Le : HasLe E1) (E2Le : HasLe E2) (E1Leb : HasLeb E1) (E2Leb : HasLeb E2) (E1s : LebSpec E1 E1Le E1Leb) (E2s : LebSpec E2 E2Le E2Leb).
  Lemma leb_le : forall x y, sum_leb E1Leb.leb E2Leb.leb x y = true <-> sum_le E1Le.le E2Le.le x y.
  Proof.
    pose proof E1s.leb_le; pose proof E2s.leb_le.
    intros [x|x] [y|y]; cbn; firstorder congruence.
  Qed.
End SumLebSpec.

Module SumLtbSpec (E1 : Typ) (E2 : Typ) (E1Lt : HasLt E1) (E2Lt : HasLt E2) (E1Ltb : HasLtb E1) (E2Ltb : HasLtb E2) (E1s : LtbSpec E1 E1Lt E1Ltb) (E2s : LtbSpec E2 E2Lt E2Ltb).
  Lemma ltb_lt : forall x y, sum_leb E1Ltb.ltb E2Ltb.ltb x y = true <-> sum_le E1Lt.lt E2Lt.lt x y.
  Proof.
    pose proof E1s.ltb_lt; pose proof E2s.ltb_lt.
    intros [x|x] [y|y]; cbn; firstorder congruence.
  Qed.
End SumLtbSpec.

Module SumLebIsTotal (E1 : TotalLeBool) (E2 : TotalLeBool).
  Local Infix "<=?" := (sum_leb E1.leb E2.leb) (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof.
    pose proof E1.leb_total; pose proof E2.leb_total.
    intros [x|x] [y|y]; cbn; firstorder fail.
  Qed.
End SumLebIsTotal.

Module SumLebIsTransitive (E1 : LeBool) (E2 : LeBool) (E1T : LebIsTransitive E1) (E2T : LebIsTransitive E2).
  Local Coercion is_true : bool >-> Sortclass.
  Lemma leb_trans : Transitive (sum_leb E1.leb E2.leb).
  Proof.
    pose proof E1T.leb_trans; pose proof E2T.leb_trans.
    intros [x|x] [y|y] [z|z]; cbn; trivial; try congruence;
      etransitivity; eassumption.
  Qed.
End SumLebIsTransitive.

Module SumUsualIsStrOrder (E1 : UsualStrOrder) (E2 : UsualStrOrder).
  Global Instance lt_strorder : StrictOrder (sum_le E1.lt E2.lt) | 1 := _.
  Global Instance lt_compat : Proper (eq==>eq==>iff) (sum_le E1.lt E2.lt) | 1 := _.
End SumUsualIsStrOrder.

Module SumUsualLeIsLtEq (E1 : UsualEqLtLe) (E2 : UsualEqLtLe) (E1s : LeIsLtEq E1) (E2s : LeIsLtEq E2).
  Local Infix "<=" := (sum_le E1.le E2.le).
  Local Infix "<" := (sum_le E1.lt E2.lt).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof.
    intros [x|x] [y|y]; cbn;
      [ pose proof (E1s.le_lteq x y)
      |
      |
      | pose proof (E2s.le_lteq x y) ];
      repeat first [ progress destruct_head' iff
                   | progress destruct_head'_or
                   | split
                   | progress intros
                   | progress inversion_sum
                   | solve [ firstorder congruence ] ].
  Qed.
End SumUsualLeIsLtEq.

Module SumUsualCmpSpec (E1 : UsualEqLt) (E2 : UsualEqLt) (E1c : HasCompare E1) (E2c : HasCompare E2).
  Local Infix "<" := (sum_le E1.lt E2.lt).
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) (Sum.compare E1c.compare E2c.compare x y).
  Proof.
    intros [x|x] [y|y]; cbn;
      [ destruct (E1c.compare_spec x y)
      |
      |
      | destruct (E2c.compare_spec x y) ];
      auto using f_equal.
  Qed.
End SumUsualCmpSpec.

Module SumUsualLtIsTotal (E1 : UsualEqLt) (E2 : UsualEqLt) (E1s : LtIsTotal E1) (E2s : LtIsTotal E2).
  Local Infix "<" := (sum_le E1.lt E2.lt).
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof.
    pose proof E1s.lt_total; pose proof E2s.lt_total.
    intros [x|x] [y|y]; cbn; firstorder auto using f_equal.
  Qed.
End SumUsualLtIsTotal.

Module SumEqLt (E1 : EqLt) (E2 : EqLt) <: EqLt := SumEq E1 E2 <+ SumHasLt E1 E2.
Module SumEqLe (E1 : EqLe) (E2 : EqLe) <: EqLe := SumEq E1 E2 <+ SumHasLe E1 E2.
Module SumEqLtLe (E1 : EqLtLe) (E2 : EqLtLe) <: EqLtLe := SumEq E1 E2 <+ SumHasLt E1 E2 <+ SumHasLe E1 E2.
Module SumEqLt' (E1 : EqLt) (E2 : EqLt) <: EqLt' := SumEq E1 E2 <+ SumHasLt E1 E2 <+ EqLtNotation.
Module SumEqLe' (E1 : EqLe) (E2 : EqLe) <: EqLe' := SumEq E1 E2 <+ SumHasLe E1 E2 <+ EqLeNotation.
Module SumEqLtLe' (E1 : EqLtLe) (E2 : EqLtLe) <: EqLtLe' := SumEq E1 E2 <+ SumHasLt E1 E2 <+ SumHasLe E1 E2 <+ EqLtLeNotation.
Module SumStrOrder (E1 : StrOrder) (E2 : StrOrder) <: StrOrder := SumEqualityType E1 E2 <+ SumHasLt E1 E2 <+ SumIsStrOrder E1 E2.
Module SumStrOrder' (E1 : StrOrder) (E2 : StrOrder) <: StrOrder' := SumStrOrder E1 E2 <+ EqLtNotation.
Module SumHasCompare (E1 : EqLt) (E2 : EqLt) (E1c : HasCompare E1) (E2c : HasCompare E2) := SumHasCmp E1 E2 E1c E2c <+ SumCmpSpec E1 E2 E1c E2c.
Module SumDecStrOrder (E1 : DecStrOrder) (E2 : DecStrOrder) <: DecStrOrder := SumStrOrder E1 E2 <+ SumHasCompare E1 E2 E1 E2.
Module SumDecStrOrder' (E1 : DecStrOrder) (E2 : DecStrOrder) <: DecStrOrder' := SumDecStrOrder E1 E2 <+ EqLtNotation <+ CmpNotation.
Module SumOrderedType (E1 : OrderedType) (E2 : OrderedType) <: OrderedType := SumDecStrOrder E1 E2 <+ SumHasEqDec E1 E2.
Module SumOrderedType' (E1 : OrderedType') (E2 : OrderedType') <: OrderedType' := SumOrderedType E1 E2 <+ EqLtNotation <+ CmpNotation.
Module SumOrderedTypeFull (E1 : OrderedTypeFull) (E2 : OrderedTypeFull) <: OrderedTypeFull := SumOrderedType E1 E2 <+ SumHasLe E1 E2 <+ SumLeIsLtEq E1 E2 E1 E2.
Module SumOrderedTypeFull' (E1 : OrderedTypeFull') (E2 : OrderedTypeFull') <: OrderedTypeFull' := SumOrderedTypeFull E1 E2 <+ EqLtLeNotation <+ CmpNotation.

Module SumUsualEqLt (E1 : UsualEqLt) (E2 : UsualEqLt) <: UsualEqLt := SumUsualEq E1 E2 <+ SumHasLt E1 E2.
Module SumUsualEqLe (E1 : UsualEqLe) (E2 : UsualEqLe) <: UsualEqLe := SumUsualEq E1 E2 <+ SumHasLe E1 E2.
Module SumUsualEqLtLe (E1 : UsualEqLtLe) (E2 : UsualEqLtLe) <: UsualEqLtLe := SumUsualEq E1 E2 <+ SumHasLt E1 E2 <+ SumHasLe E1 E2.

Module SumUsualStrOrder (E1 : UsualStrOrder) (E2 : UsualStrOrder) <: UsualStrOrder := SumUsualEqualityType E1 E2 <+ SumHasLt E1 E2 <+ SumUsualIsStrOrder E1 E2.

Module SumUsualHasCompare (E1 : UsualEqLt) (E2 : UsualEqLt) (E1c : HasCompare E1) (E2c : HasCompare E2) := SumHasCmp E1 E2 E1c E2c <+ SumUsualCmpSpec E1 E2 E1c E2c.

Module SumUsualDecStrOrder (E1 : UsualDecStrOrder) (E2 : UsualDecStrOrder) <: UsualDecStrOrder := SumUsualStrOrder E1 E2 <+ SumUsualHasCompare E1 E2 E1 E2.
Module SumUsualOrderedType (E1 : UsualOrderedType) (E2 : UsualOrderedType) <: UsualOrderedType := SumUsualDecStrOrder E1 E2 <+ SumUsualHasEqDec E1 E2.
Module SumUsualOrderedTypeFull (E1 : UsualOrderedTypeFull) (E2 : UsualOrderedTypeFull) <: UsualOrderedTypeFull := SumUsualOrderedType E1 E2 <+ SumHasLe E1 E2 <+ SumUsualLeIsLtEq E1 E2 E1 E2.

Module SumUsualStrOrder' (E1 : UsualStrOrder) (E2 : UsualStrOrder) <: UsualStrOrder' := SumUsualStrOrder E1 E2 <+ LtNotation.
Module SumUsualDecStrOrder' (E1 : UsualDecStrOrder) (E2 : UsualDecStrOrder) <: UsualDecStrOrder' := SumUsualDecStrOrder E1 E2 <+ LtNotation.
Module SumUsualOrderedType' (E1 : UsualOrderedType) (E2 : UsualOrderedType) <: UsualOrderedType' := SumUsualOrderedType E1 E2 <+ LtNotation.
Module SumUsualOrderedTypeFull' (E1 : UsualOrderedTypeFull) (E2 : UsualOrderedTypeFull) <: UsualOrderedTypeFull' := SumUsualOrderedTypeFull E1 E2 <+ LtLeNotation.

Module SumTotalOrder (E1 : TotalOrder) (E2 : TotalOrder) <: TotalOrder := SumStrOrder E1 E2 <+ SumHasLe E1 E2 <+ SumLeIsLtEq E1 E2 E1 E2 <+ SumLtIsTotal E1 E2 E1 E2.
Module SumUsualTotalOrder (E1 : UsualTotalOrder) (E2 : UsualTotalOrder) <: UsualTotalOrder
:= SumUsualStrOrder E1 E2 <+ SumHasLe E1 E2 <+ SumUsualLeIsLtEq E1 E2 E1 E2 <+ SumUsualLtIsTotal E1 E2 E1 E2.

Module SumTotalOrder' (E1 : TotalOrder) (E2 : TotalOrder) <: TotalOrder' := SumTotalOrder E1 E2 <+ EqLtLeNotation.
Module SumUsualTotalOrder' (E1 : UsualTotalOrder) (E2 : UsualTotalOrder) <: UsualTotalOrder' := SumUsualTotalOrder E1 E2 <+ LtLeNotation.

Module SumLeBool (E1 : LeBool) (E2 : LeBool) <: LeBool := SumTyp E1 E2 <+ SumHasLeb E1 E2 E1 E2.
Module SumLtBool (E1 : LtBool) (E2 : LtBool) <: LtBool := SumTyp E1 E2 <+ SumHasLtb E1 E2 E1 E2.
Module SumLeBool' (E1 : LeBool) (E2 : LeBool) <: LeBool' := SumLeBool E1 E2 <+ LebNotation.
Module SumLtBool' (E1 : LtBool) (E2 : LtBool) <: LtBool' := SumLtBool E1 E2 <+ LtbNotation.

Module SumTotalLeBool (E1 : TotalLeBool) (E2 : TotalLeBool) <: TotalLeBool := SumLeBool E1 E2 <+ SumLebIsTotal E1 E2.
Module SumTotalLeBool' (E1 : TotalLeBool) (E2 : TotalLeBool) <: TotalLeBool' := SumLeBool' E1 E2 <+ SumLebIsTotal E1 E2.

Module SumTotalTransitiveLeBool (E1 : TotalTransitiveLeBool) (E2 : TotalTransitiveLeBool) <: TotalTransitiveLeBool := SumTotalLeBool E1 E2 <+ SumLebIsTransitive E1 E2 E1 E2.
Module SumTotalTransitiveLeBool' (E1 : TotalTransitiveLeBool) (E2 : TotalTransitiveLeBool) <: TotalTransitiveLeBool' := SumTotalLeBool' E1 E2 <+ SumLebIsTransitive E1 E2 E1 E2.

Module SumHasBoolOrdFuns (E1 : Typ) (E2 : Typ) (E1s : HasBoolOrdFuns E1) (E2s : HasBoolOrdFuns E2) := SumTyp E1 E2 <+ SumHasEqb E1 E2 E1s E2s <+ SumHasLtb E1 E2 E1s E2s <+ SumHasLeb E1 E2 E1s E2s.

Module SumHasBoolOrdFuns' (E1 : Typ) (E2 : Typ) (E1s : HasBoolOrdFuns E1) (E2s : HasBoolOrdFuns E2) := SumHasBoolOrdFuns E1 E2 E1s E2s <+ SumEqbNotation E1 E2 E1s E2s <+ SumLtbNotation E1 E2 E1s E2s <+ SumLebNotation E1 E2 E1s E2s.

Module SumBoolOrdSpecs (E1 : EqLtLe) (E2 : EqLtLe) (F1 : HasBoolOrdFuns E1) (F2 : HasBoolOrdFuns E2) (E1s : BoolOrdSpecs E1 F1) (E2s : BoolOrdSpecs E2 F2)
:= SumEqbSpec E1 E2 E1 E2 F1 F2 E1s E2s <+ SumLtbSpec E1 E2 E1 E2 F1 F2 E1s E2s <+ SumLebSpec E1 E2 E1 E2 F1 F2 E1s E2s.

Module SumOrderFunctions (E1 : EqLtLe) (E2 : EqLtLe) (E1f : OrderFunctions E1) (E2f : OrderFunctions E2)
:= SumHasCompare E1 E2 E1f E2f <+ SumHasBoolOrdFuns E1 E2 E1f E2f <+ SumBoolOrdSpecs E1 E2 E1f E2f E1f E2f.
Module SumOrderFunctions' (E1 : EqLtLe) (E2 : EqLtLe) (E1f : OrderFunctions E1) (E2f : OrderFunctions E2)
:= SumHasCompare E1 E2 E1f E2f <+ SumCmpNotation E1 E2 E1f E2f <+ SumHasBoolOrdFuns' E1 E2 E1f E2f <+ SumBoolOrdSpecs E1 E2 E1f E2f E1f E2f.

Require Import Coq.Structures.OrderedType.
Require Import Crypto.Util.Structures.OrderedType.
Module SumOrderedTypeOrig (E1 : OrderedType.MiniOrderedType) (E2 : OrderedType.MiniOrderedType) <: OrderedType.OrderedType.
  Module Import _SumOrderedTypeOrig.
    Module E1' := OT_of_Orig E1.
    Module E2' := OT_of_Orig E2.
    Module S := SumOrderedType E1' E2'.
  End _SumOrderedTypeOrig.
  Include OT_of_New S.
End SumOrderedTypeOrig.
Module SumMiniOrderedType (E1 : OrderedType.MiniOrderedType) (E2 : OrderedType.MiniOrderedType) <: OrderedType.MiniOrderedType := SumOrderedTypeOrig E1 E2.
