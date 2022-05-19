Require Import Coq.Program.Basics.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.Project.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.

Local Set Implicit Arguments.

Module FlipHasLt (E : EqLt).
  Definition lt := flip E.lt.
End FlipHasLt.

Module FlipHasLe (E : EqLe).
  Definition le := flip E.le.
End FlipHasLe.

Module FlipIsStrOrder (E : StrOrder).
  Global Instance lt_strorder : StrictOrder (flip E.lt) | 10 := _.
  Global Instance lt_compat : Proper (E.eq==>E.eq==>iff) (flip E.lt) | 10 := _.
End FlipIsStrOrder.

Module FlipLeIsLtEq (E : EqLtLe') (Es : LeIsLtEq E) (Es' : IsEq E).
  Local Infix "<=" := (flip E.le).
  Local Infix "<" := (flip E.lt).
  Local Infix "==" := E.eq (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof.
    destruct Es'.eq_equiv.
    intros x y; cbv [flip]; rewrite Es.le_lteq; intuition eauto.
  Qed.
End FlipLeIsLtEq.

Module FlipHasCmp (E : Typ) (Ec : HasCmp E).
  Definition compare := flip Ec.compare.
End FlipHasCmp.

Module FlipCmpNotation (E : Typ) (Ec : HasCmp E).
  Module Import _FlipCmpNotation.
    Module C := FlipHasCmp E Ec.
  End _FlipCmpNotation.
  Include CmpNotation E C.
End FlipCmpNotation.

Module FlipCmpSpec (E : EqLt) (Ec : HasCompare E) (Ee : IsEq E).
  Local Infix "<" := (flip E.lt).
  Local Infix "==" := E.eq (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) (flip Ec.compare x y).
  Proof.
    destruct Ee.eq_equiv.
    cbv [flip]; intros x y; destruct (Ec.compare_spec y x); constructor;
      eauto.
  Qed.
End FlipCmpSpec.

Module FlipLtIsTotal (E : EqLt) (Es : LtIsTotal E) (Ee : IsEq E).
  Local Infix "<" := (flip E.lt).
  Local Infix "==" := E.eq (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof.
    destruct Ee.eq_equiv.
    intros x y; destruct (Es.lt_total y x); destruct_head'_or; eauto.
  Qed.
End FlipLtIsTotal.

Module FlipHasLeb (E : Typ) (Es : HasLeb E).
  Definition leb := flip Es.leb.
End FlipHasLeb.

Module FlipHasLtb (E : Typ) (Es : HasLtb E).
  Definition ltb := flip Es.ltb.
End FlipHasLtb.

Module FlipLebNotation (E : Typ) (Es : HasLeb E).
  Module Import _FlipLebNotation.
    Module E' := FlipHasLeb E Es.
  End _FlipLebNotation.
  Include LebNotation E E'.
End FlipLebNotation.

Module FlipLtbNotation (E : Typ) (Es : HasLtb E).
  Module Import _FlipLtbNotation.
    Module E' := FlipHasLtb E Es.
  End _FlipLtbNotation.
  Include LtbNotation E E'.
End FlipLtbNotation.

Module FlipLebSpec (E : Typ) (Ee : HasEq E) (ELe : HasLe E) (ELeb : HasLeb E) (Es : LebSpec E ELe ELeb).
  Module Import _FlipLebSpec.
    Module E' := E <+ Ee <+ ELe <+ ELeb <+ Es.
    Module F := FlipHasLe E' <+ FlipHasLeb E' E'.
  End _FlipLebSpec.
  Lemma leb_le : forall x y, flip ELeb.leb x y = true <-> flip ELe.le x y.
  Proof.
    cbv [flip]; intros x y; apply Es.leb_le.
  Qed.
End FlipLebSpec.

Module FlipLtbSpec (E : Typ) (Ee : HasEq E) (ELt : HasLt E) (ELtb : HasLtb E) (Es : LtbSpec E ELt ELtb).
  Module Import _FlipLtbSpec.
    Module E' := E <+ Ee <+ ELt <+ ELtb <+ Es.
    Module F := FlipHasLt E' <+ FlipHasLtb E' E'.
  End _FlipLtbSpec.
  Lemma ltb_lt : forall x y, flip ELtb.ltb x y = true <-> flip ELt.lt x y.
  Proof.
    cbv [flip]; intros x y; apply Es.ltb_lt.
  Qed.
End FlipLtbSpec.

Local Coercion is_true : bool >-> Sortclass.

Module FlipLebIsTotal (E : EqLtLeBool) (ETotal : LebIsTotal E).
  Module Import _FlipLebIsTotal.
    Module F := FlipHasLeb E E.
  End _FlipLebIsTotal.
  Local Infix "<=?" := (flip E.leb) (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof.
    intros x y; destruct (ETotal.leb_total y x); eauto.
  Qed.
End FlipLebIsTotal.

Module FlipLebIsTransitive (E : LeBool) (ET : LebIsTransitive E).
  Lemma leb_trans : Transitive (flip E.leb).
  Proof.
    pose proof ET.leb_trans.
    cbv in *; eauto.
  Qed.
End FlipLebIsTransitive.

Module FlipLebIsTransitive_of_TotalOrderBool (E : TotalOrderBool).
  Module Import _FlipLebIsTransitive_of_TotalOrderBool.
    Module E' := E <+ TransitiveLeBool_of_TotalOrderBool.
  End _FlipLebIsTransitive_of_TotalOrderBool.
  Include FlipLebIsTransitive E' E'.
End FlipLebIsTransitive_of_TotalOrderBool.

Module Type FlipIsStrOrderBool (E : StrOrderBool).
  Module Import _FlipIsStrOrderBool.
    Module E' := E <+ IsEqbFacts.
  End _FlipIsStrOrderBool.
  Global Instance ltb_strorder : StrictOrder (flip E.ltb) | 10.
  Proof.
    cbv [flip]; destruct E'.ltb_strorder, E'.eqb_equiv; hnf in *.
    pose proof E'.ltb_compat.
    split; cbv in *; eauto.
  Qed.
  Global Instance ltb_compat : Proper (E.eqb==>E.eqb==>eq) (flip E.ltb) | 10.
  Proof.
    destruct E'.eqb_equiv; hnf in *.
    pose proof E'.ltb_compat.
    cbv in *; eauto.
  Qed.
End FlipIsStrOrderBool.

Module FlipLebIsLtbEqb (E : EqLtLeBool') (Es : LebIsLtbEqb E) (Ee : IsEqb E E).
  Lemma leb_ltbeqb : forall x y, (flip E.leb x y = (flip E.ltb x y || E.eqb x y))%bool.
  Proof.
    intros x y.
    pose proof ((_ : Symmetric E.eqb) x y).
    pose proof ((_ : Symmetric E.eqb) y x).
    cbv [flip]; intros; rewrite Es.leb_ltbeqb.
    cbv in *; break_innermost_match; eauto.
    do 2 destruct E.eqb; intuition congruence.
  Qed.
End FlipLebIsLtbEqb.

Module FlipUsualIsStrOrder (E : UsualStrOrder).
  Global Instance lt_strorder : StrictOrder (flip E.lt) | 10 := _.
  Global Instance lt_compat : Proper (eq==>eq==>iff) (flip E.lt) | 10 := _.
End FlipUsualIsStrOrder.

Module FlipUsualLeIsLtEq (E : UsualEqLtLe) (Es : LeIsLtEq E).
  Local Infix "<=" := (flip E.le).
  Local Infix "<" := (flip E.lt).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof.
    cbv [flip]; intros; rewrite Es.le_lteq; intuition eauto.
  Qed.
End FlipUsualLeIsLtEq.

Module FlipUsualCmpSpec (E : UsualEqLt) (Ec : HasCompare E).
  Local Infix "<" := (flip E.lt).
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) (flip Ec.compare x y).
  Proof.
    cbv [flip]; intros x y; destruct (Ec.compare_spec y x); constructor; eauto.
  Qed.
End FlipUsualCmpSpec.

Module FlipUsualLtIsTotal (E : UsualEqLt) (Es : LtIsTotal E).
  Local Infix "<" := (flip E.lt).
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof.
    cbv [flip]; intros x y; destruct (Es.lt_total y x); destruct_head'_or; eauto.
  Qed.
End FlipUsualLtIsTotal.

Module FlipEqLt (E : EqLt) <: EqLt := ProjectEq E <+ FlipHasLt E.
Module FlipEqLe (E : EqLe) <: EqLe := ProjectEq E <+ FlipHasLe E.
Module FlipEqLtLe (E : EqLtLe) <: EqLtLe := ProjectEq E <+ FlipHasLt E <+ FlipHasLe E.
Module FlipEqLt' (E : EqLt) <: EqLt' := ProjectEq E <+ FlipHasLt E <+ EqLtNotation.
Module FlipEqLe' (E : EqLe) <: EqLe' := ProjectEq E <+ FlipHasLe E <+ EqLeNotation.
Module FlipEqLtLe' (E : EqLtLe) <: EqLtLe' := ProjectEq E <+ FlipHasLt E <+ FlipHasLe E <+ EqLtLeNotation.
Module FlipStrOrder (E : StrOrder) <: StrOrder := ProjectEqualityType E <+ FlipHasLt E <+ FlipIsStrOrder E.
Module FlipStrOrder' (E : StrOrder) <: StrOrder' := FlipStrOrder E <+ EqLtNotation.
Module FlipHasCompare (E : EqLt) (Ec : HasCompare E) (Ee : IsEq E) := FlipHasCmp E Ec <+ FlipCmpSpec E Ec Ee.
Module FlipDecStrOrder (E : DecStrOrder) <: DecStrOrder := FlipStrOrder E <+ FlipHasCompare E E.
Module FlipDecStrOrder' (E : DecStrOrder) <: DecStrOrder' := FlipDecStrOrder E <+ EqLtNotation <+ CmpNotation.
Module FlipOrderedType (E : OrderedType) <: OrderedType := FlipDecStrOrder E <+ ProjectHasEqDec E.
Module FlipOrderedType' (E : OrderedType') <: OrderedType' := FlipOrderedType E <+ EqLtNotation <+ CmpNotation.
Module FlipOrderedTypeFull (E : OrderedTypeFull) <: OrderedTypeFull := FlipOrderedType E <+ FlipHasLe E <+ FlipLeIsLtEq E E E.
Module FlipOrderedTypeFull' (E : OrderedTypeFull') <: OrderedTypeFull' := FlipOrderedTypeFull E <+ EqLtLeNotation <+ CmpNotation.

Module FlipUsualEqLt (E : UsualEqLt) <: UsualEqLt := ProjectUsualEq E <+ FlipHasLt E.
Module FlipUsualEqLe (E : UsualEqLe) <: UsualEqLe := ProjectUsualEq E <+ FlipHasLe E.
Module FlipUsualEqLtLe (E : UsualEqLtLe) <: UsualEqLtLe := ProjectUsualEq E <+ FlipHasLt E <+ FlipHasLe E.

Module FlipUsualStrOrder (E : UsualStrOrder) <: UsualStrOrder := ProjectUsualEqualityType E <+ FlipHasLt E <+ FlipUsualIsStrOrder E.

Module FlipUsualHasCompare (E : UsualEqLt) (Ec : HasCompare E) := FlipHasCmp E Ec <+ FlipUsualCmpSpec E Ec.

Module FlipUsualDecStrOrder (E : UsualDecStrOrder) <: UsualDecStrOrder := FlipUsualStrOrder E <+ FlipUsualHasCompare E E.
Module FlipUsualOrderedType (E : UsualOrderedType) <: UsualOrderedType := FlipUsualDecStrOrder E <+ ProjectUsualHasEqDec E.
Module FlipUsualOrderedTypeFull (E : UsualOrderedTypeFull) <: UsualOrderedTypeFull := FlipUsualOrderedType E <+ FlipHasLe E <+ FlipUsualLeIsLtEq E E.

Module FlipUsualStrOrder' (E : UsualStrOrder) <: UsualStrOrder' := FlipUsualStrOrder E <+ LtNotation.
Module FlipUsualDecStrOrder' (E : UsualDecStrOrder) <: UsualDecStrOrder' := FlipUsualDecStrOrder E <+ LtNotation.
Module FlipUsualOrderedType' (E : UsualOrderedType) <: UsualOrderedType' := FlipUsualOrderedType E <+ LtNotation.
Module FlipUsualOrderedTypeFull' (E : UsualOrderedTypeFull) <: UsualOrderedTypeFull' := FlipUsualOrderedTypeFull E <+ LtLeNotation.

Module FlipTotalOrder (E : TotalOrder) <: TotalOrder := FlipStrOrder E <+ FlipHasLe E <+ FlipLeIsLtEq E E E <+ FlipLtIsTotal E E.
Module FlipUsualTotalOrder (E : UsualTotalOrder) <: UsualTotalOrder
:= FlipUsualStrOrder E <+ FlipHasLe E <+ FlipUsualLeIsLtEq E E <+ FlipUsualLtIsTotal E E.

Module FlipTotalOrder' (E : TotalOrder) <: TotalOrder' := FlipTotalOrder E <+ EqLtLeNotation.
Module FlipUsualTotalOrder' (E : UsualTotalOrder) <: UsualTotalOrder' := FlipUsualTotalOrder E <+ LtLeNotation.

Module FlipOrderedTypeOrig (E : MiniOrderedType) <: OrderedTypeOrig.
  Module Import _FlipOrderedTypeOrig.
    Module E' := OT_of_Orig E.
    Module F := FlipOrderedType E'.
  End _FlipOrderedTypeOrig.
  Include OT_of_New F.
End FlipOrderedTypeOrig.
Module FlipMiniOrderedType (E : MiniOrderedType) <: MiniOrderedType := FlipOrderedTypeOrig E.
Module FlipUsualOrderedTypeOrig (E : UsualMiniOrderedType) <: UsualOrderedTypeOrig.
  Module Import _FlipUsualOrderedTypeOrig.
    Module E' := UsualOT_of_UsualOrig E.
    Module F := FlipUsualOrderedType E'.
  End _FlipUsualOrderedTypeOrig.
  Include OT_of_New F.
End FlipUsualOrderedTypeOrig.
Module FlipUsualMiniOrderedType (E : UsualMiniOrderedType) <: UsualMiniOrderedType := FlipUsualOrderedTypeOrig E.

Module FlipLeBool (E : EqLeBool) <: LeBool := ProjectTyp E <+ FlipHasLeb E E.
Module FlipLtBool (E : EqLtBool) <: LtBool := ProjectTyp E <+ FlipHasLtb E E.
Module FlipLeBool' (E : EqLeBool) <: LeBool' := FlipLeBool E <+ LebNotation.
Module FlipLtBool' (E : EqLtBool) <: LtBool' := FlipLtBool E <+ LtbNotation.
Module FlipEqLeBool (E : EqLeBool) <: EqLeBool := ProjectTyp E <+ ProjectHasEqb E E <+ FlipHasLeb E E.
Module FlipEqLtBool (E : EqLtBool) <: EqLtBool := ProjectTyp E <+ ProjectHasEqb E E <+ FlipHasLtb E E.
Module FlipEqLeBool' (E : EqLeBool) <: EqLeBool' := FlipEqLeBool E <+ EqbNotation <+ LebNotation.
Module FlipEqLtBool' (E : EqLtBool) <: EqLtBool' := FlipEqLtBool E <+ EqbNotation <+ LtbNotation.
Module FlipEqLtLeBool (E : EqLtLeBool) <: EqLtLeBool := ProjectTyp E <+ ProjectHasEqb E E <+ FlipHasLtb E E <+ FlipHasLeb E E.
Module FlipEqLtLeBool' (E : EqLtLeBool) <: EqLtLeBool' := FlipEqLtLeBool E <+ EqbNotation <+ LtbNotation <+ LebNotation.

Module FlipTotalLeBool (E : TotalOrderBool) <: TotalLeBool := FlipLeBool E <+ FlipLebIsTotal E E.
Module FlipTotalLeBool' (E : TotalOrderBool) <: TotalLeBool' := FlipLeBool' E <+ FlipLebIsTotal E E.
Module FlipTotalEqLeBool (E : TotalOrderBool) <: TotalEqLeBool := FlipEqLeBool E <+ FlipLebIsTotal E E.
Module FlipTotalEqLeBool' (E : TotalOrderBool) <: TotalEqLeBool' := FlipEqLeBool' E <+ FlipLebIsTotal E E.
Module FlipTotalEqLtLeBool (E : TotalOrderBool) <: TotalEqLtLeBool := FlipEqLtLeBool E <+ FlipLebIsTotal E E.
Module FlipTotalEqLtLeBool' (E : TotalOrderBool) <: TotalEqLtLeBool' := FlipEqLtLeBool' E <+ FlipLebIsTotal E E.

Module FlipTotalTransitiveLeBool (E : TotalOrderBool) <: TotalTransitiveLeBool := FlipTotalLeBool E <+ FlipLebIsTransitive_of_TotalOrderBool E.
Module FlipTotalTransitiveLeBool' (E : TotalOrderBool) <: TotalTransitiveLeBool' := FlipTotalLeBool' E <+ FlipLebIsTransitive_of_TotalOrderBool E.
Module FlipTotalTransitiveEqLeBool (E : TotalOrderBool) <: TotalTransitiveEqLeBool := FlipTotalEqLeBool E <+ FlipLebIsTransitive_of_TotalOrderBool E.
Module FlipTotalTransitiveEqLeBool' (E : TotalOrderBool) <: TotalTransitiveEqLeBool' := FlipTotalEqLeBool' E <+ FlipLebIsTransitive_of_TotalOrderBool E.
Module FlipTotalTransitiveEqLtLeBool (E : TotalOrderBool) <: TotalTransitiveEqLtLeBool := FlipTotalEqLtLeBool E <+ FlipLebIsTransitive_of_TotalOrderBool E.
Module FlipTotalTransitiveEqLtLeBool' (E : TotalOrderBool) <: TotalTransitiveEqLtLeBool' := FlipTotalEqLtLeBool' E <+ FlipLebIsTransitive_of_TotalOrderBool E.

Module FlipStrOrderBool (E : StrOrderBool) <: StrOrderBool := ProjectEqbType E <+ FlipHasLtb E E <+ FlipIsStrOrderBool E.
Module FlipStrOrderBool' (E : StrOrderBool) <: StrOrderBool' := FlipStrOrderBool E <+ EqLtBoolNotation.

Module FlipTotalOrderBool (E : TotalOrderBool) <: TotalOrderBool := FlipStrOrderBool E <+ FlipHasLeb E E <+ FlipLebIsLtbEqb E E <+ FlipLebIsTotal E E.
Module FlipTotalOrderBool' (E : TotalOrderBool) <: TotalOrderBool' := FlipTotalOrderBool E <+ EqLtLeBoolNotation.

Module FlipHasBoolOrdFuns (E : Typ) (F : HasBoolOrdFuns E) := ProjectHasEqb E F <+ FlipHasLtb E F <+ FlipHasLeb E F.

Module FlipHasBoolOrdFuns' (E : Typ) (F : HasBoolOrdFuns E) := FlipHasBoolOrdFuns E F <+ EqbNotation E F <+ FlipLtbNotation E F <+ FlipLebNotation E F.

Module FlipBoolOrdSpecs (O : EqLtLe) (F : HasBoolOrdFuns O) (S : BoolOrdSpecs O F) := ProjectEqbSpec O O F S <+ FlipLtbSpec O O O F S <+ FlipLebSpec O O O F S.

Module FlipOrderFunctions (O : EqLtLe) (F : OrderFunctions O) (Oe : IsEq O) := FlipHasCompare O F Oe <+ FlipHasBoolOrdFuns O F <+ FlipBoolOrdSpecs O F F.

Module FlipOrderFunctions' (O : EqLtLe) (F : OrderFunctions O) (Oe : IsEq O) := FlipHasCompare O F Oe <+ FlipCmpNotation O F <+ FlipHasBoolOrdFuns' O F <+ FlipBoolOrdSpecs O F F.
