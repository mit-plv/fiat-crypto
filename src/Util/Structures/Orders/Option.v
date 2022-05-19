Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.Option.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.

Local Set Implicit Arguments.

Module OptionHasLt (E : EqLt).
  Definition lt (x y : option E.t) : Prop
    := match x, y with
       | None, None => False
       | Some x, Some y => E.lt x y
       | Some _, None => False
       | None, Some _ => True
       end.
End OptionHasLt.

Module OptionHasLe (E : EqLe).
  Definition le (x y : option E.t) : Prop
    := match x, y with
       | None, _ => True
       | Some _, None => False
       | Some x, Some y => E.le x y
       end.
End OptionHasLe.

Local Ltac t :=
  repeat first [ progress intros
               | progress destruct_head' option
               | progress destruct_head'_or
               | progress break_innermost_match
               | progress subst
               | progress inversion_option
               | progress split_iff
               | progress split_and
               | congruence
               | apply conj
               | solve [ (idtac + exfalso); eauto ] ].

Module OptionIsStrOrder (E : StrOrder).
  Module Import _OptionIsStrOrder.
    Module O := OptionHasEq E <+ OptionHasLt E.
  End _OptionIsStrOrder.
  Global Instance lt_strorder : StrictOrder O.lt | 10.
  Proof.
    destruct E.lt_strorder, E.eq_equiv; hnf in *.
    pose proof E.lt_compat.
    split; cbv in *; t.
  Qed.
  Global Instance lt_compat : Proper (O.eq==>O.eq==>iff) O.lt | 10.
  Proof.
    destruct E.eq_equiv; hnf in *.
    pose proof E.lt_compat.
    cbv in *; t;
      setoid_subst_rel E.eq; t.
  Qed.
End OptionIsStrOrder.

Module OptionLeIsLtEq (E : EqLtLe') (Es : LeIsLtEq E) (Es' : IsStrOrder E) (Es'' : IsEq E).
  Module Import _OptionLeIsLtEq.
    Module O := OptionHasEq E <+ OptionHasLt E <+ OptionHasLe E.
  End _OptionLeIsLtEq.
  Local Infix "<=" := O.le.
  Local Infix "<" := O.lt.
  Local Infix "==" := O.eq (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof.
    destruct Es''.eq_equiv.
    destruct Es'.lt_strorder.
    hnf in *.
    pose proof Es'.lt_compat.
    pose proof Es.le_lteq.
    cbv in *; t.
  Qed.
End OptionLeIsLtEq.

Module OptionHasCmp (E : Typ) (Ec : HasCmp E).
  Definition compare (x y : option E.t) : comparison
    := match x, y with
       | Some x, Some y => Ec.compare x y
       | None, None => Eq
       | None, Some _ => Lt
       | Some _, None => Gt
       end.
End OptionHasCmp.

Module OptionCmpNotation (E : Typ) (Ec : HasCmp E).
  Module Import _OptionCmpNotation.
    Module T := OptionTyp E.
    Module C := OptionHasCmp E Ec.
  End _OptionCmpNotation.
  Include CmpNotation T C.
End OptionCmpNotation.

Module OptionCmpSpec (E : EqLt) (Ec : HasCompare E).
  Module Import _OptionCmpSpec.
    Module O := OptionHasEq E <+ OptionHasLt E <+ OptionHasCmp E Ec.
  End _OptionCmpSpec.
  Local Infix "<" := O.lt.
  Local Infix "==" := O.eq (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) (O.compare x y).
  Proof.
    cbv; intros [x|] [y|]; try destruct (Ec.compare_spec x y); constructor.
    all: eauto.
  Qed.
End OptionCmpSpec.

Module OptionLtIsTotal (E : EqLt) (Es : LtIsTotal E).
  Module Import _OptionLtIsTotal.
    Module O := OptionHasEq E <+ OptionHasLt E.
  End _OptionLtIsTotal.
  Local Infix "<" := O.lt.
  Local Infix "==" := O.eq (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof.
    intros [x|] [y|]; try destruct (Es.lt_total x y);
      cbv; t.
  Qed.
End OptionLtIsTotal.

Module OptionHasLeb (E : Typ) (Es : HasLeb E).
  Definition leb (x y : option E.t) : bool
    := match x, y with
       | None, _ => true
       | _, None => false
       | Some x, Some y => Es.leb x y
       end.
End OptionHasLeb.

Module OptionHasLtb (E : Typ) (Es : HasLtb E).
  Definition ltb (x y : option E.t) : bool
    := match x, y with
       | None, Some _ => true
       | None, None => false
       | _, None => false
       | Some x, Some y => Es.ltb x y
       end.
End OptionHasLtb.

Module OptionLebNotation (E : Typ) (Es : HasLeb E).
  Module Import _OptionLebNotation.
    Module T := OptionTyp E.
    Module E' := OptionHasLeb E Es.
  End _OptionLebNotation.
  Include LebNotation T E'.
End OptionLebNotation.

Module OptionLtbNotation (E : Typ) (Es : HasLtb E).
  Module Import _OptionLtbNotation.
    Module T := OptionTyp E.
    Module E' := OptionHasLtb E Es.
  End _OptionLtbNotation.
  Include LtbNotation T E'.
End OptionLtbNotation.

Module OptionLebSpec (E : Typ) (Ee : HasEq E) (ELe : HasLe E) (ELeb : HasLeb E) (Es : LebSpec E ELe ELeb).
  Module Import _OptionLebSpec.
    Module E' := E <+ Ee <+ ELe <+ ELeb <+ Es.
    Module O := OptionHasLe E' <+ OptionHasLeb E' E'.
  End _OptionLebSpec.
  Lemma leb_le : forall x y, O.leb x y = true <-> O.le x y.
  Proof.
    intros [x|] [y|]; try pose proof (E'.leb_le x y).
    all: cbv; t.
  Qed.
End OptionLebSpec.

Module OptionLtbSpec (E : Typ) (Ee : HasEq E) (ELt : HasLt E) (ELtb : HasLtb E) (Es : LtbSpec E ELt ELtb).
  Module Import _OptionLtbSpec.
    Module E' := E <+ Ee <+ ELt <+ ELtb <+ Es.
    Module O := OptionHasLt E' <+ OptionHasLtb E' E'.
  End _OptionLtbSpec.
  Lemma ltb_lt : forall x y, O.ltb x y = true <-> O.lt x y.
  Proof.
    intros [x|] [y|]; try pose proof (E'.ltb_lt x y); cbv.
    all: t.
  Qed.
End OptionLtbSpec.

Local Coercion is_true : bool >-> Sortclass.

Module OptionLebIsTotal (E : EqLtLeBool) (ETotal : LebIsTotal E).
  Module Import _OptionLebIsTotal.
    Module O := OptionHasLeb E E.
  End _OptionLebIsTotal.
  Local Infix "<=?" := O.leb (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof.
    intros [x|] [y|]; try (pose proof (ETotal.leb_total x y)).
    all: t.
  Qed.
End OptionLebIsTotal.

Module OptionLebIsTransitive (E : LeBool) (ET : LebIsTransitive E).
  Module Import _OptionLebIsTransitive.
    Module O := OptionHasLeb E E.
  End _OptionLebIsTransitive.
  Lemma leb_trans : Transitive O.leb.
  Proof.
    pose proof ET.leb_trans.
    cbv in *; t.
  Qed.
End OptionLebIsTransitive.

Module OptionLebIsTransitive_of_TotalOrderBool (E : TotalOrderBool).
  Module Import _OptionLebIsTransitive_of_TotalOrderBool.
    Module E' := E <+ TransitiveLeBool_of_TotalOrderBool.
  End _OptionLebIsTransitive_of_TotalOrderBool.
  Include OptionLebIsTransitive E' E'.
End OptionLebIsTransitive_of_TotalOrderBool.

Module Type OptionIsStrOrderBool (E : StrOrderBool).
  Module Import _OptionIsStrOrderBool.
    Module E' := E <+ IsEqbFacts.
    Module O := OptionHasEqb E E <+ OptionHasLtb E E.
  End _OptionIsStrOrderBool.
  Global Instance ltb_strorder : StrictOrder O.ltb | 10.
  Proof.
    destruct E'.ltb_strorder, E'.eqb_equiv; hnf in *.
    pose proof E'.ltb_compat.
    split; cbv in *; t.
  Qed.
  Global Instance ltb_compat : Proper (O.eqb==>O.eqb==>eq) O.ltb | 10.
  Proof.
    destruct E'.eqb_equiv; hnf in *.
    pose proof E'.ltb_compat.
    cbv in *; t.
  Qed.
End OptionIsStrOrderBool.

Module OptionLebIsLtbEqb (E : EqLtLeBool') (Es : LebIsLtbEqb E).
  Module Import _OptionLebIsLtbEqb.
    Module E' := E <+ Es.
    Module O := OptionHasEqb E E <+ OptionHasLtb E' E' <+ OptionHasLeb E' E'.
  End _OptionLebIsLtbEqb.
  Lemma leb_ltbeqb : forall x y, (O.leb x y = (O.ltb x y || O.eqb x y))%bool.
  Proof.
    cbv; t; rewrite ?Es.leb_ltbeqb in *; cbv; t.
  Qed.
End OptionLebIsLtbEqb.

Module OptionUsualIsStrOrder (E : UsualStrOrder).
  Module Import _OptionUsualIsStrOrder.
    Module O := OptionHasLt E.
  End _OptionUsualIsStrOrder.
  Global Instance lt_strorder : StrictOrder O.lt | 10.
  Proof.
    destruct E.lt_strorder; hnf in *.
    split; cbv in *; t.
  Qed.
  Global Instance lt_compat : Proper (eq==>eq==>iff) O.lt | 10.
  Proof. repeat intro; subst; reflexivity. Qed.
End OptionUsualIsStrOrder.

Module OptionUsualLeIsLtEq (E : UsualEqLtLe) (Es : LeIsLtEq E) (EIsStrOrder : IsStrOrder E).
  Module Import _OptionUsualLeIsLtEq.
    Module O := OptionHasLe E <+ OptionHasLt E.
  End _OptionUsualLeIsLtEq.
  Local Infix "<=" := O.le.
  Local Infix "<" := O.lt.
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof.
    pose proof Es.le_lteq.
    destruct (EIsStrOrder.lt_strorder); hnf in *.
    cbv in *; t.
    rewrite Es.le_lteq in *; t.
  Qed.
End OptionUsualLeIsLtEq.

Module OptionUsualCmpSpec (E : UsualEqLt) (Ec : HasCompare E).
  Module Import _OptionUsualCmpSpec.
    Module O := OptionHasLt E <+ OptionHasCmp E Ec.
  End _OptionUsualCmpSpec.
  Local Infix "<" := O.lt.
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) (O.compare x y).
  Proof.
    intros [x|] [y|]; cbv; try destruct (Ec.compare_spec x y); constructor.
    all: t.
  Qed.
End OptionUsualCmpSpec.

Module OptionUsualLtIsTotal (E : UsualEqLt) (Es : LtIsTotal E).
  Module Import _OptionUsualLtIsTotal.
    Module O := OptionHasLt E.
  End _OptionUsualLtIsTotal.
  Local Infix "<" := O.lt.
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof.
    intros [x|] [y|]; try pose proof (Es.lt_total x y).
    all: cbv in *; t.
  Qed.
End OptionUsualLtIsTotal.

Module OptionEqLt (E : EqLt) <: EqLt := OptionEq E <+ OptionHasLt E.
Module OptionEqLe (E : EqLe) <: EqLe := OptionEq E <+ OptionHasLe E.
Module OptionEqLtLe (E : EqLtLe) <: EqLtLe := OptionEq E <+ OptionHasLt E <+ OptionHasLe E.
Module OptionEqLt' (E : EqLt) <: EqLt' := OptionEq E <+ OptionHasLt E <+ EqLtNotation.
Module OptionEqLe' (E : EqLe) <: EqLe' := OptionEq E <+ OptionHasLe E <+ EqLeNotation.
Module OptionEqLtLe' (E : EqLtLe) <: EqLtLe' := OptionEq E <+ OptionHasLt E <+ OptionHasLe E <+ EqLtLeNotation.
Module OptionStrOrder (E : StrOrder) <: StrOrder := OptionEqualityType E <+ OptionHasLt E <+ OptionIsStrOrder E.
Module OptionStrOrder' (E : StrOrder) <: StrOrder' := OptionStrOrder E <+ EqLtNotation.
Module OptionHasCompare (E : EqLt) (Ec : HasCompare E) := OptionHasCmp E Ec <+ OptionCmpSpec E Ec.
Module OptionDecStrOrder (E : DecStrOrder) <: DecStrOrder := OptionStrOrder E <+ OptionHasCompare E E.
Module OptionDecStrOrder' (E : DecStrOrder) <: DecStrOrder' := OptionDecStrOrder E <+ EqLtNotation <+ CmpNotation.
Module OptionOrderedType (E : OrderedType) <: OrderedType := OptionDecStrOrder E <+ OptionHasEqDec E E.
Module OptionOrderedType' (E : OrderedType') <: OrderedType' := OptionOrderedType E <+ EqLtNotation <+ CmpNotation.
Module OptionOrderedTypeFull (E : OrderedTypeFull) <: OrderedTypeFull := OptionOrderedType E <+ OptionHasLe E <+ OptionLeIsLtEq E E E E.
Module OptionOrderedTypeFull' (E : OrderedTypeFull') <: OrderedTypeFull' := OptionOrderedTypeFull E <+ EqLtLeNotation <+ CmpNotation.

Module OptionUsualEqLt (E : UsualEqLt) <: UsualEqLt := OptionUsualEq E <+ OptionHasLt E.
Module OptionUsualEqLe (E : UsualEqLe) <: UsualEqLe := OptionUsualEq E <+ OptionHasLe E.
Module OptionUsualEqLtLe (E : UsualEqLtLe) <: UsualEqLtLe := OptionUsualEq E <+ OptionHasLt E <+ OptionHasLe E.

Module OptionUsualStrOrder (E : UsualStrOrder) <: UsualStrOrder := OptionUsualEqualityType E <+ OptionHasLt E <+ OptionUsualIsStrOrder E.

Module OptionUsualHasCompare (E : UsualEqLt) (Ec : HasCompare E) := OptionHasCmp E Ec <+ OptionUsualCmpSpec E Ec.

Module OptionUsualDecStrOrder (E : UsualDecStrOrder) <: UsualDecStrOrder := OptionUsualStrOrder E <+ OptionUsualHasCompare E E.
Module OptionUsualOrderedType (E : UsualOrderedType) <: UsualOrderedType := OptionUsualDecStrOrder E <+ OptionUsualHasEqDec E E.
Module OptionUsualOrderedTypeFull (E : UsualOrderedTypeFull) <: UsualOrderedTypeFull := OptionUsualOrderedType E <+ OptionHasLe E <+ OptionUsualLeIsLtEq E E E.

Module OptionUsualStrOrder' (E : UsualStrOrder) <: UsualStrOrder' := OptionUsualStrOrder E <+ LtNotation.
Module OptionUsualDecStrOrder' (E : UsualDecStrOrder) <: UsualDecStrOrder' := OptionUsualDecStrOrder E <+ LtNotation.
Module OptionUsualOrderedType' (E : UsualOrderedType) <: UsualOrderedType' := OptionUsualOrderedType E <+ LtNotation.
Module OptionUsualOrderedTypeFull' (E : UsualOrderedTypeFull) <: UsualOrderedTypeFull' := OptionUsualOrderedTypeFull E <+ LtLeNotation.

Module OptionTotalOrder (E : TotalOrder) <: TotalOrder := OptionStrOrder E <+ OptionHasLe E <+ OptionLeIsLtEq E E E E <+ OptionLtIsTotal E E.
Module OptionUsualTotalOrder (E : UsualTotalOrder) <: UsualTotalOrder
:= OptionUsualStrOrder E <+ OptionHasLe E <+ OptionUsualLeIsLtEq E E E <+ OptionUsualLtIsTotal E E.

Module OptionTotalOrder' (E : TotalOrder) <: TotalOrder' := OptionTotalOrder E <+ EqLtLeNotation.
Module OptionUsualTotalOrder' (E : UsualTotalOrder) <: UsualTotalOrder' := OptionUsualTotalOrder E <+ LtLeNotation.

Module OptionOrderedTypeOrig (E : MiniOrderedType) <: OrderedTypeOrig.
  Module Import _OptionOrderedTypeOrig.
    Module E' := OT_of_Orig E.
    Module O := OptionOrderedType E'.
  End _OptionOrderedTypeOrig.
  Include OT_of_New O.
End OptionOrderedTypeOrig.
Module OptionMiniOrderedType (E : MiniOrderedType) <: MiniOrderedType := OptionOrderedTypeOrig E.
Module OptionUsualOrderedTypeOrig (E : UsualMiniOrderedType) <: UsualOrderedTypeOrig.
  Module Import _OptionUsualOrderedTypeOrig.
    Module E' := UsualOT_of_UsualOrig E.
    Module O := OptionUsualOrderedType E'.
  End _OptionUsualOrderedTypeOrig.
  Include OT_of_New O.
End OptionUsualOrderedTypeOrig.
Module OptionUsualMiniOrderedType (E : UsualMiniOrderedType) <: UsualMiniOrderedType := OptionUsualOrderedTypeOrig E.

(* TODO: more precise module argument typing? *)
Module OptionIsStrOrderOrig (E : MiniOrderedType).
  Module Import _OptionIsStrOrderOrig.
    Module O := OptionOrderedTypeOrig E.
  End _OptionIsStrOrderOrig.
  Definition lt_trans := O.lt_trans.
  Definition lt_not_eq := O.lt_not_eq.
End OptionIsStrOrderOrig.
(* TODO: more precise module argument typing? *)
Module OptionHasCompareOrig (E : MiniOrderedType).
  Module Import _OptionHasCompareOrig.
    Module O := OptionOrderedTypeOrig E.
  End _OptionHasCompareOrig.
  Definition compare := O.compare.
End OptionHasCompareOrig.
(* TODO: more precise module argument typing? *)
Module OptionUsualIsStrOrderOrig (E : UsualMiniOrderedType).
  Module Import _OptionUsualIsStrOrderOrig.
    Module O := OptionUsualOrderedTypeOrig E.
  End _OptionUsualIsStrOrderOrig.
  Definition lt_trans := O.lt_trans.
  Definition lt_not_eq := O.lt_not_eq.
End OptionUsualIsStrOrderOrig.
(* TODO: more precise module argument typing? *)
Module OptionUsualHasCompareOrig (E : UsualMiniOrderedType).
  Module Import _OptionUsualHasCompareOrig.
    Module O := OptionUsualOrderedTypeOrig E.
  End _OptionUsualHasCompareOrig.
  Definition compare := O.compare.
End OptionUsualHasCompareOrig.

Module OptionLeBool (E : EqLeBool) <: LeBool := OptionTyp E <+ OptionHasLeb E E.
Module OptionLtBool (E : EqLtBool) <: LtBool := OptionTyp E <+ OptionHasLtb E E.
Module OptionLeBool' (E : EqLeBool) <: LeBool' := OptionLeBool E <+ LebNotation.
Module OptionLtBool' (E : EqLtBool) <: LtBool' := OptionLtBool E <+ LtbNotation.
Module OptionEqLeBool (E : EqLeBool) <: EqLeBool := OptionTyp E <+ OptionHasEqb E E <+ OptionHasLeb E E.
Module OptionEqLtBool (E : EqLtBool) <: EqLtBool := OptionTyp E <+ OptionHasEqb E E <+ OptionHasLtb E E.
Module OptionEqLeBool' (E : EqLeBool) <: EqLeBool' := OptionEqLeBool E <+ EqbNotation <+ LebNotation.
Module OptionEqLtBool' (E : EqLtBool) <: EqLtBool' := OptionEqLtBool E <+ EqbNotation <+ LtbNotation.
Module OptionEqLtLeBool (E : EqLtLeBool) <: EqLtLeBool := OptionTyp E <+ OptionHasEqb E E <+ OptionHasLtb E E <+ OptionHasLeb E E.
Module OptionEqLtLeBool' (E : EqLtLeBool) <: EqLtLeBool' := OptionEqLtLeBool E <+ EqbNotation <+ LtbNotation <+ LebNotation.

Module OptionTotalLeBool (E : TotalOrderBool) <: TotalLeBool := OptionLeBool E <+ OptionLebIsTotal E E.
Module OptionTotalLeBool' (E : TotalOrderBool) <: TotalLeBool' := OptionLeBool' E <+ OptionLebIsTotal E E.
Module OptionTotalEqLeBool (E : TotalOrderBool) <: TotalEqLeBool := OptionEqLeBool E <+ OptionLebIsTotal E E.
Module OptionTotalEqLeBool' (E : TotalOrderBool) <: TotalEqLeBool' := OptionEqLeBool' E <+ OptionLebIsTotal E E.
Module OptionTotalEqLtLeBool (E : TotalOrderBool) <: TotalEqLtLeBool := OptionEqLtLeBool E <+ OptionLebIsTotal E E.
Module OptionTotalEqLtLeBool' (E : TotalOrderBool) <: TotalEqLtLeBool' := OptionEqLtLeBool' E <+ OptionLebIsTotal E E.

Module OptionTotalTransitiveLeBool (E : TotalOrderBool) <: TotalTransitiveLeBool := OptionTotalLeBool E <+ OptionLebIsTransitive_of_TotalOrderBool E.
Module OptionTotalTransitiveLeBool' (E : TotalOrderBool) <: TotalTransitiveLeBool' := OptionTotalLeBool' E <+ OptionLebIsTransitive_of_TotalOrderBool E.
Module OptionTotalTransitiveEqLeBool (E : TotalOrderBool) <: TotalTransitiveEqLeBool := OptionTotalEqLeBool E <+ OptionLebIsTransitive_of_TotalOrderBool E.
Module OptionTotalTransitiveEqLeBool' (E : TotalOrderBool) <: TotalTransitiveEqLeBool' := OptionTotalEqLeBool' E <+ OptionLebIsTransitive_of_TotalOrderBool E.
Module OptionTotalTransitiveEqLtLeBool (E : TotalOrderBool) <: TotalTransitiveEqLtLeBool := OptionTotalEqLtLeBool E <+ OptionLebIsTransitive_of_TotalOrderBool E.
Module OptionTotalTransitiveEqLtLeBool' (E : TotalOrderBool) <: TotalTransitiveEqLtLeBool' := OptionTotalEqLtLeBool' E <+ OptionLebIsTransitive_of_TotalOrderBool E.

Module OptionStrOrderBool (E : StrOrderBool) <: StrOrderBool := OptionEqbType E <+ OptionHasLtb E E <+ OptionIsStrOrderBool E.
Module OptionStrOrderBool' (E : StrOrderBool) <: StrOrderBool' := OptionStrOrderBool E <+ EqLtBoolNotation.

Module OptionTotalOrderBool (E : TotalOrderBool) <: TotalOrderBool := OptionStrOrderBool E <+ OptionHasLeb E E <+ OptionLebIsLtbEqb E E <+ OptionLebIsTotal E E.
Module OptionTotalOrderBool' (E : TotalOrderBool) <: TotalOrderBool' := OptionTotalOrderBool E <+ EqLtLeBoolNotation.

Module OptionHasBoolOrdFuns (E : Typ) (F : HasBoolOrdFuns E) := OptionHasEqb E F <+ OptionHasLtb E F <+ OptionHasLeb E F.

Module OptionHasBoolOrdFuns' (E : Typ) (F : HasBoolOrdFuns E) := OptionHasBoolOrdFuns E F <+ OptionEqbNotation E F <+ OptionLtbNotation E F <+ OptionLebNotation E F.

Module OptionBoolOrdSpecs (O : EqLtLe) (F : HasBoolOrdFuns O) (S : BoolOrdSpecs O F) := OptionEqbSpec O O F S <+ OptionLtbSpec O O O F S <+ OptionLebSpec O O O F S.

Module OptionOrderFunctions (O : EqLtLe) (F : OrderFunctions O) := OptionHasCompare O F <+ OptionHasBoolOrdFuns O F <+ OptionBoolOrdSpecs O F F.

Module OptionOrderFunctions' (O : EqLtLe) (F : OrderFunctions O) := OptionHasCompare O F <+ OptionCmpNotation O F <+ OptionHasBoolOrdFuns' O F <+ OptionBoolOrdSpecs O F F.
