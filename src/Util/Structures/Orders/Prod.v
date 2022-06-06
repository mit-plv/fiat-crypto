Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.Prod.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.

Local Set Implicit Arguments.
Local Open Scope bool_scope.

Module ProdHasLt (E1 : EqLt) (E2 : EqLt).
  Definition lt (x y : E1.t * E2.t) : Prop
    := E1.lt (fst x) (fst y) \/ (E1.eq (fst x) (fst y) /\ E2.lt (snd x) (snd y)).
End ProdHasLt.

Module ProdHasLe (E1 : EqLe) (E2 : EqLe).
  Definition le (x y : E1.t * E2.t) : Prop
    := E1.le (fst x) (fst y) /\ (~E1.eq (fst x) (fst y) \/ E2.le (snd x) (snd y)).
End ProdHasLe.

Local Ltac fold_is_true :=
  repeat match goal with
         | [ H : ?x = true |- _ ] => change (is_true x) in H
         end.

Local Ltac setoid_subst_relb R :=
  repeat match goal with
         | [ H : R ?x ?y |- _ ]
           => first [ is_var x; rewrite H in *; clear x H
                    | is_var y; rewrite <- H in *; clear y H ]
         | [ H : is_true (R ?x ?y) |- _ ]
           => first [ is_var x; rewrite H in *; clear x H
                    | is_var y; rewrite <- H in *; clear y H ]
         end.

Local Ltac t :=
  repeat first [ split
               | intro
               | progress subst
               | assumption
               | progress cbv [complement is_true] in *
               | progress cbn in *
               | congruence
               | progress inversion_pair
               | rewrite Bool.andb_true_iff in *
               | rewrite Bool.orb_true_iff in *
               | rewrite Bool.negb_true_iff in *
               | rewrite Bool.orb_true_l in *
               | rewrite Bool.orb_true_r in *
               | rewrite Bool.andb_true_l in *
               | rewrite Bool.andb_true_r in *
               | rewrite Bool.orb_false_l in *
               | rewrite Bool.orb_false_r in *
               | rewrite Bool.andb_false_l in *
               | rewrite Bool.andb_false_r in *
               | progress split_and
               | progress intuition eauto 2
               | match goal with
                 | [ H : context[match ?x with _ => _ end] |- _ ]
                   => first [ is_var x; destruct x
                            | destruct x eqn:? ]
                 | [ |- context[match ?x with _ => _ end] ]
                   => first [ is_var x; destruct x
                            | destruct x eqn:? ]
                 | [ H : ?x = ?x |- _ ] => clear H
                 | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
                 | [ H : ?x = false, H' : context[?x] |- _ ] => rewrite H in H'
                 | [ H : true = _ |- _ ] => symmetry in H
                 | [ H : false = _ |- _ ] => symmetry in H
                 | [ |- context[?x = false] ]
                   => lazymatch x with
                      | true => fail
                      | false => fail
                      | _ => destruct x eqn:?
                      end
                 | [ |- context[?x = true] ]
                   => lazymatch x with
                      | true => fail
                      | false => fail
                      | _ => destruct x eqn:?
                      end
                 end
               | now constructor; t ].

Module ProdIsStrOrder (E1 : StrOrder) (E2 : StrOrder).
  Module Import _ProdIsStrOrder.
    Module P := ProdHasEq E1 E2 <+ ProdHasLt E1 E2.
  End _ProdIsStrOrder.
  Global Instance lt_strorder : StrictOrder P.lt | 1.
  Proof.
    destruct E1.lt_strorder, E2.lt_strorder, E1.eq_equiv, E2.eq_equiv; hnf in *.
    pose proof E1.lt_compat; pose proof E2.lt_compat; cbv in *.
    t.
  Qed.
  Global Instance lt_compat : Proper (P.eq==>P.eq==>iff) P.lt | 1.
  Proof.
    repeat intros [? ?].
    hnf in *.
    cbv [P.lt].
    cbn [fst snd] in *.
    destruct E1.lt_strorder, E2.lt_strorder, E1.eq_equiv, E2.eq_equiv.
    setoid_subst_relb E1.eq.
    setoid_subst_relb E2.eq.
    t.
  Qed.
End ProdIsStrOrder.

Module ProdLeIsLtEq (E1 : EqLtLe') (E2 : EqLtLe') (E1s : LeIsLtEq E1) (E2s : LeIsLtEq E2) (E1s' : IsStrOrder E1) (E1s'' : IsEq E1).
  Module Import _ProdLeIsLtEq.
    Module P := ProdHasEq E1 E2 <+ ProdHasLt E1 E2 <+ ProdHasLe E1 E2.
  End _ProdLeIsLtEq.
  Local Infix "<=" := P.le.
  Local Infix "<" := P.lt.
  Local Infix "==" := P.eq (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof.
    destruct E1s''.eq_equiv.
    destruct E1s'.lt_strorder.
    hnf in *.
    pose proof E1s'.lt_compat.
    cbv; t; rewrite ?E1s.le_lteq, ?E2s.le_lteq in *.
    all: t.
    constructor; now t; setoid_subst_relb E1.eq; t.
  Qed.
End ProdLeIsLtEq.

Module ProdHasCmp (E1 : Typ) (E2 : Typ) (E1c : HasCmp E1) (E2c : HasCmp E2).
  Definition compare (x y : E1.t * E2.t) : comparison
    := match E1c.compare (fst x) (fst y), E2c.compare (snd x) (snd y) with
       | Lt as c, _
       | Gt as c, _
       | Eq, c => c
       end.
End ProdHasCmp.

Module ProdCmpNotation (E1 : Typ) (E2 : Typ) (E1c : HasCmp E1) (E2c : HasCmp E2).
  Module Import _ProdCmpNotation.
    Module T := ProdTyp E1 E2.
    Module C := ProdHasCmp E1 E2 E1c E2c.
  End _ProdCmpNotation.
  Include CmpNotation T C.
End ProdCmpNotation.

Module ProdCmpSpec (E1 : EqLt) (E2 : EqLt) (E1c : HasCompare E1) (E2c : HasCompare E2) (E1s : IsEq E1).
  Module Import _ProdCmpSpec.
    Module P := ProdHasEq E1 E2 <+ ProdHasLt E1 E2 <+ ProdHasCmp E1 E2 E1c E2c.
  End _ProdCmpSpec.
  Local Infix "<" := P.lt.
  Local Infix "==" := P.eq (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) (P.compare x y).
  Proof.
    destruct E1s.eq_equiv.
    intros [x1 x2] [y1 y2]; cbv.
    destruct (E1c.compare_spec x1 y1), (E2c.compare_spec x2 y2); constructor; eauto.
  Qed.
End ProdCmpSpec.

Module ProdLtIsTotal (E1 : EqLt) (E2 : EqLt) (E1s : LtIsTotal E1) (E2s : LtIsTotal E2).
  Module Import _ProdLtIsTotal.
    Module P := ProdHasEq E1 E2 <+ ProdHasLt E1 E2.
  End _ProdLtIsTotal.
  Local Infix "<" := P.lt.
  Local Infix "==" := P.eq (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof.
    intros [x1 x2] [y1 y2].
    pose proof (E1s.lt_total x1 y1); pose proof (E1s.lt_total y1 x1); pose proof (E2s.lt_total x2 y2).
    cbv; t.
  Qed.
End ProdLtIsTotal.

Module ProdHasLeb (E1 : Typ) (E2 : Typ) (E1e : HasEqb E1) (E1s : HasLeb E1) (E2s : HasLeb E2).
  Definition leb (x y : E1.t * E2.t) : bool
    := E1s.leb (fst x) (fst y) && (negb (E1e.eqb (fst x) (fst y)) || E2s.leb (snd x) (snd y)).
End ProdHasLeb.

Module ProdHasLtb (E1 : Typ) (E2 : Typ) (E1e : HasEqb E1) (E1s : HasLtb E1) (E2s : HasLtb E2).
  Definition ltb (x y : E1.t * E2.t) : bool
    := E1s.ltb (fst x) (fst y) || (E1e.eqb (fst x) (fst y) && E2s.ltb (snd x) (snd y)).
End ProdHasLtb.

Module ProdLebNotation (E1 : Typ) (E2 : Typ) (E1e : HasEqb E1) (E1s : HasLeb E1) (E2s : HasLeb E2).
  Module Import _ProdLebNotation.
    Module T := ProdTyp E1 E2.
    Module E := ProdHasLeb E1 E2 E1e E1s E2s.
  End _ProdLebNotation.
  Include LebNotation T E.
End ProdLebNotation.

Module ProdLtbNotation (E1 : Typ) (E2 : Typ) (E1e : HasEqb E1) (E1s : HasLtb E1) (E2s : HasLtb E2).
  Module Import _ProdLtbNotation.
    Module T := ProdTyp E1 E2.
    Module E := ProdHasLtb E1 E2 E1e E1s E2s.
  End _ProdLtbNotation.
  Include LtbNotation T E.
End ProdLtbNotation.

Module ProdLebSpec (E1 : Typ) (E2 : Typ) (E1e : HasEq E1) (E2e : HasEq E2) (E1Le : HasLe E1) (E2Le : HasLe E2) (E1Eqb : HasEqb E1) (E1Leb : HasLeb E1) (E2Leb : HasLeb E2) (E1s : LebSpec E1 E1Le E1Leb) (E2s : LebSpec E2 E2Le E2Leb) (E1s' : EqbSpec E1 E1e E1Eqb).
  Module Import _ProdLebSpec.
    Module E1' := E1 <+ E1e <+ E1Le <+ E1Eqb <+ E1Leb <+ E1s <+ E1s'.
    Module E2' := E2 <+ E2e <+ E2Le <+ E2Leb <+ E2s.
    Module P := ProdHasLe E1' E2' <+ ProdHasLeb E1' E2' E1' E1' E2'.
  End _ProdLebSpec.
  Lemma leb_le : forall x y, P.leb x y = true <-> P.le x y.
  Proof.
    intros [x1 x2] [y1 y2].
    pose proof (E1'.leb_le x1 y1); pose proof (E2'.leb_le x2 y2).
    pose proof (E1'.eqb_eq x1 y1).
    cbv in *; t.
  Qed.
End ProdLebSpec.

Module ProdLtbSpec (E1 : Typ) (E2 : Typ) (E1e : HasEq E1) (E2e : HasEq E2) (E1Lt : HasLt E1) (E2Lt : HasLt E2) (E1Eqb : HasEqb E1) (E1Ltb : HasLtb E1) (E2Ltb : HasLtb E2) (E1s : LtbSpec E1 E1Lt E1Ltb) (E2s : LtbSpec E2 E2Lt E2Ltb) (E1s' : EqbSpec E1 E1e E1Eqb).
  Module Import _ProdLtbSpec.
    Module E1' := E1 <+ E1e <+ E1Lt <+ E1Eqb <+ E1Ltb <+ E1s <+ E1s'.
    Module E2' := E2 <+ E2e <+ E2Lt <+ E2Ltb <+ E2s.
    Module P := ProdHasLt E1' E2' <+ ProdHasLtb E1' E2' E1' E1' E2'.
  End _ProdLtbSpec.
  Lemma ltb_lt : forall x y, P.ltb x y = true <-> P.lt x y.
  Proof.
    intros [x1 x2] [y1 y2].
    pose proof (E1'.ltb_lt x1 y1); pose proof (E2'.ltb_lt x2 y2).
    pose proof (E1'.eqb_eq x1 y1).
    cbv in *; t.
  Qed.
End ProdLtbSpec.

Local Coercion is_true : bool >-> Sortclass.

Module ProdLebIsTotal (E1 : TotalOrderBool) (E2 : LeBool) (E2Total : LebIsTotal E2).
  Module Import _ProdLebIsTotal.
    Module P := ProdHasLeb E1 E2 E1 E1 E2.
  End _ProdLebIsTotal.
  Local Infix "<=?" := P.leb (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof.
    intros [x1 x2] [y1 y2].
    pose proof (E1.leb_total x1 y1).
    pose proof (E2Total.leb_total x2 y2).
    pose proof (E1.leb_ltbeqb x1 y1).
    pose proof (E1.leb_ltbeqb y1 x1).
    pose proof ((_ : Symmetric E1.eqb) x1 y1).
    pose proof ((_ : Symmetric E1.eqb) y1 x1).
    cbv in *.
    t.
  Qed.
End ProdLebIsTotal.

Module ProdLebIsTransitive (E1 : TotalOrderBool) (E2 : LeBool) (E2T : LebIsTransitive E2).
  Module Import _ProdLebIsTransitive.
    Module E1' := E1 <+ IsEqbFacts <+ TransitiveLeBool_of_TotalOrderBool.
    Module P := ProdHasLeb E1' E2 E1' E1' E2.
  End _ProdLebIsTransitive.
  Lemma leb_trans : Transitive P.leb.
  Proof.
    intros [x1 x2] [y1 y2] [z1 z2].
    pose proof (@E1'.leb_trans x1 y1 z1).
    pose proof (@E2T.leb_trans x2 y2 z2).
    pose proof (E1.leb_ltbeqb x1 y1).
    pose proof (E1.leb_ltbeqb y1 z1).
    pose proof (E1.leb_ltbeqb x1 z1).
    pose proof ((_ : Transitive E1.ltb) y1 z1 y1).
    cbv in *.
    t.
    all: pose proof E1.ltb_compat; pose proof E1.eqb_equiv.
    all: pose proof E1'.eqb_Proper.
    all: destruct E1.ltb_strorder.
    all: rewrite ?E1.leb_ltbeqb in *.
    all: repeat first [ progress cbn in *
                      | match goal with
                        | [ H : ?x = true |- _ ] => rewrite H in *
                        | [ H : ?x = false |- _ ] => rewrite H in *
                        | [ H : ?x = ?x |- _ ] => clear H
                        end ].
    all: fold_is_true; setoid_subst_relb E1.eqb.
    all: exfalso; t.
  Qed.
End ProdLebIsTransitive.

Module ProdLebIsTransitive_of_TotalOrderBool (E1 : TotalOrderBool) (E2 : TotalOrderBool).
  Module Import _ProdLebIsTransitive_of_TotalOrderBool.
    Module E2' := E2 <+ TransitiveLeBool_of_TotalOrderBool.
  End _ProdLebIsTransitive_of_TotalOrderBool.
  Include ProdLebIsTransitive E1 E2' E2'.
End ProdLebIsTransitive_of_TotalOrderBool.

Module Type ProdIsStrOrderBool (E1 : StrOrderBool) (E2 : StrOrderBool).
  Module Import _ProdIsStrOrderBool.
    Module E1' := E1 <+ IsEqbFacts.
    Module P := ProdHasEqb E1 E2 E1 E2 <+ ProdHasLtb E1 E2 E1 E1 E2.
  End _ProdIsStrOrderBool.
  Global Instance ltb_strorder : StrictOrder P.ltb | 10.
  Proof.
    destruct E1.ltb_strorder, E1.eqb_equiv; hnf in *.
    destruct E2.ltb_strorder; hnf in *.
    pose proof E1.ltb_compat.
    split; cbv; t.
    all: fold_is_true; setoid_subst_relb E1.eqb; t.
    all: firstorder congruence.
  Qed.
  Global Instance ltb_compat : Proper (P.eqb==>P.eqb==>eq) P.ltb | 10.
  Proof.
    destruct E1.eqb_equiv; hnf in *.
    pose proof E1.ltb_compat.
    pose proof E2.ltb_compat.
    cbv; t.
    all: fold_is_true; setoid_subst_relb E1.eqb; t.
    cbv in *.
    match goal with
    | [ H : context[eq] |- _ ] => now (erewrite <- H + erewrite H); t
    end.
  Qed.
End ProdIsStrOrderBool.

Module ProdLebIsLtbEqb (E1 : TotalOrderBool) (E2 : EqLtLeBool) (E2s : LebIsLtbEqb E2).
  Module Import _ProdLebIsLtbEqb.
    Module P := ProdHasEqb E1 E2 E1 E2 <+ ProdHasLtb E1 E2 E1 E1 E2 <+ ProdHasLeb E1 E2 E1 E1 E2.
  End _ProdLebIsLtbEqb.
  Lemma leb_ltbeqb : forall x y, (P.leb x y = (P.ltb x y || P.eqb x y))%bool.
  Proof.
    intros [x1 x2] [y1 y2].
    pose proof (E1.leb_ltbeqb x1 y1).
    pose proof (E2s.leb_ltbeqb x2 y2).
    destruct E1.ltb_strorder.
    cbv in *.
    generalize dependent (E1.leb x1 y1); intros.
    generalize dependent (E2.leb x2 y2); intros.
    destruct E1.eqb_equiv; hnf in *.
    pose proof E1.ltb_compat.
    t.
    all: fold_is_true; setoid_subst_relb E1.eqb.
    exfalso; eauto.
  Qed.
End ProdLebIsLtbEqb.

Module ProdUsualIsStrOrder (E1 : UsualStrOrder) (E2 : UsualStrOrder).
  Module Import _ProdUsualIsStrOrder.
    Module P := ProdHasLt E1 E2.
  End _ProdUsualIsStrOrder.
  Global Instance lt_strorder : StrictOrder P.lt | 10.
  Proof.
    destruct E1.lt_strorder, E2.lt_strorder; hnf in *.
    split; cbv; t.
  Qed.
  Global Instance lt_compat : Proper (eq==>eq==>iff) P.lt | 10.
  Proof. repeat intro; subst; reflexivity. Qed.
End ProdUsualIsStrOrder.

Module ProdUsualLeIsLtEq (E1 : UsualEqLtLe) (E2 : UsualEqLtLe) (E1s : LeIsLtEq E1) (E2s : LeIsLtEq E2) (E1IsStrOrder : IsStrOrder E1).
  Module Import _ProdUsualLeIsLtEq.
    Module P := ProdHasLe E1 E2 <+ ProdHasLt E1 E2.
  End _ProdUsualLeIsLtEq.
  Local Infix "<=" := P.le.
  Local Infix "<" := P.lt.
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof.
    destruct E1IsStrOrder.lt_strorder; hnf in *.
    intros [x1 x2] [y1 y2].
    pose proof (E1s.le_lteq x1 y1).
    pose proof (E2s.le_lteq x2 y2).
    cbv; t.
  Qed.
End ProdUsualLeIsLtEq.

Module ProdUsualCmpSpec (E1 : UsualEqLt) (E2 : UsualEqLt) (E1c : HasCompare E1) (E2c : HasCompare E2).
  Module Import _ProdUsualCmpSpec.
    Module P := ProdHasLt E1 E2 <+ ProdHasCmp E1 E2 E1c E2c.
  End _ProdUsualCmpSpec.
  Local Infix "<" := P.lt.
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) (P.compare x y).
  Proof.
    intros [x1 x2] [y1 y2].
    cbv.
    destruct (E1c.compare_spec x1 y1), (E2c.compare_spec x2 y2); constructor.
    all: subst; eauto.
  Qed.
End ProdUsualCmpSpec.

Module ProdUsualLtIsTotal (E1 : UsualEqLt) (E2 : UsualEqLt) (E1s : LtIsTotal E1) (E2s : LtIsTotal E2).
  Module Import _ProdUsualLtIsTotal.
    Module P := ProdHasLt E1 E2.
  End _ProdUsualLtIsTotal.
  Local Infix "<" := P.lt.
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof.
    intros [x1 x2] [y1 y2].
    pose proof (E1s.lt_total x1 y1).
    pose proof (E2s.lt_total x2 y2).
    cbv in *; t.
  Qed.
End ProdUsualLtIsTotal.

Module ProdEqLt (E1 : EqLt) (E2 : EqLt) <: EqLt := ProdEq E1 E2 <+ ProdHasLt E1 E2.
Module ProdEqLe (E1 : EqLe) (E2 : EqLe) <: EqLe := ProdEq E1 E2 <+ ProdHasLe E1 E2.
Module ProdEqLtLe (E1 : EqLtLe) (E2 : EqLtLe) <: EqLtLe := ProdEq E1 E2 <+ ProdHasLt E1 E2 <+ ProdHasLe E1 E2.
Module ProdEqLt' (E1 : EqLt) (E2 : EqLt) <: EqLt' := ProdEq E1 E2 <+ ProdHasLt E1 E2 <+ EqLtNotation.
Module ProdEqLe' (E1 : EqLe) (E2 : EqLe) <: EqLe' := ProdEq E1 E2 <+ ProdHasLe E1 E2 <+ EqLeNotation.
Module ProdEqLtLe' (E1 : EqLtLe) (E2 : EqLtLe) <: EqLtLe' := ProdEq E1 E2 <+ ProdHasLt E1 E2 <+ ProdHasLe E1 E2 <+ EqLtLeNotation.
Module ProdStrOrder (E1 : StrOrder) (E2 : StrOrder) <: StrOrder := ProdEqualityType E1 E2 <+ ProdHasLt E1 E2 <+ ProdIsStrOrder E1 E2.
Module ProdStrOrder' (E1 : StrOrder) (E2 : StrOrder) <: StrOrder' := ProdStrOrder E1 E2 <+ EqLtNotation.
Module ProdHasCompare (E1 : EqLt) (E2 : EqLt) (E1c : HasCompare E1) (E2c : HasCompare E2) (E1e : IsEq E1) := ProdHasCmp E1 E2 E1c E2c <+ ProdCmpSpec E1 E2 E1c E2c E1e.
Module ProdDecStrOrder (E1 : DecStrOrder) (E2 : DecStrOrder) <: DecStrOrder := ProdStrOrder E1 E2 <+ ProdHasCompare E1 E2 E1 E2 E1.
Module ProdDecStrOrder' (E1 : DecStrOrder) (E2 : DecStrOrder) <: DecStrOrder' := ProdDecStrOrder E1 E2 <+ EqLtNotation <+ CmpNotation.
Module ProdOrderedType (E1 : OrderedType) (E2 : OrderedType) <: OrderedType := ProdDecStrOrder E1 E2 <+ ProdHasEqDec E1 E2 E1 E2.
Module ProdOrderedType' (E1 : OrderedType') (E2 : OrderedType') <: OrderedType' := ProdOrderedType E1 E2 <+ EqLtNotation <+ CmpNotation.
Module ProdOrderedTypeFull (E1 : OrderedTypeFull) (E2 : OrderedTypeFull) <: OrderedTypeFull := ProdOrderedType E1 E2 <+ ProdHasLe E1 E2 <+ ProdLeIsLtEq E1 E2 E1 E2 E1 E1.
Module ProdOrderedTypeFull' (E1 : OrderedTypeFull') (E2 : OrderedTypeFull') <: OrderedTypeFull' := ProdOrderedTypeFull E1 E2 <+ EqLtLeNotation <+ CmpNotation.

Module ProdUsualEqLt (E1 : UsualEqLt) (E2 : UsualEqLt) <: UsualEqLt := ProdUsualEq E1 E2 <+ ProdHasLt E1 E2.
Module ProdUsualEqLe (E1 : UsualEqLe) (E2 : UsualEqLe) <: UsualEqLe := ProdUsualEq E1 E2 <+ ProdHasLe E1 E2.
Module ProdUsualEqLtLe (E1 : UsualEqLtLe) (E2 : UsualEqLtLe) <: UsualEqLtLe := ProdUsualEq E1 E2 <+ ProdHasLt E1 E2 <+ ProdHasLe E1 E2.

Module ProdUsualStrOrder (E1 : UsualStrOrder) (E2 : UsualStrOrder) <: UsualStrOrder := ProdUsualEqualityType E1 E2 <+ ProdHasLt E1 E2 <+ ProdUsualIsStrOrder E1 E2.

Module ProdUsualHasCompare (E1 : UsualEqLt) (E2 : UsualEqLt) (E1c : HasCompare E1) (E2c : HasCompare E2) := ProdHasCmp E1 E2 E1c E2c <+ ProdUsualCmpSpec E1 E2 E1c E2c.

Module ProdUsualDecStrOrder (E1 : UsualDecStrOrder) (E2 : UsualDecStrOrder) <: UsualDecStrOrder := ProdUsualStrOrder E1 E2 <+ ProdUsualHasCompare E1 E2 E1 E2.
Module ProdUsualOrderedType (E1 : UsualOrderedType) (E2 : UsualOrderedType) <: UsualOrderedType := ProdUsualDecStrOrder E1 E2 <+ ProdUsualHasEqDec E1 E2 E1 E2.
Module ProdUsualOrderedTypeFull (E1 : UsualOrderedTypeFull) (E2 : UsualOrderedTypeFull) <: UsualOrderedTypeFull := ProdUsualOrderedType E1 E2 <+ ProdHasLe E1 E2 <+ ProdUsualLeIsLtEq E1 E2 E1 E2 E1.

Module ProdUsualStrOrder' (E1 : UsualStrOrder) (E2 : UsualStrOrder) <: UsualStrOrder' := ProdUsualStrOrder E1 E2 <+ LtNotation.
Module ProdUsualDecStrOrder' (E1 : UsualDecStrOrder) (E2 : UsualDecStrOrder) <: UsualDecStrOrder' := ProdUsualDecStrOrder E1 E2 <+ LtNotation.
Module ProdUsualOrderedType' (E1 : UsualOrderedType) (E2 : UsualOrderedType) <: UsualOrderedType' := ProdUsualOrderedType E1 E2 <+ LtNotation.
Module ProdUsualOrderedTypeFull' (E1 : UsualOrderedTypeFull) (E2 : UsualOrderedTypeFull) <: UsualOrderedTypeFull' := ProdUsualOrderedTypeFull E1 E2 <+ LtLeNotation.

Module ProdTotalOrder (E1 : TotalOrder) (E2 : TotalOrder) <: TotalOrder := ProdStrOrder E1 E2 <+ ProdHasLe E1 E2 <+ ProdLeIsLtEq E1 E2 E1 E2 E1 E1 <+ ProdLtIsTotal E1 E2 E1 E2.
Module ProdUsualTotalOrder (E1 : UsualTotalOrder) (E2 : UsualTotalOrder) <: UsualTotalOrder
:= ProdUsualStrOrder E1 E2 <+ ProdHasLe E1 E2 <+ ProdUsualLeIsLtEq E1 E2 E1 E2 E1 <+ ProdUsualLtIsTotal E1 E2 E1 E2.

Module ProdTotalOrder' (E1 : TotalOrder) (E2 : TotalOrder) <: TotalOrder' := ProdTotalOrder E1 E2 <+ EqLtLeNotation.
Module ProdUsualTotalOrder' (E1 : UsualTotalOrder) (E2 : UsualTotalOrder) <: UsualTotalOrder' := ProdUsualTotalOrder E1 E2 <+ LtLeNotation.

Module ProdOrderedTypeOrig (E1 : MiniOrderedType) (E2 : MiniOrderedType) <: OrderedTypeOrig.
  Module Import _ProdOrderedTypeOrig.
    Module E1' := OT_of_Orig E1.
    Module E2' := OT_of_Orig E2.
    Module P := ProdOrderedType E1' E2'.
  End _ProdOrderedTypeOrig.
  Include OT_of_New P.
End ProdOrderedTypeOrig.
Module ProdMiniOrderedType (E1 : MiniOrderedType) (E2 : MiniOrderedType) <: MiniOrderedType := ProdOrderedTypeOrig E1 E2.
Module ProdUsualOrderedTypeOrig (E1 : UsualMiniOrderedType) (E2 : UsualMiniOrderedType) <: UsualOrderedTypeOrig.
  Module Import _ProdUsualOrderedTypeOrig.
    Module E1' := UsualOT_of_UsualOrig E1.
    Module E2' := UsualOT_of_UsualOrig E2.
    Module P := ProdUsualOrderedType E1' E2'.
  End _ProdUsualOrderedTypeOrig.
  Include OT_of_New P.
End ProdUsualOrderedTypeOrig.
Module ProdUsualMiniOrderedType (E1 : UsualMiniOrderedType) (E2 : UsualMiniOrderedType) <: UsualMiniOrderedType := ProdUsualOrderedTypeOrig E1 E2.

(* TODO: more precise module argument typing? *)
Module ProdIsStrOrderOrig (E1 : MiniOrderedType) (E2 : MiniOrderedType).
  Module Import _ProdIsStrOrderOrig.
    Module P := ProdOrderedTypeOrig E1 E2.
  End _ProdIsStrOrderOrig.
  Definition lt_trans := P.lt_trans.
  Definition lt_not_eq := P.lt_not_eq.
End ProdIsStrOrderOrig.
(* TODO: more precise module argument typing? *)
Module ProdHasCompareOrig (E1 : MiniOrderedType) (E2 : MiniOrderedType).
  Module Import _ProdHasCompareOrig.
    Module P := ProdOrderedTypeOrig E1 E2.
  End _ProdHasCompareOrig.
  Definition compare := P.compare.
End ProdHasCompareOrig.
(* TODO: more precise module argument typing? *)
Module ProdUsualIsStrOrderOrig (E1 : UsualMiniOrderedType) (E2 : UsualMiniOrderedType).
  Module Import _ProdUsualIsStrOrderOrig.
    Module P := ProdUsualOrderedTypeOrig E1 E2.
  End _ProdUsualIsStrOrderOrig.
  Definition lt_trans := P.lt_trans.
  Definition lt_not_eq := P.lt_not_eq.
End ProdUsualIsStrOrderOrig.
(* TODO: more precise module argument typing? *)
Module ProdUsualHasCompareOrig (E1 : UsualMiniOrderedType) (E2 : UsualMiniOrderedType).
  Module Import _ProdUsualHasCompareOrig.
    Module P := ProdUsualOrderedTypeOrig E1 E2.
  End _ProdUsualHasCompareOrig.
  Definition compare := P.compare.
End ProdUsualHasCompareOrig.

Module ProdLeBool (E1 : EqLeBool) (E2 : LeBool) <: LeBool := ProdTyp E1 E2 <+ ProdHasLeb E1 E2 E1 E1 E2.
Module ProdLtBool (E1 : EqLtBool) (E2 : LtBool) <: LtBool := ProdTyp E1 E2 <+ ProdHasLtb E1 E2 E1 E1 E2.
Module ProdLeBool' (E1 : EqLeBool) (E2 : LeBool) <: LeBool' := ProdLeBool E1 E2 <+ LebNotation.
Module ProdLtBool' (E1 : EqLtBool) (E2 : LtBool) <: LtBool' := ProdLtBool E1 E2 <+ LtbNotation.
Module ProdEqLeBool (E1 : EqLeBool) (E2 : EqLeBool) <: EqLeBool := ProdTyp E1 E2 <+ ProdHasEqb E1 E2 E1 E2 <+ ProdHasLeb E1 E2 E1 E1 E2.
Module ProdEqLtBool (E1 : EqLtBool) (E2 : EqLtBool) <: EqLtBool := ProdTyp E1 E2 <+ ProdHasEqb E1 E2 E1 E2 <+ ProdHasLtb E1 E2 E1 E1 E2.
Module ProdEqLeBool' (E1 : EqLeBool) (E2 : EqLeBool) <: EqLeBool' := ProdEqLeBool E1 E2 <+ EqbNotation <+ LebNotation.
Module ProdEqLtBool' (E1 : EqLtBool) (E2 : EqLtBool) <: EqLtBool' := ProdEqLtBool E1 E2 <+ EqbNotation <+ LtbNotation.
Module ProdEqLtLeBool (E1 : EqLtLeBool) (E2 : EqLtLeBool) <: EqLtLeBool := ProdTyp E1 E2 <+ ProdHasEqb E1 E2 E1 E2 <+ ProdHasLtb E1 E2 E1 E1 E2 <+ ProdHasLeb E1 E2 E1 E1 E2.
Module ProdEqLtLeBool' (E1 : EqLtLeBool) (E2 : EqLtLeBool) <: EqLtLeBool' := ProdEqLtLeBool E1 E2 <+ EqbNotation <+ LtbNotation <+ LebNotation.

Module ProdTotalLeBool (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalLeBool := ProdLeBool E1 E2 <+ ProdLebIsTotal E1 E2 E2.
Module ProdTotalLeBool' (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalLeBool' := ProdLeBool' E1 E2 <+ ProdLebIsTotal E1 E2 E2.
Module ProdTotalEqLeBool (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalEqLeBool := ProdEqLeBool E1 E2 <+ ProdLebIsTotal E1 E2 E2.
Module ProdTotalEqLeBool' (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalEqLeBool' := ProdEqLeBool' E1 E2 <+ ProdLebIsTotal E1 E2 E2.
Module ProdTotalEqLtLeBool (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalEqLtLeBool := ProdEqLtLeBool E1 E2 <+ ProdLebIsTotal E1 E2 E2.
Module ProdTotalEqLtLeBool' (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalEqLtLeBool' := ProdEqLtLeBool' E1 E2 <+ ProdLebIsTotal E1 E2 E2.

Module ProdTotalTransitiveLeBool (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalTransitiveLeBool := ProdTotalLeBool E1 E2 <+ ProdLebIsTransitive_of_TotalOrderBool E1 E2.
Module ProdTotalTransitiveLeBool' (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalTransitiveLeBool' := ProdTotalLeBool' E1 E2 <+ ProdLebIsTransitive_of_TotalOrderBool E1 E2.
Module ProdTotalTransitiveEqLeBool (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalTransitiveEqLeBool := ProdTotalEqLeBool E1 E2 <+ ProdLebIsTransitive_of_TotalOrderBool E1 E2.
Module ProdTotalTransitiveEqLeBool' (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalTransitiveEqLeBool' := ProdTotalEqLeBool' E1 E2 <+ ProdLebIsTransitive_of_TotalOrderBool E1 E2.
Module ProdTotalTransitiveEqLtLeBool (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalTransitiveEqLtLeBool := ProdTotalEqLtLeBool E1 E2 <+ ProdLebIsTransitive_of_TotalOrderBool E1 E2.
Module ProdTotalTransitiveEqLtLeBool' (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalTransitiveEqLtLeBool' := ProdTotalEqLtLeBool' E1 E2 <+ ProdLebIsTransitive_of_TotalOrderBool E1 E2.

Module ProdStrOrderBool (E1 : StrOrderBool) (E2 : StrOrderBool) <: StrOrderBool := ProdEqbType E1 E2 <+ ProdHasLtb E1 E2 E1 E1 E2 <+ ProdIsStrOrderBool E1 E2.
Module ProdStrOrderBool' (E1 : StrOrderBool) (E2 : StrOrderBool) <: StrOrderBool' := ProdStrOrderBool E1 E2 <+ EqLtBoolNotation.

Module ProdTotalOrderBool (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalOrderBool := ProdStrOrderBool E1 E2 <+ ProdHasLeb E1 E2 E1 E1 E2 <+ ProdLebIsLtbEqb E1 E2 E2 <+ ProdLebIsTotal E1 E2 E2.
Module ProdTotalOrderBool' (E1 : TotalOrderBool) (E2 : TotalOrderBool) <: TotalOrderBool' := ProdTotalOrderBool E1 E2 <+ EqLtLeBoolNotation.

Module ProdHasBoolOrdFuns (E1 : Typ) (E2 : Typ) (F1 : HasBoolOrdFuns E1) (F2 : HasBoolOrdFuns E2) := ProdHasEqb E1 E2 F1 F2 <+ ProdHasLtb E1 E2 F1 F1 F2 <+ ProdHasLeb E1 E2 F1 F1 F2.

Module ProdHasBoolOrdFuns' (E1 : Typ) (E2 : Typ) (F1 : HasBoolOrdFuns E1) (F2 : HasBoolOrdFuns E2) := ProdHasBoolOrdFuns E1 E2 F1 F2 <+ ProdEqbNotation E1 E2 F1 F2 <+ ProdLtbNotation E1 E2 F1 F1 F2 <+ ProdLebNotation E1 E2 F1 F1 F2.

Module ProdBoolOrdSpecs (O1 : EqLtLe) (O2 : EqLtLe) (F1 : HasBoolOrdFuns O1) (F2 : HasBoolOrdFuns O2) (S1 : BoolOrdSpecs O1 F1) (S2 : BoolOrdSpecs O2 F2) := ProdEqbSpec O1 O2 O1 O2 F1 F2 S1 S2 <+ ProdLtbSpec O1 O2 O1 O2 O1 O2 F1 F1 F2 S1 S2 S1 <+ ProdLebSpec O1 O2 O1 O2 O1 O2 F1 F1 F2 S1 S2 S1.

Module ProdOrderFunctions (O1 : EqLtLe) (O2 : EqLtLe) (F1 : OrderFunctions O1) (F2 : OrderFunctions O2) (O1e : IsEq O1) := ProdHasCompare O1 O2 F1 F2 O1e <+ ProdHasBoolOrdFuns O1 O2 F1 F2 <+ ProdBoolOrdSpecs O1 O2 F1 F2 F1 F2.

Module ProdOrderFunctions' (O1 : EqLtLe) (O2 : EqLtLe) (F1 : OrderFunctions O1) (F2 : OrderFunctions O2) (O1e : IsEq O1) := ProdHasCompare O1 O2 F1 F2 O1e <+ ProdCmpNotation O1 O2 F1 F2 <+ ProdHasBoolOrdFuns' O1 O2 F1 F2 <+ ProdBoolOrdSpecs O1 O2 F1 F2 F1 F2.
