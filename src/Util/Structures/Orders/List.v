Require Import Coq.Lists.List Coq.Lists.SetoidList.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.List.
Require Import Crypto.Util.Structures.Orders.
Import ListNotations.
Local Open Scope list_scope.

Local Set Implicit Arguments.

Module ListHasLe (E : EqLe).
  Fixpoint le (x y : list E.t) : Prop
    := match x, y with
       | nil, _ => True
       | _, nil => False
       | x :: xs, y :: ys => E.le x y /\ (~E.eq x y \/ le xs ys)
       end.
End ListHasLe.

Module ListHasLt (E : EqLt).
  (** There are two potential versions of [lt]: We could prefer
      shorter-length lists, or we could prefer lists with lesser
      elements in the first place.  We choose the latter for
      compatibility with defining tries. *)
  Fixpoint lt (x y : list E.t) : Prop
    := match x, y with
       | nil, _::_ => True
       | nil, nil => False
       | _, nil => False
       | x :: xs, y :: ys => E.lt x y \/ (E.eq x y /\ lt xs ys)
       end.
End ListHasLt.

Local Ltac setoid_subst_rel R :=
  repeat match goal with
         | [ H : R ?x ?y |- _ ]
           => first [ is_var x; rewrite H in *; clear x H
                    | is_var y; rewrite <- H in *; clear y H ]
         | [ H : is_true (R ?x ?y) |- _ ]
           => first [ is_var x; rewrite H in *; clear x H
                    | is_var y; rewrite <- H in *; clear y H ]
         end.

Local Ltac fold_is_true :=
  repeat match goal with
         | [ H : ?x = true |- _ ] => change (is_true x) in H
         end.

Local Ltac t :=
  repeat first [ split
               | intro
               | progress subst
               | assumption
               | progress cbv [complement is_true] in *
               | progress cbn in *
               | congruence
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
               | progress intuition eauto 2
               | match goal with
                 | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
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

Module ListIsStrOrder (E : StrOrder).
  Module Import _ListIsStrOrder.
    Module L := ListHasEq E <+ ListHasLt E.
  End _ListIsStrOrder.
  Global Instance lt_strorder : StrictOrder L.lt | 10.
  Proof.
    destruct E.lt_strorder, E.eq_equiv; hnf in *.
    pose proof E.lt_compat.
    split;
      intro xs; induction xs as [|x xs IH]; hnf; cbn.
    all: t; setoid_subst_rel E.eq; t.
  Qed.
  Global Instance lt_compat : Proper (L.eq==>L.eq==>iff) L.lt | 10.
  Proof.
    destruct E.eq_equiv; hnf in *.
    pose proof E.lt_compat.
    induction 1; hnf; cbn; destruct 1; try reflexivity.
    t; setoid_subst_rel E.eq; t; hnf in *.
    all: match goal with
         | [ H : context[iff] |- _ ] => now (rewrite <- H + rewrite H); t
         end.
  Qed.
End ListIsStrOrder.

Module ListLeIsLtEq (E : EqLtLe') (Es : LeIsLtEq E) (Es' : IsStrOrder E) (Es'' : IsEq E).
  Module Import _ListLeIsLtEq.
    Module L := ListHasEq E <+ ListHasLt E <+ ListHasLe E.
  End _ListLeIsLtEq.
  Local Infix "<=" := L.le.
  Local Infix "<" := L.lt.
  Local Infix "==" := L.eq (at level 70).
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x == y.
  Proof.
    destruct Es''.eq_equiv.
    destruct Es'.lt_strorder.
    hnf in *.
    pose proof Es'.lt_compat.
    induction x as [|x xs IH], y as [|y ys]; cbn.
    all: rewrite ?Es.le_lteq in *.
    all: repeat first [ progress invlist L.eq
                      | match goal with
                        | [ H : ?R _ _, H' : context[?R _ _ <-> _] |- _ ]
                          => rewrite H' in H
                        | [ H' : context[?R _ _ <-> _] |- context[?R _ _] ]
                          => rewrite H'
                        end
                      | progress t
                      | now constructor; t; setoid_subst_rel E.eq; t ].
  Qed.
End ListLeIsLtEq.

Module ListHasCmp (E : Typ) (Ec : HasCmp E).
  Fixpoint compare (xs ys : list E.t) : comparison
    := match xs, ys with
       | [], [] => Eq
       | [], _ => Lt
       | _, [] => Gt
       | x :: xs, y :: ys
         => match Ec.compare x y with
            | Lt => Lt
            | Gt => Gt
            | Eq => compare xs ys
            end
       end.
End ListHasCmp.

Module ListCmpNotation (E : Typ) (Ec : HasCmp E).
  Module Import _ListCmpNotation.
    Module T := ListTyp E.
    Module C := ListHasCmp E Ec.
  End _ListCmpNotation.
  Include CmpNotation T C.
End ListCmpNotation.

Module ListCmpSpec (E : EqLt) (Ec : HasCompare E) (Es : IsEq E).
  Module Import _ListCmpSpec.
    Module L := ListHasEq E <+ ListHasLt E <+ ListHasCmp E Ec.
  End _ListCmpSpec.
  Local Infix "<" := L.lt.
  Local Infix "==" := L.eq (at level 70).
  Lemma compare_spec : forall x y, CompareSpec (x == y) (x < y) (y < x) (L.compare x y).
  Proof.
    induction x as [|x xs IH], y as [|y ys]; cbn in *; try (specialize (IH ys); inversion IH); let H := fresh in try (pose proof (Ec.compare_spec x y); inversion H).
    all: try solve [ constructor; constructor ].
    all: t.
  Qed.
End ListCmpSpec.

Module ListLtIsTotal (E : EqLt) (Es : LtIsTotal E).
  Module Import _ListLtIsTotal.
    Module L := ListHasEq E <+ ListHasLt E.
  End _ListLtIsTotal.
  Local Infix "<" := L.lt.
  Local Infix "==" := L.eq (at level 70).
  Lemma lt_total : forall x y, x < y \/ x == y \/ y < x.
  Proof.
    induction x as [|x xs IH], y as [|y ys]; try specialize (IH ys);
      try (pose proof (Es.lt_total x y); pose proof (Es.lt_total y x)).
    all: t.
  Qed.
End ListLtIsTotal.

Module ListHasLeb (E : Typ) (EEqb : HasEqb E) (ELeb : HasLeb E).
  Fixpoint leb (x y : list E.t) : bool
    := match x, y with
       | nil, _ => true
       | _, nil => false
       | x :: xs, y :: ys => ELeb.leb x y && (negb (EEqb.eqb x y) || leb xs ys)
       end%bool.
End ListHasLeb.

Module ListHasLtb (E : Typ) (EEqb : HasEqb E) (ELtb : HasLtb E).
  Fixpoint ltb (x y : list E.t) : bool
    := match x, y with
       | nil, _::_ => true
       | nil, nil => false
       | _, nil => false
       | x :: xs, y :: ys => ELtb.ltb x y || (EEqb.eqb x y && ltb xs ys)
       end%bool.
End ListHasLtb.

Module ListLebNotation (E : Typ) (EEqb : HasEqb E) (ELeb : HasLeb E).
  Module Import _ListLebNotation.
    Module T := ListTyp E.
    Module E' := ListHasLeb E EEqb ELeb.
  End _ListLebNotation.
  Include LebNotation T E'.
End ListLebNotation.

Module ListLtbNotation (E : Typ) (EEqb : HasEqb E) (ELtb : HasLtb E).
  Module Import _ListLtbNotation.
    Module T := ListTyp E.
    Module E' := ListHasLtb E EEqb ELtb.
  End _ListLtbNotation.
  Include LtbNotation T E'.
End ListLtbNotation.

Module ListLebSpec (E : Typ) (Ee : HasEq E) (ELe : HasLe E) (EEqb : HasEqb E) (ELeb : HasLeb E) (Es : LebSpec E ELe ELeb) (Es' : EqbSpec E Ee EEqb).
  Module Import _ListLebSpec.
    Module E' := E <+ Ee <+ ELe <+ EEqb <+ ELeb <+ Es <+ Es'.
    Module L := ListHasLe E' <+ ListHasLeb E' E' E'.
  End _ListLebSpec.
  Lemma leb_le : forall x y, L.leb x y = true <-> L.le x y.
  Proof.
    induction x as [|x xs IH], y as [|y ys]; try specialize (IH ys);
      try (pose proof (E'.leb_le x y); pose proof (E'.eqb_eq x y)).
    all: t.
  Qed.
End ListLebSpec.

Module ListLtbSpec (E : Typ) (Ee : HasEq E) (ELt : HasLt E) (EEqb : HasEqb E) (ELtb : HasLtb E) (Es : LtbSpec E ELt ELtb) (Es' : EqbSpec E Ee EEqb).
  Module Import _ListLtbSpec.
    Module E' := E <+ Ee <+ ELt <+ EEqb <+ ELtb <+ Es <+ Es'.
    Module L := ListHasLt E' <+ ListHasLtb E' E' E'.
  End _ListLtbSpec.
  Lemma ltb_lt : forall x y, L.ltb x y = true <-> L.lt x y.
  Proof.
    induction x as [|x xs IH], y as [|y ys]; try specialize (IH ys);
      try (pose proof (E'.ltb_lt x y); pose proof (E'.eqb_eq x y)).
    all: t.
  Qed.
End ListLtbSpec.

Local Coercion is_true : bool >-> Sortclass.

Module ListLebIsTotal (E : TotalOrderBool).
  Module Import _ListLebIsTotal.
    Module L := ListHasLeb E E E.
  End _ListLebIsTotal.
  Local Infix "<=?" := L.leb (at level 70).
  Lemma leb_total : forall x y, (x <=? y) = true \/ (y <=? x) = true.
  Proof.
    induction x as [|x xs IH], y as [|y ys]; try specialize (IH ys);
      try (pose proof (E.leb_total x y); pose proof (E.leb_ltbeqb x y); pose proof (E.leb_ltbeqb y x); pose proof ((_ : Symmetric E.eqb) x y); pose proof ((_ : Symmetric E.eqb) y x)).
    all: t.
  Qed.
End ListLebIsTotal.

Module ListLebIsTransitive (E : TotalOrderBool).
  Module Import _ListLebIsTransitive.
    Module E' := E <+ IsEqbFacts <+ TransitiveLeBool_of_TotalOrderBool.
    Module L := ListHasLeb E E E.
  End _ListLebIsTransitive.
  Lemma leb_trans : Transitive L.leb.
  Proof.
    hnf.
    induction x as [|x xs IH], y as [|y ys], z as [|z zs];
      try (specialize (IH ys zs); pose proof (@E'.leb_trans x y z); pose proof (E.leb_ltbeqb x y); pose proof (E.leb_ltbeqb y z); pose proof (E.leb_ltbeqb x z); pose proof ((_ : Transitive E.ltb) y z y));
      t.
    all: pose proof E.ltb_compat; pose proof E.eqb_equiv.
    all: pose proof E'.eqb_Proper.
    all: destruct E.ltb_strorder.
    all: rewrite ?E.leb_ltbeqb in *.
    all: repeat first [ progress cbn in *
                      | match goal with
                        | [ H : ?x = true |- _ ] => rewrite H in *
                        | [ H : ?x = false |- _ ] => rewrite H in *
                        | [ H : ?x = ?x |- _ ] => clear H
                        end ].
    all: fold_is_true; setoid_subst_rel E.eqb.
    all: exfalso; t.
  Qed.
End ListLebIsTransitive.

Module Type ListIsStrOrderBool (E : StrOrderBool).
  Module Import _ListIsStrOrderBool.
    Module E' := E <+ IsEqbFacts.
    Module L := ListHasEqb E E <+ ListHasLtb E E E.
  End _ListIsStrOrderBool.
  Global Instance ltb_strorder : StrictOrder L.ltb | 10.
  Proof.
    destruct E'.ltb_strorder, E'.eqb_equiv; hnf in *.
    pose proof E'.ltb_compat.
    split;
      intro xs; induction xs as [|x xs IH]; hnf; cbn.
    all: t; fold_is_true; setoid_subst_rel E.eqb; t.
  Qed.
  Global Instance ltb_compat : Proper (L.eqb==>L.eqb==>eq) L.ltb | 10.
  Proof.
    destruct E'.eqb_equiv; hnf in *.
    pose proof E'.ltb_compat.
    induction x as [|x xs IH], y as [|y ys]; try specialize (IH ys); cbn; intros ? [|??] [|??]; cbn in *; try reflexivity; try congruence.
    t; fold_is_true; setoid_subst_rel E.eqb; t; hnf in *.
    match goal with
    | [ H : context[eq] |- _ ] => now (erewrite <- H + erewrite H); t
    end.
  Qed.
End ListIsStrOrderBool.

Module ListLebIsLtbEqb (E : TotalOrderBool).
  Module Import _ListLebIsLtbEqb.
    Module L := ListHasEqb E E <+ ListHasLtb E E E <+ ListHasLeb E E E.
  End _ListLebIsLtbEqb.
  Lemma leb_ltbeqb : forall x y, (L.leb x y = (L.ltb x y || L.eqb x y))%bool.
  Proof.
    pose proof E.ltb_compat.
    destruct E.eqb_equiv; hnf in *.
    destruct E.ltb_strorder.
    induction x as [|x xs IH], y as [|y ys];
      try (specialize (IH ys); pose proof (E.leb_ltbeqb x y));
      try reflexivity.
    cbn; cbv [orb andb negb] in *.
    t.
    fold_is_true; setoid_subst_rel E.eqb.
    cbv -[L.ltb L.leb L.eqb] in *; exfalso.
    intuition eauto.
  Qed.
End ListLebIsLtbEqb.

Module ListUsualIsStrOrder (E : UsualStrOrder).
  Module Import _ListUsualIsStrOrder.
    Module L := ListHasLt E.
  End _ListUsualIsStrOrder.
  Global Instance lt_strorder : StrictOrder L.lt | 10.
  Proof.
    destruct E.lt_strorder; hnf in *.
    split;
      intro xs; induction xs as [|x xs IH]; hnf; cbn.
    all: t.
  Qed.
  Global Instance lt_compat : Proper (eq==>eq==>iff) L.lt | 10.
  Proof. repeat intro; subst; reflexivity. Qed.
End ListUsualIsStrOrder.

Module ListUsualLeIsLtEq (E : UsualEqLtLe) (Es : LeIsLtEq E) (EIsStrOrder : IsStrOrder E).
  Module Import _ListUsualLeIsLtEq.
    Module L := ListHasLe E <+ ListHasLt E.
  End _ListUsualLeIsLtEq.
  Local Infix "<=" := L.le.
  Local Infix "<" := L.lt.
  Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
  Proof.
    destruct (EIsStrOrder.lt_strorder); hnf in *.
    induction x as [|x xs IH], y as [|y ys];
      try (specialize (IH ys); pose proof (Es.le_lteq x y));
      t.
  Qed.
End ListUsualLeIsLtEq.

Module ListUsualCmpSpec (E : UsualEqLt) (Ec : HasCompare E).
  Module Import _ListUsualCmpSpec.
    Module L := ListHasLt E <+ ListHasCmp E Ec.
  End _ListUsualCmpSpec.
  Local Infix "<" := L.lt.
  Lemma compare_spec : forall x y, CompareSpec (x = y) (x < y) (y < x) (L.compare x y).
  Proof.
    induction x as [|x xs IH], y as [|y ys];
      cbn;
      try (specialize (IH ys); destruct IH, (Ec.compare_spec x y));
      t.
  Qed.
End ListUsualCmpSpec.

Module ListUsualLtIsTotal (E : UsualEqLt) (Es : LtIsTotal E).
  Module Import _ListUsualLtIsTotal.
    Module L := ListHasLt E.
  End _ListUsualLtIsTotal.
  Local Infix "<" := L.lt.
  Lemma lt_total : forall x y, x < y \/ x = y \/ y < x.
  Proof.
    induction x as [|x xs IH], y as [|y ys];
      cbn;
      try (specialize (IH ys); pose proof (Es.lt_total x y));
      t.
  Qed.
End ListUsualLtIsTotal.

Module ListEqLt (E : EqLt) <: EqLt := ListEq E <+ ListHasLt E.
Module ListEqLe (E : EqLe) <: EqLe := ListEq E <+ ListHasLe E.
Module ListEqLtLe (E : EqLtLe) <: EqLtLe := ListEq E <+ ListHasLt E <+ ListHasLe E.
Module ListEqLt' (E : EqLt) <: EqLt' := ListEq E <+ ListHasLt E <+ EqLtNotation.
Module ListEqLe' (E : EqLe) <: EqLe' := ListEq E <+ ListHasLe E <+ EqLeNotation.
Module ListEqLtLe' (E : EqLtLe) <: EqLtLe' := ListEq E <+ ListHasLt E <+ ListHasLe E <+ EqLtLeNotation.
Module ListStrOrder (E : StrOrder) <: StrOrder := ListEqualityType E <+ ListHasLt E <+ ListIsStrOrder E.
Module ListStrOrder' (E : StrOrder) <: StrOrder' := ListStrOrder E <+ EqLtNotation.
Module ListHasCompare (E : EqLt) (Ec : HasCompare E) (Es : IsEq E) := ListHasCmp E Ec <+ ListCmpSpec E Ec Es.
Module ListDecStrOrder (E : DecStrOrder) <: DecStrOrder := ListStrOrder E <+ ListHasCompare E E E.
Module ListDecStrOrder' (E : DecStrOrder) <: DecStrOrder' := ListDecStrOrder E <+ EqLtNotation <+ CmpNotation.
Module ListOrderedType (E : OrderedType) <: OrderedType := ListDecStrOrder E <+ ListHasEqDec E E.
Module ListOrderedType' (E : OrderedType') <: OrderedType' := ListOrderedType E <+ EqLtNotation <+ CmpNotation.
Module ListOrderedTypeFull (E : OrderedTypeFull) <: OrderedTypeFull := ListOrderedType E <+ ListHasLe E <+ ListLeIsLtEq E E E E.
Module ListOrderedTypeFull' (E : OrderedTypeFull') <: OrderedTypeFull' := ListOrderedTypeFull E <+ EqLtLeNotation <+ CmpNotation.

Module ListUsualEqLt (E : UsualEqLt) <: UsualEqLt := ListUsualEq E <+ ListHasLt E.
Module ListUsualEqLe (E : UsualEqLe) <: UsualEqLe := ListUsualEq E <+ ListHasLe E.
Module ListUsualEqLtLe (E : UsualEqLtLe) <: UsualEqLtLe := ListUsualEq E <+ ListHasLt E <+ ListHasLe E.

Module ListUsualStrOrder (E : UsualStrOrder) <: UsualStrOrder := ListUsualEqualityType E <+ ListHasLt E <+ ListUsualIsStrOrder E.

Module ListUsualHasCompare (E : UsualEqLt) (Ec : HasCompare E) := ListHasCmp E Ec <+ ListUsualCmpSpec E Ec.

Module ListUsualDecStrOrder (E : UsualDecStrOrder) <: UsualDecStrOrder := ListUsualStrOrder E <+ ListUsualHasCompare E E.
Module ListUsualOrderedType (E : UsualOrderedType) <: UsualOrderedType := ListUsualDecStrOrder E <+ ListUsualHasEqDec E E.
Module ListUsualOrderedTypeFull (E : UsualOrderedTypeFull) <: UsualOrderedTypeFull := ListUsualOrderedType E <+ ListHasLe E <+ ListUsualLeIsLtEq E E E.

Module ListUsualStrOrder' (E : UsualStrOrder) <: UsualStrOrder' := ListUsualStrOrder E <+ LtNotation.
Module ListUsualDecStrOrder' (E : UsualDecStrOrder) <: UsualDecStrOrder' := ListUsualDecStrOrder E <+ LtNotation.
Module ListUsualOrderedType' (E : UsualOrderedType) <: UsualOrderedType' := ListUsualOrderedType E <+ LtNotation.
Module ListUsualOrderedTypeFull' (E : UsualOrderedTypeFull) <: UsualOrderedTypeFull' := ListUsualOrderedTypeFull E <+ LtLeNotation.

Module ListTotalOrder (E : TotalOrder) <: TotalOrder := ListStrOrder E <+ ListHasLe E <+ ListLeIsLtEq E E E E <+ ListLtIsTotal E E.
Module ListUsualTotalOrder (E : UsualTotalOrder) <: UsualTotalOrder
:= ListUsualStrOrder E <+ ListHasLe E <+ ListUsualLeIsLtEq E E E <+ ListUsualLtIsTotal E E.

Module ListTotalOrder' (E : TotalOrder) <: TotalOrder' := ListTotalOrder E <+ EqLtLeNotation.
Module ListUsualTotalOrder' (E : UsualTotalOrder) <: UsualTotalOrder' := ListUsualTotalOrder E <+ LtLeNotation.

Module ListOrderedTypeOrig (E : MiniOrderedType) <: OrderedTypeOrig.
  Module Import _ListOrderedTypeOrig.
    Module E' := OT_of_Orig E.
    Module L := ListOrderedType E'.
  End _ListOrderedTypeOrig.
  Include OT_of_New L.
End ListOrderedTypeOrig.
Module ListMiniOrderedType (E : MiniOrderedType) <: MiniOrderedType := ListOrderedTypeOrig E.
Module ListUsualOrderedTypeOrig (E : UsualMiniOrderedType) <: UsualOrderedTypeOrig.
  Module Import _ListUsualOrderedTypeOrig.
    Module E' := UsualOT_of_UsualOrig E.
    Module L := ListUsualOrderedType E'.
  End _ListUsualOrderedTypeOrig.
  Include OT_of_New L.
End ListUsualOrderedTypeOrig.
Module ListUsualMiniOrderedType (E : UsualMiniOrderedType) <: UsualMiniOrderedType := ListUsualOrderedTypeOrig E.

(* TODO: more precise module argument typing? *)
Module ListIsStrOrderOrig (E : MiniOrderedType).
  Module Import _ListIsStrOrderOrig.
    Module L := ListOrderedTypeOrig E.
  End _ListIsStrOrderOrig.
  Definition lt_trans := L.lt_trans.
  Definition lt_not_eq := L.lt_not_eq.
End ListIsStrOrderOrig.
(* TODO: more precise module argument typing? *)
Module ListHasCompareOrig (E : MiniOrderedType).
  Module Import _ListHasCompareOrig.
    Module L := ListOrderedTypeOrig E.
  End _ListHasCompareOrig.
  Definition compare := L.compare.
End ListHasCompareOrig.
(* TODO: more precise module argument typing? *)
Module ListUsualIsStrOrderOrig (E : UsualMiniOrderedType).
  Module Import _ListUsualIsStrOrderOrig.
    Module L := ListUsualOrderedTypeOrig E.
  End _ListUsualIsStrOrderOrig.
  Definition lt_trans := L.lt_trans.
  Definition lt_not_eq := L.lt_not_eq.
End ListUsualIsStrOrderOrig.
(* TODO: more precise module argument typing? *)
Module ListUsualHasCompareOrig (E : UsualMiniOrderedType).
  Module Import _ListUsualHasCompareOrig.
    Module L := ListUsualOrderedTypeOrig E.
  End _ListUsualHasCompareOrig.
  Definition compare := L.compare.
End ListUsualHasCompareOrig.

Module ListLeBool (E : EqLeBool) <: LeBool := ListTyp E <+ ListHasLeb E E E.
Module ListLtBool (E : EqLtBool) <: LtBool := ListTyp E <+ ListHasLtb E E E.
Module ListLeBool' (E : EqLeBool) <: LeBool' := ListLeBool E <+ LebNotation.
Module ListLtBool' (E : EqLtBool) <: LtBool' := ListLtBool E <+ LtbNotation.
Module ListEqLeBool (E : EqLeBool) <: EqLeBool := ListTyp E <+ ListHasEqb E E <+ ListHasLeb E E E.
Module ListEqLtBool (E : EqLtBool) <: EqLtBool := ListTyp E <+ ListHasEqb E E <+ ListHasLtb E E E.
Module ListEqLeBool' (E : EqLeBool) <: EqLeBool' := ListEqLeBool E <+ EqbNotation <+ LebNotation.
Module ListEqLtBool' (E : EqLtBool) <: EqLtBool' := ListEqLtBool E <+ EqbNotation <+ LtbNotation.
Module ListEqLtLeBool (E : EqLtLeBool) <: EqLtLeBool := ListTyp E <+ ListHasEqb E E <+ ListHasLtb E E E <+ ListHasLeb E E E.
Module ListEqLtLeBool' (E : EqLtLeBool) <: EqLtLeBool' := ListEqLtLeBool E <+ EqbNotation <+ LtbNotation <+ LebNotation.

Module ListTotalLeBool (E : TotalOrderBool) <: TotalLeBool := ListLeBool E <+ ListLebIsTotal E.
Module ListTotalLeBool' (E : TotalOrderBool) <: TotalLeBool' := ListLeBool' E <+ ListLebIsTotal E.
Module ListTotalEqLeBool (E : TotalOrderBool) <: TotalEqLeBool := ListEqLeBool E <+ ListLebIsTotal E.
Module ListTotalEqLeBool' (E : TotalOrderBool) <: TotalEqLeBool' := ListEqLeBool' E <+ ListLebIsTotal E.
Module ListTotalEqLtLeBool (E : TotalOrderBool) <: TotalEqLtLeBool := ListEqLtLeBool E <+ ListLebIsTotal E.
Module ListTotalEqLtLeBool' (E : TotalOrderBool) <: TotalEqLtLeBool' := ListEqLtLeBool' E <+ ListLebIsTotal E.

Module ListTotalTransitiveLeBool (E : TotalOrderBool) <: TotalTransitiveLeBool := ListTotalLeBool E <+ ListLebIsTransitive E.
Module ListTotalTransitiveLeBool' (E : TotalOrderBool) <: TotalTransitiveLeBool' := ListTotalLeBool' E <+ ListLebIsTransitive E.
Module ListTotalTransitiveEqLeBool (E : TotalOrderBool) <: TotalTransitiveEqLeBool := ListTotalEqLeBool E <+ ListLebIsTransitive E.
Module ListTotalTransitiveEqLeBool' (E : TotalOrderBool) <: TotalTransitiveEqLeBool' := ListTotalEqLeBool' E <+ ListLebIsTransitive E.
Module ListTotalTransitiveEqLtLeBool (E : TotalOrderBool) <: TotalTransitiveEqLtLeBool := ListTotalEqLtLeBool E <+ ListLebIsTransitive E.
Module ListTotalTransitiveEqLtLeBool' (E : TotalOrderBool) <: TotalTransitiveEqLtLeBool' := ListTotalEqLtLeBool' E <+ ListLebIsTransitive E.

Module ListStrOrderBool (E : StrOrderBool) <: StrOrderBool := ListEqbType E <+ ListHasLtb E E E <+ ListIsStrOrderBool E.
Module ListStrOrderBool' (E : StrOrderBool) <: StrOrderBool' := ListStrOrderBool E <+ EqLtBoolNotation.

Module ListTotalOrderBool (E : TotalOrderBool) <: TotalOrderBool := ListStrOrderBool E <+ ListHasLeb E E E <+ ListLebIsLtbEqb E <+ ListLebIsTotal E.
Module ListTotalOrderBool' (E : TotalOrderBool) <: TotalOrderBool' := ListTotalOrderBool E <+ EqLtLeBoolNotation.

Module ListHasBoolOrdFuns (E : Typ) (F : HasBoolOrdFuns E) := ListHasEqb E F <+ ListHasLtb E F F <+ ListHasLeb E F F.

Module ListHasBoolOrdFuns' (E : Typ) (F : HasBoolOrdFuns E) := ListHasBoolOrdFuns E F <+ ListEqbNotation E F <+ ListLtbNotation E F F <+ ListLebNotation E F F.

Module ListBoolOrdSpecs (O : EqLtLe) (F : HasBoolOrdFuns O) (S : BoolOrdSpecs O F) := ListEqbSpec O O F S <+ ListLtbSpec O O O F F S S <+ ListLebSpec O O O F F S S.

Module ListOrderFunctions (O : EqLtLe) (F : OrderFunctions O) (Oe : IsEq O) := ListHasCompare O F Oe <+ ListHasBoolOrdFuns O F <+ ListBoolOrdSpecs O F F.

Module ListOrderFunctions' (O : EqLtLe) (F : OrderFunctions O) (Oe : IsEq O) := ListHasCompare O F Oe <+ ListCmpNotation O F <+ ListHasBoolOrdFuns' O F <+ ListBoolOrdSpecs O F F.
