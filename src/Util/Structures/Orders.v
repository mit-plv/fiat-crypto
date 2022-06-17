Require Import Coq.btauto.Btauto.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.

Module Type UsualEqLt := UsualEq <+ HasLt.
Module Type UsualEqLe := UsualEq <+ HasLe.
Module Type UsualEqLtLe := UsualEq <+ HasLt <+ HasLe.

Module Type UsualEqLt' := UsualEqLt <+ EqNotation <+ LtNotation.
Module Type UsualEqLe' := UsualEqLe <+ EqNotation <+ LeNotation.
Module Type UsualEqLtLe' := UsualEqLtLe <+ EqNotation <+ LtNotation <+ LeNotation.

Module Type EqLeBool := Typ <+ HasEqb <+ HasLeb.
Module Type EqLtBool := Typ <+ HasEqb <+ HasLtb.
Module Type EqLtLeBool := Typ <+ HasEqb <+ HasLtb <+ HasLeb.

Module Type EqLtBoolNotation (E:EqLtBool) := EqbNotation E E <+ LtbNotation E E.
Module Type EqLeBoolNotation (E:EqLeBool) := EqbNotation E E <+ LebNotation E E.
Module Type EqLtLeBoolNotation (E:EqLtLeBool) := EqbNotation E E <+ LtbNotation E E <+ LebNotation E E.

Module Type EqLeBool' := EqLeBool <+ EqLeBoolNotation.
Module Type EqLtBool' := EqLtBool <+ EqLtBoolNotation.
Module Type EqLtLeBool' := EqLtLeBool <+ EqLtLeBoolNotation.

Module Type TotalEqLeBool := EqLeBool <+ LebIsTotal.
Module Type TotalEqLtLeBool := EqLtLeBool <+ LebIsTotal.
Module Type TotalEqLeBool' := EqLeBool' <+ LebIsTotal.
Module Type TotalEqLtLeBool' := EqLtLeBool' <+ LebIsTotal.

Module Type TotalTransitiveEqLeBool := TotalEqLeBool <+ LebIsTransitive.
Module Type TotalTransitiveEqLtLeBool := TotalEqLtLeBool <+ LebIsTransitive.
Module Type TotalTransitiveEqLeBool' := TotalEqLeBool' <+ LebIsTransitive.
Module Type TotalTransitiveEqLtLeBool' := TotalEqLtLeBool' <+ LebIsTransitive.

Local Coercion is_true : bool >-> Sortclass.

Module Type IsStrOrderBool (Import E:EqLtBool').
#[global]
  Declare Instance ltb_strorder : StrictOrder ltb.
#[global]
  Declare Instance ltb_compat : Proper (eqb==>eqb==>eq) ltb.
End IsStrOrderBool.

Module Type StrOrderBool := EqbType <+ HasLtb <+ IsStrOrderBool.
Module Type StrOrderBool' := StrOrderBool <+ EqLtBoolNotation.

Module Type LebIsLtbEqb (Import E:EqLtLeBool').
  Axiom leb_ltbeqb : forall x y, ((x <=? y) = ((x <? y) || (x =? y)))%bool.
End LebIsLtbEqb.

Module Type TotalOrderBool := StrOrderBool <+ HasLeb <+ LebIsLtbEqb <+ LebIsTotal.
Module Type TotalOrderBool' := TotalOrderBool <+ EqLtLeBoolNotation.

Module TransitiveLeBool_of_TotalOrderBool (Import T : TotalOrderBool') <: LebIsTransitive T.
  Instance leb_trans : Transitive T.leb | 10.
  Proof.
    intros x y z.
    pose proof (_ : Transitive ltb) as ltb_trans.
    pose proof (_ : Transitive eqb) as eqb_trans.
    pose proof (_ : Symmetric eqb) as eqb_sym.
    pose proof (_ : Reflexive eqb) as eqb_refl.
    pose proof (_ : Irreflexive ltb) as ltb_irr.
    pose proof (fun x y z w H => ltb_compat x y H z w).
    hnf in *.
    cbv [respectful complement is_true] in *.
    specialize_all_ways.
    repeat match goal with
           | [ H : forall x : t, _ |- _ ] => clear H
           end.
    generalize (leb_total x y).
    generalize (leb_total y z).
    generalize (leb_total x z).
    rewrite !leb_ltbeqb, !Bool.orb_true_iff.
    cbv [is_true].
    intros.
    let t :=
    repeat first [ match goal with
                   | [ H : false = true |- _ ] => exfalso; clear -H; congruence
                   | [ H : False |- _ ] => exfalso; exact H
                   | [ H : true = true |- _ ] => clear H
                   | [ H : false = false |- _ ] => clear H
                   | [ H : false = true -> _ |- _ ] => clear H
                   | [ H : _ -> false = true -> _ |- _ ] => clear H
                   | [ H : _ -> true = true |- _ ] => clear H
                   | [ H : _ -> _ -> true = true |- _ ] => clear H
                   | [ H : true = true -> _ |- _ ] => specialize (H eq_refl)
                   | [ H : _ -> true = true -> _ |- _ ] => specialize (fun H' => H H' eq_refl)
                   | [ |- true = true \/ _ ] => left; reflexivity
                   | [ |- false = true \/ _ ] => right
                   | [ |- true = true ] => reflexivity
                   | [ |- false = true ] => exfalso
                   | [ |- ?x = true ] => destruct x
                   | [ |- ?x = true \/ _ ] => destruct x
                   | [ H : context[false = true] |- _ ]
                     => lazymatch type of H with _ \/ _ => idtac end;
                        destruct H
                   | [ H : ?x = true |- _ ] => generalize dependent x; intros; subst
                   | [ H : ?x = true -> false = true |- _ ] => destruct x
                   | [ H : ?x = true -> False |- _ ] => destruct x
                   end ] in
    t; destruct_one_head'_or; t.
  Qed.
End TransitiveLeBool_of_TotalOrderBool.

Require Import Coq.Structures.OrderedType.

Module Type MiniOrderedType := MiniOrderedType.
Module Type OrderedTypeOrig := OrderedType.OrderedType.

Module Type IsStrOrderOrig (Import T : EqLt).
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
End IsStrOrderOrig.
Module Type HasCompareOrig (Import T : EqLt).
  Parameter compare : forall x y : t, Compare lt eq x y.
End HasCompareOrig.

Module Type HasMiniOrderedType (T : EqLt) := Nop <+ IsStrOrderOrig T <+ HasCompareOrig T.

Module Type UsualMiniOrderedType <: MiniOrderedType := Typ <+ HasUsualEq <+ UsualIsEqOrig <+ HasLt <+ HasMiniOrderedType.

(* variant that can be included nicely *)
Module OT_of_MOT (Import O : MiniOrderedType).
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof with auto with ordered_type.
   intros x y; elim (compare x y); intro H; [ right | left | right ]...
   assert (~ eq y x)...
  Defined.
End OT_of_MOT.

Module Type UsualOrderedTypeOrig <: OrderedTypeOrig := UsualMiniOrderedType <+ HasEqDec.

Module BackportStrOrder (Import E : EqLt) (EE : IsEq E) (S : IsStrOrder E) <: IsStrOrderOrig E.
  Definition lt_trans : Transitive lt := _.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    pose proof (_ : Irreflexive lt) as H.
    intros x y H1 H2.
    rewrite H2 in H1.
    apply H in H1.
    assumption.
  Qed.
End BackportStrOrder.
Module BackportCompare (Import E : EqLt) (C : HasCmp E) (CS : CmpSpec E C) <: HasCompareOrig E.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    refine (match C.compare x y as c return CompareSpec _ _ _ c -> Compare _ _ _ _ with
            | Eq => fun H => EQ _
            | Lt => fun H => LT _
            | Gt => fun H => GT _
            end (CS.compare_spec x y));
      inversion H; assumption.
  Defined.
End BackportCompare.
Module UpdateStrOrder_StrOrder (Import E : EqLt) (EE : IsEqOrig E) (S : IsStrOrderOrig E).
  Instance lt_strorder : StrictOrder lt | 100.
  Proof.
    pose proof S.lt_trans.
    pose proof S.lt_not_eq.
    pose proof EE.eq_refl.
    split; cbv in *; eauto.
  Qed.
End UpdateStrOrder_StrOrder.
Module UpdateStrOrder_Compat (Import E : EqLt) (EE : IsEqOrig E) (S : IsStrOrderOrig E) (C : HasCompareOrig E).
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt | 100.
  Proof.
    cbv.
    intros x y H x' y' H'.
    let t :=
      repeat match goal with
             | [ H : ?T, H' : ~?T |- _ ] => exfalso; apply H', H
             | [ H : ?T |- ?T ] => exact H
             | [ H : ?T, H' : ?T |- _ ] => clear H'
             | [ H : eq _ _, H' : eq _ _ |- _ ]
               => unique pose proof (EE.eq_trans H H')
             | [ H : eq _ _ |- _ ]
               => unique pose proof (EE.eq_sym H)
             | [ H : lt _ _ |- _ ]
               => unique pose proof (@S.lt_not_eq _ _ H)
             | [ H : lt _ _, H' : lt _ _ |- _ ]
               => unique pose proof (@S.lt_trans _ _ _ H H')
             | [ |- _ /\ _ ] => split; intros
             end in
    t;
    destruct (C.compare y y'); t;
    destruct (C.compare x x'); t;
    destruct (C.compare x y'); t.
  Qed.
End UpdateStrOrder_Compat.
Module UpdateStrOrder (E : EqLt) (EE : IsEqOrig E) (S : IsStrOrderOrig E) (C : HasCompareOrig E) <: IsStrOrder E := UpdateStrOrder_StrOrder E EE S <+ UpdateStrOrder_Compat E EE S C.
Module UpdateCmp (Import E : EqLt) (C : HasCompareOrig E) <: HasCmp E.
  Definition compare (x y : t) : comparison
    := match C.compare x y with
       | EQ _ => Eq
       | LT _ => Lt
       | GT _ => Gt
       end.
End UpdateCmp.
Module UpdateCompare (Import E : EqLt) (C : HasCompareOrig E) <: HasCompare E.
  Include UpdateCmp E C.
  Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    cbv [compare]; destruct C.compare; constructor; assumption.
  Qed.
End UpdateCompare.
Module HasEqDec_DecStrOrder (Import E : DecStrOrder') <: HasEqDec E.
  Lemma eq_dec (x y : t) : { x==y } + { ~ x==y }.
  Proof.
    refine (match compare x y as c return CompareSpec _ _ _ c -> _ with
            | Eq
              => fun pf
                 => left match pf in CompareSpec _ _ _ c return match c return Prop with Eq => _ | _ => True end with
                         | CompEq pf => pf
                         | _ => I
                         end
            | Lt
              => fun pf
                 => right match pf in CompareSpec _ _ _ c return match c return Prop with Lt => _ | _ => True end with
                          | CompLt pf' => _
                          | _ => I
                          end
            | Gt
              => fun pf
                 => right match pf in CompareSpec _ _ _ c return match c return Prop with Gt => _ | _ => True end with
                          | CompGt pf' => _
                          | _ => I
                          end
            end (compare_spec x y));
      clear pf; intro; eapply (_ : Irreflexive lt), lt_compat; (eassumption + reflexivity).
  Defined.
End HasEqDec_DecStrOrder.

Module OT_of_New (Import O : Orders.OrderedType) <: OrderedTypeOrig.
  Definition t := O.t.
  Definition eq := O.eq.
  Definition lt := O.lt.
  Include BackportEq O O.
  Include BackportStrOrder O O O.
  Include BackportCompare O O O.
  Include OT_of_MOT.
End OT_of_New.

Module OT_of_Orig (Import O : MiniOrderedType) <: Orders.OrderedType.
  Definition t := O.t.
  Definition eq := O.eq.
  Definition lt := O.lt.
  Include UpdateEq O O.
  Include UpdateStrOrder O O O O.
  Include UpdateCompare O O.
  Include HasEqDec_DecStrOrder.
End OT_of_Orig.

Module UsualOT_of_UsualOrig (Import O : UsualMiniOrderedType) <: UsualOrderedType.
  Definition t := O.t.
  Definition lt := O.lt.
  Include HasUsualEq.
  Include UsualIsEq.
  Include UpdateStrOrder O O O O.
  Include UpdateCompare O O.
  Include HasEqDec_DecStrOrder.
End UsualOT_of_UsualOrig.

Module OrderedTypeOrigFacts (O:OrderedTypeOrig) := OrderedType.OrderedTypeFacts O.
Module Type OrderedTypeOrigFactsT (O:OrderedTypeOrig) := Nop <+ OrderedTypeOrigFacts O.
Module OrderedTypeOrigFacts_RemoveHints (O:OrderedTypeOrig) (F:OrderedTypeOrigFactsT O).
  Global Remove Hints
         F.eq_equiv
         F.lt_compat
         F.lt_strorder
    : typeclass_instances.
End OrderedTypeOrigFacts_RemoveHints.

Module Type KeyOrderedTypeT (O:OrderedType) := Nop <+ KeyOrderedType O.
Module KeyOrderedType_RemoveHints (O:OrderedTypeOrig) (F:KeyOrderedTypeT O).
  Include OrderedTypeOrigFacts_RemoveHints O F.MO.
  Global Remove Hints
         F.eqk_equiv
         F.eqke_equiv
         F.ltk_strorder
         F.ltk_compat
         F.ltk_compat'
    : typeclass_instances.
End KeyOrderedType_RemoveHints.
