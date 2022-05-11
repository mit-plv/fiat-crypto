Require Import Coq.Structures.OrderedType.

(* variant that can be included nicely *)
Module OT_of_MOT (Import O : MiniOrderedType).
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof with auto with ordered_type.
   intros x y; elim (compare x y); intro H; [ right | left | right ]...
   assert (~ eq y x)...
  Defined.
End OT_of_MOT.

Require Import Coq.Structures.Orders.

Module OT_of_New (Import O : Orders.OrderedType) <: OrderedType.OrderedType.
  Definition t := O.t.
  Definition eq := O.eq.
  Definition lt := O.lt.
  Definition eq_refl : Reflexive eq := _.
  Definition eq_sym : Symmetric eq := _.
  Definition eq_trans : Transitive eq := _.
  Definition lt_trans : Transitive lt := _.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    pose proof (_ : Irreflexive lt) as H.
    intros x y H1 H2.
    cbv [lt eq] in *.
    rewrite H2 in H1.
    apply H in H1.
    assumption.
  Qed.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    refine (match O.compare x y as c return CompareSpec _ _ _ c -> Compare _ _ _ _ with
            | Eq => fun H => EQ _
            | Lt => fun H => LT _
            | Gt => fun H => GT _
            end (O.compare_spec x y));
      inversion H; assumption.
  Defined.
  Include OT_of_MOT.
End OT_of_New.

Module OT_of_Orig (Import O : OrderedType.MiniOrderedType) <: Orders.OrderedType.
  Module O' := O <+ OT_of_MOT O.
  Module O'' := OrderedTypeFacts O'.
  Definition t := O.t.
  Definition eq := O.eq.
  Definition lt := O.lt.
  Instance eq_equiv : Equivalence eq | 100 := O''.eq_equiv.
  Instance lt_strorder : StrictOrder lt | 100 := O''.lt_strorder.
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt | 100.
  Proof.
    cbv.
    intros x y H x' y' H'.
    split; intro Hlt.
    all: let t := (eassumption + (symmetry; eassumption) + eapply O''.eq_not_lt + eapply O''.le_lt_trans + eapply O''.lt_le_trans) in
         solve [ t; t; t; t ].
  Qed.
  Definition compare (x y : t) : comparison
    := match O.compare x y with
       | EQ _ => Eq
       | LT _ => Lt
       | GT _ => Gt
       end.
  Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    cbv [compare]; destruct O.compare; constructor; assumption.
  Qed.
  Definition eq_dec := O'.eq_dec.
End OT_of_Orig.
