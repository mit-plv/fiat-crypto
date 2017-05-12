Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.PartiallyReifiedProp.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.NatUtil.

Global Instance dec_eq_base_type : DecidableRel (@eq base_type)
  := base_type_eq_dec.
Global Instance dec_eq_flat_type : DecidableRel (@eq (flat_type base_type)) := _.
Global Instance dec_eq_type : DecidableRel (@eq (type base_type)) := _.

Definition base_type_eq_semidec_transparent (t1 t2 : base_type)
  : option (t1 = t2)
  := match base_type_eq_dec t1 t2 with
     | left pf => Some pf
     | right _ => None
     end.
Lemma base_type_eq_semidec_is_dec t1 t2 : base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2.
Proof.
  unfold base_type_eq_semidec_transparent; break_match; congruence.
Qed.

Definition op_beq_hetero {t1 tR t1' tR'} (f : op t1 tR) (g : op t1' tR') : bool
  := match f, g return bool with
     | OpConst T1 v, OpConst T2 v'
       => base_type_beq T1 T2 && Z.eqb v v'
     | Add T1 T2 Tout, Add T1' T2' Tout'
     | Sub T1 T2 Tout, Sub T1' T2' Tout'
     | Mul T1 T2 Tout, Mul T1' T2' Tout'
     | Shl T1 T2 Tout, Shl T1' T2' Tout'
     | Shr T1 T2 Tout, Shr T1' T2' Tout'
     | Land T1 T2 Tout, Land T1' T2' Tout'
     | Lor T1 T2 Tout, Lor T1' T2' Tout'
       => base_type_beq T1 T1' && base_type_beq T2 T2' && base_type_beq Tout Tout'
     | Opp Tin Tout, Opp Tin' Tout'
       => base_type_beq Tin Tin' && base_type_beq Tout Tout'
     | Zselect T1 T2 T3 Tout, Zselect T1' T2' T3' Tout'
       => base_type_beq T1 T1' && base_type_beq T2 T2' && base_type_beq T3 T3' && base_type_beq Tout Tout'
     | AddWithCarry T1 T2 T3 Tout, AddWithCarry T1' T2' T3' Tout'
       => base_type_beq T1 T1' && base_type_beq T2 T2' && base_type_beq T3 T3' && base_type_beq Tout Tout'
     | AddWithGetCarry bitwidth T1 T2 T3 Tout1 Tout2, AddWithGetCarry bitwidth' T1' T2' T3' Tout1' Tout2'
       => Z.eqb bitwidth bitwidth' && base_type_beq T1 T1' && base_type_beq T2 T2' && base_type_beq T3 T3' && base_type_beq Tout1 Tout1' && base_type_beq Tout2 Tout2'
     | OpConst _ _, _
     | Add _ _ _, _
     | Sub _ _ _, _
     | Mul _ _ _, _
     | Shl _ _ _, _
     | Shr _ _ _, _
     | Land _ _ _, _
     | Lor _ _ _, _
     | Opp _ _, _
     | Zselect _ _ _ _, _
     | AddWithCarry _ _ _ _, _
     | AddWithGetCarry _ _ _ _ _ _, _
       => false
     end%bool.

Definition op_beq t1 tR (f g : op t1 tR) : bool
  := Eval cbv [op_beq_hetero] in op_beq_hetero f g.

Definition op_beq_hetero_type_eq {t1 tR t1' tR'} f g : to_prop (@op_beq_hetero t1 tR t1' tR' f g) -> t1 = t1' /\ tR = tR'.
Proof.
  destruct f, g;
    repeat match goal with
           | _ => progress unfold op_beq_hetero in *
           | _ => simpl; intro; exfalso; assumption
           | _ => solve [ repeat constructor ]
           | [ |- context[reified_Prop_of_bool ?b] ]
             => let H := fresh in destruct (Sumbool.sumbool_of_bool b) as [H|H]; rewrite H
           | [ H : nat_beq _ _ = true |- _ ] => apply internal_nat_dec_bl in H; subst
           | [ H : base_type_beq _ _ = true |- _ ] => apply internal_base_type_dec_bl in H; subst
           | [ H : wordT_beq_hetero _ _ = true |- _ ] => apply wordT_beq_bl in H; subst
           | [ H : wordT_beq_hetero _ _ = true |- _ ] => apply wordT_beq_hetero_bl in H; destruct H; subst
           | [ H : andb ?x ?y = true |- _ ]
             => assert (x = true /\ y = true) by (destruct x, y; simpl in *; repeat constructor; exfalso; clear -H; abstract congruence);
                  clear H
           | [ H : and _ _ |- _ ] => destruct H
           | [ H : false = true |- _ ] => exfalso; clear -H; abstract congruence
           | [ H : true = false |- _ ] => exfalso; clear -H; abstract congruence
           | _ => progress break_match_hyps
           end.
Defined.

Definition op_beq_hetero_type_eqs {t1 tR t1' tR'} f g : to_prop (@op_beq_hetero t1 tR t1' tR' f g) -> t1 = t1'
  := fun H => let (p, q) := @op_beq_hetero_type_eq t1 tR t1' tR' f g H in p.
Definition op_beq_hetero_type_eqd {t1 tR t1' tR'} f g : to_prop (@op_beq_hetero t1 tR t1' tR' f g) -> tR = tR'
  := fun H => let (p, q) := @op_beq_hetero_type_eq t1 tR t1' tR' f g H in q.

Definition op_beq_hetero_eq {t1 tR t1' tR'} f g
  : forall pf : to_prop (@op_beq_hetero t1 tR t1' tR' f g),
    eq_rect
      _ (fun src => op src tR')
      (eq_rect _ (fun dst => op t1 dst) f _ (op_beq_hetero_type_eqd f g pf))
      _ (op_beq_hetero_type_eqs f g pf)
    = g.
Proof.
  destruct f, g;
    repeat match goal with
           | _ => solve [ intros [] ]
           | _ => reflexivity
           | [ H : False |- _ ] => exfalso; assumption
           | _ => intro
           | [ |- context[op_beq_hetero_type_eqd ?f ?g ?pf] ]
             => generalize (op_beq_hetero_type_eqd f g pf), (op_beq_hetero_type_eqs f g pf)
           | _ => intro
           | _ => progress eliminate_hprop_eq
           | _ => progress inversion_flat_type
           | _ => progress unfold op_beq_hetero in *
           | _ => progress simpl in *
           | [ H : context[andb ?x ?y] |- _ ]
             => destruct x eqn:?, y eqn:?; simpl in H
           | [ H : Z.eqb _ _ = true |- _ ] => apply Z.eqb_eq in H
           | [ H : to_prop (reified_Prop_of_bool ?b) |- _ ] => destruct b eqn:?; compute in H
           | _ => progress subst
           | _ => progress break_match_hyps
           | [ H : wordT_beq_hetero _ _ = true |- _ ] => apply wordT_beq_bl in H; subst
           | [ H : wordT_beq_hetero _ _ = true |- _ ] => apply wordT_beq_hetero_bl in H; destruct H; subst
           | _ => congruence
           end.
Qed.

Lemma op_beq_bl : forall t1 tR x y, to_prop (op_beq t1 tR x y) -> x = y.
Proof.
  intros ?? f g H.
  pose proof (op_beq_hetero_eq f g H) as H'.
  generalize dependent (op_beq_hetero_type_eqd f g H).
  generalize dependent (op_beq_hetero_type_eqs f g H).
  intros; eliminate_hprop_eq; simpl in *; assumption.
Qed.

Section encode_decode.
  Definition base_type_code (t1 t2 : base_type) : Prop
    := match t1, t2 with
       | TZ, TZ => True
       | TWord s1, TWord s2 => s1 = s2
       | TZ, _
       | TWord _, _
         => False
       end.

    Definition base_type_encode (x y : base_type) : x = y -> base_type_code x y.
    Proof. intro p; destruct p, x; repeat constructor. Defined.

    Definition base_type_decode (x y : base_type) : base_type_code x y -> x = y.
    Proof.
      destruct x, y; simpl in *; intro H;
        try first [ apply f_equal; assumption
                  | exfalso; assumption
                  | reflexivity
                  | apply f_equal2; destruct H; assumption ].
    Defined.
    Definition path_base_type_rect {x y : base_type} (Q : x = y -> Type)
               (f : forall p, Q (base_type_decode x y p))
      : forall p, Q p.
    Proof. intro p; specialize (f (base_type_encode x y p)); destruct x, p; exact f. Defined.
End encode_decode.

Ltac induction_type_in_using H rect :=
  induction H as [H] using (rect _ _);
  cbv [base_type_code] in H;
  let H1 := fresh H in
  let H2 := fresh H in
  try lazymatch type of H with
      | False => exfalso; exact H
      | True => destruct H
      end.
Ltac inversion_base_type_step :=
  lazymatch goal with
  | [ H : _ = TWord _ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  | [ H : TWord _ = _ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  | [ H : _ = TZ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  | [ H : TZ = _ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  end.
Ltac inversion_base_type := repeat inversion_base_type_step.
Ltac inversion_base_type_constr_step :=
  lazymatch goal with
  | [ H : TWord _ = TWord _ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  | [ H : TWord _ = TZ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  | [ H : TZ = TWord _ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  | [ H : TZ = TZ |- _ ]
    => induction_type_in_using H @path_base_type_rect
  end.
Ltac inversion_base_type_constr := repeat inversion_base_type_constr_step.
