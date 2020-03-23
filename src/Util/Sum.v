Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.GlobalSettings.

Scheme Equality for sum.

Definition sumwise {A B} (RA:relation A) (RB : relation B) : relation (A + B)
  := fun x y => match x, y with
                | inl x', inl y' => RA x' y'
                | inr x', inr y' => RB x' y'
                | _, _ => False
                end.

Arguments sumwise {A B} _ _ _ _.

Global Instance inl_Proper_sumwise {A B RA RB}
  : Proper (RA ==> sumwise RA RB) (@inl A B) | 10.
Proof. repeat intro; cbv; assumption. Qed.
Global Instance inr_Proper_sumwise {A B RA RB}
  : Proper (RB ==> sumwise RA RB) (@inr A B) | 10.
Proof. repeat intro; cbv; assumption. Qed.

Global Instance Equivalence_sumwise
  : forall {A B} {RA:relation A} {RB:relation B}
           {RA_equiv:Equivalence RA} {RB_equiv:Equivalence RB},
    Equivalence (sumwise RA RB) | 10.
Proof.
  intros A B RA RB RA_equiv RB_equiv.
  split; repeat intros [?|?]; simpl; trivial; destruct RA_equiv, RB_equiv; try tauto; eauto.
Qed.

Lemma sumwise_beq_bp {A B} {A_beq B_beq} {A_le : relation A} {B_le : relation B}
      (A_bp : forall x y, A_beq x y = true -> A_le x y)
      (B_bp : forall x y, B_beq x y = true -> B_le x y)
  : forall x y, sum_beq _ _ A_beq B_beq x y = true -> sumwise A_le B_le x y.
Proof.
  intros [x|x] [y|y]; cbn; auto using Bool.diff_false_true.
Defined.

Lemma sumwise_beq_pb {A B} {A_beq B_beq} {A_le : relation A} {B_le : relation B}
      (A_pb : forall x y, A_le x y -> A_beq x y = true)
      (B_pb : forall x y, B_le x y -> B_beq x y = true)
  : forall x y, sumwise A_le B_le x y -> sum_beq _ _ A_beq B_beq x y = true.
Proof.
  intros [x|x] [y|y]; cbn; auto using Bool.diff_false_true.
Defined.

Definition sum_le {A B} (RA:relation A) (RB : relation B) : relation (A + B)
  := fun x y => match x, y with
                | inl x', inl y' => RA x' y'
                | inr x', inr y' => RB x' y'
                | inl _, inr _ => True
                | inr _, inl _ => False
                end.

Arguments sum_le {A B} _ _ _ _.

Global Instance inl_Proper_sum_le {A B RA RB}
  : Proper (RA ==> sum_le RA RB) (@inl A B) | 10.
Proof. repeat intro; cbv; assumption. Qed.
Global Instance inr_Proper_sum_le {A B RA RB}
  : Proper (RB ==> sum_le RA RB) (@inr A B) | 10.
Proof. repeat intro; cbv; assumption. Qed.

Global Instance sum_le_Reflexive {A B RA RB}
       `{@Reflexive A RA,@Reflexive B RB}
  : Reflexive (sum_le RA RB) | 10.
Proof. repeat intro; destruct_head'_sum; cbn; reflexivity. Defined.

Global Instance sum_le_Transitive {A B RA RB}
       `{@Transitive A RA,@Transitive B RB}
  : Transitive (sum_le RA RB) | 10.
Proof.
  repeat intro; destruct_head'_sum; cbn in *.
  all: try ((idtac + exfalso); assumption).
  all: etransitivity; eassumption.
Defined.

Global Instance sum_le_Irreflexive {A B RA RB}
       `{@Irreflexive A RA,@Irreflexive B RB}
  : Irreflexive (sum_le RA RB) | 10.
Proof.
  intros [?|?] H'; cbn in H'; apply irreflexivity in H'; assumption.
Qed.

Definition sum_leb {A B} (A_leb : A -> A -> bool) (B_leb : B -> B -> bool)
  : A + B -> A + B -> bool
  := fun x y => match x, y with
                | inl x', inl y' => A_leb x' y'
                | inr x', inr y' => B_leb x' y'
                | inl _, inr _ => true
                | inr _, inl _ => false
                end.

Arguments sum_leb {A B} _ _ _ _.

Lemma sum_leb_bp {A B} {A_leb B_leb} {A_le : relation A} {B_le : relation B}
      (A_bp : forall x y, A_leb x y = true -> A_le x y)
      (B_bp : forall x y, B_leb x y = true -> B_le x y)
  : forall x y, sum_leb A_leb B_leb x y = true -> sum_le A_le B_le x y.
Proof.
  intros [x|x] [y|y]; cbn; auto using Bool.diff_false_true.
Defined.

Lemma sum_leb_pb {A B} {A_leb B_leb} {A_le : relation A} {B_le : relation B}
      (A_pb : forall x y, A_le x y -> A_leb x y = true)
      (B_pb : forall x y, B_le x y -> B_leb x y = true)
  : forall x y, sum_le A_le B_le x y -> sum_leb A_leb B_leb x y = true.
Proof.
  intros [x|x] [y|y]; cbn; auto using Bool.diff_false_true.
Defined.

Ltac congruence_sum_step :=
  match goal with
  | [ H : inl _ = inr _ |- _ ] => solve [ inversion H ]
  | [ H : inr _ = inl _ |- _ ] => solve [ inversion H ]
  | [ H : inl _ = inl _ |- _ ] => inversion H; clear H
  | [ H : inr _ = inr _ |- _ ] => inversion H; clear H
  end.
Ltac congruence_sum := repeat congruence_sum_step.

Local Hint Extern 0 => solve [ solve_decidable_transparent ] : typeclass_instances.
Global Instance dec_sumwise {A B RA RB} {HA : DecidableRel RA} {HB : DecidableRel RB} : DecidableRel (@sumwise A B RA RB) | 10.
Proof.
  intros [x|x] [y|y]; exact _.
Defined.

Global Instance dec_sum_le {A B RA RB} {HA : DecidableRel RA} {HB : DecidableRel RB} : DecidableRel (@sum_le A B RA RB) | 10.
Proof.
  intros [x|x] [y|y]; exact _.
Defined.

Global Instance sum_le_StrictOrder {A B RA RB} `{@StrictOrder A RA,@StrictOrder B RB} : StrictOrder (sum_le RA RB) | 10.
Proof. split; exact _. Defined.

Global Instance sumwise_Proper_iff {A B eqA eqB leA leB}
       {A_Proper : Proper (eqA ==> eqA ==> iff) leA}
       {B_Proper : Proper (eqB ==> eqB ==> iff) leB}
  : Proper (@sumwise A B eqA eqB ==> @sumwise A B eqA eqB ==> iff)
           (@sumwise A B leA leB) | 5.
Proof.
  cbv [Proper respectful] in *; repeat intro; destruct_head'_sum; cbn in *.
  all: try (exfalso; assumption).
  all: try reflexivity.
  all: eauto with nocore.
Qed.

Global Instance sum_le_Proper_iff {A B eqA eqB leA leB}
       {A_Proper : Proper (eqA ==> eqA ==> iff) leA}
       {B_Proper : Proper (eqB ==> eqB ==> iff) leB}
  : Proper (@sumwise A B eqA eqB ==> @sumwise A B eqA eqB ==> iff)
           (@sum_le A B leA leB) | 5.
Proof.
  cbv [Proper respectful] in *; repeat intro; destruct_head'_sum; cbn in *.
  all: try (exfalso; assumption).
  all: try reflexivity.
  all: eauto with nocore.
Qed.

Global Instance sum_le_Proper_le {A B leA leB}
       {A_Proper : Proper (Basics.flip leA ==> leA ==> Basics.impl) leA}
       {B_Proper : Proper (Basics.flip leB ==> leB ==> Basics.impl) leB}
  : Proper (Basics.flip (@sum_le A B leA leB) ==> @sum_le A B leA leB ==> Basics.impl)
           (@sum_le A B leA leB) | 10.
Proof.
  cbv [Basics.flip Basics.impl Proper respectful] in *; repeat intro; destruct_head'_sum; cbn in *.
  all: try (exfalso; assumption).
  all: try exact I.
  all: eauto with nocore.
Qed.

Global Instance sum_le_Proper_le_flip {A B leA leB}
       {A_Proper : Proper (leA ==> Basics.flip leA ==> Basics.flip Basics.impl) leA}
       {B_Proper : Proper (leB ==> Basics.flip leB ==> Basics.flip Basics.impl) leB}
  : Proper (@sum_le A B leA leB ==> Basics.flip (@sum_le A B leA leB) ==> Basics.flip Basics.impl)
           (@sum_le A B leA leB) | 10.
Proof.
  cbv [Basics.flip Basics.impl Proper respectful] in *; repeat intro; destruct_head'_sum; cbn in *.
  all: try (exfalso; assumption).
  all: try exact I.
  all: eauto with nocore.
Qed.

Module Sum.
  Notation eqb := sum_beq.
  Notation eqb_bl := internal_sum_dec_bl.
  Notation eqb_lb := internal_sum_dec_lb.

  Definition compare {A B}
             (A_compare : A -> A -> comparison)
             (B_compare : B -> B -> comparison)
             (x y : A + B)
    : comparison
    := match x, y with
       | inl x, inl y => A_compare x y
       | inr x, inr y => B_compare x y
       | inl _, inr _ => Lt
       | inr _, inl _ => Gt
       end.
End Sum.

(** ** Equality for [sum] *)
Section sum.
  Local Notation sum_code u v
    := (match u, v with
        | inl u', inl v'
        | inr u', inr v'
          => u' = v'
        | inl _, _
        | inr _, _
          => False
        end).

  (** *** Equality of [sum] is a [match] *)
  Definition path_sum {A B} (u v : sum A B) (p : sum_code u v)
    : u = v.
  Proof. destruct u, v; first [ apply f_equal | exfalso ]; exact p. Defined.

  (** *** Equivalence of equality of [sum] with [sum_code] *)
  Definition unpath_sum {A B} {u v : sum A B} (p : u = v)
    : sum_code u v.
  Proof. subst v; destruct u; reflexivity. Defined.

  Definition path_sum_iff {A B}
             (u v : @sum A B)
    : u = v <-> sum_code u v.
  Proof.
    split; [ apply unpath_sum | apply path_sum ].
  Defined.

  (** *** Eta-expansion of [@eq (sum _ _)] *)
  Definition path_sum_eta {A B} {u v : @sum A B} (p : u = v)
    : p = path_sum u v (unpath_sum p).
  Proof. destruct u, p; reflexivity. Defined.

  (** *** Induction principle for [@eq (sum _ _)] *)
  Definition path_sum_rect {A B} {u v : @sum A B} (P : u = v -> Type)
             (f : forall p, P (path_sum u v p))
    : forall p, P p.
  Proof. intro p; specialize (f (unpath_sum p)); destruct u, p; exact f. Defined.
  Definition path_sum_rec {A B u v} (P : u = v :> @sum A B -> Set) := path_sum_rect P.
  Definition path_sum_ind {A B u v} (P : u = v :> @sum A B -> Prop) := path_sum_rec P.
End sum.

(** ** Useful Tactics *)
(** *** [inversion_sum] *)
Ltac induction_path_sum H :=
  induction H as [H] using path_sum_rect;
  try match type of H with
      | False => exfalso; exact H
      end.
Ltac inversion_sum_step :=
  match goal with
  | [ H : inl _ = inl _ |- _ ]
    => induction_path_sum H
  | [ H : inl _ = inr _ |- _ ]
    => induction_path_sum H
  | [ H : inr _ = inl _ |- _ ]
    => induction_path_sum H
  | [ H : inr _ = inr _ |- _ ]
    => induction_path_sum H
  end.
Ltac inversion_sum := repeat inversion_sum_step.
