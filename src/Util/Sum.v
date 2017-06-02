Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.GlobalSettings.

Definition sumwise {A B} (RA:relation A) (RB : relation B) : relation (A + B)
  := fun x y => match x, y with
                | inl x', inl y' => RA x' y'
                | inr x', inr y' => RB x' y'
                | _, _ => False
                end.

Global Instance Equivalence_sumwise
  : forall {A B} {RA:relation A} {RB:relation B}
           {RA_equiv:Equivalence RA} {RB_equiv:Equivalence RB},
    Equivalence (sumwise RA RB).
Proof.
  intros A B RA RB RA_equiv RB_equiv.
  split; repeat intros [?|?]; simpl; trivial; destruct RA_equiv, RB_equiv; try tauto; eauto.
Qed.

Arguments sumwise {A B} _ _ _ _.

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
Qed.

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
