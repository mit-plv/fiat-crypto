Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.ArithmeticSimplifier.

(** ** Equality for [inverted_expr] *)
Section inverted_expr.
  Context {var : base_type -> Type}.
  Local Notation inverted_expr := (@inverted_expr var).
  Local Notation inverted_expr_code u v
    := (match u, v with
        | const_of u', const_of v'
        | gen_expr u', gen_expr v'
        | neg_expr u', neg_expr v'
          => u' = v'
        | const_of _, _
        | gen_expr _, _
        | neg_expr _, _
          => False
        end).

  (** *** Equality of [inverted_expr] is a [match] *)
  Definition path_inverted_expr {T} (u v : inverted_expr T) (p : inverted_expr_code u v)
    : u = v.
  Proof. destruct u, v; first [ apply f_equal | exfalso ]; exact p. Defined.

  (** *** Equivalence of equality of [inverted_expr] with [inverted_expr_code] *)
  Definition unpath_inverted_expr {T} {u v : inverted_expr T} (p : u = v)
    : inverted_expr_code u v.
  Proof. subst v; destruct u; reflexivity. Defined.

  Definition path_inverted_expr_iff {T}
             (u v : @inverted_expr T)
    : u = v <-> inverted_expr_code u v.
  Proof.
    split; [ apply unpath_inverted_expr | apply path_inverted_expr ].
  Defined.

  (** *** Eta-expansion of [@eq (inverted_expr _ _)] *)
  Definition path_inverted_expr_eta {T} {u v : @inverted_expr T} (p : u = v)
    : p = path_inverted_expr u v (unpath_inverted_expr p).
  Proof. destruct u, p; reflexivity. Defined.

  (** *** Induction principle for [@eq (inverted_expr _ _)] *)
  Definition path_inverted_expr_rect {T} {u v : @inverted_expr T} (P : u = v -> Type)
             (f : forall p, P (path_inverted_expr u v p))
    : forall p, P p.
  Proof. intro p; specialize (f (unpath_inverted_expr p)); destruct u, p; exact f. Defined.
  Definition path_inverted_expr_rec {T u v} (P : u = v :> @inverted_expr T -> Set) := path_inverted_expr_rect P.
  Definition path_inverted_expr_ind {T u v} (P : u = v :> @inverted_expr T -> Prop) := path_inverted_expr_rec P.
End inverted_expr.

(** ** Useful Tactics *)
(** *** [inversion_inverted_expr] *)
Ltac induction_path_inverted_expr H :=
  induction H as [H] using path_inverted_expr_rect;
  try match type of H with
      | False => exfalso; exact H
      end.
Ltac inversion_inverted_expr_step :=
  match goal with
  | [ H : const_of _ _ = const_of _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : const_of _ _ = gen_expr _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : const_of _ _ = neg_expr _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : gen_expr _ _ = const_of _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : gen_expr _ _ = gen_expr _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : gen_expr _ _ = neg_expr _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : neg_expr _ _ = const_of _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : neg_expr _ _ = gen_expr _ _ |- _ ]
    => induction_path_inverted_expr H
  | [ H : neg_expr _ _ = neg_expr _ _ |- _ ]
    => induction_path_inverted_expr H
  end.
Ltac inversion_inverted_expr := repeat inversion_inverted_expr_step.
