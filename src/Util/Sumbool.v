(** * Classification of the [{_} + {_}] Type *)
(** In this file, we classify the basic structure of [sumbool] types. *)
Require Import Crypto.Util.GlobalSettings.

(*Local Set Keep Proof Equalities.
Scheme Equality for sumbool.*)

(** ** Equality for [sumbool] *)
Section sumbool.
  Local Notation sumbool_code u v
    := (match u, v with
        | left u', left v'
        | right u', right v'
          => u' = v'
        | left _, _
        | right _, _
          => False
        end).

  (** *** Equality of [sumbool] is a [match] *)
  Definition path_sumbool {A B} (u v : sumbool A B) (p : sumbool_code u v)
    : u = v.
  Proof. destruct u, v; first [ apply f_equal | exfalso ]; exact p. Defined.

  (** *** Equivalence of equality of [sumbool] with [sumbool_code] *)
  Definition unpath_sumbool {A B} {u v : sumbool A B} (p : u = v)
    : sumbool_code u v.
  Proof. subst v; destruct u; reflexivity. Defined.

  Definition path_sumbool_iff {A B}
             (u v : @sumbool A B)
    : u = v <-> sumbool_code u v.
  Proof.
    split; [ apply unpath_sumbool | apply path_sumbool ].
  Defined.

  (** *** Eta-expansion of [@eq (sumbool _ _)] *)
  Definition path_sumbool_eta {A B} {u v : @sumbool A B} (p : u = v)
    : p = path_sumbool u v (unpath_sumbool p).
  Proof. destruct u, p; reflexivity. Defined.

  (** *** Induction principle for [@eq (sumbool _ _)] *)
  Definition path_sumbool_rect {A B} {u v : @sumbool A B} (P : u = v -> Type)
             (f : forall p, P (path_sumbool u v p))
    : forall p, P p.
  Proof. intro p; specialize (f (unpath_sumbool p)); destruct u, p; exact f. Defined.
  Definition path_sumbool_rec {A B u v} (P : u = v :> @sumbool A B -> Set) := path_sumbool_rect P.
  Definition path_sumbool_ind {A B u v} (P : u = v :> @sumbool A B -> Prop) := path_sumbool_rec P.
End sumbool.

(** ** Useful Tactics *)
(** *** [inversion_sumbool] *)
Ltac induction_path_sumbool H :=
  induction H as [H] using path_sumbool_rect;
  try match type of H with
      | False => exfalso; exact H
      end.
Ltac inversion_sumbool_step :=
  match goal with
  | [ H : left _ = left _ |- _ ]
    => induction_path_sumbool H
  | [ H : left _ = right _ |- _ ]
    => induction_path_sumbool H
  | [ H : right _ = left _ |- _ ]
    => induction_path_sumbool H
  | [ H : right _ = right _ |- _ ]
    => induction_path_sumbool H
  end.
Ltac inversion_sumbool := repeat inversion_sumbool_step.
