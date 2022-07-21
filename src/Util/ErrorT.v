Require Import Crypto.Util.Notations.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Local Set Implicit Arguments.
Inductive ErrorT {ErrT T} :=
| Success (v : T)
| Error (msg : ErrT).

Global Arguments ErrorT : clear implicits.
Declare Scope error_scope.
Delimit Scope error_scope with error.
Bind Scope error_scope with ErrorT.

Definition invert_result {ErrT T} (v : ErrorT ErrT T)
  := match v return match v with Success _ => T | _ => ErrT end with
     | Success v => v
     | Error msg => msg
     end.

Definition bind {A B ErrT} (x : ErrorT ErrT A) (k : A -> ErrorT ErrT B) : ErrorT ErrT B
  := match x with
     | Success v => k v
     | Error msg => Error msg
     end.

Definition map2 {ErrT1 ErrT2 A B} (f : A -> B) (fe : ErrT1 -> ErrT2) (x : ErrorT ErrT1 A) : ErrorT ErrT2 B
  := match x with
     | Success v => Success (f v)
     | Error e => Error (fe e)
     end.

Definition map {ErrT A B} (f : A -> B) : ErrorT ErrT A -> ErrorT ErrT B
  := map2 f id.

Definition map_error {ErrT1 ErrT2 A} (fe : ErrT1 -> ErrT2) : ErrorT ErrT1 A -> ErrorT ErrT2 A
  := map2 id fe.

Definition error_bind {ErrT1 ErrT2 A} (x : ErrorT ErrT1 A) (k : ErrT1 -> ErrorT ErrT2 A) : ErrorT ErrT2 A
  := match x with
     | Success v => Success v
     | Error msg => k msg
     end.

Notation "x <- y ; f" := (bind y (fun x => f%error)) : error_scope.

(** ** Equality for [ErrorT] *)
Section ErrorT.
  Local Notation ErrorT_code u v
    := (match u, v with
        | Success u', Success v'
        | Error u', Error v'
          => u' = v'
        | Success _, _
        | Error _, _
          => False
        end).

  (** *** Equality of [ErrorT] is a [match] *)
  Definition path_ErrorT {A B} (u v : ErrorT A B) (p : ErrorT_code u v)
    : u = v.
  Proof. destruct u, v; first [ apply f_equal | exfalso ]; exact p. Defined.

  (** *** Equivalence of equality of [ErrorT] with [ErrorT_code] *)
  Definition unpath_ErrorT {A B} {u v : ErrorT A B} (p : u = v)
    : ErrorT_code u v.
  Proof. subst v; destruct u; reflexivity. Defined.

  Definition path_ErrorT_iff {A B}
             (u v : @ErrorT A B)
    : u = v <-> ErrorT_code u v.
  Proof.
    split; [ apply unpath_ErrorT | apply path_ErrorT ].
  Defined.

  (** *** Eta-expansion of [@eq (ErrorT _ _)] *)
  Definition path_ErrorT_eta {A B} {u v : @ErrorT A B} (p : u = v)
    : p = path_ErrorT u v (unpath_ErrorT p).
  Proof. destruct u, p; reflexivity. Defined.

  (** *** Induction principle for [@eq (ErrorT _ _)] *)
  Definition path_ErrorT_rect {A B} {u v : @ErrorT A B} (P : u = v -> Type)
             (f : forall p, P (path_ErrorT u v p))
    : forall p, P p.
  Proof. intro p; specialize (f (unpath_ErrorT p)); destruct u, p; exact f. Defined.
  Definition path_ErrorT_rec {A B u v} (P : u = v :> @ErrorT A B -> Set) := path_ErrorT_rect P.
  Definition path_ErrorT_ind {A B u v} (P : u = v :> @ErrorT A B -> Prop) := path_ErrorT_rec P.
End ErrorT.

(** ** Useful Tactics *)
(** *** [inversion_ErrorT] *)
Ltac induction_path_ErrorT H :=
  induction H as [H] using path_ErrorT_rect;
  try match type of H with
      | False => exfalso; exact H
      end.
Ltac inversion_ErrorT_step :=
  match goal with
  | [ H : Success _ = Success _ |- _ ]
    => induction_path_ErrorT H
  | [ H : Success _ = Error _ |- _ ]
    => induction_path_ErrorT H
  | [ H : Error _ = Success _ |- _ ]
    => induction_path_ErrorT H
  | [ H : Error _ = Error _ |- _ ]
    => induction_path_ErrorT H
  end.
Ltac inversion_ErrorT := repeat inversion_ErrorT_step.
