Require Import Crypto.Reflection.Syntax.

Section language.
  Context {base_type_code : Type}.

  Definition preinvert_Tbase (P : flat_type base_type_code -> Type) (Q : forall t, P (Tbase t) -> Type)
    : (forall t (p : P t), match t return P t -> Type with
                           | Tbase t' => Q t'
                           | _ => fun _ => True
                           end p)
      -> forall t p, Q t p.
  Proof.
    intros H t p; specialize (H (Tbase t) p); assumption.
  Defined.

  Definition preinvert_Unit (P : flat_type base_type_code -> Type) (Q : P Unit -> Type)
    : (forall t (p : P t), match t return P t -> Type with
                           | Unit => Q
                           | _ => fun _ => True
                           end p)
      -> forall p, Q p.
  Proof.
    intros H p; specialize (H _ p); assumption.
  Defined.

  Definition preinvert_Prod (P : flat_type base_type_code -> Type) (Q : forall A B, P (Prod A B) -> Type)
    : (forall t (p : P t), match t return P t -> Type with
                           | Prod A B => Q A B
                           | _ => fun _ => True
                           end p)
      -> forall A B p, Q A B p.
  Proof.
    intros H A B p; specialize (H _ p); assumption.
  Defined.

  Definition preinvert_Arrow (P : type base_type_code -> Type) (Q : forall A B, P (Arrow A B) -> Type)
    : (forall t (p : P t), match t return P t -> Type with
                           | Arrow A B => Q A B
                           | _ => fun _ => True
                           end p)
      -> forall A B p, Q A B p.
  Proof.
    intros H A B p; specialize (H _ p); assumption.
  Defined.

  Definition preinvert_Tflat (P : type base_type_code -> Type) (Q : forall T, P (Tflat T) -> Type)
    : (forall t (p : P t), match t return P t -> Type with
                           | Tflat T => Q T
                           | _ => fun _ => True
                           end p)
      -> forall T p, Q T p.
  Proof.
    intros H T p; specialize (H _ p); assumption.
  Defined.
End language.

Ltac preinvert_one_type e :=
  lazymatch type of e with
  | ?P (Tbase ?T)
    => is_var T;
       move e at top;
       revert dependent T;
       refine (preinvert_Tbase P _ _)
  | ?P (Prod ?A ?B)
    => is_var A; is_var B;
       move e at top; revert dependent A; intros A e;
       move e at top; revert dependent B; revert A;
       refine (preinvert_Prod P _ _)
  | ?P Unit
    => revert dependent e;
       refine (preinvert_Unit P _ _)
  | ?P (Tflat ?T)
    => is_var T;
       move e at top;
       revert dependent T;
       refine (preinvert_Tflat P _ _)
  | ?P (Arrow ?A ?B)
    => is_var A; is_var B;
       move e at top; revert dependent A; intros A e;
       move e at top; revert dependent B; revert A;
       refine (preinvert_Arrow P _ _)
  end.
