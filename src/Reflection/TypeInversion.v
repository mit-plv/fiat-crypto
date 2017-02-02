Require Import Crypto.Reflection.Syntax.

Section language.
  Context {base_type_code : Type}.

  Section flat.
    Context (P : flat_type base_type_code -> Type).

    Local Ltac t :=
      let H := fresh in
      intro H; intros;
      match goal with
      | [ p : _ |- _ ] => specialize (H _ p)
      end;
      assumption.

    Definition preinvert_Tbase (Q : forall t, P (Tbase t) -> Type)
      : (forall t (p : P t), match t return P t -> Type with Tbase _ => Q _ | _ => fun _ => True end p)
        -> forall t p, Q t p.
    Proof. t. Defined.

    Definition preinvert_Unit (Q : P Unit -> Type)
      : (forall t (p : P t), match t return P t -> Type with Unit => Q | _ => fun _ => True end p)
        -> forall p, Q p.
    Proof. t. Defined.

    Definition preinvert_Prod (Q : forall A B, P (Prod A B) -> Type)
      : (forall t (p : P t), match t return P t -> Type with Prod _ _ => Q _ _ | _ => fun _ => True end p)
        -> forall A B p, Q A B p.
    Proof. t. Defined.

    Definition preinvert_Prod2 (Q : forall A B, P (Prod (Tbase A) (Tbase B)) -> Type)
      : (forall t (p : P t), match t return P t -> Type with Prod (Tbase _) (Tbase _) => Q _ _ | _ => fun _ => True end p)
        -> forall A B p, Q A B p.
    Proof. t. Defined.

    Definition preinvert_Prod3 (Q : forall A B C, P (Tbase A * Tbase B * Tbase C)%ctype -> Type)
      : (forall t (p : P t), match t return P t -> Type with Prod (Prod (Tbase _) (Tbase _)) (Tbase _) => Q _ _ _ | _ => fun _ => True end p)
        -> forall A B C p, Q A B C p.
    Proof. t. Defined.

    Definition preinvert_Prod4 (Q : forall A B C D, P (Tbase A * Tbase B * Tbase C * Tbase D)%ctype -> Type)
      : (forall t (p : P t), match t return P t -> Type with Prod (Prod (Prod (Tbase _) (Tbase _)) (Tbase _)) (Tbase _) => Q _ _ _ _ | _ => fun _ => True end p)
        -> forall A B C D p, Q A B C D p.
    Proof. t. Defined.
  End flat.

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
  | ?P (Prod (Tbase ?A) (Tbase ?B))
    => is_var A; is_var B;
       move e at top; revert dependent A; intros A e;
       move e at top; revert dependent B; revert A;
       refine (preinvert_Prod2 P _ _)
  | ?P (Prod (Prod (Tbase ?A) (Tbase ?B)) (Tbase ?C))
    => is_var A; is_var B; is_var C;
       move e at top; revert dependent A; intros A e;
       move e at top; revert dependent B; intros B e;
       move e at top; revert dependent C; revert A B;
       refine (preinvert_Prod3 P _ _)
  | ?P (Prod (Prod (Prod (Tbase ?A) (Tbase ?B)) (Tbase ?C)) (Tbase ?D))
    => is_var A; is_var B; is_var C; is_var D;
       move e at top; revert dependent A; intros A e;
       move e at top; revert dependent B; intros B e;
       move e at top; revert dependent C; intros C e;
       move e at top; revert dependent D; revert A B C;
       refine (preinvert_Prod4 P _ _)
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
