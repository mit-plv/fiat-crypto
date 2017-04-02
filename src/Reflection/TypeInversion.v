Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.FixCoqMistakes.

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
      cbv beta iota in *;
      try specialize (H eq_refl); simpl in *;
      try assumption.

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

    Definition preinvert_Prod2_same (Q : forall A, P (Prod (Tbase A) (Tbase A)) -> Type)
      : (forall t (p : P t), match t return P t -> Type with
                             | Prod (Tbase A) (Tbase B)
                               => fun p => forall pf : A = B, Q B (eq_rect _ (fun a => P (Prod (Tbase a) (Tbase B))) p _ pf)
                             | _ => fun _ => True
                             end p)
        -> forall A p, Q A p.
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
                           end p)
      -> forall A B p, Q A B p.
  Proof.
    intros H A B p; specialize (H _ p); assumption.
  Defined.

  Section encode_decode.
    Definition flat_type_code (t1 t2 : flat_type base_type_code) : Prop
      := match t1, t2 with
         | Unit, Unit => True
         | Tbase t1, Tbase t2 => t1 = t2
         | Prod A B, Prod A' B' => A = A' /\ B = B'
         | Unit, _
         | Tbase _, _
         | Prod _ _, _
           => False
         end.

    Definition type_code (t1 t2 : type base_type_code) : Prop
      := domain t1 = domain t2 /\ codomain t1 = codomain t2.

    Definition flat_type_encode (x y : flat_type base_type_code) : x = y -> flat_type_code x y.
    Proof. intro p; destruct p, x; repeat constructor. Defined.
    Definition type_encode (x y : type base_type_code) : x = y -> type_code x y.
    Proof. intro p; destruct p, x; repeat constructor. Defined.

    Definition flat_type_decode (x y : flat_type base_type_code) : flat_type_code x y -> x = y.
    Proof.
      destruct x, y; simpl in *; intro H;
        try first [ apply f_equal; assumption
                  | exfalso; assumption
                  | reflexivity
                  | apply f_equal2; destruct H; assumption ].
    Defined.
    Definition type_decode (x y : type base_type_code) : type_code x y -> x = y.
    Proof.
      destruct x, y; simpl; intro H;
        try first [ exfalso; assumption
                  | apply f_equal; assumption
                  | apply f_equal2; destruct H; assumption ].
    Defined.
    Definition path_flat_type_rect {x y : flat_type base_type_code} (Q : x = y -> Type)
               (f : forall p, Q (flat_type_decode x y p))
      : forall p, Q p.
    Proof. intro p; specialize (f (flat_type_encode x y p)); destruct x, p; exact f. Defined.
    Definition path_type_rect {x y : type base_type_code} (Q : x = y -> Type)
               (f : forall p, Q (type_decode x y p))
      : forall p, Q p.
    Proof. intro p; specialize (f (type_encode x y p)); destruct x, p; exact f. Defined.
  End encode_decode.
End language.

Ltac preinvert_one_type e :=
  lazymatch type of e with
  | ?P (Tbase ?T)
    => is_var T;
       move e at top;
       revert dependent T;
       refine (preinvert_Tbase P _ _)
  | ?P (Prod (Tbase ?A) (Tbase ?A))
    => is_var A;
       move e at top; revert dependent A;
       refine (preinvert_Prod2_same P _ _)
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
  | ?P (Prod ?A ?B)
    => is_var A; is_var B;
       move e at top; revert dependent A; intros A e;
       move e at top; revert dependent B; revert A;
       refine (preinvert_Prod P _ _)
  | ?P Unit
    => revert dependent e;
       refine (preinvert_Unit P _ _)
  | ?P (Arrow ?A ?B)
    => is_var A; is_var B;
       move e at top; revert dependent A; intros A e;
       move e at top; revert dependent B; revert A;
       refine (preinvert_Arrow P _ _)
  end.

Ltac induction_type_in_using H rect :=
  induction H as [H] using (rect _ _ _);
  cbv [flat_type_code type_code] in H;
  let H1 := fresh H in
  let H2 := fresh H in
  try lazymatch type of H with
      | False => exfalso; exact H
      | True => destruct H
      | _ /\ _ => destruct H as [H1 H2]
      end.
Ltac inversion_flat_type_step :=
  lazymatch goal with
  | [ H : _ = Tbase _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : Tbase _ = _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : _ = Prod _ _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : Prod _ _ = _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : _ = Unit |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : Unit = _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  end.
Ltac inversion_flat_type := repeat inversion_flat_type_step.

Ltac inversion_type_step :=
  lazymatch goal with
  | [ H : _ = Arrow _ _ |- _ ]
    => induction_type_in_using H @path_type_rect
  | [ H : Arrow _ _ = _ |- _ ]
    => induction_type_in_using H @path_type_rect
  end.
Ltac inversion_type := repeat inversion_type_step.
