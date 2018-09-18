(** * Definition and classification of the [Σ] Type, with primitive projections *)
(** In this file, we classify the basic structure of Σ types ([sigT]
    in Coq).  In particular, we classify equalities of dependent pairs
    (inhabitants of Σ types), so that when we have an equality between
    two such pairs, or when we want such an equality, we have a
    systematic way of reducing such equalities to equalities at
    simpler types. *)
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.IffT.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Notations.

Local Set Primitive Projections.

Delimit Scope primproj_type_scope with primproj_type.
Delimit Scope primproj_scope with primproj.

Import EqNotations.
Module Import Primitive.
  Record sigT {A} P := existT { projT1 : A ; projT2 : P projT1 }.
  Global Arguments existT {_} _ _ _.
  Global Arguments projT1 {_ _} _.
  Global Arguments projT2 {_ _} _.

  Module Export Notations.
    Notation "{ x  &  P }" := (sigT (fun x => P)) : type_scope.
    Notation "{ x : A  & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
    Add Printing Let sigT.
  End Notations.

  Add Printing Let sigT.

  Local Set Implicit Arguments.

  Definition sigT_beq A P (eq_A : A -> A -> bool) (eq_P : forall a a', P a -> P a' -> bool) (X Y : @sigT A P) : bool
    := let (a, b) := X in let (a', b') := Y in (eq_A a a' && eq_P _ _ b b')%bool.
  Global Arguments sigT_beq / .
  Lemma sigT_dec_bl A P eq_A eq_P
        (A_bl : forall x y : A, eq_A x y = true -> x = y)
        (P_bl : forall a a' x y (pf : eq_A a a' = true), eq_P a a' x y = true -> rew [P] (A_bl _ _ pf) in x = y)
        (x y : @sigT A P)
    : sigT_beq eq_A eq_P x y = true -> x = y.
  Proof.
    destruct x as [a b], y as [a' b'].
    specialize (P_bl a a' b b'); cbn.
    generalize dependent (A_bl a a'); clear A_bl; intros A_bl P_bl H.
    edestruct eq_A; cbn in *;
      destruct (eq_A a a');
      first [ specialize (P_bl eq_refl); generalize dependent (A_bl eq_refl)
            | specialize (P_bl H); generalize dependent (A_bl H) ];
      clear A_bl; intros A_bl P_bl; try specialize (P_bl H); subst;
        cbn [eq_rect] in *;
        try reflexivity.
    all: edestruct eq_P; first [ specialize (P_bl eq_refl) | specialize (P_bl H) ]; subst;
      reflexivity.
  Defined.
  Lemma sigT_dec_bl_nd A P eq_A eq_P
        (A_bl : forall x y : A, eq_A x y = true -> x = y)
        (P_bl : forall a a' x y (pf : a = a'), rew [P] pf in x = y)
        (x y : @sigT A P)
    : sigT_beq eq_A eq_P x y = true -> x = y.
  Proof.
    apply (@sigT_dec_bl A P eq_A eq_P A_bl); intros; apply P_bl.
  Defined.

  Lemma sigT_dec_lb A P eq_A (eq_P : forall a a', P a -> P a' -> bool)
        (A_lb : forall x y : A, x = y -> eq_A x y = true)
        (P_lb : forall a (x y : P a), x = y -> eq_P a a x y = true)
        (x y : @sigT A P)
    : x = y -> sigT_beq eq_A eq_P x y = true.
  Proof.
    intro; subst y; specialize (A_lb _ _ (eq_refl (projT1 x))); specialize (P_lb _ _ _ (eq_refl (projT2 x))); cbn in *.
    edestruct eq_A, eq_P; (reflexivity + assumption).
  Defined.
  Definition sigT_eq_dec A P eq_A eq_P
             (A_bl : forall x y : A, eq_A x y = true -> x = y)
             (P_bl : forall a a' x y (pf : eq_A a a' = true), eq_P a a' x y = true -> rew [P] (A_bl _ _ pf) in x = y)
             (A_lb : forall x y : A, x = y -> eq_A x y = true)
             (P_lb : forall a (x y : P a), x = y -> eq_P a a x y = true)
             (x y : @sigT A P)
    : {x = y} + {x <> y}.
  Proof.
    refine (let H := let b := @sigT_beq A P eq_A eq_P x y in if b as b0 return ({b0 = true} + {b0 = false}) then left eq_refl else right eq_refl in
            match H with
            | left e => left (@sigT_dec_bl A P eq_A eq_P A_bl P_bl x y e)
            | right H' => right (fun e => _ (@sigT_dec_lb A P eq_A eq_P A_lb P_lb x y e))
            end).
    congruence.
  Defined.
End Primitive.
Notation "{ x  &  P }" := (sigT (fun x => P%primproj_type)) : primproj_type_scope.
Notation "{ x : A  & P }" := (sigT (A:=A%primproj_type) (fun x => P%primproj_type)) : primproj_type_scope.
Add Printing Let sigT.

Local Arguments f_equal {_ _} _ {_ _} _.

Definition projT1_existT {A B} (a:A) (b:B a) : projT1 (existT B a b) = a := eq_refl.
Definition projT2_existT {A B} (a:A) (b:B a) : projT2 (existT B a b) = b := eq_refl.
Create HintDb cancel_primsig discriminated. Hint Rewrite @projT1_existT @projT2_existT : cancel_primsig.

(** ** Equality for [sigT] *)
Section sigT.

  (** *** Projecting an equality of a pair to equality of the first components *)
  Definition pr1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : projT1 u = projT1 v
    := f_equal (@projT1 _ _) p.

  (** *** Projecting an equality of a pair to equality of the second components *)
  Definition pr2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
    : eq_rect _ _ (projT2 u) _ (pr1_path p) = projT2 v.
  Proof.
    destruct p; reflexivity.
  Defined.

  (** *** Equality of [sigT] is itself a [sigT] *)
  Definition path_sigT_uncurried {A : Type} {P : A -> Type} (u v : sigT P)
             (pq : sigT (fun p : projT1 u = projT1 v => eq_rect _ _ (projT2 u) _ p = projT2 v))
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  (** *** Curried version of proving equality of sigma types *)
  Definition path_sigT {A : Type} {P : A -> Type} (u v : sigT P)
             (p : projT1 u = projT1 v) (q : eq_rect _ _ (projT2 u) _ p = projT2 v)
  : u = v
    := path_sigT_uncurried u v (existT _ p q).

  (** *** Equality of [sigT] when the property is an hProp *)
  Definition path_sigT_hprop {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sigT A P)
             (p : projT1 u = projT1 v)
    : u = v
    := path_sigT u v p (P_hprop _ _ _).

  (** *** Equivalence of equality of [sigT] with a [sigT] of equality *)
  (** We could actually use [IsIso] here, but for simplicity, we
      don't.  If we wanted to deal with proofs of equality of Σ types
      in dependent positions, we'd need it. *)
  Definition path_sigT_uncurried_iff {A P}
             (u v : @sigT A P)
    : u = v <-> (sigT (fun p : projT1 u = projT1 v => eq_rect _ _ (projT2 u) _ p = projT2 v)).
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply path_sigT_uncurried ].
  Defined.

  (** *** Induction principle for [@eq (sigT _)] *)
  Definition path_sigT_rect {A P} {u v : @sigT A P} (Q : u = v -> Type)
             (f : forall p q, Q (path_sigT u v p q))
    : forall p, Q p.
  Proof. intro p; specialize (f (pr1_path p) (pr2_path p)); destruct p; exact f. Defined.
  Definition path_sigT_rec {A P u v} (Q : u = v :> @sigT A P -> Set) := path_sigT_rect Q.
  Definition path_sigT_ind {A P u v} (Q : u = v :> @sigT A P -> Prop) := path_sigT_rec Q.

  (** *** Equivalence of equality of [sigT] involving hProps with equality of the first components *)
  Definition path_sigT_hprop_iff {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sigT A P)
    : u = v <-> (projT1 u = projT1 v)
    := conj (f_equal projT1) (path_sigT_hprop P_hprop u v).

  (** *** Non-dependent classification of equality of [sigT] *)
  Definition path_sigT_nondep {A B : Type} (u v : @sigT A (fun _ => B))
             (p : projT1 u = projT1 v) (q : projT2 u = projT2 v)
  : u = v
    := @path_sigT _ _ u v p (eq_trans (transport_const _ _) q).

  (** *** Classification of transporting across an equality of [sigT]s *)
  Lemma eq_rect_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sigT (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => sigT (Q a)) u y H
    = existT
        (Q y)
        (eq_rect x P (projT1 u) y H)
        match H in (_ = y) return Q y (eq_rect x P (projT1 u) y H) with
          | eq_refl => projT2 u
        end.
  Proof.
    destruct H; reflexivity.
  Defined.

  (** *** η Principle for [sigT] *)
  Definition sigT_eta {A P} (p : { a : A & P a })
    : p = existT _ (projT1 p) (projT2 p)
    := eq_refl.
End sigT.

(** ** Useful Tactics *)
(** *** [inversion_sigma] *)
(** The built-in [inversion] will frequently leave equalities of
    dependent pairs.  When the first type in the pair is an hProp or
    otherwise simplifies, [inversion_sigma] is useful; it will replace
    the equality of pairs with a pair of equalities, one involving a
    term casted along the other.  This might also prove useful for
    writing a version of [inversion] / [dependent destruction] which
    does not lose information, i.e., does not turn a goal which is
    provable into one which requires axiom K / UIP.  *)
Ltac simpl_proj_exist_in H :=
  repeat match type of H with
         | context G[projT1 (existT _ ?x ?p)]
           => let G' := context G[x] in change G' in H
         | context G[projT2 (existT _ ?x ?p)]
           => let G' := context G[p] in change G' in H
         end.
Ltac induction_sigma_in_as_using H H0 H1 rect :=
  induction H as [H0 H1] using (rect _ _ _ _);
  simpl_proj_exist_in H0;
  simpl_proj_exist_in H1.
Ltac induction_sigma_in_using H rect :=
  let H0 := fresh H in
  let H1 := fresh H in
  induction_sigma_in_as_using H H0 H1 rect.
Ltac inversion_sigma_step :=
  match goal with
  | [ H : _ = existT _ _ _ |- _ ]
    => induction_sigma_in_using H @path_sigT_rect
  | [ H : existT _ _ _ = _ |- _ ]
    => induction_sigma_in_using H @path_sigT_rect
  end.
Ltac inversion_sigma := repeat inversion_sigma_step.
