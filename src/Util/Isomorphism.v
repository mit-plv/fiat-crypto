(** * Isomorphisms *)
(** Following the category-theoretic definition, [f : A → B] is an
    isomorphism when it has an inverse [f⁻¹ : B → A] which is both a
    left and a right inverse.  In the language of homotopy type
    theory, we are formalizing quasi-invertibility; this notion of
    isomorphism is not an hProp.  The better notations of equivalence
    (such that all proofs of [IsEquiv f] are equal when only assuming
    function extensionality) are more complicated.  Possibilities
    include: *)

(** - Adjoint equivalence, the default of HoTT/HoTT: *)
(**
<<
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.
>> *)
(** - Contractible fibers: [∀ y : B, Contr { x : A | f x = y }] where
      [Contr T := { center : T | forall y, center = y }] *)

(** This is useful for classifying equalities in a theoretically nice
    way. *)

Class IsIso {A B} (f : A -> B) :=
  { iso_inv : B -> A;
    is_right_inv : forall x, f (iso_inv x) = x;
    is_left_inv : forall x, iso_inv (f x) = x }.

Arguments iso_inv {_ _} _ {_} _.
Arguments is_right_inv {_ _} _ {_} _.
Arguments is_left_inv {_ _} _ {_} _.
