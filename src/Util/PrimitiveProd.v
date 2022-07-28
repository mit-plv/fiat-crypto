(** * Definition and classification of the [×] Type, with primitive projections *)
(** In this file, we classify the basic structure of [×] types ([prod]
    in Coq).  In particular, we classify equalities of non-dependent
    pairs (inhabitants of [×] types), so that when we have an equality
    between two such pairs, or when we want such an equality, we have
    a systematic way of reducing such equalities to equalities at
    simpler types. *)
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.IffT.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.GlobalSettings.

Local Set Primitive Projections.

Declare Scope primproj_type_scope.
Declare Scope primproj_scope.
Delimit Scope primproj_type_scope with primproj_type.
Delimit Scope primproj_scope with primproj.

Module Import Primitive.
  Record prod A B := pair { fst : A ; snd : B }.
  Global Arguments pair {_ _}.
  Global Arguments fst {_ _}.
  Global Arguments snd {_ _}.

  Module Export Notations.
    Notation "x * y" := (@prod x y) : type_scope.
    Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
  End Notations.

  Local Set Implicit Arguments.
  Definition prod_beq A B (eq_A : A -> A -> bool) (eq_B : B -> B -> bool) (X Y : A * B) : bool
    := let '(a, b) := X in let '(a', b') := Y in (eq_A a a' && eq_B b b')%bool.
  Global Arguments prod_beq / .
  Lemma prod_dec_bl A B eq_A eq_B
        (A_bl : forall x y : A, eq_A x y = true -> x = y)
        (B_bl : forall x y : B, eq_B x y = true -> x = y)
        (x y : A * B)
    : prod_beq eq_A eq_B x y = true -> x = y.
  Proof.
    destruct x as [a b], y as [a' b'].
    specialize (A_bl a a'); specialize (B_bl b b').
    cbn; intro H; destruct A_bl; [ | destruct B_bl; [ | reflexivity ] ];
      edestruct eq_A; edestruct eq_B; cbn in *; try reflexivity; try assumption.
  Defined.
  Lemma prod_dec_lb A B eq_A eq_B
        (A_lb : forall x y : A, x = y -> eq_A x y = true)
        (B_lb : forall x y : B, x = y -> eq_B x y = true)
        (x y : A * B)
    : x = y -> prod_beq eq_A eq_B x y = true.
  Proof.
    intro H; specialize (A_lb _ _ (f_equal fst H)); specialize (B_lb _ _ (f_equal snd H)).
    cbn in *; cbv [fst snd] in *.
    rewrite A_lb, B_lb; reflexivity.
  Defined.
  Definition prod_eq_dec A B eq_A eq_B
        (A_bl : forall x y : A, eq_A x y = true -> x = y)
        (B_bl : forall x y : B, eq_B x y = true -> x = y)
        (A_lb : forall x y : A, x = y -> eq_A x y = true)
        (B_lb : forall x y : B, x = y -> eq_B x y = true)
        (x y : A * B)
    : {x = y} + {x <> y}.
  Proof.
    refine (let H := let b := @prod_beq A B eq_A eq_B x y in if b as b0 return ({b0 = true} + {b0 = false}) then left eq_refl else right eq_refl in
            match H with
            | left e => left (@prod_dec_bl A B eq_A eq_B A_bl B_bl x y e)
            | right H' => right (fun e => _ (@prod_dec_lb A B eq_A eq_B A_lb B_lb x y e))
            end).
    congruence.
  Defined.
End Primitive.
Notation "x * y" := (@prod x%primproj_type y%primproj_type) : primproj_type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x%primproj y%primproj) .. z%primproj) : primproj_scope.

Local Arguments f_equal {_ _} _ {_ _} _.

Definition fst_pair {A B} (a:A) (b:B) : fst (a,b) = a := eq_refl.
Definition snd_pair {A B} (a:A) (b:B) : snd (a,b) = b := eq_refl.
Create HintDb cancel_primpair discriminated. #[global] Hint Rewrite @fst_pair @snd_pair : cancel_primpair.

(** ** Equality for [prod] *)
Section prod.
  (** *** Projecting an equality of a pair to equality of the first components *)
  Definition fst_path {A B} {u v : prod A B} (p : u = v)
  : fst u = fst v
    := f_equal fst p.

  (** *** Projecting an equality of a pair to equality of the second components *)
  Definition snd_path {A B} {u v : prod A B} (p : u = v)
  : snd u = snd v
    := f_equal snd p.

  (** *** Equality of [prod] is itself a [prod] *)
  Definition path_prod_uncurried {A B : Type} (u v : prod A B)
             (pq : prod (fst u = fst v) (snd u = snd v))
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct p, q; simpl in *.
    reflexivity.
  Defined.

  (** *** Curried version of proving equality of sigma types *)
  Definition path_prod {A B : Type} (u v : prod A B)
             (p : fst u = fst v) (q : snd u = snd v)
    : u = v
    := path_prod_uncurried u v (pair p q).

  (** *** Equivalence of equality of [prod] with a [prod] of equality *)
  (** We could actually use [IsIso] here, but for simplicity, we
      don't.  If we wanted to deal with proofs of equality of × types
      in dependent positions, we'd need it. *)
  Definition path_prod_uncurried_iff {A B}
             (u v : @prod A B)
    : u = v <-> (prod (fst u = fst v) (snd u = snd v)).
  Proof.
    split; [ intro; subst; split; reflexivity | apply path_prod_uncurried ].
  Defined.

  (** *** Eta-expansion of [@eq (prod _ _)] *)
  Definition path_prod_eta {A B} {u v : @prod A B} (p : u = v)
    : p = path_prod_uncurried u v (fst_path p, snd_path p).
  Proof. destruct p; reflexivity. Defined.

  (** *** Induction principle for [@eq (prod _ _)] *)
  Definition path_prod_rect {A B} {u v : @prod A B} (P : u = v -> Type)
             (f : forall p q, P (path_prod_uncurried u v (p, q)))
    : forall p, P p.
  Proof. intro p; specialize (f (fst_path p) (snd_path p)); destruct p; exact f. Defined.
  Definition path_prod_rec {A B u v} (P : u = v :> @prod A B -> Set) := path_prod_rect P.
  Definition path_prod_ind {A B u v} (P : u = v :> @prod A B -> Prop) := path_prod_rec P.
End prod.

Lemma prod_iff_and (A B : Prop) : (A /\ B) <-> (A * B).
Proof. repeat (intros [? ?] || intro || split); assumption. Defined.

Global Instance iff_prod_Proper
  : Proper (iff ==> iff ==> iff) (fun A B => prod A B).
Proof. repeat intro; tauto. Defined.
Global Instance iff_iffTp_prod_Proper
  : Proper (iff ==> iffTp ==> iffTp) (fun A B => prod A B) | 1.
Proof.
  intros ?? [?] ?? [?]; constructor; tauto.
Defined.
Global Instance iffTp_iff_prod_Proper
  : Proper (iffTp ==> iff ==> iffTp) (fun A B => prod A B) | 1.
Proof.
  intros ?? [?] ?? [?]; constructor; tauto.
Defined.
Global Instance iffTp_iffTp_prod_Proper
  : Proper (iffTp ==> iffTp ==> iffTp) (fun A B => prod A B) | 1.
Proof.
  intros ?? [?] ?? [?]; constructor; tauto.
Defined.
Global Hint Extern 2 (Proper _ prod) => apply iffTp_iffTp_prod_Proper : typeclass_instances.
Global Hint Extern 2 (Proper _ (fun A => prod A)) => refine iff_iffTp_prod_Proper : typeclass_instances.
Global Hint Extern 2 (Proper _ (fun A B => prod A B)) => refine iff_prod_Proper : typeclass_instances.

(** ** Useful Tactics *)
(** *** [inversion_prod] *)
Ltac simpl_proj_pair_in H :=
  repeat match type of H with
         | context G[fst (pair ?x ?p)]
           => let G' := context G[x] in change G' in H
         | context G[snd (pair ?x ?p)]
           => let G' := context G[p] in change G' in H
         end.
Ltac induction_path_prod H :=
  let H0 := fresh H in
  let H1 := fresh H in
  induction H as [H0 H1] using path_prod_rect;
  simpl_proj_pair_in H0;
  simpl_proj_pair_in H1.
Ltac inversion_prod_step :=
  match goal with
  | [ H : _ = pair _ _ |- _ ]
    => induction_path_prod H
  | [ H : pair _ _ = _ |- _ ]
    => induction_path_prod H
  end.
Ltac inversion_prod := repeat inversion_prod_step.

(** *** [subst_prod] *)
(** The tactic [subst_prod] is like [subst], but it works on equations
    of the form [_ = (x, y)] and [(x, y) = _] for [x] and [y]
    identifiers. *)
Ltac do_subst_prod A B x y :=
  is_var x; is_var y;
  let H := fresh in
  let xy := fresh x in
  remember (@pair A B x y) as xy eqn:H;
  assert (fst xy = x) by (subst xy; reflexivity);
  assert (snd xy = y) by (subst xy; reflexivity);
  subst x y;
  clear H; try subst xy.
Ltac subst_prod_step :=
  match goal with
  | [ H : _ = @pair ?A ?B ?x ?y |- _ ] => do_subst_prod A B x y
  | [ H : @pair ?A ?B ?x ?y = _ |- _ ] => do_subst_prod A B x y
  end.
Ltac subst_prod := repeat subst_prod_step.
