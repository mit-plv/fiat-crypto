(** * Classification of the [×] Type *)
(** In this file, we classify the basic structure of [×] types ([prod]
    in Coq).  In particular, we classify equalities of non-dependent
    pairs (inhabitants of [×] types), so that when we have an equality
    between two such pairs, or when we want such an equality, we have
    a systematic way of reducing such equalities to equalities at
    simpler types. *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.IffT.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.GlobalSettings.

Local Arguments fst {_ _} _.
Local Arguments snd {_ _} _.
Local Arguments f_equal {_ _} _ {_ _} _.

Scheme Equality for prod.

Definition prod_beq_hetero {A1 B1 A2 B2} (A_beq_hetero : A1 -> A2 -> bool) (B_beq_hetero : B1 -> B2 -> bool)
           (x : A1 * B1) (y : A2 * B2) : bool
  := (A_beq_hetero (fst x) (fst y) && B_beq_hetero (snd x) (snd y))%bool.

Arguments prod_beq_hetero {_ _ _ _} _ _ x y / .

Lemma prod_bl_hetero {A1 B1 A2 B2}
      {A_beq_hetero : A1 -> A2 -> bool} {A_R : A1 -> A2 -> Prop}
      {B_beq_hetero : B1 -> B2 -> bool} {B_R : B1 -> B2 -> Prop}
      (A_bl : forall x y, A_beq_hetero x y = true -> A_R x y)
      (B_bl : forall x y, B_beq_hetero x y = true -> B_R x y)
      {x y}
  : prod_beq_hetero A_beq_hetero B_beq_hetero x y = true -> A_R (fst x) (fst y) /\ B_R (snd x) (snd y).
Proof using Type.
  destruct x, y; cbn in *; rewrite ?Bool.andb_true_iff; intuition auto.
Qed.

Lemma prod_lb_hetero {A1 B1 A2 B2}
      {A_beq_hetero : A1 -> A2 -> bool} {A_R : A1 -> A2 -> Prop}
      {B_beq_hetero : B1 -> B2 -> bool} {B_R : B1 -> B2 -> Prop}
      (A_lb : forall x y, A_R x y -> A_beq_hetero x y = true)
      (B_lb : forall x y, B_R x y -> B_beq_hetero x y = true)
      {x y}
  : A_R (fst x) (fst y) /\ B_R (snd x) (snd y) -> prod_beq_hetero A_beq_hetero B_beq_hetero x y = true.
Proof using Type.
  destruct x, y; cbn in *; rewrite ?Bool.andb_true_iff; intuition auto.
Qed.

Lemma prod_beq_hetero_uniform {A B : Type} A_beq B_beq {x y}
  : prod_beq_hetero A_beq B_beq x y = @prod_beq A B A_beq B_beq x y.
Proof. destruct x, y; reflexivity. Qed.

Lemma prod_bl_hetero_eq {A B}
      {A_beq : A -> A -> bool}
      {B_beq : B -> B -> bool}
      (A_bl : forall x y, A_beq x y = true -> x = y)
      (B_bl : forall x y, B_beq x y = true -> x = y)
      {x y}
  : prod_beq_hetero A_beq B_beq x y = true -> x = y.
Proof using Type. rewrite prod_beq_hetero_uniform; now apply internal_prod_dec_bl. Qed.

Lemma prod_lb_hetero_eq {A B}
      {A_beq : A -> A -> bool}
      {B_beq : B -> B -> bool}
      (A_lb : forall x y, x = y -> A_beq x y = true)
      (B_lb : forall x y, x = y -> B_beq x y = true)
      {x y}
  : x = y -> prod_beq_hetero A_beq B_beq x y = true.
Proof using Type. rewrite prod_beq_hetero_uniform; now apply internal_prod_dec_lb. Qed.

Definition fst_pair {A B} (a:A) (b:B) : fst (a,b) = a := eq_refl.
Definition snd_pair {A B} (a:A) (b:B) : snd (a,b) = b := eq_refl.
Create HintDb cancel_pair discriminated. Hint Rewrite @fst_pair @snd_pair : cancel_pair.

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

  (** *** Equality of [pair]s is itself a [prod] *)
  Definition path_pair_uncurried {A B : Type} (a1 a2 : A) (b1 b2 : B)
             (pq : prod (a1 = a2) (b1 = b2))
    : (a1, b1) = (a2, b2)
    := path_prod_uncurried (_, _) (_, _) pq.

  (** *** Curried version of proving equality of prod types *)
  Definition path_prod {A B : Type} (u v : prod A B)
             (p : fst u = fst v) (q : snd u = snd v)
    : u = v
    := path_prod_uncurried u v (pair p q).

  (** *** Curried version of proving equality of prod types *)
  Definition path_pair {A B : Type} (a1 a2 : A) (b1 b2 : B)
             (p : a1 = a2) (q : b1 = b2)
    : (a1, b1) = (a2, b2)
    := path_pair_uncurried _ _ _ _ (pair p q).

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

  Definition path_pair_uncurried_iff {A B}
             (a1 a2 : A) (b1 b2 : B)
    : (a1, b1) = (a2, b2) <-> (prod (a1 = a2) (b1 = b2))
    := path_prod_uncurried_iff (_, _) (_, _).

  (** *** Eta-expansion of [@eq (prod _ _)] *)
  Definition path_prod_eta {A B} {u v : @prod A B} (p : u = v)
    : p = path_prod_uncurried u v (fst_path p, snd_path p).
  Proof. destruct u, p; reflexivity. Defined.

  (** *** Induction principle for [@eq (prod _ _)] *)
  Definition path_prod_rect {A B} {u v : @prod A B} (P : u = v -> Type)
             (f : forall p q, P (path_prod_uncurried u v (p, q)))
    : forall p, P p.
  Proof. intro p; specialize (f (fst_path p) (snd_path p)); destruct u, p; exact f. Defined.
  Definition path_prod_rec {A B u v} (P : u = v :> @prod A B -> Set) := path_prod_rect P.
  Definition path_prod_ind {A B u v} (P : u = v :> @prod A B -> Prop) := path_prod_rec P.

  Definition path_pair_rect {A B} {a1 a2 : A} {b1 b2 : B} (P : (a1, b1) = (a2, b2) -> Type)
             (f : forall p q, P (path_pair_uncurried _ _ _ _ (p, q)))
    : forall p, P p
    := path_prod_rect P f.
  Definition path_pair_rec {A B a1 a2 b1 b2} (P : (a1, b1) = (a2, b2) :> @prod A B -> Set) := path_pair_rect P.
  Definition path_pair_ind {A B a1 a2 b1 b2} (P : (a1, b1) = (a2, b2) :> @prod A B -> Prop) := path_pair_rec P.
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

(** *** [inversion_pair] *)
(** A version of [inversion_prod] that occurs only when there are pairs on both sides *)
Ltac induction_path_pair H :=
  let H0 := fresh H in
  let H1 := fresh H in
  induction H as [H0 H1] using path_pair_rect.
Ltac inversion_pair_step :=
  match goal with
  | [ H : pair _ _ = pair _ _ |- _ ]
    => induction_path_pair H
  | [ H : pair _ _ = pair _ _ |- _ ]
    => induction_path_pair H
  end.
Ltac inversion_pair := repeat inversion_pair_step.


(** This turns a goal like [x = let v := p in let '(x, y) := f v in x
    + y)] into a goal like [x = fst (f p) + snd (f p)].  Note that it
    inlines [let ... in ...] as well as destructuring lets. *)
Ltac only_eta_expand_and_contract_step :=
  match goal with
  | [ |- context[let '(x, y) := ?e in _] ]
    => rewrite (surjective_pairing e)
  | [ H : context[let '(x, y) := ?e in _] |- _ ]
    => rewrite (surjective_pairing e) in H
  | _ => rewrite <- !surjective_pairing
  | [ H : context[(fst ?e, snd ?e)] |- _ ]
    => rewrite <- !surjective_pairing in H
  end.
Ltac only_eta_expand_and_contract := repeat only_eta_expand_and_contract_step.
Ltac eta_expand :=
  repeat first [ progress cbv beta iota zeta
               | only_eta_expand_and_contract_step ].

(** *** [subst_prod] *)
(** The tactic [subst_prod] is like [subst], but it works on equations
    of the form [_ = (x, y)] and [(x, y) = _] for [x] and [y]
    identifiers (or recursively pairs of identitifers). *)
Ltac on_pair_vars tac x :=
  lazymatch x with
  | pair ?x ?y => on_pair_vars tac x; on_pair_vars tac y
  | _ => tac x
  end.
Ltac is_pair_var x := on_pair_vars is_var x.
Ltac do_subst_prod v :=
  lazymatch v with
  | @pair ?A ?B ?x ?y
    => let H := fresh in
       let xy := fresh v in
       remember v as xy eqn:H;
       assert (fst xy = x) by (subst xy; reflexivity);
       assert (snd xy = y) by (subst xy; reflexivity);
       clear H;
       do_subst_prod x; do_subst_prod y;
       try subst xy
  | _ => subst v
  end.
Ltac subst_prod_step :=
  first [ inversion_pair_step
        | match goal with
          | [ H : _ = ?v |- _ ] => is_pair_var v; do_subst_prod v
          | [ H : ?v = _ |- _ ] => is_pair_var v; do_subst_prod v
          end ].
Ltac subst_prod := repeat subst_prod_step.
