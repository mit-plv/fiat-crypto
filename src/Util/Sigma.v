(** * Classification of the Σ Type *)
(** In this file, we classify the basic structure of Σ types ([sigT],
    [sig], and [ex], in Coq).  In particular, we classify equalities
    of dependent pairs (inhabitants of Σ types), so that when we have
    an equality between two such pairs, or when we want such an
    equality, we have a systematic way of reducing such equalities to
    equalities at simpler types. *)
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.GlobalSettings.

Local Arguments projT1 {_ _} _.
Local Arguments projT2 {_ _} _.
Local Arguments proj1_sig {_ _} _.
Local Arguments proj1_sig {_ _} _.
Local Arguments f_equal {_ _} _ {_ _} _.

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
  Proof. intro p; specialize (f (pr1_path p) (pr2_path p)); destruct u, p; exact f. Defined.
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
    destruct H, u; reflexivity.
  Defined.

  (** *** η Principle for [sigT] *)
  Definition sigT_eta {A P} (p : { a : A & P a })
    : p = existT _ (projT1 p) (projT2 p).
  Proof. destruct p; reflexivity. Defined.

  (** *** Boolean equality for [sigT] *)
  Definition sigT_beq {A A' P P'} (eqA : A -> A' -> bool) (eqP : forall a a', P a -> P' a' -> bool) (p : { a : A & P a }) (q : { a' : A' & P' a' })
    : bool
    := andb (eqA (projT1 p) (projT1 q)) (eqP _ _ (projT2 p) (projT2 q)).

  Lemma sigT_dec_bl {A P}
        (eqA : A -> A -> bool) (eqP : forall a a', P a -> P a' -> bool)
        (blA : forall a a', eqA a a' = true -> a = a')
        (blP : forall a p p', eqP a a p p' = true -> p = p')
        {p q}
    : sigT_beq eqA eqP p q = true -> p = q.
  Proof.
    destruct p as [a p], q as [a' q]; cbv.
    specialize (blA a a'); specialize (blP a p).
    destruct (eqA a a') eqn:H'; [ specialize (blA eq_refl) | discriminate ]; subst.
    intro H''; specialize (blP _ H''); subst; reflexivity.
  Qed.

  Lemma sigT_dec_lb {A P}
        (eqA : A -> A -> bool) (eqP : forall a a', P a -> P a' -> bool)
        (lbA : forall a a', a = a' -> eqA a a' = true)
        (lbP : forall a p p', p = p' -> eqP a a p p' = true)
        {p q}
    : p = q -> sigT_beq eqA eqP p q = true.
  Proof.
    intro; subst q; destruct p as [a p]; cbv in *.
    specialize (lbA a a eq_refl); specialize (lbP a p p eq_refl).
    now rewrite lbA, lbP.
  Qed.

  Lemma sigT_dec_bl_hprop {A P}
        (eqA : A -> A -> bool)
        (blA : forall a a', eqA a a' = true -> a = a')
        (P_hprop : forall (x : A) (p q : P x), p = q)
        {p q}
    : @sigT_beq A A P P eqA (fun _ _ _ _ => true) p q = true -> p = q.
  Proof. apply sigT_dec_bl; eauto. Qed.

  Lemma sigT_dec_lb_hprop {A P}
        (eqA : A -> A -> bool)
        (lbA : forall a a', a = a' -> eqA a a' = true)
        (P_hprop : forall (x : A) (p q : P x), p = q)
        {p q}
    : p = q -> @sigT_beq A A P P eqA (fun _ _ _ _ => true) p q = true.
  Proof. apply sigT_dec_lb; eauto. Qed.

  Definition sigT_eq_dec {A P}
             (eqA : A -> A -> bool) (eqP : forall a a', P a -> P a' -> bool)
             (blA : forall a a', eqA a a' = true -> a = a')
             (blP : forall a p p', eqP a a p p' = true -> p = p')
             (lbA : forall a a', a = a' -> eqA a a' = true)
             (lbP : forall a p p', p = p' -> eqP a a p p' = true)
             (p q : { a : A & P a })
    : {p = q} + {p <> q}.
  Proof.
    destruct (sigT_beq eqA eqP p q) eqn:H; [ left | right; intro H' ].
    { eapply sigT_dec_bl; eassumption. }
    { eapply sigT_dec_lb in H'; [ | eassumption.. ].
      generalize (eq_trans (eq_sym H) H'); clear; abstract discriminate. }
  Defined.
End sigT.

(** ** Equality for [sig] *)
Section sig.
  Definition proj1_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : proj1_sig u = proj1_sig v
    := f_equal (@proj1_sig _ _) p.

  Definition proj2_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : eq_rect _ _ (proj2_sig u) _ (proj1_sig_path p) = proj2_sig v.
  Proof.
    destruct p; reflexivity.
  Defined.

  Definition path_sig_uncurried {A : Type} {P : A -> Prop} (u v : sig P)
             (pq : {p : proj1_sig u = proj1_sig v | eq_rect _ _ (proj2_sig u) _ p = proj2_sig v})
  : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  Definition path_sig {A : Type} {P : A -> Prop} (u v : sig P)
             (p : proj1_sig u = proj1_sig v) (q : eq_rect _ _ (proj2_sig u) _ p = proj2_sig v)
  : u = v
    := path_sig_uncurried u v (exist _ p q).

  Definition path_sig_rect {A P} {u v : @sig A P} (Q : u = v -> Type)
             (f : forall p q, Q (path_sig u v p q))
    : forall p, Q p.
  Proof. intro p; specialize (f (proj1_sig_path p) (proj2_sig_path p)); destruct u, p; exact f. Defined.
  Definition path_sig_rec {A P u v} (Q : u = v :> @sig A P -> Set) := path_sig_rect Q.
  Definition path_sig_ind {A P u v} (Q : u = v :> @sig A P -> Prop) := path_sig_rec Q.

  Definition path_sig_hprop {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sig A P)
             (p : proj1_sig u = proj1_sig v)
    : u = v
    := path_sig u v p (P_hprop _ _ _).

  Definition path_sig_uncurried_iff {A} {P : A -> Prop}
             (u v : @sig A P)
    : u = v <-> (sig (fun p : proj1_sig u = proj1_sig v => eq_rect _ _ (proj2_sig u) _ p = proj2_sig v)).
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply path_sig_uncurried ].
  Defined.

  Definition path_sig_hprop_iff {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sig A P)
    : u = v <-> (proj1_sig u = proj1_sig v)
    := conj (f_equal proj1_sig) (path_sig_hprop P_hprop u v).

  Lemma eq_rect_sig {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sig (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => sig (Q a)) u y H
    = exist
        (Q y)
        (eq_rect x P (proj1_sig u) y H)
        match H in (_ = y) return Q y (eq_rect x P (proj1_sig u) y H) with
          | eq_refl => proj2_sig u
        end.
  Proof.
    destruct H, u; reflexivity.
  Defined.

  (** *** η Principle for [sig] *)
  Definition sig_eta {A P} (p : { a : A | P a })
    : p = exist _ (proj1_sig p) (proj2_sig p).
  Proof. destruct p; reflexivity. Defined.

  (** *** Boolean equality for [sig] *)
  Definition sig_beq {A A'} {P P' : _ -> Prop} (eqA : A -> A' -> bool) (eqP : forall a a', P a -> P' a' -> bool) (p : { a : A | P a }) (q : { a' : A' | P' a' })
    : bool
    := andb (eqA (proj1_sig p) (proj1_sig q)) (eqP _ _ (proj2_sig p) (proj2_sig q)).

  Lemma sig_dec_bl {A} {P : A -> Prop}
        (eqA : A -> A -> bool) (eqP : forall a a', P a -> P a' -> bool)
        (blA : forall a a', eqA a a' = true -> a = a')
        (blP : forall a p p', eqP a a p p' = true -> p = p')
        {p q}
    : sig_beq eqA eqP p q = true -> p = q.
  Proof.
    destruct p as [a p], q as [a' q]; cbv.
    specialize (blA a a'); specialize (blP a p).
    destruct (eqA a a') eqn:H'; [ specialize (blA eq_refl) | discriminate ]; subst.
    intro H''; specialize (blP _ H''); subst; reflexivity.
  Qed.

  Lemma sig_dec_lb {A} {P : A -> Prop}
        (eqA : A -> A -> bool) (eqP : forall a a', P a -> P a' -> bool)
        (lbA : forall a a', a = a' -> eqA a a' = true)
        (lbP : forall a p p', p = p' -> eqP a a p p' = true)
        {p q}
    : p = q -> sig_beq eqA eqP p q = true.
  Proof.
    intro; subst q; destruct p as [a p]; cbv in *.
    specialize (lbA a a eq_refl); specialize (lbP a p p eq_refl).
    now rewrite lbA, lbP.
  Qed.

  Lemma sig_dec_bl_hprop {A} {P : A -> Prop}
        (eqA : A -> A -> bool)
        (blA : forall a a', eqA a a' = true -> a = a')
        (P_hprop : forall (x : A) (p q : P x), p = q)
        {p q}
    : @sig_beq A A P P eqA (fun _ _ _ _ => true) p q = true -> p = q.
  Proof. apply sig_dec_bl; eauto. Qed.

  Lemma sig_dec_lb_hprop {A} {P : A -> Prop}
        (eqA : A -> A -> bool)
        (lbA : forall a a', a = a' -> eqA a a' = true)
        (P_hprop : forall (x : A) (p q : P x), p = q)
        {p q}
    : p = q -> @sig_beq A A P P eqA (fun _ _ _ _ => true) p q = true.
  Proof. apply sig_dec_lb; eauto. Qed.

  Definition sig_eq_dec {A} {P : A -> Prop}
             (eqA : A -> A -> bool) (eqP : forall a a', P a -> P a' -> bool)
             (blA : forall a a', eqA a a' = true -> a = a')
             (blP : forall a p p', eqP a a p p' = true -> p = p')
             (lbA : forall a a', a = a' -> eqA a a' = true)
             (lbP : forall a p p', p = p' -> eqP a a p p' = true)
             (p q : { a : A | P a })
    : {p = q} + {p <> q}.
  Proof.
    destruct (sig_beq eqA eqP p q) eqn:H; [ left | right; intro H' ].
    { eapply sig_dec_bl; eassumption. }
    { eapply sig_dec_lb in H'; [ | eassumption.. ].
      generalize (eq_trans (eq_sym H) H'); clear; abstract discriminate. }
  Defined.
End sig.

(** ** Equality for [ex] *)
Section ex.
  Definition path_ex_uncurried' {A : Type} (P : A -> Prop) {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : exists p : u1 = v1, eq_rect _ _ u2 _ p = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2.
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  Definition path_ex' {A : Type} {P : A -> Prop} (u1 v1 : A) (u2 : P u1) (v2 : P v1)
             (p : u1 = v1) (q : eq_rect _ _ u2 _ p = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2
    := path_ex_uncurried' P (ex_intro _ p q).

  Definition path_ex'_hprop {A} {P : A -> Prop} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u1 v1 : A) (u2 : P u1) (v2 : P v1)
             (p : u1 = v1)
    : ex_intro P u1 u2 = ex_intro P v1 v2
    := path_ex' u1 v1 u2 v2 p (P_hprop _ _ _).

  Lemma eq_rect_ex {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : ex (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => ex (Q a)) u y H
    = match u with
        | ex_intro u1 u2
          => ex_intro
               (Q y)
               (eq_rect x P u1 y H)
               match H in (_ = y) return Q y (eq_rect x P u1 y H) with
                 | eq_refl => u2
               end
      end.
  Proof.
    destruct H, u; reflexivity.
  Defined.
End ex.

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
         | context G[proj1_sig (exist _ ?x ?p)]
           => let G' := context G[x] in change G' in H
         | context G[proj2_sig (exist _ ?x ?p)]
           => let G' := context G[p] in change G' in H
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
  | [ H : _ = exist _ _ _ |- _ ]
    => induction_sigma_in_using H @path_sig_rect
  | [ H : _ = existT _ _ _ |- _ ]
    => induction_sigma_in_using H @path_sigT_rect
  | [ H : exist _ _ _ = _ |- _ ]
    => induction_sigma_in_using H @path_sig_rect
  | [ H : existT _ _ _ = _ |- _ ]
    => induction_sigma_in_using H @path_sigT_rect
  end.
Ltac inversion_sigma := repeat inversion_sigma_step.
