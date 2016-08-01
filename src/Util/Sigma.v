Require Import Crypto.Util.Equality.
Require Import Crypto.Util.GlobalSettings.

Local Arguments projT1 {_ _} _.
Local Arguments projT2 {_ _} _.
Local Arguments proj1_sig {_ _} _.
Local Arguments proj1_sig {_ _} _.
Local Arguments f_equal {_ _} _ {_ _} _.

Section sigT.
  Definition pr1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : projT1 u = projT1 v
    := f_equal (@projT1 _ _) p.

  Definition pr2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : eq_rect _ _ (projT2 u) _ (pr1_path p) = projT2 v.
  Proof.
    destruct p; reflexivity.
  Defined.

  Definition path_sigT_uncurried {A : Type} {P : A -> Type} (u v : sigT P)
             (pq : sigT (fun p : projT1 u = projT1 v => eq_rect _ _ (projT2 u) _ p = projT2 v))
  : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  Definition path_sigT {A : Type} {P : A -> Type} (u v : sigT P)
             (p : projT1 u = projT1 v) (q : eq_rect _ _ (projT2 u) _ p = projT2 v)
  : u = v
    := path_sigT_uncurried u v (existT _ p q).

  Definition path_sigT_hprop {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sigT A P)
             (p : projT1 u = projT1 v)
    : u = v
    := path_sigT u v p (P_hprop _ _ _).

  Definition path_sigT_uncurried_iff {A P}
             (u v : @sigT A P)
    : u = v <-> (sigT (fun p : projT1 u = projT1 v => eq_rect _ _ (projT2 u) _ p = projT2 v)).
  Proof.
    split; [ intro; subst; exists eq_refl; reflexivity | apply path_sigT_uncurried ].
  Defined.

  Definition path_sigT_hprop_iff {A P} (P_hprop : forall (x : A) (p q : P x), p = q)
             (u v : @sigT A P)
    : u = v <-> (projT1 u = projT1 v)
    := conj (f_equal projT1) (path_sigT_hprop P_hprop u v).

  Definition path_sigT_nondep {A B : Type} (u v : @sigT A (fun _ => B))
             (p : projT1 u = projT1 v) (q : projT2 u = projT2 v)
  : u = v
    := @path_sigT _ _ u v p (eq_trans (transport_const _ _) q).

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
End sigT.

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
End sig.

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
Ltac inversion_sigma_step :=
  match goal with
  | [ H : exist _ _ _ = exist _ _ _ |- _ ]
    => apply path_sig_uncurried_iff in H; simpl_proj_exist_in H; destruct H
  | [ H : existT _ _ _ = existT _ _ _ |- _ ]
    => apply path_sigT_uncurried_iff in H; simpl_proj_exist_in H; destruct H
  end.
Ltac inversion_sigma := repeat inversion_sigma_step.
