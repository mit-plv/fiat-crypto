Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.IsTrue.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Notations.

Delimit Scope zbounded_scope with zbounded.
Local Open Scope Z_scope.
Local Set Primitive Projections.
Record zbounded {r : zrange}
  := { value :> Z ;
       value_bounded : is_true ((upper r <? lower r)
                                || ((lower r <=? value) && (value <=? upper r))) }.
Bind Scope zbounded_scope with zbounded.
Global Arguments Build_zbounded {r} value {_}, {r} value _, r value _.
Global Arguments zbounded r : clear implicits.

Definition adjust_zbounded {r} (v : zbounded r) : zbounded r
  := {| value := value v ;
        value_bounded := adjust_is_true (value_bounded v) |}.

(** ** Equality for [zbounded] *)
Section eq.
  Definition value_path {r} {u v : zbounded r} (p : u = v)
  : value u = value v
    := f_equal (@value _) p.

  Definition value_bounded_path {r} {u v : zbounded r} (p : u = v)
    : eq_rect
        _ (fun v => is_true (_ || ((lower r <=? v) && (v <=? upper r))))
        (value_bounded u) _ (value_path p)
      = value_bounded v.
  Proof.
    destruct p; reflexivity.
  Defined.

  Definition path_zbounded_full {r} (u v : zbounded r)
             (p : value u = value v)
             (q : eq_rect
                    _ (fun v => is_true (_ || ((lower r <=? v) && (v <=? upper r))))
                    (value_bounded u) _ p
                  = value_bounded v)
    : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *; subst v1 v2; reflexivity.
  Defined.

  Definition path_zbounded {r} (u v : zbounded r)
             (p : value u = value v)
    : u = v.
  Proof.
    apply (path_zbounded_full u v p).
    destruct u as [u1 u2], v as [v1 v2]; simpl in *; subst v1; simpl.
    let P := lazymatch type of u2 with is_true ?P => P end in
    generalize dependent P.
    compute; intros b p q; clear.
    transitivity (adjust_is_true q); clear; subst; reflexivity.
  Defined.

  Definition path_zbounded_rect_full {r} {u v : zbounded r} (Q : u = v -> Type)
             (f : forall p q, Q (path_zbounded_full u v p q))
    : forall p, Q p.
  Proof.
    intro p; specialize (f (value_path p) (value_bounded_path p));
      destruct u as [u0 u1], p; exact f.
  Defined.
  Definition path_zbounded_rec_full {r u v} (Q : u = v :> zbounded r -> Set) := path_zbounded_rect_full Q.
  Definition path_zbounded_ind_full {r u v} (Q : u = v :> zbounded r -> Prop) := path_zbounded_rec_full Q.

  Definition path_zbounded_rect {r} {u v : zbounded r} (Q : u = v -> Type)
             (f : forall p, Q (path_zbounded u v p))
    : forall p, Q p.
  Proof.
    intro p; specialize (f (value_path p));
      destruct u as [u0 u1], p.
    simpl in *.
    generalize dependent (@Build_zbounded r u0); intros.
    let P := lazymatch type of u1 with is_true ?P => P end in
    generalize dependent P; intros.
    unfold is_true in *.
    subst.
    exact f.
  Defined.
  Definition path_zbounded_rec {r u v} (Q : u = v :> zbounded r -> Set) := path_zbounded_rect Q.
  Definition path_zbounded_ind {r u v} (Q : u = v :> zbounded r -> Prop) := path_zbounded_rec Q.

  (** *** η Principle for [zbounded] *)
  Definition sigT_eta {r} (p : zbounded r)
    : p = {| value := value p ; value_bounded := value_bounded p |}
    := eq_refl.
End eq.

Ltac induction_zbounded_in_as_using H H0 H1 rect :=
  induction H as [H0 H1] using (rect _ _ _);
  cbn [value value_bounded] in H0, H1.
Ltac induction_zbounded_in_using H rect :=
  let H0 := fresh H in
  let H1 := fresh H in
  induction_zbounded_in_as_using H H0 H1 rect.
Ltac inversion_zbounded_step :=
  match goal with
  | [ H : _ = @Build_zbounded _ _ _ |- _ ]
    => induction_zbounded_in_using H @path_zbounded_rect_full
  | [ H : @Build_zbounded _ _ _ = _ |- _ ]
    => induction_zbounded_in_using H @path_zbounded_rect_full
  end.
Ltac inversion_zbounded := repeat inversion_zbounded_step.

Lemma is_bounded_by'_zbounded {r} (v : zbounded r) : lower r <= upper r -> is_bounded_by' None r v.
Proof.
  destruct v as [v H]; cbv [is_bounded_by']; simpl.
  apply Bool.orb_true_iff in H; destruct H; split_andb; Z.ltb_to_lt; try omega.
  intros; repeat apply conj; trivial.
Qed.

Global Instance dec_eq_zrange {r} : DecidableRel (@eq (zbounded r)) | 10.
Proof.
  intros [x ?] [y ?].
  destruct (dec (x = y));
    [ left; apply path_zbounded; assumption
    | abstract (right; intro H; inversion_zbounded; tauto) ].
Defined.

Definition modulo (z : Z) (r : zrange) : zbounded r.
Proof.
  refine {| value := if (upper r <? lower r)
                     then z
                     else lower r + Z.modulo (z - lower r) (upper r - lower r + 1) |}.
  abstract (
      destruct (upper r <? lower r) eqn:H; [ reflexivity | ];
      pose proof (Z.mod_pos_bound (z - lower r) (upper r - lower r + 1)) as Hmod;
      destruct r as [l u];
      simpl in *; apply Bool.andb_true_iff; split;
      destruct (l =? u) eqn:H';
      Z.ltb_to_lt; subst;
      repeat rewrite ?Z.sub_diag, ?Zmod_0_r, ?Z.add_0_r, ?Z.add_0_l, ?Z.mod_1_r;
      try reflexivity; try omega
    ).
Defined.

Lemma modulo_value_id {r} (v : zbounded r) : modulo (value v) r = v.
Proof.
  apply path_zbounded; simpl.
  destruct v as [v H]; simpl.
  destruct (upper r <? lower r) eqn:H'; [ reflexivity | ].
  simpl in *; unfold is_true in *; split_andb; Z.ltb_to_lt.
  rewrite Z.mod_small by omega.
  omega.
Qed.
