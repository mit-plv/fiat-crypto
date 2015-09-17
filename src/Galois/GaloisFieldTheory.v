
Require Import BinInt BinNat ZArith Znumtheory.
Require Export Coq.Classes.Morphisms Setoid.
Require Export Ring_theory Field_theory Field_tac.
Require Export Crypto.Galois.GaloisField.

Set Implicit Arguments.
Unset Strict Implicits.

Module Type GaloisFieldTheory (M: Modulus) (Field: GaloisField M).
  Import M.
  Import Field.

  (* Notations *)
  Notation "x {+} y" := (GFplus x y)   (at level 60, right associativity).
  Notation "x {-} y" := (GFminus x y)  (at level 60, right associativity).
  Notation "x {*} y" := (GFmult x y)   (at level 50, left associativity).
  Notation "x {/} y" := (GFdiv x y)    (at level 50, left associativity).
  Notation "x {^} y" := (GFexp x y)    (at level 40, left associativity).
  Notation "{1}"     := GFone.
  Notation "{0}"     := GFzero.

  (* Basic Properties *)

  Theorem GFplus_0_l: forall x : GF, {0}{+}x = x.
    intro x. apply gf_eq. unfold GFzero, GFplus, GFToZ; simpl.
    destruct x. destruct e. simpl. rewrite e.
    rewrite Zmod_mod. trivial.
  Qed.

  Theorem GFplus_commutative: forall x y : GF, x{+}y = y{+}x.
    intros x y. apply gf_eq. unfold GFzero, GFplus, GFToZ; simpl.
    destruct x. destruct e.
    destruct y. destruct e0.
    simpl. rewrite Zplus_comm. rewrite e, e0. trivial.
  Qed.

  Theorem GFplus_associative: forall x y z : GF, x{+}y{+}z = (x{+}y){+}z.
    intros x y z. apply gf_eq. unfold GFzero, GFplus, GFToZ; simpl.
    destruct x. destruct e.
    destruct y. destruct e0.
    destruct z. destruct e1.
    simpl. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zplus_assoc. trivial.
  Qed.

  Theorem GFmult_1_l: forall x : GF, {1}{*}x = x.
    intro x. apply gf_eq. unfold GFzero, GFmult, GFToZ; simpl.
    destruct x. destruct e. simpl. rewrite e.

    (* TODO: how do we make this automatic?
    *        I'd like to case, but we need to keep the mod.*)
    assert (forall z,
      match z with
      | 0 => 0
      | Z.pos y' => Z.pos y'
      | Z.neg y' => Z.neg y'
      end = z).
      intros; induction z; simpl; intuition.

    rewrite H, Zmod_mod. trivial.
  Qed.

  Theorem GFmult_commutative: forall x y : GF, x{*}y = y{*}x.
    intros x y. apply gf_eq. unfold GFzero, GFmult, GFToZ; simpl.
    destruct x. destruct e.
    destruct y. destruct e0.
    simpl. rewrite Zmult_comm. rewrite e, e0. trivial.
  Qed.

  Theorem GFmult_associative: forall x y z : GF, x{*}(y{*}z) = x{*}y{*}z.
    intros x y z. apply gf_eq. unfold GFzero, GFmult, GFToZ; simpl.
    destruct x. destruct e.
    destruct y. destruct e0.
    destruct z. destruct e1.
    simpl. rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r, Zmult_assoc. trivial.
  Qed.

  Theorem GFdistributive: forall x y z : GF, (x{+}y){*}z = x{*}z{+}y{*}z.
    intros x y z. apply gf_eq. unfold GFzero, GFmult, GFplus, GFToZ; simpl.
    destruct x. destruct e.
    destruct y. destruct e0.
    destruct z. destruct e1.
    simpl.
    rewrite Zmult_mod_idemp_l.
    rewrite <- Zplus_mod.
    rewrite Z.mul_add_distr_r.
    trivial.
  Qed.

  Theorem GFminus_opp: forall x y : GF, x{-}y = x{+}GFopp y.
    intros x y. apply gf_eq. unfold GFzero, GFmult, GFToZ; simpl.
    destruct x. destruct e.
    destruct y. destruct e0.
    simpl.
    rewrite Zplus_mod_idemp_r.
    trivial.
  Qed.

  Theorem GFopp_inverse: forall x : GF, x{+}GFopp x = {0}.
    intro x. apply gf_eq. unfold GFzero, GFplus, GFToZ; simpl.
    destruct x. destruct e. simpl. rewrite e.
    rewrite <- Zplus_mod.
    rewrite Z.add_opp_r.
    rewrite Zminus_mod_idemp_r.
    rewrite Z.sub_diag.
    trivial.
  Qed.

  (* Ring Theory*)

  Instance GFplus_compat : Proper (eq==>eq==>eq) GFplus.
    intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; intuition; simpl in *.
    assert (p1 + r1 = q1 + s1).
      apply exist_eq in H; apply exist_eq in H0. rewrite H, H0. trivial.
    unfold GFplus; simpl; rewrite H1; trivial.
  Qed.

  Instance GFminus_compat : Proper (eq==>eq==>eq) GFminus.
    intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; intuition; simpl in *.
    assert (p1 - r1 = q1 - s1).
      apply exist_eq in H; apply exist_eq in H0. rewrite H, H0. trivial.
    unfold GFminus; simpl; rewrite H1; trivial.
  Qed.

  Instance GFmult_compat : Proper (eq==>eq==>eq) GFmult.
    intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; intuition; simpl in *.
    assert (p1 * r1 = q1 * s1).
      apply exist_eq in H; apply exist_eq in H0. rewrite H, H0. trivial.
    unfold GFmult; simpl; rewrite H1; trivial.
  Qed.

  Instance GFopp_compat : Proper (eq==>eq) GFopp.
    intros x y H; intuition; simpl in *.
    unfold GFopp, GFzero, GFminus; simpl. apply exist_eq.
    destruct x. destruct e. rewrite e in *.
    destruct y. destruct e0. rewrite e0 in *.
    simpl in *. apply exist_eq in H.

    assert (HX := (Z.eq_dec (x0 mod modulus) 0)); destruct HX.
    rewrite e1; rewrite H in e1; rewrite e1; simpl; intuition.
    repeat rewrite Z_mod_nz_opp_full;
      try repeat rewrite Zmod_mod;
      simpl; intuition.
  Qed.

  Definition GFring_theory : ring_theory GFzero GFone GFplus GFmult GFminus GFopp eq.
    constructor.
    exact GFplus_0_l.
    exact GFplus_commutative.
    exact GFplus_associative.
    exact GFmult_1_l.
    exact GFmult_commutative.
    exact GFmult_associative.
    exact GFdistributive.
    exact GFminus_opp.
    exact GFopp_inverse.
  Defined.

  Add Ring GFring : GFring_theory.

  (* Power theory *)


  Lemma GFpower_theory : power_theory GFone GFmult eq id GFexp.
    constructor. intros.
    induction n; simpl; intuition.

    (* Prove the doubling case, which we'll use alot *)
    assert (forall q r0, GFexp' r0 q{*}GFexp' r0 q = GFexp' (r0{*}r0) q).
      induction q.
      intros. assert (Q := (IHq (r0{*}r0))).
        unfold GFexp'; simpl; fold GFexp'.
        rewrite <- Q. ring.
      intros. assert (Q := (IHq (r0{*}r0))).
        unfold GFexp'; simpl; fold GFexp'.
        rewrite <- Q. ring.
      intros; simpl; ring.

    (* Take it case-by-case *)
    unfold GFexp; induction p.

    (* Odd case *)
    unfold GFexp'; simpl; fold GFexp'; fold pow_pos.
    rewrite <- (H p r).
    rewrite <- IHp. trivial.

    (* Even case *)
    unfold GFexp'; simpl; fold GFexp'; fold pow_pos.
    rewrite <- (H p r).
    rewrite <- IHp. trivial.

    (* Base case *)
    simpl; intuition.
  Qed.

  (* Field Theory*)

  Instance GFinv_compat : Proper (eq==>eq) GFinv.
    unfold GFinv; simpl; intuition.
  Qed.

  Instance GFdiv_compat : Proper (eq==>eq==>eq) GFdiv.
    unfold GFdiv; simpl; intuition.
  Qed.

  Definition GFfield_theory : field_theory GFzero GFone GFplus GFmult GFminus GFopp GFdiv GFinv eq.
    constructor; simpl; intuition.
    exact GFring_theory.
    unfold GFone, GFzero in H; apply exist_eq in H; simpl in H; intuition.

    (* Prove multiplicative inverses *)
    unfold GFinv.
    destruct totient; simpl. destruct i.
    replace (p{^}(N.pred x){*}p) with (p{^}x); simpl; intuition.
    apply N.gt_lt in H0; apply N.lt_neq in H0.
    replace x with (N.succ (N.pred x)).
      induction (N.pred x).
      simpl. ring.
      rewrite N.pred_succ.

    (* Just the N.succ case *)
    generalize p. induction p0; simpl in *; intuition.
      rewrite (IHp0 (p1{*}p1)). ring.
      ring.

    (* cleanup *)
    rewrite N.succ_pred; intuition.
  Defined.

  Add Field GFfield : GFfield_theory.

End GaloisFieldTheory.

