
Require Import BinInt BinNat ZArith Znumtheory.
Require Export Coq.Classes.Morphisms Setoid.
Require Export Ring_theory Field_theory Field_tac.
Require Export Crypto.Galois.GaloisField.

Set Implicit Arguments.
Unset Strict Implicits.

Module GaloisFieldTheory (M: Modulus).
  Module Field := GaloisField M.
  Import M Field.

  (* Notations *)
  Infix "{+}"    := GFplus   (at level 60, right associativity).
  Infix "{-}"    := GFminus  (at level 60, right associativity).
  Infix "{*}"    := GFmult   (at level 50, left associativity).
  Infix "{/}"    := GFdiv    (at level 50, left associativity).
  Infix "{^}"    := GFexp    (at level 40, left associativity).
  Notation "{1}" := GFone.
  Notation "{0}" := GFzero.

  (* Basic Properties *)

  (* Fails iff the input term does some arithmetic with mod'd values. *)
  Ltac notFancy E :=
    match E with
    | - (_ mod _) => idtac
    | context[_ mod _] => fail 1
    | _ => idtac
    end.

  Lemma Zplus_neg : forall n m, n + -m = n - m.
  Proof.
    auto.
  Qed.

  (* Remove redundant [mod] operations from the conclusion. *)
  Ltac demod :=
    repeat match goal with
           | [ |- context[(?x mod _ + _) mod _] ] =>
             notFancy x; rewrite (Zplus_mod_idemp_l x)
           | [ |- context[(_ + ?y mod _) mod _] ] =>
             notFancy y; rewrite (Zplus_mod_idemp_r y)
           | [ |- context[(?x mod _ - _) mod _] ] =>
             notFancy x; rewrite (Zminus_mod_idemp_l x)
           | [ |- context[(_ - ?y mod _) mod _] ] =>
             notFancy y; rewrite (Zminus_mod_idemp_r _ y)
           | [ |- context[(?x mod _ * _) mod _] ] =>
             notFancy x; rewrite (Zmult_mod_idemp_l x)
           | [ |- context[(_ * (?y mod _)) mod _] ] =>
             notFancy y; rewrite (Zmult_mod_idemp_r y)
           | _ => rewrite Zplus_neg in * || rewrite Z.sub_diag in *
           end.

  (* General big hammer for proving Galois arithmetic facts *)
  Ltac galois := intros; apply gf_eq; simpl;
                 repeat match goal with
                        | [ x : GF |- _ ] => destruct x
                        | [ H : ex _ |- _ ] => destruct H; subst
                        end; simpl in *; autorewrite with core;
                 intuition; demod; try solve [ f_equal; intuition ].

  Lemma modmatch_eta : forall n,
    match n with
    | 0 => 0
    | Z.pos y' => Z.pos y'
    | Z.neg y' => Z.neg y'
    end = n.
  Proof.
    destruct n; auto.
  Qed.

  Hint Rewrite Zmod_mod modmatch_eta.

  Theorem GFplus_0_l: forall x : GF, {0} {+} x = x.
  Proof.
    galois.
  Qed.

  Theorem GFplus_commutative: forall x y : GF, x {+} y = y {+} x.
  Proof.
    galois.
  Qed.

  Theorem GFplus_associative: forall x y z : GF, x {+} (y {+} z) = (x {+} y) {+} z.
  Proof.
    galois.
  Qed.

  Theorem GFmult_1_l: forall x : GF, {1} {*} x = x.
  Proof.
    galois.
  Qed.

  Theorem GFmult_commutative: forall x y : GF, x {*} y = y {*} x.
  Proof.
    galois.
  Qed.

  Theorem GFmult_associative: forall x y z : GF, x {*} (y {*} z) = (x {*} y) {*} z.
  Proof.
    galois.
  Qed.

  Theorem GFdistributive: forall x y z : GF, (x {+} y) {*} z = x {*} z {+} y {*} z.
  Proof.
    galois.
  Qed.

  Theorem GFminus_opp: forall x y : GF, x {-} y = x {+} GFopp y.
  Proof.
    galois.
  Qed.

  Theorem GFopp_inverse: forall x : GF, x {+} GFopp x = {0}.
  Proof.
    galois.
  Qed.

  (* Ring Theory*)

  Ltac compat := repeat intro; subst; trivial.

  Instance GFplus_compat : Proper (eq==>eq==>eq) GFplus.
  Proof.
    compat.
  Qed.

  Instance GFminus_compat : Proper (eq==>eq==>eq) GFminus.
  Proof.
    compat.
  Qed.

  Instance GFmult_compat : Proper (eq==>eq==>eq) GFmult.
  Proof.
    compat.
  Qed.

  Instance GFopp_compat : Proper (eq==>eq) GFopp.
  Proof.
    compat.
  Qed.

  Definition GFring_theory : ring_theory GFzero GFone GFplus GFmult GFminus GFopp eq.
  Proof.
    constructor; galois.
  Qed.

  Add Ring GFring : GFring_theory.

  (* Power theory *)

  Lemma GFpower_theory : power_theory GFone GFmult eq id GFexp.
  Proof.
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
  Proof.
    compat.
  Qed.

  Instance GFdiv_compat : Proper (eq==>eq==>eq) GFdiv.
  Proof.
    compat.
  Qed.

  Definition GFfield_theory : field_theory GFzero GFone GFplus GFmult GFminus GFopp GFdiv GFinv eq.
  Proof.
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
