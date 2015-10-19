
Require Import BinInt BinNat ZArith Znumtheory NArith.
Require Import Eqdep_dec.
Require Export Coq.Classes.Morphisms Setoid.
Require Export Ring_theory Field_theory Field_tac.
Require Export Crypto.Galois.Galois.

Set Implicit Arguments.
Unset Strict Implicits.

Module GaloisTheory (M: Modulus).
  Module G := Galois M.
  Export M G.

  (* Notations *)
  Delimit Scope GF_scope with GF.
  Notation "1" := GFone : GF_scope.
  Notation "0" := GFzero : GF_scope.
  Infix "+"    := GFplus : GF_scope.
  Infix "-"    := GFminus : GF_scope.
  Infix "*"    := GFmult : GF_scope.
  Infix "/"    := GFdiv : GF_scope.
  Infix "^"    := GFexp : GF_scope.

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

  Lemma Zmod_eq : forall a b n, a = b -> a mod n = b mod n.
  Proof.
    intros; rewrite H; trivial.
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
           | [ |- context[(?x mod _) mod _] ] =>
             notFancy x; rewrite (Zmod_mod x)
           | _ => rewrite Zplus_neg in * || rewrite Z.sub_diag in *
           end.

  (* Remove exists under equals: we do this a lot *)
  Ltac eq_remove_proofs := match goal with
    | [ |- ?a = ?b ] =>
      assert (Q := gf_eq a b);
      simpl in *; apply Q; clear Q
    end.

  (* General big hammer for proving Galois arithmetic facts *)
  Ltac galois := intros; apply gf_eq; simpl;
                 repeat match goal with
                        | [ x : GF |- _ ] => destruct x
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

  (* Power theory *)

  Local Open Scope GF_scope.

  Lemma GFexp'_doubling : forall q r0, GFexp' (r0 * r0) q = GFexp' r0 q * GFexp' r0 q.
  Proof.
    induction q; simpl; intuition.
    rewrite (IHq (r0 * r0)); generalize (GFexp' (r0 * r0) q); intro.
    galois.
    apply Zmod_eq; ring.
  Qed.

  Lemma GFexp'_correct : forall r p, GFexp' r p = pow_pos GFmult r p.
  Proof.
    induction p; simpl; intuition;
      rewrite GFexp'_doubling; congruence.
  Qed.

  Hint Immediate GFexp'_correct.

  Lemma GFexp_correct : forall r n,
    r^n = pow_N 1 GFmult r n.
  Proof.
    induction n; simpl; intuition.
  Qed.

  Lemma GFexp_correct' : forall r n,
    r^id n = pow_N 1 GFmult r n.
  Proof.
    apply GFexp_correct.
  Qed.

  Hint Immediate GFexp_correct'.

  Lemma GFpower_theory : power_theory GFone GFmult eq id GFexp.
  Proof.
    constructor; auto.
  Qed.

  (* Ring properties *)

  Ltac GFexp_tac t :=
    match t with
    | Z0 => N0
    | Zpos ?n => Ncst (Npos n)
    | Z_of_N ?n => Ncst n
    | NtoZ ?n => Ncst n
    | _ => NotConstant
    end.

  Lemma GFdecidable : forall (x y: GF), Zeq_bool x y = true -> x = y.
  Proof.
    intros; galois.
    apply Zeq_is_eq_bool.
    trivial.
  Qed.

  Lemma GFcomplete : forall (x y: GF), x = y -> Zeq_bool x y = true.
  Proof.
    intros.
    apply Zeq_is_eq_bool.
    galois.
  Qed.

  (* Division Theory *)
  Definition inject(x: Z):  GF.
    exists (x mod modulus).
    abstract (demod; trivial).
  Defined.

  Definition GFquotrem(a b: GF): GF * GF :=
    match (Z.quotrem a b) with
    | (q, r) => (inject q, inject r)
    end.

  Lemma GFdiv_theory : div_theory eq GFplus GFmult (@id _) GFquotrem.
  Proof.
    constructor; intros; unfold GFquotrem.

    replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b);
      try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).

    eq_remove_proofs; demod;
      rewrite <- (Z.quot_rem' a b);
      destruct a; simpl; trivial.
  Qed.

  (* Now add the ring with all modifiers *)

  Add Ring GFring : GFring_theory
    (decidable GFdecidable,
     div GFdiv_theory,
     power_tac GFpower_theory [GFexp_tac]).

  (* Field Theory*)

  Lemma GFexp'_pred' : forall x p,
    GFexp' p (Pos.succ x) = GFexp' p x * p.
  Proof.
    induction x; simpl; intuition; try ring.
    rewrite IHx; ring.
  Qed.

  Lemma GFexp'_pred : forall x p,
    p <> 0
    -> x <> 1%positive
    -> GFexp' p x = GFexp' p (Pos.pred x) * p.
  Proof.
    intros; rewrite <- (Pos.succ_pred x) at 1; auto using GFexp'_pred'.
  Qed.

  Lemma GFexp_pred : forall p x,
    p <> 0
    -> x <> 0%N
    -> p^x = p^N.pred x * p.
  Proof.
    destruct x; simpl; intuition.
    destruct (Pos.eq_dec p0 1); subst; simpl; try ring.
    rewrite GFexp'_pred by auto.
    destruct p0; intuition.
  Qed.

  Lemma GF_multiplicative_inverse : forall p,
    p <> 0
    -> GFinv p * p = 1.
  Proof.
    unfold GFinv; destruct totient as [ ? [ ] ]; simpl.
    intros.
    rewrite <- GFexp_pred; auto using N.gt_lt, N.lt_neq.
    intro; subst.
    eapply N.lt_irrefl; eauto using N.gt_lt.
  Qed.

  Instance GFinv_compat : Proper (eq==>eq) GFinv.
  Proof.
    compat.
  Qed.

  Instance GFdiv_compat : Proper (eq==>eq==>eq) GFdiv.
  Proof.
    compat.
  Qed.

  Hint Immediate GF_multiplicative_inverse GFring_theory.

  Local Hint Extern 1 False => discriminate.

  Definition GFfield_theory : field_theory GFzero GFone GFplus GFmult GFminus GFopp GFdiv GFinv eq.
  Proof.
    constructor; auto.
  Qed.
End GaloisTheory.
