Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Notations Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.Sigma.

Module Projective.
  Section Projective.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x*x^2).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).

    (* Originally from
    <http://www.mat.uniroma3.it/users/pappa/CORSI/CR510_13_14/BosmaLenstra.pdf>
    "Commplete Systems of Addition Laws" by Bosma and Lenstra;
    optimized in <https://eprint.iacr.org/2015/1060.pdf> "Complete
    addition formulas for prime order elliptic curves" Algorithm 1
    "Complete, projective point addition for arbitrary prime order
    short Weierstrass curves" by Joost Renes, Craig Costello, and
    Lejla Batina. *)

    Ltac t :=
      repeat match goal with
             | _ => solve [ discriminate | contradiction | trivial ]
             | _ => progress cbv zeta
             | _ => progress intros
             | _ => progress destruct_head' @W.point
             | _ => progress destruct_head' sum
             | _ => progress destruct_head' prod
             | _ => progress destruct_head' unit
             | _ => progress destruct_head' and
             | _ => progress specialize_by assumption
             | _ => progress cbv [W.eq W.add W.coordinates proj1_sig] in *
             | _ => progress break_match_hyps
             | _ => progress break_match
             | |- _ /\ _ => split | |- _ <-> _ => split
             | [H:~ _ <> _ |- _ ] => rewrite (not_not (_ = _)) in H
             | [H: not ?P, G: ?P -> _ |- _ ] => clear G
             | [H: ?P, G: not ?P -> _ |- _ ] => clear G
             | [H: ?x = ?x |- _ ] => clear H
             | [H: True |- _ ] => clear H
             end.

    Definition point : Type := { P : F*F*F | let '(X,Y,Z) := P in Y^2*Z = X^3 + a*X*Z^2 + b*Z^3 /\ (Z = 0 -> Y <> 0) }.

    Program Definition to_affine (P:point) : Wpoint :=
      match proj1_sig P return F*F+_ with
      | (X, Y, Z) =>
        if dec (Z = 0) then inr tt
        else inl (X/Z, Y/Z)
      end.
    Next Obligation. Proof. t. fsatz. Qed.

    Program Definition of_affine (P:Wpoint) : point :=
      match W.coordinates P return F*F*F with
      | inl (x, y) => (x, y, 1)
      | inr _ => (0, 1, 0)
      end.
    Next Obligation. Proof. t; fsatz. Qed.

    Definition eq (P Q:point) : Prop :=
      match proj1_sig P, proj1_sig Q with
      | (X1, Y1, Z1), (X2, Y2, Z2) =>
        if dec (Z1 = 0) then Z2 = 0
        else if dec (Z2 = 0) then False
             else X1*Z2 = X2*Z1 /\ Y1*Z2 = Y2*Z1
      end.

    Lemma eq_iff_Weq P Q : eq P Q <-> W.eq (to_affine P) (to_affine Q).
    Proof.
      cbv [W.eq eq to_affine] in *; t; specialize_by_assumption; fsatz.
    Qed.

    Program Definition opp (P:point) : point :=
      match proj1_sig P return F*F*F with
      | (X, Y, Z) => (X, Fopp Y, Z)
      end.
    Next Obligation. Proof. t; fsatz. Qed.

    Context (three_b:F) (three_b_correct: three_b = b+b+b).
    Local Notation "4" := (1+1+1+1). Local Notation "27" := (4*4 + 4+4 +1+1+1).
    Context {discriminant_nonzero: id(4*a*a*a + 27*b*b <> 0)}.

    Let not_exceptional_y (P Q:point) :=
      match W.coordinates (W.add (to_affine P) (to_affine (opp Q))) return Prop with
      | inr _ => True
      | inl (_, y) => y <> 0
      end.

    Global Instance DecidableRel_not_exceptional_y : DecidableRel not_exceptional_y.
    Proof.
      cbv [not_exceptional_y]; intros; break_match; exact _.
    Defined.

    Lemma exceptional_P_neq_Q P Q (H:~not_exceptional_y P Q) :
      ~ W.eq (to_affine P) (to_affine Q).
    Proof using three_b_correct three_b.
      destruct P as [p ?]; destruct p as [p Z1]; destruct p as [X1 Y1].
      destruct Q as [q ?]; destruct q as [q Z2]; destruct q as [X2 Y2].
      cbv [not_exceptional_y opp to_affine] in *; clear not_exceptional_y.
      t; try exact id.
      all: repeat match goal with
                    [H:~ _ <> _ |- _ ] => rewrite (not_not (_ = _)) in H
                  end.
      all: intro HX; destruct HX; fsatz.
    Qed.

    Import BinPos.
    Context {char_ge_21 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 21}.
    Lemma exceptional_2P_eq_2Q P Q (H:~not_exceptional_y P Q) :
      W.eq
        (W.add (to_affine P) (to_affine P))
        (W.add (to_affine Q) (to_affine Q)).
    Proof using three_b_correct three_b discriminant_nonzero char_ge_21 .
      destruct P as [p ?]; destruct p as [p Z1]; destruct p as [X1 Y1].
      destruct Q as [q ?]; destruct q as [q Z2]; destruct q as [X2 Y2].
      cbv [not_exceptional_y opp to_affine] in *; clear not_exceptional_y.
      t.
      par: abstract solve [ fsatz | cbv [id] in * ; fsatz ].
   Qed.

    Definition not_exceptional P Q :=
      let p := to_affine P in
      let q := to_affine Q in
      (W.eq (W.add p p) (W.add q q) -> W.eq p q).
    Lemma not_exceptional_y_of_not_exceptional P Q
       : not_exceptional P Q -> not_exceptional_y P Q.
    Proof.
      cbv [not_exceptional].
      pose proof exceptional_2P_eq_2Q P Q.
      pose proof exceptional_P_neq_Q P Q.
      intro Himpl.
      rewrite <-not_not by typeclasses eauto.
      intuition trivial.
    Qed.

    Program Definition add (P Q:point) (except: not_exceptional P Q) : point :=
      match proj1_sig P, proj1_sig Q return F*F*F with (X1, Y1, Z1), (X2, Y2, Z2) =>
        let t0 := X1*X2 in
        let t1 := Y1*Y2 in
        let t2 := Z1*Z2 in
        let t3 := X1+Y1 in
        let t4 := X2+Y2 in
        let t3 := t3*t4 in
        let t4 := t0+t1 in
        let t3 := t3-t4 in
        let t4 := X1+Z1 in
        let t5 := X2+Z2 in
        let t4 := t4*t5 in
        let t5 := t0+t2 in
        let t4 := t4-t5 in
        let t5 := Y1+Z1 in
        let X3 := Y2+Z2 in
        let t5 := t5*X3 in
        let X3 := t1+t2 in
        let t5 := t5-X3 in
        let Z3 := a*t4 in
        let X3 := three_b*t2 in
        let Z3 := X3+Z3 in
        let X3 := t1-Z3 in
        let Z3 := t1+Z3 in
        let Y3 := X3*Z3 in
        let t1 := t0+t0 in
        let t1 := t1+t0 in
        let t2 := a*t2 in
        let t4 := three_b*t4 in
        let t1 := t1+t2 in
        let t2 := t0-t2 in
        let t2 := a*t2 in
        let t4 := t4+t2 in
        let t0 := t1*t4 in
        let Y3 := Y3+t0 in
        let t0 := t5*t4 in
        let X3 := t3*X3 in
        let X3 := X3-t0 in
        let t0 := t3*t1 in
        let Z3 := t5*Z3 in
        let Z3 := Z3+t0 in
        (X3, Y3, Z3)
      end.
    Next Obligation.
    Proof using three_b three_b_correct discriminant_nonzero char_ge_21.
      apply not_exceptional_y_of_not_exceptional in except.
      cbv [not_exceptional_y to_affine opp] in except. clear not_exceptional_y.
      destruct P as [p ?]; destruct p as [p Z1]; destruct p as [X1 Y1].
      destruct Q as [q ?]; destruct q as [q Z2]; destruct q as [X2 Y2].
      t.
      par: abstract solve [ fsatz | cbv [id] in * ; fsatz ].
    Qed.

    Lemma to_affine_add P Q except :
      W.eq
        (to_affine (add P Q except))
        (WeierstrassCurve.W.add (to_affine P) (to_affine Q)).
    Proof using Type.
      destruct P as [p ?]; destruct p as [p Z1]; destruct p as [X1 Y1].
      destruct Q as [q ?]; destruct q as [q Z2]; destruct q as [X2 Y2].
      pose proof (not_exceptional_y_of_not_exceptional _ _ except).
      cbv [not_exceptional_y opp to_affine add] in *; t;
        clear except not_exceptional_y;
        specialize_by_assumption.
      all: try abstract fsatz.

      (* zero + P = P   -- cases for x and y *)
      assert (X1 = 0) by (setoid_subst_rel Feq; Nsatz.nsatz_power 3%nat); t; fsatz.
      assert (X1 = 0) by (setoid_subst_rel Feq; Nsatz.nsatz_power 3%nat); t; fsatz.

      (* P  + zero = P   -- cases for x and y *)
      assert (X2 = 0) by (setoid_subst_rel Feq; Nsatz.nsatz_power 3%nat); t; fsatz.
      assert (X2 = 0) by (setoid_subst_rel Feq; Nsatz.nsatz_power 3%nat); t; fsatz.
    Qed.
  End Projective.
End Projective.
