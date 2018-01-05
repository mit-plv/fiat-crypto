Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Notations Crypto.Util.LetIn.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.Sigma.

Module Jacobian.
  Section Jacobian.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x^2*x).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).

    Definition point : Type := { P : F*F*F | let '(X,Y,Z) := P in
                                             if dec (Z=0) then True else Y^2 = X^3 + a*X*(Z^2)^2 + b*(Z^3)^2 }.
    Definition eq (P Q : point) : Prop :=
      match proj1_sig P, proj1_sig Q with
      | (X1, Y1, Z1), (X2, Y2, Z2) =>
        if dec (Z1 = 0) then Z2 = 0
        else Z2 <> 0 /\
             X1*Z2^2 = X2*Z1^2
             /\ Y1*Z2^3 = Y2*Z1^3
      end.

    Ltac prept :=
      repeat match goal with
             | _ => progress intros
             | _ => progress specialize_by trivial
             | _ => progress cbv [proj1_sig fst snd]
             | _ => progress autounfold with points_as_coordinates in *
             | _ => progress destruct_head'_True
             | _ => progress destruct_head'_unit
             | _ => progress destruct_head'_prod
             | _ => progress destruct_head'_sig
             | _ => progress destruct_head'_and
             | _ => progress destruct_head'_sum
             | _ => progress destruct_head'_bool
             | _ => progress destruct_head'_or
             | H: context[dec ?P] |- _ => destruct (dec P)
             | |- context[dec ?P]      => destruct (dec P)
             | |- ?P => lazymatch type of P with Prop => split end
             end.
    Ltac t := prept; trivial; try contradiction; fsatz.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold Proper respectful Reflexive Symmetric Transitive : points_as_coordinates.
    Hint Unfold point eq W.eq W.point W.coordinates proj1_sig fst snd : points_as_coordinates.

    Global Instance Equivalence_eq : Equivalence eq.
    Proof. t. Qed.

    Program Definition of_affine (P:Wpoint) : point :=
      match W.coordinates P return F*F*F with
      | inl (x, y) => (x, y, 1)
      | inr _ => (0, 0, 0)
      end.
    Next Obligation. Proof. t. Qed.

    Program Definition to_affine (P:point) : Wpoint :=
      match proj1_sig P return F*F+_ with
      | (X, Y, Z) =>
        if dec (Z = 0) then inr tt
        else inl (X/Z^2, Y/Z^3)
      end.
    Next Obligation. Proof. t. Qed.

    Hint Unfold to_affine of_affine : points_as_coordinates.
    Global Instance Proper_of_affine : Proper (W.eq ==> eq) of_affine. Proof. t. Qed.
    Global Instance Proper_to_affine : Proper (eq ==> W.eq) to_affine. Proof. t. Qed.
    Lemma to_affine_of_affine P : W.eq (to_affine (of_affine P)) P. Proof. t. Qed.
    Lemma of_affine_to_affine P : eq (of_affine (to_affine P)) P. Proof. t. Qed.

    Program Definition opp (P:point) : point :=
      match proj1_sig P return F*F*F with
      | (X, Y, Z) => (X, Fopp Y, Z)
      end.
    Next Obligation. Proof. t. Qed.

    Section AEqMinus3.
      Context (a_eq_minus3 : a = Fopp (1+1+1)).

      Program Definition double (P : point) : point :=
        match proj1_sig P return F*F*F with
        | (x_in, y_in, z_in) =>
          let delta := z_in^2 in
          let gamma := y_in^2 in
          let beta := x_in * gamma in
          let ftmp := x_in - delta in
          let ftmp2 := x_in + delta in
          let tmptmp := ftmp2 + ftmp2 in
          let ftmp2 := ftmp2 + tmptmp in
          let alpha := ftmp * ftmp2 in
          let x_out := alpha^2 in
          let fourbeta := beta + beta in
          let fourbeta := fourbeta + fourbeta in
          let tmptmp := fourbeta + fourbeta in
          let x_out := x_out - tmptmp in
          let delta := gamma + delta in
          let ftmp := y_in + z_in in
          let z_out := ftmp^2 in
          let z_out := z_out - delta in
          let y_out := fourbeta - x_out in
          let gamma := gamma + gamma in
          let gamma := gamma^2 in
          let y_out := alpha * y_out in
          let gamma := gamma + gamma in
          let y_out := y_out - gamma in
          (x_out, y_out, z_out)
        end.
      Next Obligation. Proof. t. Qed.

      Definition z_is_zero_or_one (Q : point) : Prop :=
        match proj1_sig Q with
        | (_, _, z) => z = 0 \/ z = 1
        end.

      Definition add_precondition (Q : point) (mixed : bool) : Prop :=
        match mixed with
        | false => True
        | true => z_is_zero_or_one Q
        end.

      Hint Unfold double negb andb add_precondition z_is_zero_or_one : points_as_coordinates.
      Program Definition add_impl (mixed : bool) (P Q : point)
              (H : add_precondition Q mixed) : point :=
        match proj1_sig P, proj1_sig Q return F*F*F with
        | (x1, y1, z1), (x2, y2, z2) =>
          let z1nz := if dec (z1 = 0) then false else true in
          let z2nz := if dec (z2 = 0) then false else true in
          let z1z1 := z1^2 in
          let '(u1, s1, two_z1z2) := if negb mixed
          then
            let z2z2 := z2^2 in
            let u1 := x1 * z2z2 in
            let two_z1z2 := z1 + z2 in
            let two_z1z2 := two_z1z2^2 in
            let two_z1z2 := two_z1z2 - z1z1 in
            let two_z1z2 := two_z1z2 - z2z2 in
            let s1 := z2 * z2z2 in
            let s1 := s1 * y1 in
            (u1, s1, two_z1z2)
          else
            let u1 := x1 in
            let two_z1z2 := z1 + z1 in
            let s1 := y1 in
            (u1, s1, two_z1z2)
          in
          let u2 := x2 * z1z1 in
          let h := u2 - u1 in
          let xneq := if dec (h = 0) then false else true in
          let z_out := h * two_z1z2 in
          let z1z1z1 := z1 * z1z1 in
          let s2 := y2 * z1z1z1 in
          let r := s2 - s1 in
          let r := r + r in
          let yneq := if dec (r = 0) then false else true in
          if (negb xneq && negb yneq && z1nz && z2nz)%bool
          then proj1_sig (double P)
          else
            let i := h + h in
            let i := i^2 in
            let j := h * i in
            let v := u1 * i in
            let x_out := r^2 in
            let x_out := x_out - j in
            let x_out := x_out - v in
            let x_out := x_out - v in
            let y_out := v - x_out in
            let y_out := y_out * r in
            let s1j := s1 * j in
            let y_out := y_out - s1j in
            let y_out := y_out - s1j in
            let x_out := if z1nz then x_out else x2 in
            let x3 := if z2nz then x_out else x1 in
            let y_out := if z1nz then y_out else y2 in
            let y3 := if z2nz then y_out else y1 in
            let z_out := if z1nz then z_out else z2 in
            let z3 := if z2nz then z_out else z1 in
            (x3, y3, z3)
        end.
      Next Obligation. Proof. t. Qed.
      Definition add (P Q : point) : point :=
        add_impl false P Q I.
      Definition add_mixed (P : point) (Q : point) (H : z_is_zero_or_one Q) :=
        add_impl true P Q H.

      Hint Unfold W.eq W.add to_affine add add_mixed add_impl : points_as_coordinates.

      Lemma Proper_double : Proper (eq ==> eq) double. Proof. t. Qed.
      Lemma to_affine_double P :
        W.eq (to_affine (double P)) (W.add (to_affine P) (to_affine P)).
      Proof. t. Qed.

      Lemma add_mixed_eq_add (P : point) (Q : point) (H : z_is_zero_or_one Q) :
        eq (add P Q) (add_mixed P Q H).
      Proof. t. Qed.

      Lemma Proper_add : Proper (eq ==> eq ==> eq) add. Proof. t. Qed.
      Import BinPos.
      Lemma to_affine_add P Q
        : W.eq (to_affine (add P Q)) (W.add (to_affine P) (to_affine Q)).
      Proof. prept; trivial; try contradiction. Time all: abstract t. Time Qed.
      (* 306.478 secs (43.916u,1.032s) ;; 18.857 secs (18.856u,0.008s) *)
    End AEqMinus3.
  End Jacobian.
End Jacobian.
