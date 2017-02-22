Require Crypto.Algebra.
Require Crypto.Util.GlobalSettings.

Require Import Crypto.Spec.WeierstrassCurve.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq} {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30). Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2).

    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F} {b_nonzero:b <> 0}.

    Definition point := { P | match P with
                              | (x, y) => b*y^2 = x^3 + a*x^2 + x
                              | ∞ => True
                              end }.
    Definition coordinates (P:point) : (F*F + ∞) := proj1_sig P.

    Definition eq (P1 P2:point) :=
      match coordinates P1, coordinates P2 with
      | (x1, y1), (x2, y2) => x1 = x2 /\ y1 = y2
      | ∞, ∞ => True
      | _, _ => False
      end.

    Import Crypto.Util.Tactics Crypto.Algebra.Field.
    Ltac t :=
      destruct_head' point; destruct_head' sum; destruct_head' prod;
        break_match; simpl in *; break_match_hyps; trivial; try discriminate;
        repeat match goal with
               | |- _ /\ _ => split
               | [H:@Logic.eq (sum _ _ ) _ _ |- _] => symmetry in H; injection H; intros; clear H
               | [H:@Logic.eq (prod _ _ ) _ _ |- _] => symmetry in H; injection H; intros; clear H
               end;
        subst; try fsatz.

    Program Definition add (P1 P2:point) : point :=
            match coordinates P1, coordinates P2 return F*F+∞ with
              (x1, y1), (x2, y2) =>
              if Decidable.dec (x1 = x2)
              then if Decidable.dec (y1 = - y2)
                   then ∞
                   else (b*(3*x1^2+2*a*x1+1)^2/(2*b*y1)^2-a-x1-x1, (2*x1+x1+a)*(3*x1^2+2*a*x1+1)/(2*b*y1)-b*(3*x1^2+2*a*x1+1)^3/(2*b*y1)^3-y1)
              else (b*(y2-y1)^2/(x2-x1)^2-a-x1-x2, (2*x1+x2+a)*(y2-y1)/(x2-x1)-b*(y2-y1)^3/(x2-x1)^3-y1)
            | ∞, ∞ =>                      ∞
            | ∞, _ =>                      coordinates P2
            | _, ∞ =>                      coordinates P1
            end.
    Next Obligation. Proof. t. Qed.

    Program Definition opp (P:point) : point :=
      match P return F*F+∞ with
      | (x, y) => (x, -y)
      | ∞ => ∞
      end.
    Next Obligation. Proof. t. Qed.

    Local Notation "4" := (1+3).
    Local Notation "16" := (4*4).
    Local Notation "9" := (3*3).
    Local Notation "27" := (3*9).
    Context {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}.

    Let WeierstrassA := ((3-a^2)/(3*b^2)).
    Let WeierstrassB := ((2*a^3-9*a)/(27*b^3)).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul WeierstrassA WeierstrassB).
    Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 WeierstrassA WeierstrassB).

    Program Definition of_Weierstrass (P:Wpoint) : point :=
      match W.coordinates P return F*F+∞ with
      | (x,y) => (b*x-a/3, b*y)
      | _ => ∞
      end.
    Next Obligation.
    Proof. clear char_ge_3; subst WeierstrassA; subst WeierstrassB; destruct P; t. Qed.

    Lemma of_Weierstrass_add P1 P2 :
      eq (of_Weierstrass (W.add P1 P2))
         (add (of_Weierstrass P1) (of_Weierstrass P2)).
    Proof. cbv [WeierstrassA WeierstrassB eq of_Weierstrass W.add add coordinates W.coordinates proj1_sig] in *; clear char_ge_3; t. Qed.
    
    Section AddX.
      Lemma homogeneous_x_differential_addition_releations P1 P2 :
          match coordinates (add P2 (opp P1)), coordinates P1, coordinates P2, coordinates (add P1 P2) with
          | (x, _), (x1, _), (x2, _), (x3, _) =>
            if Decidable.dec (x1 = x2)
            then x3 * (4*x1*(x1^2 + a*x1 + 1)) = (x1^2 - 1)^2
            else x3 * (x*(x1-x2)^2) = (x1*x2 - 1)^2
          | _, _, _, _ => True
          end.
      Proof. t. Qed.

      Program Definition to_xz (P:point) : F*F :=
        match coordinates P with
        | (x, y) => pair x 1
        | ∞ => pair 1 0
        end.

      (* From Explicit Formulas Database by Lange and Bernstein,
         credited to 1987 Montgomery "Speeding the Pollard and elliptic curve
         methods of factorization", page 261, fifth and sixth displays, plus
         common-subexpression elimination, plus assumption Z1=1 *)
      
      Context {a24:F} {a24_correct:4*a24 = a+2}. (* TODO: +2 or -2 ? *)
      Definition xzladderstep (X1:F) (P1 P2:F*F) : ((F*F)*(F*F)) :=
        match P1, P2 with
          pair X2 Z2, pair X3 Z3 => 
          let A := X2+Z2 in
          let AA := A^2 in
          let B := X2-Z2 in
          let BB := B^2 in
          let E := AA-BB in
          let C := X3+Z3 in
          let D := X3-Z3 in
          let DA := D*A in
          let CB := C*B in
          let X5 := (DA+CB)^2 in
          let Z5 := X1*(DA-CB)^2 in
          let X4 := AA*BB in
          let Z4 := E*(BB + a24*E) in
          (pair (pair X4 Z4) (pair X5 Z5))
        end.

      Require Import Crypto.Util.Tuple.

      (* TODO: look up this lemma statement -- the current one may not be right *)
      Lemma xzladderstep_to_xz X1 P1 P2
        (HX1 : match coordinates (add P1 (opp P2)) with (x,y) => X1 = x | _ => False end)
        : fieldwise (n:=2) (fieldwise (n:=2) Feq)
                    (xzladderstep X1 (to_xz P1) (to_xz P2))
                    (pair (to_xz (add P1 P2)) (to_xz (add P1 P1))).
        destruct P1 as [[[??]|?]?], P2 as [[[??]|?]?];
          cbv [fst snd xzladderstep to_xz add coordinates proj1_sig opp fieldwise fieldwise'] in *;
          break_match_hyps; break_match; repeat split; try contradiction.
      Abort.
    End AddX.
  End MontgomeryCurve.
End M.