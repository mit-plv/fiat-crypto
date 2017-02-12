Require Crypto.Algebra.
Require Crypto.Util.GlobalSettings.

Require Import Crypto.Spec.WeierstrassCurve.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq} {char_gt_2:@Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul 2}.
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

    Import Crypto.Util.Tactics Crypto.Algebra.Field.
    Ltac t :=
      destruct_head' point; destruct_head' sum; destruct_head' prod;
        break_match; simpl in *; break_match_hyps; trivial; try discriminate;
        repeat match goal with
               | |- _ /\ _ => split
               | [H:@eq (sum _ _ ) _ _ |- _] => symmetry in H; injection H; intros; clear H
               | [H:@eq (prod _ _ ) _ _ |- _] => symmetry in H; injection H; intros; clear H
               end;
        subst; try fsatz.

    Program Definition add (P1 P2:point) : point :=
      exist _
            match coordinates P1, coordinates P2 return _ with
              (x1, y1), (x2, y2) =>
              if Decidable.dec (x1 = x2)
              then if Decidable.dec (y1 = - y2)
                   then ∞
                   else (b*(3*x1^2+2*a*x1+1)^2/(2*b*y1)^2-a-x1-x1, (2*x1+x1+a)*(3*x1^2+2*a*x1+1)/(2*b*y1)-b*(3*x1^2+2*a*x1+1)^3/(2*b*y1)^3-y1)
              else (b*(y2-y1)^2/(x2-x1)^2-a-x1-x2, (2*x1+x2+a)*(y2-y1)/(x2-x1)-b*(y2-y1)^3/(x2-x1)^3-y1)
            | ∞, ∞ =>                      ∞
            | ∞, _ =>                      coordinates P2
            | _, ∞ =>                      coordinates P1
            end _.
    Next Obligation. Proof. t. Qed.

    Program Definition opp (P:point) : point :=
      exist _
            match P with
            | (x, y) => (x, -y)
            | ∞ => ∞
            end _.
    Next Obligation.
    Proof. t. Qed.

    Local Notation "4" := (1+3).
    Local Notation "16" := (4*4).
    Local Notation "9" := (3*3).
    Local Notation "27" := (3*9).
    Context {char_gt_27:@Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul 27}.

    Let WeierstrassA := ((3-a^2)/(3*b^2)).
    Let WeierstrassB := ((2*a^3-9*a)/(27*b^3)).

    Local Notation Wpoint := (@W.point F Feq Fadd Fmul WeierstrassA WeierstrassB).
    Program Definition MontgomeryOfWeierstrass (P:Wpoint) : point :=
      exist
        _
        match W.coordinates P return _ with
        | (x,y) => (b*x-a/3, b*y)
        | _ => ∞
        end
        _.
    Next Obligation.
    Proof. subst WeierstrassA; subst WeierstrassB; destruct P; t. Qed.

    Definition eq (P1 P2:point) :=
      match coordinates P1, coordinates P2 with
      | (x1, y1), (x2, y2) => x1 = x2 /\ y1 = y2
      | ∞, ∞ => True
      | _, _ => False
      end.

    Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_gt_2 WeierstrassA WeierstrassB).
    Lemma MontgomeryOfWeierstrass_add P1 P2 :
      eq (MontgomeryOfWeierstrass (W.add P1 P2))
         (add (MontgomeryOfWeierstrass P1) (MontgomeryOfWeierstrass P2)).
    Proof.
      cbv [WeierstrassA WeierstrassB eq MontgomeryOfWeierstrass W.add add coordinates W.coordinates proj1_sig] in *; t.
    Qed.
    
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

      Definition onCurve xy := let 'pair x y := xy in b*y^2 = x^3 + a*x^2 + x.
      Definition xzpoint := { xz | let 'pair x z := xz in (z = 0 \/ exists y, onCurve (pair (x/z) y)) }.
      Definition xzcoordinates (P:xzpoint) : F*F := proj1_sig P.
      Program Definition toxz (P:point) : xzpoint :=
        exist _
              match coordinates P with
              | (x, y) => pair x 1
              | ∞ => pair 1 0
              end _.
      Next Obligation. t; [right; exists f0; t | left; reflexivity ]. Qed.

      Definition sig_pair_to_pair_sig {T T' I I'} (xy:{xy | let 'pair x y := xy in I x /\ I' y})
        : prod {x:T | I x} {y:T' | I' y}
        := let 'exist (pair x y) (conj pfx pfy) := xy in  pair  (exist _ x pfx) (exist _ y pfy).

      (* From Explicit Formulas Database by Lange and Bernstein,
         credited to 1987 Montgomery "Speeding the Pollard and elliptic curve
         methods of factorization", page 261, fifth and sixth displays, plus
         common-subexpression elimination, plus assumption Z1=1 *)
      
      Context {a24:F} {a24_correct:4*a24 = a+2}.
      Definition xzladderstep (X1:F) (P1 P2:xzpoint) : prod xzpoint xzpoint. refine (
        sig_pair_to_pair_sig (exist _
        match xzcoordinates P1, xzcoordinates P2 return _ with
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
        end _) ).
      Proof.
        destruct P1, P2; cbv [onCurve xzcoordinates] in *. t; intuition idtac.
        { left. fsatz. }
        { left. fsatz. }
        admit.
        admit.
        admit.
        admit.
        { right.
          admit. (* the following used to work, but slowly:
          exists ((fun x1 y1 x2 y2 => (2*x1+x1+a)*(3*x1^2+2*a*x1+1)/(2*b*y1)-b*(3*x1^2+2*a*x1+1)^3/(2*b*y1)^3-y1) (f1/f2) x0 (f/f0) x).
          Algebra.common_denominator_in H.
          Algebra.common_denominator_in H0.
          Algebra.common_denominator.
          abstract Algebra.nsatz.

          idtac.
          admit.
          admit.
          admit.
          admit.
          admit. *) }
        { right.
          (* exists ((fun x1 y1 x2 y2 => (2*x1+x2+a)*(y2-y1)/(x2-x1)-b*(y2-y1)^3/(x2-x1)^3-y1) (f1/f2) x0 (f/f0) x). *)
          (* XXX: this case is probably not true -- there is not necessarily a guarantee that the output x/z is on curve if [X1] was not the x coordinate of the difference of input points as requored *)
      Abort.
    End AddX.
  End MontgomeryCurve.
End M.