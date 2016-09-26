Require Crypto.Algebra.
Require Crypto.Util.GlobalSettings.

Require Crypto.Spec.WeierstrassCurve.
Module W := Crypto.Spec.WeierstrassCurve.E. (* TODO: rename the module? *)

Module M.
  Section MontgomeryCurve.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq}.
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

    Context {a b: F} {b_nonzero:b <> 0} {char_gt_2:2 <> 0} {char_gt_3:3 <> 0}.

    Definition point := { P | match P with
                              | (x, y) => b*y^2 = x^3 + a*x^2 + x
                              | ∞ => True
                              end }.
    Definition coordinates (P:point) : (F*F + ∞) := proj1_sig P.

    Add Field MontgomeryCurveField : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).
    Local Ltac t :=
      repeat match goal with
             | _ => progress (intros; cbv [coordinates proj1_sig])
             | _ => solve [trivial|intuition idtac]
             | [P:point |- _] => destruct P as [[[??]|?]?]
             | |- context [if @Decidable.dec ?P ?pf then _ else _] => destruct (@Decidable.dec P pf)
             | |- context [match ?tt with tt => _ end] => destruct tt
             | |- context [?a/?b] => progress Algebra.common_denominator
             | |- _ = _ => Algebra.nsatz
             | |- _ <> _ =>
               solve [unfold not; rewrite !Algebra.Ring.zero_product_iff_zero_factor; intuition idtac|
                      Algebra.nsatz_contradict]
             end.
    Local Obligation Tactic := idtac.

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
    Next Obligation.
    Proof.
      t.
      unfold not; rewrite !Algebra.Ring.zero_product_iff_zero_factor; intuition idtac.
      assert (b * f0^2     = b * 0^2   ) by Algebra.nsatz.
      Import Field_tac. field_simplify_eq in H.
      rewrite !Algebra.Ring.zero_product_iff_zero_factor in H; intuition idtac; Algebra.nsatz_contradict.
    Qed.

    Program Definition opp (P:point) : point :=
      exist _
            match P with
            | (x, y) => (x, -y)
            | ∞ => ∞
            end _.
    Next Obligation.
    Proof.
      t.
    Qed.

    Local Notation "4" := (1+3).
    Local Notation "16" := (4*4).
    Local Notation "9" := (3*3).
    Local Notation "27" := (3*9).

    Let WeierstrassA := ((3-a^2)/(3*b^2)).
    Let WeierstrassB := ((2*a^3-9*a)/(27*b^3)).

    Context {Hparams:16*(a^2 - 4)/(b^3)^2 <> 0} {char_gt_27:27<>0}.

    Import Field_tac.
    Local Ltac doHparams :=
      let LH := match type of Hparams with ?LH <> 0 => LH end in
      match goal with
        |- ?LHS <> 0 =>
        let H := fresh "H" in
        assert (H:LHS = LH);
          [|rewrite H; assumption]
      end;
      try field; repeat split; try trivial.

    Local Ltac do27 :=
      let LH := match type of char_gt_27 with ?LH <> 0 => LH end in
      match goal with
        |- ?LHS <> 0 =>
        let H := fresh "H" in
        assert (H:LHS = LH);
          [|rewrite H; assumption]
      end;
      try field; repeat split; try trivial.

    Global Instance WeierstrassParamsOfMontgomery : @W.weierstrass_params
                                                      F Feq Fzero Fone Fopp Fadd Fmul
                                                      WeierstrassA WeierstrassB.
    Proof.
      (* I am not sure [common_denominator] is behaving correctly here *)
      cbv [WeierstrassA WeierstrassB]; split; trivial; doHparams; do27.
    Qed.
    
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
    Proof.
      repeat match goal with
             | _ => solve [trivial]
             | [P:Wpoint |- _] => destruct P as [[[??]|?]?]
             | _ => progress (intros; cbv [W.coordinates W.point proj1_sig])
             | _ => progress subst WeierstrassA
             | _ => progress subst WeierstrassB
             end.
      field_simplify_eq in y; try field_simplify_eq; repeat split; trivial; try Algebra.nsatz.
      do27.
    Defined.

    Definition eq (P1 P2:point) :=
      match coordinates P1, coordinates P2 with
      | (x1, y1), (x2, y2) => x1 = x2 /\ y1 = y2
      | ∞, ∞ => True
      | _, _ => False
      end.

    Lemma MontgomeryOfWeierstrass_add P1 P2 :
      eq (MontgomeryOfWeierstrass (W.add P1 P2))
         (add (MontgomeryOfWeierstrass P1) (MontgomeryOfWeierstrass P2)).
    Proof.
      cbv [eq MontgomeryOfWeierstrass W.add add coordinates W.coordinates proj1_sig].
      repeat match goal with
             | _ => solve [trivial]
             | [P:Wpoint |- _] => destruct P as [[[??]|?]?]
             | |- context [if @Decidable.dec ?P ?pf then _ else _] => destruct (@Decidable.dec P pf)
             | |- context [match ?tt with tt => _ end] => destruct tt
             | _ => split
             | _ => progress subst WeierstrassA
             | _ => progress subst WeierstrassB
             end.
      { apply n. Algebra.nsatz. }
      { apply n. field_simplify_eq; try assumption. Algebra.nsatz. }
      { apply n. admit. }
      { field_simplify_eq; repeat split; trivial.
        field_simplify_eq in y; repeat split; trivial; try do27.
        field_simplify_eq in y0; repeat split; trivial; try do27.
        field_simplify_eq in f4; repeat split; trivial.
        Algebra.nsatz.
        intro Hz. apply n. Algebra.nsatz. }
      Focus 4. {
        apply n.
        field_simplify_eq in f3; repeat split; trivial.
        admit. } Unfocus.
      (* The remaining cases are about points with coordinates (not ∞).
         I have not worked through them, and they might be untrue
         in case we have an error in either set of addition formulas. *)
    Abort.
    
    Section AddX.

      Lemma homogeneous_x_differential_addition_releations P1 P2 :
          match coordinates (add P2 (opp P1)), coordinates P1, coordinates P2, coordinates (add P1 P2) with
          | (x, _), (x1, _), (x2, _), (x3, _) =>
            if Decidable.dec (x1 = x2)
            then x3 * (4*x1*(x1^2 + a*x1 + 1)) = (x1^2 - 1)^2
            else x3 * (x*(x1-x2)^2) = (x1*x2 - 1)^2
          | _, _, _, _ => True
          end.
      Proof.
        cbv [opp add coordinates proj1_sig]. t.
        unfold not; rewrite !Algebra.Ring.zero_product_iff_zero_factor; intuition idtac.
        apply n. field_simplify_eq.
        (* true by LHS of y0 and y *)
      Admitted.

      Definition onCurve xy := let 'pair x y := xy in b*y^2 = x^3 + a*x^2 + x.
      Definition xzpoint := { xz | let 'pair x z := xz in (z = 0 \/ exists y, onCurve (pair (x/z) y)) }.
      Definition xzcoordinates (P:xzpoint) : F*F := proj1_sig P.
      Axiom one_neq_zero : 1 <> 0.
      Program Definition toxz (P:point) : xzpoint :=
        exist _
              match coordinates P with
              | (x, y) => pair x 1
              | ∞ => pair 1 0
              end _.
      Next Obligation.
      Proof.
        t.
        { right. exists f0. cbv [onCurve]. Algebra.common_denominator. Algebra.nsatz. apply one_neq_zero. }
        { left; reflexivity. }
      Qed.

      Definition sig_pair_to_pair_sig {T T' I I'} (xy:{xy | let 'pair x y := xy in I x /\ I' y})
        : prod {x:T | I x} {y:T' | I' y}
        := let 'exist (pair x y) (conj pfx pfy) := xy in  pair  (exist _ x pfx) (exist _ y pfy).

    Local Ltac t :=
      repeat match goal with
             | _ => progress (intros; cbv [coordinates proj1_sig])
             | _ => solve [trivial|intuition idtac]
             | [P:point |- _] => destruct P as [[[??]|?]?]
             | [P:xzpoint |- _] => destruct P as [[??][?|[??]]]
             | |- context [if @Decidable.dec ?P ?pf then _ else _] => destruct (@Decidable.dec P pf)
             | |- context [match ?tt with tt => _ end] => destruct tt
             | |- context [?a/?b] => progress Algebra.common_denominator
             | |- _ = _ => Algebra.nsatz
             | |- _ <> _ =>
               solve [unfold not; rewrite !Algebra.Ring.zero_product_iff_zero_factor; intuition idtac|
                      Algebra.nsatz_contradict]
             end.

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
        cbv [onCurve xzcoordinates] in *.
        t; intuition idtac; cbv [onCurve xzcoordinates] in *.
        { left. Algebra.nsatz. }
        { left. Algebra.nsatz. }
        admit.
        admit.
        admit.
        admit.
        { right.
          admit. (* the following works, but slowly:
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
          exists ((fun x1 y1 x2 y2 => (2*x1+x2+a)*(y2-y1)/(x2-x1)-b*(y2-y1)^3/(x2-x1)^3-y1) (f1/f2) x0 (f/f0) x).
          (* XXX: this case is probably not true -- there is not necessarily a guarantee that the output x/z is on curve if [X1] was not the x coordinate of the difference of input points as requored *)
      Abort.
    End AddX.
  End MontgomeryCurve.
End M.