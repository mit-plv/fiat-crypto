Require Import Coq.Numbers.BinNums.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.

Module W.
  Section W.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_gt_2:@Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul 2}
            {char_gt_10000:@Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul 10000} (* TODO: we need only 3, but we may need to factor some coefficients *)
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation eq := (@W.eq F Feq Fadd Fmul a b).
    Local Notation point := (@W.point F Feq Fadd Fmul a b).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2). Local Notation "4" := (1+3).
    Local Notation "8" := (1+(1+(1+(1+4)))). Local Notation "12" := (1+(1+(1+(1+8)))).
    Local Notation "16" := (1+(1+(1+(1+12)))). Local Notation "20" := (1+(1+(1+(1+16)))).
    Local Notation "24" := (1+(1+(1+(1+20)))). Local Notation "27" := (1+(1+(1+24))).
    Local Notation "x ^ 2" := (x*x) (at level 30). Local Notation "x ^ 3" := (x*x^2) (at level 30).

    Ltac t_step :=
      match goal with
      | _ => exact _
      | _ => intro
      | |- Equivalence _ => split
      | |- abelian_group => split | |- group => split | |- monoid => split
      | |- is_associative => split | |- is_commutative => split 
      | |- is_left_inverse => split | |- is_right_inverse => split
      | |- is_left_identity => split | |- is_right_identity => split
      | p:point |- _ => destruct p
      | _ => progress destruct_head' sum
      | _ => progress destruct_head' prod
      | _ => progress destruct_head' unit
      | _ => progress destruct_head' and
      | _ => progress cbv [eq W.eq W.add W.coordinates proj1_sig] in *
      (* [_gather_nonzeros] must run before [fst_pair] or [simpl] but after splitting E.eq and unfolding [E.add] *)
      | _ => progress simpl in *
      | |- _ /\ _ => split | |- _ <-> _ => split
      | _ => solve [trivial]
      end.
    Ltac t := repeat t_step.

    (*
    Lemma weierstrass_associativity_main x1 y1 x2 y2 x4 y4
          (A: y1^2=x1^3+a*x1+b)
          (B: y2^2=x2^3+a*x2+b)
          (C: y4^2=x4^3+a*x4+b)
          (Hi3: x2 <> x1)
          λ3 (Hλ3: λ3 = (y2-y1)/(x2-x1))
          x3 (Hx3: x3 = λ3^2-x1-x2)
          y3 (Hy3: y3 = λ3*(x1-x3)-y1)
          (Hi7: x4 <> x3)
          λ7 (Hλ7: λ7 = (y4-y3)/(x4-x3))
          x7 (Hx7: x7 = λ7^2-x3-x4)
          y7 (Hy7: y7 = λ7*(x3-x7)-y3)
          (Hi6: x4 <> x2)
          λ6 (Hλ6: λ6 = (y4-y2)/(x4-x2))
          x6 (Hx6: x6 = λ6^2-x2-x4)
          y6 (Hy6: y6 = λ6*(x2-x6)-y2)
          (Hi9: x6 <> x1)
          λ9 (Hλ9: λ9 = (y6-y1)/(x6-x1))
          x9 (Hx9: x9 = λ9^2-x1-x6)
          y9 (Hy9: y9 = λ9*(x1-x9)-y1)
      : x7 = x9 /\ y7 = y9.
    Proof. split; fsatz. Qed.
    *)

    Definition opaque_id {T} := @id T.
    Local Opaque opaque_id.
    
    Global Instance associative_add : is_associative(eq:=W.eq)(op:=W.add).
    Proof.
      (* the automation currently does not pick up
       that x1 = x2 and y2 =? -y1 implies that y2 = y1 *)
      split; intros [[[xA yA]|] A] [[[xB yB]|] B] [[[xC yC]|] C].
      repeat (break_match || t).
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      { rewrite <-H in *; clear H xC.
        rewrite H0 in *; clear H0 yC C.
        assert (yB = ((yB - yA) / (xB - xA) * (xA - (((yB - yA) / (xB - xA)) ^ 2 - xA - xB)) -
          yA)) by fsatz; clear H3.
        symmetry in H2.
        (* A+B = B? But A is a point with coordinates, not the identity *)
        admit. }
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      { assert (yC = yB) by fsatz.
        symmetry in H.
        setoid_subst_rel Feq.

        assert (yA<>Fopp((3 * xB ^ 2 + a) / (2 * yB) * (xB - (((3 * xB ^ 2 + a) / (2 * yB)) ^ 2 - xB - xB)) - yB)) by fsatz; clear H2.
        destruct(dec((yA=((3 * xB ^ 2 + a) / (2 * yB) * (xB - (((3 * xB ^ 2 + a) / (2 * yB)) ^ 2 - xB - xB)) - yB)))). fsatz.
        assert (yA^2 = ((3 * xB ^ 2 + a) / (2 * yB) *
      (xB - (((3 * xB ^ 2 + a) / (2 * yB)) ^ 2 - xB - xB)) - yB)^2) by fsatz.
        only_two_square_roots. }
      { assert (yC = yB) by fsatz.
        symmetry in H.
        setoid_subst_rel Feq.

        assert (yA<>Fopp((3 * xB ^ 2 + a) / (2 * yB) * (xB - (((3 * xB ^ 2 + a) / (2 * yB)) ^ 2 - xB - xB)) - yB)) by fsatz; clear H2.
        destruct(dec((yA=((3 * xB ^ 2 + a) / (2 * yB) * (xB - (((3 * xB ^ 2 + a) / (2 * yB)) ^ 2 - xB - xB)) - yB)))). fsatz.
        assert (yA^2 = ((3 * xB ^ 2 + a) / (2 * yB) *
      (xB - (((3 * xB ^ 2 + a) / (2 * yB)) ^ 2 - xB - xB)) - yB)^2) by fsatz.
        only_two_square_roots. }
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      { rewrite H3 in *; clear H3.
        rewrite <-H2 in *; clear H2.
        replace (Fopp yA ^ 2) with (yA^2) in * by admit.
        clear B xB yB.
        assert ((yC - Fopp yA) / (xC - xA) * (xA - (((yC - Fopp yA) / (xC - xA)) ^ 2 - xA - xC))=0) by fsatz; clear H1.
        admit.
        }
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      { 
        assert (yA = (yC - yB) / (xC - xB) * (xB - (((yC - yB) / (xC - xB)) ^ 2 - xB - xC)) - yB) by admit.
        assert (yC = 
         ((yB - yA) / (xB - xA) *
          (xA - (((yB - yA) / (xB - xA)) ^ 2 - xA - xB)) - yA)) by admit.
        fsatz. }

      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      { 
        assert (yC = ((yB - yA) / (xB - xA) * (xA - (((yB - yA) / (xB - xA)) ^ 2 - xA - xB)) - yA)) by admit.
        assert (yA = (yC - yB) / (xC - xB) * (xB - (((yC - yB) / (xC - xB)) ^ 2 - xB - xC)) - yB) by admit.
        fsatz. }
      { assert (yA = (yC - yB) / (xC - xB) * (xB - (((yC - yB) / (xC - xB)) ^ 2 - xB - xC)) - yB) by admit.
        fsatz. }
      { assert (yA = (yC - yB) / (xC - xB) * (xB - (((yC - yB) / (xC - xB)) ^ 2 - xB - xC)) - yB) by admit. fsatz. }
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
      fsatz.
    Admitted.

  End W.
End W.
