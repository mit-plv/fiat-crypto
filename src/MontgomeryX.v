Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.GlobalSettings Crypto.Util.Notations.
Require Import (*Crypto.Util.Tactics*) Crypto.Util.Sum Crypto.Util.Prod.
Require Import Crypto.Spec.MontgomeryCurve Crypto.MontgomeryCurveTheorems.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {char_ge_5:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 5}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).

    Context {a b: F} {b_nonzero:b <> 0}.
    Local Notation add := (M.add(b_nonzero:=b_nonzero)).
    Local Notation opp := (M.opp(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).

    Program Definition to_xz (P:point) : F*F :=
      match M.coordinates P with
      | (x, y) => pair x 1
      | ∞ => pair 1 0
      end.

    (* From Curve25519 paper by djb, appendix B. Credited to Montgomery *)
    Context {a24:F} {a24_correct:(1+1+1+1)*a24 = a-(1+1)}.
    Definition xzladderstep (x1:F) (Q Q':F*F) : ((F*F)*(F*F)) :=
      match Q, Q' with
        pair x z, pair x' z' => 
        let A := x+z in
        let B := x-z in
        let AA := A^2 in
        let BB := B^2 in
        let x2 := AA*BB in
        let E := AA-BB in
        let z2 := E*(AA + a24*E) in
        let C := x'+z' in
        let D := x'-z' in
        let CB := C*B in
        let DA := D*A in
        let x3 := (DA+CB)^2 in
        let z3 := x1*(DA-CB)^2 in
        (pair (pair x2 z2) (pair x3 z3))
      end.

    Ltac t :=
      repeat
        match goal with
        | _ => solve [ contradiction | trivial ]
        | _ => progress intros
        | _ => progress subst
        | _ => progress Tactics.DestructHead.destruct_head' @M.point
        | _ => progress Tactics.DestructHead.destruct_head' @prod
        | _ => progress Tactics.DestructHead.destruct_head' @sum
        | _ => progress Tactics.DestructHead.destruct_head' @and
        | _ => progress Sum.inversion_sum
        | _ => progress Prod.inversion_prod
        | _ => progress Tactics.BreakMatch.break_match_hyps
        | _ => progress Tactics.BreakMatch.break_match
        | _ => progress cbv [fst snd M.coordinates M.add M.zero M.eq M.opp proj1_sig xzladderstep to_xz] in *
        | |- _ /\ _ => split
        end.

    Lemma xzladderstep_correct 
          (Q Q':point) x z x' z' x1 x2 z2 x3 z3
          (Hl:Logic.eq (pair(pair x2 z2)(pair x3 z3)) (xzladderstep x1 (pair x z) (pair x' z')))
          (H:match M.coordinates Q with∞=>z=0/\x<>0|(xQ,y)=>xQ=x/z/\z<>0  (* TODO *) /\ y <> 0 (* TODO: prove this from non-squareness of a^2 - 4 *) end)
          (H':match M.coordinates Q' with∞=>z'=0/\x'<>0|(xQ',_)=>xQ'=x'/z'/\z'<>0 end)
          (H1:match M.coordinates (add Q (opp Q')) with∞=>False|(x,y)=>x=x1/\x<>0 end):
      match M.coordinates (add Q Q) with∞=>z2=0/\x2<>0|(xQQ,_)=>xQQ=x2/z2/\z2<>0 end /\
      match M.coordinates (add Q Q') with∞=>z3=0/\x3<>0|(xQQ',_)=>xQQ'=x3/z3/\z3<>0 end.
    Proof. t; abstract fsatz. Qed.
  End MontgomeryCurve.
End M.