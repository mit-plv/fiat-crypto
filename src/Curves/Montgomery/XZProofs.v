Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Curves.Montgomery.XZ BinPos.

Module M.
  Section MontgomeryCurve.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_5:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 5}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).

    Let char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two)).
    Proof. eapply Algebra.Hierarchy.char_ge_weaken; eauto; vm_decide. Qed.

    Context {a b: F} {b_nonzero:b <> 0}.
    Context {a24:F} {a24_correct:(1+1+1+1)*a24 = a-(1+1)}.
    Local Notation add := (M.add(a:=a)(b_nonzero:=b_nonzero)(char_ge_3:=char_ge_3)).
    Local Notation opp := (M.opp(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).
    Local Notation xzladderstep := (M.xzladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).

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
        | _ => progress cbv [fst snd M.coordinates M.add M.zero M.eq M.opp proj1_sig M.xzladderstep M.to_xz Let_In] in *
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
    Proof using a24_correct char_ge_5. t; abstract fsatz. Qed.
  End MontgomeryCurve.
End M.
