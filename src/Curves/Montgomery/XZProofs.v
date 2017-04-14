Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Curves.Montgomery.XZ BinPos.
Require Import Coq.Classes.Morphisms.

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
    Local Notation Madd := (M.add(a:=a)(b_nonzero:=b_nonzero)(char_ge_3:=char_ge_3)).
    Local Notation Mopp := (M.opp(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation Mpoint := (@M.point F Feq Fadd Fmul a b).
    Local Notation xzladderstep := (M.xzladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).
    Local Notation to_xz := (M.to_xz(Fzero:=Fzero)(Fone:=Fone)(Feq:=Feq)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(b:=b)).

    Definition eq (P Q:F*F) := fst P * snd Q = fst Q * snd P.

    Context {nonsquare_a24:forall r, r*r <> a*a - (1+1+1+1)}.
    Let y_nonzero (Q:Mpoint) : match M.coordinates Q with ∞ => True | (x,y) => x <> 0 -> y <> 0 end.
    Proof.
      destruct Q as [Q pfQ]; destruct Q as [[x y]|[]]; cbv -[not]; intros; trivial.
      specialize (nonsquare_a24 (x+x+a)); fsatz.
    Qed.

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
        | _ => progress cbv [eq fst snd M.coordinates M.add M.zero M.eq M.opp proj1_sig xzladderstep M.to_xz Let_In Proper respectful] in *
        | |- _ /\ _ => split
        end.

    Lemma add_0_denominators A B C D
      :  snd (fst (xzladderstep 0 (pair A 0) (pair C 0))) = 0
      /\ snd (snd (xzladderstep 0 (pair B 0) (pair D 0))) = 0.
    Proof. t; fsatz. Qed.

    Lemma add_0_numerator_l A B C D
      :  snd (fst (xzladderstep 0 (pair 0 C) (pair A 0))) = 0
      /\ snd (snd (xzladderstep 0 (pair 0 D) (pair B 0))) = 0.
    Proof. t; fsatz. Qed.

    Lemma add_0_numerator_r A B C D
      :  snd (fst (xzladderstep 0 (pair C 0) (pair 0 A))) = 0
      /\ snd (snd (xzladderstep 0 (pair D 0) (pair 0 B))) = 0.
    Proof. t; fsatz. Qed.

    Lemma to_xz_add (x1:F) (Q Q':Mpoint)
          (difference_correct:match M.coordinates (Madd Q (Mopp Q')) with
                              | ∞ => False                  (* Q <> Q' *)
                              | (x,y) => x = x1 /\ x1 <> 0  (* Q-Q' <> (0, 0) *)
                              end)
      :  eq (to_xz (Madd Q Q )) (fst (xzladderstep x1 (to_xz Q) (to_xz Q )))
      /\ eq (to_xz (Madd Q Q')) (snd (xzladderstep x1 (to_xz Q) (to_xz Q'))).
    Proof. specialize (y_nonzero Q); t; fsatz. Qed.
  End MontgomeryCurve.
End M.
