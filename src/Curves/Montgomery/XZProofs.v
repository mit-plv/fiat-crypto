Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
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

    Definition projective (P:F*F) :=
      (fst P = 0 -> snd P <> 0) /\ (snd P = 0 -> fst P <> 0).
    Definition eq (P Q:F*F) := fst P * snd Q = fst Q * snd P.

    Context {nonsquare_a24:forall r, r*r <> a*a - (1+1+1+1)}.
    Let y_nonzero (Q:Mpoint) : match M.coordinates Q with ∞ => True | (x,y) => x <> 0 -> y <> 0 end.
    Proof.
      destruct Q as [Q pfQ]; destruct Q as [[x y]|[]]; cbv -[not]; intros; trivial.
      specialize (nonsquare_a24 (x+x+a)); fsatz.
    Qed.

    Ltac t_step :=
      match goal with
      | _ => solve [ contradiction | trivial ]
      | _ => progress intros
      | _ => progress subst
      | _ => progress destruct_head' @M.point
      | _ => progress destruct_head' @prod
      | _ => progress destruct_head' @sum
      | _ => progress destruct_head' @and
      | _ => progress Sum.inversion_sum
      | _ => progress Prod.inversion_prod
      | _ => progress break_match_hyps
      | _ => progress break_match
      | _ => progress cbv [eq projective fst snd M.coordinates M.add M.zero M.eq M.opp proj1_sig xzladderstep M.to_xz Let_In Proper respectful] in *
      | |- _ /\ _ => split
      end.
    Ltac t := repeat t_step.

    Lemma projective_fst_xzladderstep x1 Q (HQ:projective Q)
      :  projective (fst (xzladderstep x1 Q Q)).
    Proof.
      specialize (nonsquare_a24 (fst Q/snd Q  - fst Q/snd Q)).
      destruct (dec (snd Q = 0)); t; specialize_by assumption; fsatz.
    Qed.

    (* happens if u=0 in montladder, all denominators remain 0 *)
    Lemma add_0_numerator_r A B C D
      :  snd (fst (xzladderstep 0 (pair C 0) (pair 0 A))) = 0
      /\ snd (snd (xzladderstep 0 (pair D 0) (pair 0 B))) = 0.
    Proof. t; fsatz. Qed.
    Lemma add_0_denominators A B C D
      :  snd (fst (xzladderstep 0 (pair A 0) (pair C 0))) = 0
      /\ snd (snd (xzladderstep 0 (pair B 0) (pair D 0))) = 0.
    Proof. t; fsatz. Qed.

    Lemma to_xz_add (x1:F) (xz x'z':F*F)
          (Hxz:projective xz) (Hz'z':projective x'z')
          (Q Q':Mpoint)
          (HQ:eq xz (to_xz Q)) (HQ':eq x'z' (to_xz Q'))
          (difference_correct:match M.coordinates (Madd Q (Mopp Q')) with
                              | ∞ => False                  (* Q <> Q' *)
                              | (x,y) => x = x1 /\ x1 <> 0  (* Q-Q' <> (0, 0) *)
                              end)
      :  eq (to_xz (Madd Q Q )) (fst (xzladderstep x1 xz xz))
      /\ eq (to_xz (Madd Q Q')) (snd (xzladderstep x1 xz x'z'))
      /\ projective (snd (xzladderstep x1 xz x'z')).
    Proof.
      pose proof (nonsquare_a24 (fst xz/snd xz  - fst xz/snd xz)) as Hsq1.
      pose proof (y_nonzero Q) as Hsq2.
      destruct xz as [x z];
      destruct x'z' as [x' z'];
      destruct Q as [Q pfQ]; destruct Q as [[xQ yQ]|[]];
      destruct Q' as [Q' pfQ']; destruct Q' as [[xQ' yQ']|[]];
      t.
      
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      {
        rename f into xQ.
        rename f0 into yQ.
        intro HH.
        assert (((x' - z') * (x + z) + (x' + z') * (x - z)) = 0 /\ ((x' - z') * (x + z) - (x' + z') * (x - z)) = 0) by (
        repeat match goal with
               | H : _ |- _ => apply Hierarchy.zero_product_zero_factor in H; destruct H as [H|H]
               end; split; try contradiction; try assumption); destruct_head and; clear HH H10.
        clear Hsq2.
        assert ((x' - z') * (x + z) = 0) by fsatz; assert ((x' + z') * (x - z) = 0) by fsatz.
        assert (xQ*xQ = 1).
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
      }
      {
        rename f into xQ.
        rename f0 into yQ.
        intro HH.
        assert (((x' - z') * (x + z) + (x' + z') * (x - z)) = 0 /\ ((x' - z') * (x + z) - (x' + z') * (x - z)) = 0) by (
        repeat match goal with
               | H : _ |- _ => apply Hierarchy.zero_product_zero_factor in H; destruct H as [H|H]
               end; split; try contradiction; try assumption); destruct_head and; clear HH H10.
        clear Hsq2.
        assert ((x' - z') * (x + z) = 0) by fsatz; assert ((x' + z') * (x - z) = 0) by fsatz.
        assert (xQ*xQ = 1).
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
      }
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      { destruct (dec(f=0)); [|destruct Hsq2; fsatz].
        assert (x = 0) by fsatz. 
        assert (xQ' - f <> 0) by fsatz.
        specialize_by assumption. 
        destruct (dec(x'=0)). specialize_by assumption. abstract fsatz.
        destruct (dec(z'=0)). specialize_by assumption. abstract fsatz.
        abstract fsatz. }
      { destruct (dec(f=0)); [|destruct Hsq2; fsatz].
        assert (x = 0) by fsatz. 
        assert (xQ' - f <> 0) by fsatz.
        specialize_by assumption. 
        destruct (dec(x'=0)). specialize_by assumption. abstract fsatz.
        destruct (dec(z'=0)). specialize_by assumption. abstract fsatz.
        abstract fsatz. }
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      { rename f into xQ. rename f0 into yQ.
        intro HH.
        apply H5.
        assert ((x' - z') * (x + z) - (x' + z') * (x - z) =0 /\ ((x' - z') * (x + z) + (x' + z') * (x - z))=0) by (
        repeat match goal with
               | H : _ |- _ => apply Hierarchy.zero_product_zero_factor in H; destruct H as [H|H]
               end; split; try contradiction; try assumption); destruct_head and; clear HH H8.
        clear Hsq2 Hsq1. (* TODO: removing this clear gives stack overflow *)
        assert (x'*x = z'*z) by fsatz.
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
      }
      { rename f into xQ. rename f0 into yQ.
        intro HH.
        apply H5.
        assert ((x' - z') * (x + z) - (x' + z') * (x - z) =0 /\ ((x' - z') * (x + z) + (x' + z') * (x - z))=0) by (
        repeat match goal with
               | H : _ |- _ => apply Hierarchy.zero_product_zero_factor in H; destruct H as [H|H]
               end; split; try contradiction; try assumption); destruct_head and; clear HH H8.
        clear Hsq2 Hsq1. (* TODO: removing this clear gives stack overflow *)
        assert (x'*x = z'*z) by fsatz.
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
      }
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      { 
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz. }
      { 
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz. }
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      { 
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz. }
      {
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz. }
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      clear Hsq1 Hsq2; abstract fsatz.
      { 
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz. }
      { 
        destruct (dec(z' = 0)), (dec(z = 0)); specialize_by assumption.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz.
        abstract fsatz. }
    Qed.

    Context {group:@Hierarchy.abelian_group Mpoint M.eq Madd M.zero Mopp}.
    Lemma difference_preserved Q Q' :
          M.eq
            (Madd (Madd Q Q) (Mopp (Madd Q Q')))
            (Madd Q (Mopp Q')).
    Proof.
      rewrite Group.inv_op.
      rewrite <-Hierarchy.associative.
      rewrite Group.cancel_left.
      rewrite Hierarchy.commutative.
      rewrite <-Hierarchy.associative.
      rewrite Hierarchy.left_inverse.
      rewrite Hierarchy.right_identity.
      reflexivity.
    Qed.

    Lemma to_xz_add'
          (x1:F)
          (xz x'z':F*F)
          (Q Q':Mpoint)

          (HQ:eq xz (to_xz Q))
          (HQ':eq x'z' (to_xz Q'))
          (Hxz:projective xz)
          (Hx'z':projective x'z')
          (difference_correct:match M.coordinates (Madd Q (Mopp Q')) with
                              | ∞ => False                  (* Q <> Q' *)
                              | (x,y) => x = x1 /\ x1 <> 0  (* Q-Q' <> (0, 0) *)
                              end)
      :
           eq (to_xz (Madd Q Q )) (fst (xzladderstep x1 xz xz))
        /\ eq (to_xz (Madd Q Q')) (snd (xzladderstep x1 xz x'z'))
        /\ projective (fst (xzladderstep x1 xz x'z'))
        /\ projective (snd (xzladderstep x1 xz x'z'))
        /\ match M.coordinates (Madd (Madd Q Q) (Mopp (Madd Q Q'))) with
                              | ∞ => False                  (* Q <> Q' *)
                              | (x,y) => x = x1 /\ x1 <> 0  (* Q-Q' <> (0, 0) *)
                              end.
    Proof.
      destruct (to_xz_add x1 xz x'z' Hxz Hx'z' Q Q' HQ HQ' difference_correct) as [? [? ?]].
      split; [|split; [|split;[|split]]]; eauto.
      pose proof projective_fst_xzladderstep x1 xz Hxz.
      destruct_head prod.
      cbv [projective fst xzladderstep] in *; eauto.
      {
        pose proof difference_preserved Q Q' as HQQ;
        destruct (Madd (Madd Q Q) (Mopp (Madd Q Q'))) as [[[xQ yQ]|[]]pfQ];
        destruct (Madd Q (Mopp Q')) as [[[xD yD]|[]]pfD];
        cbv [M.coordinates proj1_sig M.eq];
        cbv [M.coordinates proj1_sig M.eq] in HQQ;
        cbv [M.coordinates proj1_sig M.eq] in difference_correct;
          destruct_head' and; try split; try contradiction; try etransitivity; eauto.
      }
    Qed.

    Definition to_x (xz:F*F) : F :=
      if dec (snd xz = 0) then 0 else fst xz / snd xz.

    Lemma to_x_to_xz Q : to_x (to_xz Q) = match M.coordinates Q with
                                          | ∞ => 0
                                          | (x,y) => x
                                          end.
    Proof.
      cbv [to_x]; t; fsatz.
    Qed.

    Lemma proper_to_x_projective xz x'z'
           (Hxz:projective xz) (Hx'z':projective x'z')
           (H:eq xz x'z') : Feq (to_x xz) (to_x x'z').
    Proof.
      destruct (dec (snd xz = 0)), (dec(snd x'z' = 0));
        cbv [to_x]; t;
        specialize_by (assumption||reflexivity);
        try fsatz.
    Qed.

    Lemma to_x_zero x : to_x (pair x 0) = 0.
    Proof. cbv; t; fsatz. Qed.

    Lemma projective_to_xz Q : projective (to_xz Q).
    Proof. t; fsatz. Qed.
  End MontgomeryCurve.
End M.
