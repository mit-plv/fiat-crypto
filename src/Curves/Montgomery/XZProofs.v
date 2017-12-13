Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Curves.Montgomery.AffineInstances.
Require Import Crypto.Curves.Montgomery.XZ BinPos.
Require Import Coq.Classes.Morphisms.

Module M.
  Section MontgomeryCurve.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3}
            {char_ge_5:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 5}
            {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12}
            {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).

    Context {a b: F} {b_nonzero:b <> 0}.
    Context {a24:F} {a24_correct:(1+1+1+1)*a24 = a-(1+1)}.
    Context {ap2d4:F} {ap2d4_correct:(1+1+1+1)*a24 = a+1+1}.
    Local Notation Madd := (M.add(a:=a)(b_nonzero:=b_nonzero)(char_ge_3:=char_ge_3)).
    Local Notation Mopp := (M.opp(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation Mpoint := (@M.point F Feq Fadd Fmul a b).
    Local Notation xzladderstep := (M.xzladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).
    Local Notation donnaladderstep := (M.donnaladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).
    Local Notation boringladderstep := (M.boringladderstep(ap2d4:=ap2d4)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).
    Local Notation to_xz := (M.to_xz(Fzero:=Fzero)(Fone:=Fone)(Feq:=Feq)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(b:=b)).

    (* TODO(#152): deduplicate between curves files *)
    Ltac prept_step :=
      match goal with
      | _ => progress intros
      | _ => progress autounfold with points_as_coordinates in *
      | _ => progress destruct_head' @unit
      | _ => progress destruct_head' @bool
      | _ => progress destruct_head' @prod
      | _ => progress destruct_head' @sig
      | _ => progress destruct_head' @sum
      | _ => progress destruct_head' @and
      | _ => progress destruct_head' @or
      | H: context[dec ?P] |- _ => destruct (dec P)
      | |- context[dec ?P]      => destruct (dec P)
      | |- ?P => lazymatch type of P with Prop => split end
      end.
    Ltac prept := repeat prept_step.
    Ltac t := prept; trivial; try contradiction; fsatz.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold Proper respectful Reflexive Symmetric Transitive : points_as_coordinates.
    Hint Unfold Let_In : points_as_coordinates.
    Hint Unfold fst snd proj1_sig : points_as_coordinates.
    Hint Unfold fieldwise fieldwise' : points_as_coordinates.
    Hint Unfold M.add M.opp M.point M.coordinates M.xzladderstep M.donnaladderstep M.boringladderstep M.to_xz : points_as_coordinates.

    Lemma donnaladderstep_ok x1 Q Q' :
      fieldwise (n:=2) (fieldwise (n:=2) Feq)
                (xzladderstep x1 Q Q')
                (donnaladderstep x1 Q Q').
    Proof. t. Qed.

    Lemma boringladderstep_ok x1 Q Q' :
      fieldwise (n:=2) (fieldwise (n:=2) Feq)
                (xzladderstep x1 Q Q')
                (boringladderstep x1 Q Q').
    Proof. t. Qed.

    Definition projective (P:F*F) :=
      if dec (snd P = 0) then fst P <> 0 else True.
    Definition eq (P Q:F*F) := fst P * snd Q = fst Q * snd P.

    Hint Unfold projective eq : points_as_coordinates.

    (* happens if u=0 in montladder, all denominators remain 0 *)
    Lemma add_0_numerator_r A B C D
      :  snd (fst (xzladderstep 0 (pair C 0) (pair 0 A))) = 0
      /\ snd (snd (xzladderstep 0 (pair D 0) (pair 0 B))) = 0.
    Proof. t. Qed.
    Lemma add_0_denominators A B C D
      :  snd (fst (xzladderstep 0 (pair A 0) (pair C 0))) = 0
      /\ snd (snd (xzladderstep 0 (pair B 0) (pair D 0))) = 0.
    Proof. t. Qed.

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
    Proof. Time prept. Time par : abstract t. Time Qed.

    Context {a2m4_nonsquare:forall r, r*r <> a*a - (1+1+1+1)}.

    Lemma projective_fst_xzladderstep x1 Q (HQ:projective Q)
      :  projective (fst (xzladderstep x1 Q Q)).
    Proof.
      specialize (a2m4_nonsquare (fst Q/snd Q  - fst Q/snd Q)).
      destruct (dec (snd Q = 0)); t.
    Qed.

    Local Definition a2m4_nz : a*a - (1+1+1+1) <> 0.
    Proof. specialize (a2m4_nonsquare 0). fsatz. Qed.

    Lemma difference_preserved Q Q' :
          M.eq
            (Madd (Madd Q Q) (Mopp (Madd Q Q')))
            (Madd Q (Mopp Q')).
    Proof.
      pose proof (let (_, h, _, _) := AffineInstances.M.MontgomeryWeierstrassIsomorphism b_nonzero (a:=a) a2m4_nz in h) as commutative_group.
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
      {
        pose proof projective_fst_xzladderstep x1 xz Hxz.
        destruct_head prod. 
        cbv [projective fst xzladderstep] in *; eauto. }
      {
        pose proof difference_preserved Q Q' as HQQ;
        destruct (Madd (Madd Q Q) (Mopp (Madd Q Q'))) as [[[xQ yQ]|[]]pfQ];
        destruct (Madd Q (Mopp Q')) as [[[xD yD]|[]]pfD];
        cbv [M.coordinates proj1_sig M.eq] in *;
        destruct_head' and; try split;
          try contradiction; try etransitivity; eauto.
      }
    Qed.

    Definition to_x (xz:F*F) : F :=
      if dec (snd xz = 0) then 0 else fst xz / snd xz.
    Hint Unfold to_x : points_as_coordinates.

    Lemma to_x_to_xz Q : to_x (to_xz Q) = match M.coordinates Q with
                                          | ∞ => 0
                                          | (x,y) => x
                                          end.
    Proof. t. Qed.

    Lemma proper_to_x_projective xz x'z'
           (Hxz:projective xz) (Hx'z':projective x'z')
           (H:eq xz x'z') : Feq (to_x xz) (to_x x'z').
    Proof. destruct (dec (snd xz = 0)), (dec(snd x'z' = 0)); t. Qed.

    Lemma to_x_zero x : to_x (pair x 0) = 0.
    Proof. t. Qed.

    Lemma projective_to_xz Q : projective (to_xz Q).
    Proof. t. Qed.
  End MontgomeryCurve.
End M.
