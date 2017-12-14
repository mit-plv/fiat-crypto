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
    Local Notation Madd := (M.add(a:=a)(b_nonzero:=b_nonzero)(char_ge_3:=char_ge_3)).
    Local Notation Mopp := (M.opp(a:=a)(b_nonzero:=b_nonzero)).
    Local Notation Mpoint := (@M.point F Feq Fadd Fmul a b).
    Local Notation to_xz := (M.to_xz(Fzero:=Fzero)(Fone:=Fone)(Feq:=Feq)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(b:=b)).
    Local Notation xzladderstep := (M.xzladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).

    (* TODO(#152): deduplicate between curves files *)
    Ltac prept_step :=
      match goal with
      | _ => progress intros
      | _ => progress autounfold with points_as_coordinates in *
      | _ => progress destruct_head'_True
      | _ => progress destruct_head'_unit
      | _ => progress destruct_head'_prod
      | _ => progress destruct_head'_sig
      | _ => progress destruct_head'_bool
      | _ => progress destruct_head'_sum
      | _ => progress destruct_head'_and
      | _ => progress destruct_head'_or
      | H: context[dec ?P] |- _ => destruct (dec P)
      | |- context[dec ?P]      => destruct (dec P)
      | |- ?P => lazymatch type of P with Prop => split end
      end.
    Ltac prept := repeat prept_step.
    Ltac t_fast := prept; trivial; try contradiction.
    Ltac t := prept; fsatz.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold Proper respectful Reflexive Symmetric Transitive : points_as_coordinates.
    Hint Unfold Let_In : points_as_coordinates.
    Hint Unfold fst snd proj1_sig : points_as_coordinates.
    Hint Unfold fieldwise fieldwise' : points_as_coordinates.
    Hint Unfold M.add M.opp M.point M.coordinates M.xzladderstep M.donnaladderstep M.boringladderstep M.to_xz : points_as_coordinates.

    Lemma donnaladderstep_same x1 Q Q' :
      fieldwise (n:=2) (fieldwise (n:=2) Feq)
                (xzladderstep x1 Q Q')
                (M.donnaladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul) x1 Q Q').
    Proof. t. Qed.

    Lemma boringladderstep_same (ap2d4:F) (ap2d4_correct:(1+1+1+1)*a24 = a+1+1) x1 Q Q' :
      fieldwise (n:=2) (fieldwise (n:=2) Feq)
                (xzladderstep x1 Q Q')
                (M.boringladderstep(ap2d4:=ap2d4)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul) x1 Q Q').
    Proof. t. Qed.

    Definition projective (P:F*F) :=
      if dec (snd P = 0) then fst P <> 0 else True.
    Definition eq (P Q:F*F) := fst P * snd Q = fst Q * snd P.
    Definition ladder_invariant x1 Q Q' :=
      match M.coordinates (Madd Q (Mopp Q')) with
      | ∞ => False                  (* Q <> Q' *)
      | (x,y) => x = x1 /\ x1 <> 0  (* Q-Q' <> (0, 0) *)
      end.
    Hint Unfold projective eq ladder_invariant : points_as_coordinates.

    (* happens if u=0 in montladder, all denominators remain 0 *)
    Lemma add_0_numerator_r A B C D
      :  snd (fst (xzladderstep 0 (pair C 0) (pair 0 A))) = 0
      /\ snd (snd (xzladderstep 0 (pair D 0) (pair 0 B))) = 0.
    Proof. t. Qed.
    Lemma add_0_denominators A B C D
      :  snd (fst (xzladderstep 0 (pair A 0) (pair C 0))) = 0
      /\ snd (snd (xzladderstep 0 (pair B 0) (pair D 0))) = 0.
    Proof. t. Qed.

    Lemma to_xz_add_coordinates (x1:F) (xz x'z':F*F)
          (Hxz:projective xz) (Hz'z':projective x'z')
          (Q Q':Mpoint)
          (HQ:eq xz (to_xz Q)) (HQ':eq x'z' (to_xz Q'))
          (HI:ladder_invariant x1 Q Q')
      :  projective (snd (xzladderstep x1 xz x'z'))
      /\ eq (fst (xzladderstep x1 xz xz)) (to_xz (Madd Q Q ))
      /\ eq (snd (xzladderstep x1 xz x'z')) (to_xz (Madd Q Q')).
    Proof. Time t_fast. Time par: abstract fsatz. Time Qed.

    Context {a2m4_nonsquare:forall r, r*r <> a*a - (1+1+1+1)}.

    Lemma projective_fst_xzladderstep x1 Q (HQ:projective Q) Q'
      :  projective (fst (xzladderstep x1 Q Q')).
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

    Lemma ladder_invariant_preserved x1 Q Q' (H:ladder_invariant x1 Q Q')
      : ladder_invariant x1 (Madd Q Q) (Madd Q Q').
    Proof.
      cbv [ladder_invariant] in *.
      pose proof difference_preserved Q Q' as Hrw.
      (* TODO: rewrite with in match argument with [sumwise (fieldwise (n:=2) Feq) (fun _ _ => True)] *)
      match type of Hrw with
        M.eq ?X ?Y => replace X with Y by admit
      end.
      assumption.
    Admitted.

    Lemma to_xz_add x1 xz x'z' Q Q'
          (Hxz : projective xz) (Hx'z' : projective x'z')
          (HQ : eq xz (to_xz Q)) (HQ' : eq x'z' (to_xz Q'))
          (HI : ladder_invariant x1 Q Q')
      :    projective (fst (xzladderstep x1 xz x'z'))
        /\ projective (snd (xzladderstep x1 xz x'z'))
        /\ eq (fst (xzladderstep x1 xz xz)) (to_xz (Madd Q Q ))
        /\ eq (snd (xzladderstep x1 xz x'z')) (to_xz (Madd Q Q'))
        /\ ladder_invariant x1 (Madd Q Q) (Madd Q Q').
    Proof.
      destruct (to_xz_add_coordinates x1 xz x'z' Hxz Hx'z' Q Q' HQ HQ' HI) as [? [? ?]].
      eauto 99 using projective_fst_xzladderstep, ladder_invariant_preserved.
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
