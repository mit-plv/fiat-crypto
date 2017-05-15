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
    Local Notation xzladderstep := (M.xzladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).
    Local Notation donnaladderstep := (M.donnaladderstep(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)).
    Local Notation to_xz := (M.to_xz(Fzero:=Fzero)(Fone:=Fone)(Feq:=Feq)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(b:=b)).

    Lemma donnaladderstep_ok x1 Q Q' :
      let eq := fieldwise (n:=2) (fieldwise (n:=2) Feq) in
      eq (xzladderstep x1 Q Q') (donnaladderstep x1 Q Q').
    Proof. cbv; break_match; repeat split; fsatz. Qed.

    Definition projective (P:F*F) :=
      if dec (snd P = 0) then fst P <> 0 else True.
    Definition eq (P Q:F*F) := fst P * snd Q = fst Q * snd P.

    Local Ltac do_unfold :=
      cbv [eq projective fst snd M.coordinates M.add M.zero M.eq M.opp proj1_sig xzladderstep M.to_xz Let_In Proper respectful] in *.

    Ltac t_step _ :=
      match goal with
      | _ => solve [ contradiction | trivial ]
      | _ => progress intros
      | _ => progress subst
      | _ => progress specialize_by_assumption
      | [ H : ?x = ?x |- _ ] => clear H
      | [ H : ?x <> ?x |- _ ] => specialize (H (reflexivity _))
      | [ H0 : ?T, H1 : ~?T -> _ |- _ ] => clear H1
      | _ => progress destruct_head'_prod
      | _ => progress destruct_head'_and
      | _ => progress Sum.inversion_sum
      | _ => progress Prod.inversion_prod
      | _ => progress cbv [fst snd proj1_sig projective eq] in * |-
      | _ => progress cbn [to_xz M.coordinates proj1_sig] in * |-
      | _ => progress destruct_head' @M.point
      | _ => progress destruct_head'_sum
      | [ H : context[dec ?T], H' : ~?T -> _ |- _ ]
        => let H'' := fresh in
           destruct (dec T) as [H''|H'']; [ clear H' | specialize (H' H'') ]
      | _ => progress break_match_hyps
      | _ => progress break_match
      | |- _ /\ _ => split
      | _ => progress do_unfold
      end.
    Ltac t := repeat t_step ().

    (* happens if u=0 in montladder, all denominators remain 0 *)
    Lemma add_0_numerator_r A B C D
      :  snd (fst (xzladderstep 0 (pair C 0) (pair 0 A))) = 0
      /\ snd (snd (xzladderstep 0 (pair D 0) (pair 0 B))) = 0.
    Proof. t; fsatz. Qed.
    Lemma add_0_denominators A B C D
      :  snd (fst (xzladderstep 0 (pair A 0) (pair C 0))) = 0
      /\ snd (snd (xzladderstep 0 (pair B 0) (pair D 0))) = 0.
    Proof. t; fsatz. Qed.

    (** This tactic is to work around deficiencies in the Coq 8.6
        (released) version of [nsatz]; it has some heuristics for
        clearing hypotheses and running [exfalso], and then tries to
        solve the goal with [tac].  If [tac] fails on a goal, this
        tactic does nothing. *)
    Local Ltac exfalso_smart_clear_solve_by tac :=
      try lazymatch goal with
          | [ fld : Hierarchy.field (T:=?F) (eq:=?Feq), Feq_dec : DecidableRel ?Feq |- _ ]
            => lazymatch goal with
               | [ H : ?x * 1 = ?y * ?z, H' : ?x <> 0, H'' : ?z = 0 |- _ ]
                 => clear -H H' H'' fld Feq_dec; exfalso; tac
               | [ H : ?x * 0 = 1 * ?y, H' : ?y <> 0 |- _ ]
                 => clear -H H' fld Feq_dec; exfalso; tac
               | _
                 => match goal with
                    | [ H : ?b * ?lhs = ?rhs, H' : ?b * ?lhs' = ?rhs', Heq : ?x = ?y, Hb : ?b <> 0 |- _ ]
                      => exfalso;
                         repeat match goal with H : Ring.char_ge _ |- _ => revert H end;
                         let rhs := match (eval pattern x in rhs) with ?f _ => f end in
                         let rhs' := match (eval pattern y in rhs') with ?f _ => f end in
                         unify rhs rhs';
                         match goal with
                         | [ H'' : ?x = ?Fopp ?x, H''' : ?x <> ?Fopp (?Fopp ?y) |- _ ]
                           => let lhs := match (eval pattern x in lhs) with ?f _ => f end in
                              let lhs' := match (eval pattern y in lhs') with ?f _ => f end in
                              unify lhs lhs';
                              clear -H H' Heq H'' H''' Hb fld Feq_dec; intros
                         | [ H'' : ?x <> ?Fopp ?y, H''' : ?x <> ?Fopp (?Fopp ?y) |- _ ]
                           => let lhs := match (eval pattern x in lhs) with ?f _ => f end in
                              let lhs' := match (eval pattern y in lhs') with ?f _ => f end in
                              unify lhs lhs';
                              clear -H H' Heq H'' H''' Hb fld Feq_dec; intros
                         end;
                         tac
                    | [ H : ?x * (?y * ?z) = 0 |- _ ]
                      => exfalso;
                         repeat match goal with
                                | [ H : ?x * 1 = ?y * ?z |- _ ]
                                  => is_var x; is_var y; is_var z;
                                     revert H
                                end;
                         generalize fld;
                         let lhs := match type of H with ?lhs = _ => lhs end in
                         repeat match goal with
                                | [ x : F |- _ ] => lazymatch type of H with
                                                    | context[x] => fail
                                                    | _ => clear dependent x
                                                    end
                                end;
                         intros _; intros;
                         tac
                    end
               end
          end.

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
      fsatz_prepare_hyps.
      Time t.
      Time par: abstract (exfalso_smart_clear_solve_by fsatz || fsatz).
    Time Qed.

    Context {a2m4_nonsquare:forall r, r*r <> a*a - (1+1+1+1)}.

    Lemma projective_fst_xzladderstep x1 Q (HQ:projective Q)
      :  projective (fst (xzladderstep x1 Q Q)).
    Proof.
      specialize (a2m4_nonsquare (fst Q/snd Q  - fst Q/snd Q)).
      destruct (dec (snd Q = 0)); t; specialize_by assumption; fsatz.
    Qed.

    Let a2m4_nz : a*a - (1+1+1+1) <> 0.
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
