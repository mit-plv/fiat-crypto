Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.ScalarMult.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Curves.Montgomery.AffineInstances.
Require Import Crypto.Curves.Montgomery.XZ BinPos.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Lia.

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

    (** This tactic is to solve goals that fsatz also solves, but to
        do so faster in some cases common in this file. It may also
        work around deficiencies in the Coq 8.6 (released) version of
        [nsatz]; it has some heuristics for clearing hypotheses and
        running [exfalso], and then tries [fsatz] *)
    Local Ltac maybefast :=
      try lazymatch goal with
          | [ fld : Hierarchy.field (T:=?F) (eq:=?Feq), Feq_dec : DecidableRel ?Feq |- _ ]
            => lazymatch goal with
               | [ H : ?x * 1 = ?y * ?z, H' : ?x <> 0, H'' : ?z = 0 |- _ ]
                 => clear -H H' H'' fld Feq_dec; exfalso; fsatz
               | [ H : ?x * 0 = 1 * ?y, H' : ?y <> 0 |- _ ]
                 => clear -H H' fld Feq_dec; exfalso; fsatz
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
                         fsatz
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
                         fsatz
                    end
               end
          end.

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
    Ltac t := t_fast; maybefast; fsatz.

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
      /\ eq (fst (xzladderstep x1 xz x'z')) (to_xz (Madd Q Q ))
      /\ eq (snd (xzladderstep x1 xz x'z')) (to_xz (Madd Q Q')).
    Proof. Time t_fast. Time par: abstract (maybefast; fsatz). Time Qed.
    (* 12 ;; 24 ;; 3 *)

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
      (* FIXME: what we actually want to do here is to rewrite with in
      match argument with
      [sumwise (fieldwise (n:=2) Feq) (fun _ _ => True)] *)
      cbv [M.eq] in *; break_match; break_match_hyps;
        destruct_head' @and; repeat split; subst;
          try solve [intuition congruence].
      congruence (* congruence failed, idk WHY *)
      || (match goal with
            [H:?f1 = ?x1, G:?f = ?f1 |- ?f = ?x1] => rewrite G; exact H
          end).
    Qed.

    Lemma ladder_invariant_swap x1 Q Q' (H:ladder_invariant x1 Q Q')
      : ladder_invariant x1 Q' Q.
    Proof. t. Qed.

    Lemma to_xz_add x1 xz x'z' Q Q'
          (Hxz : projective xz) (Hx'z' : projective x'z')
          (HQ : eq xz (to_xz Q)) (HQ' : eq x'z' (to_xz Q'))
          (HI : ladder_invariant x1 Q Q')
      :    projective (fst (xzladderstep x1 xz x'z'))
        /\ projective (snd (xzladderstep x1 xz x'z'))
        /\ eq (fst (xzladderstep x1 xz x'z')) (to_xz (Madd Q Q ))
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

    Hint Unfold M.eq : points_as_coordinates.
    Global Instance Proper_to_xz : Proper (M.eq ==> eq) to_xz.
    Proof. t. Qed.

    Global Instance  Reflexive_eq : Reflexive eq.
    Proof. t. Qed.
    Global Instance  Symmetric_eq : Symmetric eq.
    Proof. t. Qed.
    Lemma transitive_eq {p} q {r} : projective q -> eq p q -> eq q r -> eq p r.
    Proof. t. Qed.
    
    Lemma projective_to_xz Q : projective (to_xz Q).
    Proof. t. Qed.

    Global Instance Proper_ladder_invariant : Proper (Feq ==> M.eq ==> M.eq ==> iff) ladder_invariant.
    Proof. t. Qed.

    Local Notation montladder := (M.montladder(a24:=a24)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)(Fzero:=Fzero)(Fone:=Fone)(Finv:=Finv)(cswap:=fun b x y => if b then pair y x else pair x y)).
    Local Notation scalarmult := (@ScalarMult.scalarmult_ref Mpoint Madd M.zero Mopp).

    Import Crypto.Experiments.Loops.
    Import Coq.ZArith.BinInt.

    Lemma to_x_inv00 (HFinv:Finv 0 = 0) x z : to_x (pair x z) = x * Finv z.
    Proof. t_fast; setoid_subst_rel Feq; rewrite ?HFinv in *; fsatz. Qed.

    Lemma Z_shiftr_testbit_1 n i: Logic.eq (n>>i)%Z (Z.div2 (n >> i) + Z.div2 (n >> i) + Z.b2z (Z.testbit n i))%Z.
    Proof. rewrite ?Z.testbit_odd, ?Z.add_diag, <-?Z.div2_odd; reflexivity. Qed.

    Lemma montladder_correct_nz
          (HFinv : Finv 0 = 0)
          (n : Z) (P : M.point)
          (scalarbits : Z) (point : F)
          (Hnz : point <> 0)
          (Hn : (0 <= n < 2^scalarbits)%Z)
          (Hscalarbits : (0 <= scalarbits)%Z)
          (Hpoint : point = to_x (to_xz P))
      : montladder scalarbits (Z.testbit n) point = to_x (to_xz (scalarmult n P)).
    Proof.
      pose proof (let (_, h, _, _) := AffineInstances.M.MontgomeryWeierstrassIsomorphism b_nonzero (a:=a) a2m4_nz in h) as commutative_group.
      cbv beta delta [M.montladder].
      (* [while.by_invariant] expects a goal like [?P (while _ _ _ _)], make it so: *)
      lazymatch goal with |- context [while ?t ?b ?l ?i] => pattern (while t b l i) end.
      eapply (while.by_invariant
                (fun '(x2, z2, x3, z3, swap, i) =>
                   (i >= -1)%Z /\
                   projective (pair x2 z2) /\
                   projective (pair x3 z3) /\
                   let q := if (swap:bool) then (pair x3 z3) else (pair x2 z2) in
                   let q' := if (swap:bool) then (pair x2 z2) else (pair x3 z3) in
                   let r := (n >> Z.succ i)%Z in
                   eq q (to_xz (scalarmult r P)) /\
                   eq q' (to_xz (scalarmult (Z.succ r) P)) /\
                   ladder_invariant point (scalarmult r P) (scalarmult (Z.succ r) P))
                (fun s => Z.to_nat (Z.succ (snd s))) (* decreasing measure *) ).
      { (* invariant holds in the beginning *) cbn.
        rewrite ?Z.succ_pred, ?Z.lt_pow_2_shiftr, <-?Z.one_succ by tauto.
        repeat split; [lia|t..]. }
      { intros [ [ [ [ [x2 z2] x3] z3] swap] i] [Hi [Hx2z2 [Hx3z3 [Hq [Hq' Hladder]]]]].
        destruct (i >=? 0)%Z eqn:Hbranch; (* did the loop continue? *)
          rewrite Z.geb_ge_iff in Hbranch.
        { (* if loop continued, invariant is preserved *)
          let group _ := ltac:(repeat rewrite ?scalarmult_add_l, ?scalarmult_0_l, ?scalarmult_1_l, ?Hierarchy.left_identity, ?Hierarchy.right_identity, ?Hierarchy.associative, ?(Hierarchy.commutative _ P); reflexivity) in
          destruct (Z.testbit n i) eqn:Hbit in *;
            destruct swap eqn:Hswap in *;
            repeat match goal with
                   | _ => solve [ congruence | assumption | lia ]
                   | _ => progress cbv beta delta [Let_In]
                   | _ => progress cbn [xorb Z.b2z]
                   | _ => progress autorewrite with cancel_pair in *
                   | _ => rewrite <-!@surjective_pairing
                   | _ => progress inversion_prod
                   | _ => progress subst
                   | _ => break_match_hyps_step ltac:(fun _ => idtac)
                   | _ => break_match_step ltac:(fun _ => idtac)
                   | H:projective ?xz, G:projective ?x'z', HQ: eq ?xz (to_xz ?Q), HQ': eq ?x'z' (to_xz ?Q')
                     |- context [xzladderstep ?p ?xz ?x'z']
                     => let pf := constr:(to_xz_add p xz x'z' _ _ H G HQ HQ' ltac:(auto using ladder_invariant_swap)) in
                        unique pose proof (proj1 pf); destruct (proj2 pf) as [? [? [? ?]]] (* because there is no unique destruct *)
                   | _ => progress rewrite ?Z.succ_pred, ?Z.shiftr_succ, <-?Z.div2_spec, <-?Z.add_1_r in *
                   | |- context [scalarmult (n>>i) ] => rewrite (Z_shiftr_testbit_1 n i), Hbit; cbn [Z.b2z]
                   | |- context [scalarmult (n>>i+1) ] => rewrite (Z_shiftr_testbit_1 n i), Hbit; cbn [Z.b2z]
                   | |- ?P => match type of P with Prop => split end
                   | H: eq (?f _) (to_xz ?LHS) |- eq (?f _) (to_xz ?RHS)
                     => eapply (transitive_eq (to_xz LHS) ltac:(auto using projective_to_xz) H); f_equiv; group ()
                   | H: ladder_invariant _ _ _ |- ladder_invariant _ _ _
                     => refine (proj1 (Proper_ladder_invariant _ _ (reflexivity _)  _ _ _  _ _ _) H); group ()
                   | H: ladder_invariant _ _ _ |- ladder_invariant _ _ _
                     => refine (proj1 (Proper_ladder_invariant _ _ (reflexivity _)  _ _ _  _ _ _) (ladder_invariant_swap _ _ _ H)); group ()
                   | |- ?P => match type of P with Prop => split end
                   end. }
        { (* if loop exited, invariant implies postcondition *)
          destruct_head' @and; autorewrite with cancel_pair in *.
          replace i with ((-(1))%Z) in * by lia; clear Hi Hbranch.
          rewrite Z.succ_m1, Z.shiftr_0_r in *.
          destruct swap eqn:Hswap; rewrite <-!to_x_inv00 by assumption;
            eauto using projective_to_xz, proper_to_x_projective. } }
      { (* fuel <= measure *) cbn. rewrite Z.succ_pred. reflexivity. }
      { (* measure decreases *) intros [? i].
        destruct (i >=? 0)%Z eqn:Hbranch;rewrite Z.geb_ge_iff in Hbranch; [|exact I].
        cbv [Let_In]; break_match; cbn; rewrite Z.succ_pred; apply Znat.Z2Nat.inj_lt; lia. }
    Qed.
  End MontgomeryCurve.
End M.
