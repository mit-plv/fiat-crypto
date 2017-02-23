Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.Algebra Crypto.Algebra Crypto.Util.Decidable.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tuple Crypto.Util.Notations Crypto.Util.Tactics.
Require Export Crypto.Util.FixCoqMistakes.

Module E.
  Import Group ScalarMult Ring Field CompleteEdwardsCurve.E.

  Notation onCurve_zero := Pre.onCurve_zero.
  Notation denominator_nonzero := Pre.denominator_nonzero.
  Notation denominator_nonzero_x := Pre.denominator_nonzero_x.
  Notation denominator_nonzero_y := Pre.denominator_nonzero_y.
  Notation onCurve_add := Pre.onCurve_add.

  Section CompleteEdwardsCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two)}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).

    Context {a d: F}
            {nonzero_a : a <> 0}
            {square_a : exists sqrt_a, sqrt_a^2 = a}
            {nonsquare_d : forall x, x^2 <> d}.
    
    Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).
    Local Notation point := (@E.point F Feq Fone Fadd Fmul a d).
    Local Notation eq    := (@E.eq F Feq Fone Fadd Fmul a d).
    Local Notation zero  := (E.zero(nonzero_a:=nonzero_a)(d:=d)).
    Local Notation add   := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).
    Local Notation mul   := (E.mul(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).

    Program Definition opp (P:point) : point := (Fopp (fst P), (snd P)).
    Next Obligation. destruct P as [ [??]?]; cbv; fsatz. Qed.

    Ltac t_step :=
      match goal with
      | _ => solve [trivial | exact _ ]
      | _ => intro
      | |- Equivalence _ => split
      | |- abelian_group => split | |- group => split | |- monoid => split
      | |- is_associative => split | |- is_commutative => split 
      | |- is_left_inverse => split | |- is_right_inverse => split
      | |- is_left_identity => split | |- is_right_identity => split
      | _ => progress destruct_head' @E.point
      | _ => progress destruct_head' prod
      | _ => progress destruct_head' and
      | |- context[E.add ?P ?Q] =>
        unique pose proof (Pre.denominator_nonzero_x _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q));
        unique pose proof (Pre.denominator_nonzero_y _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q))
      | _ => progress cbv [opp E.zero E.eq E.add E.coordinates proj1_sig fieldwise fieldwise'] in *
      (* [_gather_nonzeros] must run before [fst_pair] or [simpl] but after splitting E.eq and unfolding [E.add] *)
      | |- _ /\ _ => split | |- _ <-> _ => split
      end.
    Ltac t := repeat t_step; fsatz.

    Global Instance associative_add : is_associative(eq:=E.eq)(op:=add).
    Proof.
      (* [nsatz_compute] for a denominator runs out of 6GB of stack space *)
      (* COQBUG: https://coq.inria.fr/bugs/show_bug.cgi?id=5359 *)
      Add Field _field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).
      Import Field_tac.
      repeat t_step; (field_simplify_eq; [IntegralDomain.nsatz|]); repeat split; trivial.
      { intro. eapply H3. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
      { intro. eapply H. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
      { intro. eapply H4. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
      { intro. eapply H0. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
    Qed.

    Global Instance edwards_curve_abelian_group : abelian_group (eq:=eq)(op:=add)(id:=zero)(inv:=opp).
    Proof. t. Qed.

    Global Instance Proper_coordinates : Proper (eq==>fieldwise (n:=2) Feq) coordinates. Proof. repeat t_step. Qed.

    Global Instance Proper_mul : Proper (Logic.eq==>eq==>eq) mul.
    Proof.
      intros n n'; repeat intro; subst n'.
      induction n; (reflexivity || eapply (_:Proper (eq==>eq==>eq) add); eauto).
    Qed.

    Global Instance mul_is_scalarmult : @is_scalarmult point eq add zero mul.
    Proof. split; intros; (reflexivity || exact _). Qed.

    Section PointCompression.
      Local Notation "x ^ 2" := (x*x).

      Lemma a_d_y2_nonzero y : d * y^2 - a <> 0.
      Proof.
        destruct square_a as [sqrt_a], (dec (y=0));
          pose proof nonzero_a; pose proof (nonsquare_d (sqrt_a/y)); fsatz.
      Qed.

      Lemma solve_correct : forall x y, onCurve x y <-> (x^2 = (y^2-1) / (d*y^2-a)).
      Proof. pose proof a_d_y2_nonzero; t. Qed.

      (* TODO: move *)
      Definition exist_option {A} (P : A -> Prop) (x : option A)
        : match x with Some v => P v | None => True end -> option { a : A | P a }.
        destruct x; intros; [apply Some | apply None]; eauto. Defined.
      Lemma exist_option_Some {A} P (x:option A) pf s
            (H:Logic.eq (exist_option P x pf) (Some s))
            : Logic.eq x (Some (proj1_sig s)).
      Proof. destruct x, s; cbv [exist_option proj1_sig] in *; congruence. Qed.
      Lemma exist_option_None {A} P (x:option A) pf
            (H:Logic.eq (exist_option P x pf) None)
            : Logic.eq x None.
      Proof. destruct x; cbv [exist_option proj1_sig] in *; congruence. Qed.

      Context
        {sqrt_div:F -> F -> option F}
        {sqrt_Some: forall u v r, Logic.eq (sqrt_div u v) (Some r) -> r^2 = u/v}
        {sqrt_None: forall u v, Logic.eq (sqrt_div u v) None -> forall r, r^2 <> u/v}
        {parity:F -> bool} {Proper_parity: Proper (Feq ==> Logic.eq) parity}
        {parity_opp: forall x, x <> 0 -> Logic.eq (parity (Fopp x)) (negb (parity x)) }.

      Definition compress (P:point) : (bool*F) :=
        let (x, y) := coordinates P in pair (parity x) y.
      Definition set_sign r p : option F :=
        if dec (Logic.eq (parity r) p)
        then Some r
        else
          let r' := Fopp r in
          if dec (Logic.eq (parity r') p)
          then Some r'
          else None.
      Lemma set_sign_None r p s (H:Logic.eq (set_sign r p) (Some s))
            : s^2 = r^2 /\ Logic.eq (parity s) p.
      Proof.
        repeat match goal with
               | _ => progress subst
               | _ => progress cbv [set_sign] in *
               | _ => progress break_match_hyps
               | _ => progress Option.inversion_option
               | _ => split
               | _ => solve [ trivial | fsatz ]
               end.
      Qed.
      Lemma set_sign_Some r p (H:Logic.eq (set_sign r p) None)
            : forall s, s^2 = r^2 -> not (Logic.eq (parity s) p).
        repeat match goal with
               | _ => progress intros
               | _ => progress subst
               | _ => progress cbv [set_sign] in *
               | _ => progress break_match_hyps
               | _ => progress Option.inversion_option
               end.
        destruct (dec (r = 0)).
        assert (s = 0); [|solve[setoid_subst_rel Feq; trivial] ].
        admit.
        progress rewrite parity_opp in * by assumption.
        destruct (parity r), p; cbv [negb] in *; congruence.
      Admitted.

      Local Ltac t_step :=
        match goal with
        | _ => progress subst
        | _ => progress destruct_head' @E.point
        | _ => progress destruct_head' and
        | _ => progress break_match
        | _ => progress break_match_hyps
        | _ => progress Option.inversion_option
        | _ => progress Prod.inversion_prod
        | H:_ |- _ => unique pose proof (sqrt_Some _ _ _ H); clear H
        | H:_ |- _ => unique pose proof (sqrt_None _ _ H); clear H
        | H:_ |- _ => unique pose proof (set_sign_None _ _ _ H); clear H
        | H:_ |- _ => unique pose proof (set_sign_Some _ _ H); clear H
        | H:_ |- _ => unique pose proof (exist_option_Some _ _ _ _ H); clear H
        | H:_ |- _ => unique pose proof (exist_option_None _ _ _ H); clear H
        | _ => solve [trivial | eapply solve_correct; fsatz]
        end.
      Local Ltac t := repeat t_step.
      
      Program Definition decompress (b:bool*F) : option point :=
        exist_option _
            match b return option (F*F) with
              (p, y) =>
              match sqrt_div (y^2 - 1) (d*y^2 - a) return option (F*F) with
              | None => None
              | Some r =>
                match set_sign r p return option (F*F) with
                | Some x => Some (x, y)
                | None => None
                end
              end
            end _.
      Next Obligation. t. Qed.

      Lemma decompress_Some b P (H:Logic.eq (decompress b) (Some P))
        : Logic.eq (compress P) b.
      Proof. cbv [compress decompress] in *; t. Qed.

      Lemma decompress_None b (H:Logic.eq (decompress b) None)
        : forall P, not (Logic.eq (compress P) b).
      Proof.
        cbv [compress decompress exist_option coordinates] in *; intros.
        t.
        intro.
        apply (H0 f); [|congruence].
        admit.
        intro. Prod.inversion_prod; subst.
        rewrite solve_correct in y.
        eapply H. eapply y.
      Admitted.
    End PointCompression.
  End CompleteEdwardsCurveTheorems.
  Section Homomorphism.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fchar_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two)}
            {Feq_dec:DecidableRel Feq}.

    Context {Fa Fd: F}
            {nonzero_a : not (Feq Fa Fzero)}
            {square_a : exists sqrt_a, Feq (Fmul sqrt_a sqrt_a) Fa}
            {nonsquare_d : forall x, not (Feq (Fmul x x) Fd)}.
    
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {fieldK: @Algebra.field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Keq_dec:DecidableRel Keq}.
    Context {FtoK:F->K} {HFtoK:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                     K Keq Kone Kadd Kmul FtoK}.
    Context {KtoF:K->F} {HKtoF:@Ring.is_homomorphism K Keq Kone Kadd Kmul
                                                     F Feq Fone Fadd Fmul KtoF}.
    Context {HisoF:forall x, Feq (KtoF (FtoK x)) x}.
    Context {Ka} {Ha:Keq (FtoK Fa) Ka} {Kd} {Hd:Keq (FtoK Fd) Kd}.

    Lemma nonzero_Ka : ~ Keq Ka Kzero.
    Proof.
      rewrite <-Ha.
      Ring.pull_homomorphism FtoK.
      intro X.
      eapply (Monoid.is_homomorphism_phi_proper(phi:=KtoF)) in X.
      rewrite 2HisoF in X.
      auto.
    Qed.

    Lemma square_Ka : exists sqrt_a, Keq (Kmul sqrt_a sqrt_a) Ka.
    Proof.
      destruct square_a as [sqrt_a]. exists (FtoK sqrt_a).
      Ring.pull_homomorphism FtoK. rewrite <-Ha.
      eapply Monoid.is_homomorphism_phi_proper; assumption.
    Qed.

    Lemma nonsquare_Kd : forall x, not (Keq (Kmul x x) Kd).
    Proof.
      intros x X. apply (nonsquare_d (KtoF x)).
      Ring.pull_homomorphism KtoF. rewrite X. rewrite <-Hd, HisoF.
      reflexivity.
    Qed.

      (* TODO: character respects isomorphism *)
    Global Instance Kchar_ge_2 :
      @char_ge K Keq Kzero Kone Kopp Kadd Ksub Kmul (BinNat.N.succ_pos BinNat.N.two).
    Proof.
      intros p Hp X; apply (Fchar_ge_3 p Hp).
      eapply Monoid.is_homomorphism_phi_proper in X.
      rewrite (homomorphism_zero(zero:=Fzero)(phi:=KtoF)) in X.
      etransitivity; [|eexact X]; clear X.
      (* TODO: Ring.of_Z of isomorphism *)
    Admitted.
      
    Local Notation Fpoint := (@E.point F Feq Fone Fadd Fmul Fa Fd).
    Local Notation Kpoint := (@E.point K Keq Kone Kadd Kmul Ka Kd).
    Local Notation FzeroP  := (E.zero(nonzero_a:=nonzero_a)(d:=Fd)).
    Local Notation KzeroP  := (E.zero(nonzero_a:=nonzero_Ka)(d:=Kd)).
    Local Notation FaddP   := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).
    Local Notation KaddP   := (E.add(nonzero_a:=nonzero_Ka)(square_a:=square_Ka)(nonsquare_d:=nonsquare_Kd)).

    Obligation Tactic := idtac.
    Program Definition point_phi (P:Fpoint) : Kpoint := exist _ (
      let (x, y) := coordinates P in (FtoK x, FtoK y)) _.
    Next Obligation.
      destruct P as [ [? ?] ?]; cbv.
      rewrite <-!Ha, <-!Hd; pull_homomorphism FtoK.
      eapply Monoid.is_homomorphism_phi_proper; assumption.
    Qed.

    Lemma Proper_point_phi : Proper (eq==>eq) point_phi.
    Proof.
      intros P Q H.
      destruct P as [ [? ?] ?], Q as [ [? ?] ?], H as [Hl Hr]; cbv.
      rewrite !Hl, !Hr. split; reflexivity.
    Qed.

    Lemma lift_ismorphism : @Monoid.is_homomorphism Fpoint eq FaddP
                                                    Kpoint eq KaddP point_phi.
    Proof.
      repeat match goal with
             | |- _ => intro
             | |- Monoid.is_homomorphism => split
             | _ => progress destruct_head' @E.point
             | _ => progress destruct_head' prod
             | _ => progress destruct_head' and
             | |- context[E.add ?P ?Q] =>
               unique pose proof (Pre.denominator_nonzero_x _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q));
                 unique pose proof (Pre.denominator_nonzero_y _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q))
             | _ => progress cbv [eq add point_phi coordinates] in *
             | |- _ /\ _ => split
             | _ => rewrite !(homomorphism_div(phi:=FtoK)) by assumption
             | _ => rewrite !Ha
             | _ => rewrite !Hd
             | _ => Ring.push_homomorphism FtoK
             | |- _ ?x ?x => reflexivity
             | _ => eapply Monoid.is_homomorphism_phi_proper; assumption
             end.
    Qed.
  End Homomorphism.
End E.