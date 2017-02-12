Require Import Crypto.Util.Tactics.
Require Import Crypto.Algebra Crypto.Algebra.Ring.

Module IntegralDomain.
  Section IntegralDomain.
    Context {T eq zero one opp add sub mul} `{@integral_domain T eq zero one opp add sub mul}.

    Lemma nonzero_product_iff_nonzero_factors :
      forall x y : T, ~ eq (mul x y) zero <-> ~ eq x zero /\ ~ eq y zero.
    Proof. setoid_rewrite Ring.zero_product_iff_zero_factor; intuition. Qed.

    Global Instance Integral_domain :
      @Integral_domain.Integral_domain T zero one add mul sub opp eq Ring.Ncring_Ring_ops
                                       Ring.Ncring_Ring Ring.Cring_Cring_commutative_ring.
    Proof. split; cbv; eauto using zero_product_zero_factor, one_neq_zero. Qed.
  End IntegralDomain.

  Module _LargeCharacteristicReflective.
    Section ReflectiveNsatzSideConditionProver.
      Import BinInt BinNat BinPos.
      Lemma N_one_le_pos p : (N.one <= N.pos p)%N. Admitted.
      Context {R eq zero one opp add sub mul}
              {ring:@Algebra.ring R eq zero one opp add sub mul}
              {zpzf:@Algebra.is_zero_product_zero_factor R eq zero mul}.
      Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
      Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
      Local Infix "+" := add.  Local Infix "-" := sub. Local Infix "*" := mul.
      
      Inductive coef :=
      | Coef_one
      | Coef_opp (_:coef)
      | Coef_add (_ _:coef)
      | Coef_mul (_ _:coef).
      Fixpoint denote (c:coef) : R :=
        match c with
        | Coef_one => one
        | Coef_opp c => opp (denote c)
        | Coef_add c1 c2 => add (denote c1) (denote c2)
        | Coef_mul c1 c2 => mul (denote c1) (denote c2)
        end.
      Fixpoint CtoZ (c:coef) : Z :=
        match c with
        | Coef_one => Z.one
        | Coef_opp c => Z.opp (CtoZ c)
        | Coef_add c1 c2 => Z.add (CtoZ c1) (CtoZ c2)
        | Coef_mul c1 c2 => Z.mul (CtoZ c1) (CtoZ c2)
        end.
      Local Notation of_Z := (@Ring.of_Z R zero one opp add).

      Lemma CtoZ_correct c : of_Z (CtoZ c) = denote c.
      Proof.
        induction c; simpl CtoZ; simpl denote;
          repeat (rewrite_hyp ?*; Ring.push_homomorphism constr:(of_Z)); reflexivity.
      Qed.

      Section WithChar.
        Context C (char_gt_C:@Ring.char_gt R eq zero one opp add sub mul C).
        Fixpoint is_nonzero (c:coef) : bool :=
          match c with
          | Coef_opp c => is_nonzero c
          | Coef_mul c1 c2 => andb (is_nonzero c1) (is_nonzero c2)
          | _ =>
            match CtoZ c with
            | Z0 => false
            | Zpos p => N.leb (N.pos p) C
            | Zneg p => N.leb (N.pos p) C
            end
          end.
        Lemma is_nonzero_correct c (refl:Logic.eq (is_nonzero c) true) : denote c <> zero.
        Proof.
          induction c;
            repeat match goal with
                   | _ => progress unfold Algebra.char_gt, Ring.char_gt in *
                   | _ => progress (unfold is_nonzero in *; fold is_nonzero in * )
                   | _ => progress change (denote (Coef_opp c)) with (opp (denote c)) in *
                   | _ => progress change (denote (Coef_mul c1 c2)) with (denote c1 * denote c2) in *
                   | _ => rewrite N.leb_le in *
                   | _ => rewrite <-Pos2Z.opp_pos in *
                   | H:@Logic.eq Z (CtoZ ?x) ?y |- _ => rewrite <-(CtoZ_correct x), H
                   | H: Logic.eq match ?x with _ => _ end true |- _ => destruct x eqn:?
                   | H:_ |- _ => unique pose proof (proj1 (Bool.andb_true_iff _ _) H)
                   | H:_/\_|- _ => unique pose proof (proj1 H)
                   | H:_/\_|- _ => unique pose proof (proj2 H)
                   | H: _ |- _ => unique pose proof (z_nonzero_correct _ H)
                   | |- _ * _ <> zero => eapply Ring.nonzero_product_iff_nonzero_factor
                   | |- opp _ <> zero => eapply Ring.opp_nonzero_nonzero
                   | _ => rewrite <-!Znat.N2Z.inj_pos
                   | |- _ => solve [eauto using N_one_le_pos | discriminate]
                   | _ => progress Ring.push_homomorphism constr:(of_Z)
                   end.
        Qed.
      End WithChar.
    End ReflectiveNsatzSideConditionProver.

    Ltac reify one opp add mul x :=
      match x with
      | one => constr:(Coef_one)
      | opp ?a =>
        let a := reify one opp add mul a in
        constr:(Coef_opp a)
      | add ?a ?b =>
        let a := reify one opp add mul a in
        let b := reify one opp add mul b in
        constr:(Coef_add a b)
      | mul ?a ?b =>
        let a := reify one opp add mul a in
        let b := reify one opp add mul b in
        constr:(Coef_mul a b)
      end.
  End _LargeCharacteristicReflective.

  Ltac solve_constant_nonzero :=
    match goal with (* TODO: change this match to a typeclass resolution *)
    | |- not (?eq ?x _) =>
      let cg := constr:(_:Ring.char_gt (eq:=eq) _) in
      match type of cg with
        @Ring.char_gt ?R eq ?zero ?one ?opp ?add ?sub ?mul ?C =>
        let x' := _LargeCharacteristicReflective.reify one opp add mul x in
        let x' := constr:(@_LargeCharacteristicReflective.denote R one opp add mul x') in
        change (not (eq x' zero));
        apply (_LargeCharacteristicReflective.is_nonzero_correct(eq:=eq)(zero:=zero) C cg);
        abstract (vm_cast_no_check (eq_refl true))
      end
    end.
End IntegralDomain.

(** Tactics for polynomial equations over integral domains *)

Require Coq.nsatz.Nsatz.

Ltac dropAlgebraSyntax :=
  cbv beta delta [
      Algebra_syntax.zero
        Algebra_syntax.one
        Algebra_syntax.addition
        Algebra_syntax.multiplication
        Algebra_syntax.subtraction
        Algebra_syntax.opposite
        Algebra_syntax.equality
        Algebra_syntax.bracket
        Algebra_syntax.power
        ] in *.

Ltac dropRingSyntax :=
  dropAlgebraSyntax;
  cbv beta delta [
      Ncring.zero_notation
        Ncring.one_notation
        Ncring.add_notation
        Ncring.mul_notation
        Ncring.sub_notation
        Ncring.opp_notation
        Ncring.eq_notation
    ] in *.
Ltac nsatz := Algebra_syntax.Nsatz.nsatz; dropRingSyntax.
