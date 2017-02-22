Require Import Crypto.Util.Tactics Crypto.Util.Relations.
Require Import Crypto.Util.Factorize.
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
        Set Printing All.
        induction c; simpl CtoZ; simpl denote;
          repeat (rewrite_hyp ?* || Ring.push_homomorphism constr:(of_Z)); reflexivity.
      Qed.

      (* TODO: move *)
      Lemma nonzero_of_Z_abs z : of_Z (Z.abs z) <> zero <-> of_Z z <> zero.
      Proof.
        destruct z; simpl Z.abs; [reflexivity..|].
        simpl of_Z. setoid_rewrite opp_zero_iff. reflexivity.
      Qed.

      Section WithChar.
        Context C (char_ge_C:@Ring.char_ge R eq zero one opp add sub mul C) (HC: Pos.lt xH C).
        
        Definition is_factor_nonzero (n:N) : bool :=
          match n with N0 => false | N.pos p => BinPos.Pos.ltb p C end.
        Lemma is_factor_nonzero_correct (n:N) (refl:Logic.eq (is_factor_nonzero n) true)
          : of_Z (Z.of_N n) <> zero.
        Proof.
          destruct n; [discriminate|]; rewrite Znat.positive_N_Z; apply char_ge_C, Pos.ltb_lt, refl.
        Qed.

        Lemma RZN_product_nonzero l (H : forall x : N, List.In x l -> of_Z (Z.of_N x) <> zero)
          : of_Z (Z.of_N (List.fold_right N.mul 1%N l)) <> zero.
        Proof.
          rewrite <-List.Forall_forall in H; induction H; simpl List.fold_right.
          { eapply char_ge_C; assumption. }
          { rewrite Znat.N2Z.inj_mul; Ring.push_homomorphism constr:(of_Z).
            eapply Ring.nonzero_product_iff_nonzero_factor; eauto. }
        Qed.
          
        Definition is_constant_nonzero (z:Z) : bool :=
          match factorize_or_fail (Z.abs_N z) with
          | Some factors => List.forallb is_factor_nonzero factors
          | None => false
          end.
        Lemma is_constant_nonzero_correct z (refl:Logic.eq (is_constant_nonzero z) true)
          : of_Z z <> zero.
        Proof.
            rewrite <-nonzero_of_Z_abs, <-Znat.N2Z.inj_abs_N.
            repeat match goal with
                   | _ => progress cbv [is_constant_nonzero] in *
                   | _ => progress break_match_hyps; try congruence; []
                   | _ => progress rewrite ?List.forallb_forall in *
                   |H:_|-_ => apply product_factorize_or_fail in H; rewrite <- H in *
                   | _ => solve [eauto using RZN_product_nonzero, is_factor_nonzero_correct]
                   end.
        Qed.

        Fixpoint is_nonzero (c:coef) : bool :=
          match c with
          | Coef_one => true
          | Coef_opp c => is_nonzero c
          | Coef_mul c1 c2 => andb (is_nonzero c1) (is_nonzero c2)
          | _ => is_constant_nonzero (CtoZ c)
          end.
        Lemma is_nonzero_correct' c (refl:Logic.eq (is_nonzero c) true) : denote c <> zero.
        Proof.
          induction c;
            repeat match goal with
                   | H:_|-_ => progress rewrite Bool.andb_true_iff in H; destruct H
                   | H:_|-_ => progress apply is_constant_nonzero_correct in H
                   | _ => progress (unfold is_nonzero in *; fold is_nonzero in * )
                   | _ => progress (change (denote (Coef_one)) with (of_Z 1) in * )
                   | _ => progress (change (denote (Coef_opp c)) with (opp (denote c)) in * )
                   | _ => progress (change (denote (Coef_mul c1 c2)) with (denote c1 * denote c2) in * )
                   | |- opp _ <> zero => setoid_rewrite Ring.opp_zero_iff
                   | |- _ * _ <> zero => eapply Ring.nonzero_product_iff_nonzero_factor
                   | _ => solve [eauto using is_constant_nonzero_correct, Pos.le_1_l]
                   | _ => progress rewrite <-CtoZ_correct
                   end.
        Qed.
      End WithChar.

      Lemma is_nonzero_correct
            C
            (char_ge_C:@Ring.char_ge R eq zero one opp add sub mul C)
            c (refl:Logic.eq (andb (Pos.ltb xH C) (is_nonzero C c)) true)
        : denote c <> zero.
      Proof.
        rewrite Bool.andb_true_iff in refl; destruct refl.
        eapply @is_nonzero_correct'; try apply Pos.ltb_lt; eauto.
      Qed.

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
    match goal with
    | |- not (?eq ?x _) =>
      let cg := constr:(_:Ring.char_ge (eq:=eq) _) in
      match type of cg with
        @Ring.char_ge ?R eq ?zero ?one ?opp ?add ?sub ?mul ?C =>
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
