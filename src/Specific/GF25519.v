Require Import Galois GaloisTheory Galois.BaseSystem Galois.ModularBaseSystem.
Require Import List Util.ListUtil.
Import ListNotations.
Require Import ZArith.ZArith Zpower ZArith Znumtheory.
Require Import QArith.QArith QArith.Qround.
Require Import VerdiTactics.
Close Scope Q.

Module Base25Point5_10limbs <: BaseCoefs.
  Local Open Scope Z_scope.
  Definition base := map (fun i => two_p (Qceiling (Z_of_nat i *255 # 10))) (seq 0 10).
  Lemma base_positive : forall b, In b base -> b > 0.
  Proof.
    compute; intros; repeat break_or_hyp; intuition.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    reflexivity.
  Qed.

  Lemma base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    intros.
    assert (In i (seq 0 (length base))) by nth_tac.
    assert (In j (seq 0 (length base))) by nth_tac.
    subst b; subst r; simpl in *.
    repeat break_or_hyp; try omega; vm_compute; reflexivity.
  Qed.
End Base25Point5_10limbs.

Module Modulus25519 <: Modulus.
  Local Open Scope Z_scope.
  Definition two_255_19 := two_p 255 - 19.
  Lemma two_255_19_prime : prime two_255_19. Admitted.
  Definition prime25519 := exist _ two_255_19 two_255_19_prime.
  Definition modulus := prime25519.
End Modulus25519.

Module GF25519Base25Point5Params <: PseudoMersenneBaseParams Base25Point5_10limbs Modulus25519.
  Import Base25Point5_10limbs.
  Import Modulus25519.
  Local Open Scope Z_scope.
  (* TODO: do we actually want B and M "up there" in the type parameters? I was
  * imagining writing something like "Paramter Module M : Modulus". *)

  Definition k := 255.
  Definition c := 19.
  Lemma modulus_pseudomersenne :
    primeToZ modulus = 2^k - c.
  Proof.
    reflexivity.
  Qed.

  Lemma base_matches_modulus :
    forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat).
  Proof.
    intros.
    assert (In i (seq 0 (length base))) by nth_tac.
    assert (In j (seq 0 (length base))) by nth_tac.
    subst b; subst r; simpl in *.
    repeat break_or_hyp; try omega; vm_compute; reflexivity.
  Qed.

  Lemma base_succ : forall i, ((S i) < length base)%nat -> 
    let b := nth_default 0 base in
    b (S i) mod b i = 0.
  Proof.
    intros.
    assert (In i (seq 0 (length base))) by nth_tac.
    assert (In (S i) (seq 0 (length base))) by nth_tac.
    subst b; simpl in *.
    repeat break_or_hyp; try omega; vm_compute; reflexivity.
  Qed.

  Lemma base_tail_matches_modulus:
    2^k mod nth_default 0 base (pred (length base)) = 0.
  Proof.
    nth_tac.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    reflexivity.
  Qed.

  Lemma k_nonneg : 0 <= k.
  Proof.
    rewrite Zle_is_le_bool; reflexivity.
  Qed.
End GF25519Base25Point5Params.

Module GF25519Base25Point5 := GFPseudoMersenneBase Base25Point5_10limbs Modulus25519 GF25519Base25Point5Params.

Ltac expand_list f :=
  assert ((length f < 100)%nat) as _ by (simpl length in *; omega);
    repeat progress (
    let n := fresh f in
    destruct f as [ | n ];
    try solve [simpl length in *; try discriminate]).

(* TODO: move to ListUtil *)
Lemma cons_eq_head : forall {T} (x y:T) xs ys, x::xs = y::ys -> x=y.
Proof.
  intros; solve_by_inversion.
Qed.
Lemma cons_eq_tail : forall {T} (x y:T) xs ys, x::xs = y::ys -> xs=ys.
Proof.
  intros; solve_by_inversion.
Qed.

Ltac expand_list_equalities := repeat match goal with
  | [H: (?x::?xs = ?y::?ys) |- _ ] =>
      let eq_head := fresh "Heq" x in
      assert (x = y) as eq_head by (eauto using cons_eq_head);
      assert (xs = ys) by (eauto using cons_eq_tail);
      clear H
  | [H:?x = ?x|-_] => clear H
end.

Section GF25519Base25Point5Formula.
  Local Open Scope Z_scope.
  Import GF25519Base25Point5.
  Import GF.

  Lemma GF25519Base25Point5_mul_reduce_formula :
    forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 
      g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
      {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                        -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                        -> rep ls (f*g)%GF}.
  Proof.
    intros.
    eexists.
    intros f g Hf Hg.

    pose proof (mul_rep _ _  _ _ Hf Hg) as HmulRef.
    remember (GF25519Base25Point5.mul [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9]) as h.
    unfold
      GF25519Base25Point5.mul,
      GF25519Base25Point5.B.add,
      GF25519Base25Point5.E.mul,
      GF25519Base25Point5.E.mul',
      GF25519Base25Point5.E.mul_bi,
      GF25519Base25Point5.E.mul_bi',
      GF25519Base25Point5.E.mul_each,
      GF25519Base25Point5.E.add,
      GF25519Base25Point5.B.digits,
      GF25519Base25Point5.E.digits,
      Base25Point5_10limbs.base,
      GF25519Base25Point5.E.crosscoef,
      nth_default
    in Heqh; simpl in Heqh.

    unfold
      two_power_pos,
      shift_pos
    in Heqh; simpl in Heqh.

    (* evaluate row-column crossing coefficients for variable base multiplication *)
    (* unfoldZ.div in Heqh; simpl in Heqh. *) (* THIS TAKES TOO LONG *)
    repeat rewrite Z_div_same_full in Heqh by (abstract (apply Zeq_bool_neq; reflexivity)).
    repeat match goal with [ Heqh : context[ (?a / ?b)%Z ]  |- _ ] =>
      replace (a / b)%Z with 2%Z in Heqh by
        (abstract (symmetry; erewrite <- Z.div_unique_exact; try apply Zeq_bool_neq; reflexivity))
    end.

    Hint Rewrite
      Z.mul_0_l
      Z.mul_0_r
      Z.mul_1_l
      Z.mul_1_r
      Z.add_0_l
      Z.add_0_r
      : Z_identities.
    autorewrite with Z_identities in Heqh.

    (* inline explicit formulas for modular reduction *)
    cbv beta iota zeta delta [GF25519Base25Point5.reduce Base25Point5_10limbs.base] in Heqh.
    remember GF25519Base25Point5Params.c as c in Heqh; unfold GF25519Base25Point5Params.c in Heqc.
    simpl in Heqh.

    (* prettify resulting modular multiplication expression *)
    repeat rewrite (Z.mul_add_distr_l c) in Heqh.
    repeat rewrite (Z.mul_assoc _ _ 2) in Heqh.
    repeat rewrite (Z.mul_comm _ 2) in Heqh.
    repeat rewrite (Z.mul_assoc 2 c) in Heqh.
    remember (2 * c)%Z as TwoC in Heqh; subst c; simpl in HeqTwoC; subst TwoC. (* perform operations on constants *)
    repeat rewrite Z.add_assoc in Heqh.
    repeat rewrite Z.mul_assoc in Heqh.
    assert (Hhl: length h = 10%nat) by (subst h; reflexivity); expand_list h; clear Hhl.
    expand_list_equalities.
    (* pretty-print: sh -c "tr -d '\n' | tr 'Z' '\n' | tr -d \% | sed 's:\s\s*\*\s\s*:\*:g' | column -o' ' -t" *)
    (* output:
      h0 = (f0*g0 + 38*f9*g1 + 19*f8*g2 + 38*f7*g3 + 19*f6*g4 + 38*f5*g5 + 19*f4*g6 + 38*f3*g7 + 19*f2*g8 + 38*f1*g9)
      h1 = (f1*g0 + f0*g1    + 19*f9*g2 + 19*f8*g3 + 19*f7*g4 + 19*f6*g5 + 19*f5*g6 + 19*f4*g7 + 19*f3*g8 + 19*f2*g9)
      h2 = (f2*g0 + 2*f1*g1  + f0*g2    + 38*f9*g3 + 19*f8*g4 + 38*f7*g5 + 19*f6*g6 + 38*f5*g7 + 19*f4*g8 + 38*f3*g9)
      h3 = (f3*g0 + f2*g1    + f1*g2    + f0*g3    + 19*f9*g4 + 19*f8*g5 + 19*f7*g6 + 19*f6*g7 + 19*f5*g8 + 19*f4*g9)
      h4 = (f4*g0 + 2*f3*g1  + f2*g2    + 2*f1*g3  + f0*g4    + 38*f9*g5 + 19*f8*g6 + 38*f7*g7 + 19*f6*g8 + 38*f5*g9)
      h5 = (f5*g0 + f4*g1    + f3*g2    + f2*g3    + f1*g4    + f0*g5    + 19*f9*g6 + 19*f8*g7 + 19*f7*g8 + 19*f6*g9)
      h6 = (f6*g0 + 2*f5*g1  + f4*g2    + 2*f3*g3  + f2*g4    + 2*f1*g5  + f0*g6    + 38*f9*g7 + 19*f8*g8 + 38*f7*g9)
      h7 = (f7*g0 + f6*g1    + f5*g2    + f4*g3    + f3*g4    + f2*g5    + f1*g6    + f0*g7    + 19*f9*g8 + 19*f8*g9)
      h8 = (f8*g0 + 2*f7*g1  + f6*g2    + 2*f5*g3  + f4*g4    + 2*f3*g5  + f2*g6    + 2*f1*g7  + f0*g8    + 38*f9*g9)
      h9 = (f9*g0 + f8*g1    + f7*g2    + f6*g3    + f5*g4    + f4*g5    + f3*g6    + f2*g7    + f1*g8    + f0*g9)
    *)
    
    (* prove equivalence of multiplication to the stated *)
    assert (rep [h0; h1; h2; h3; h4; h5; h6; h7; h8; h9] (f * g)%GF) as Hh. {
      subst h0. subst h1. subst h2. subst h3. subst h4. subst h5. subst h6. subst h7. subst h8. subst h9.
      repeat match goal with [H: _ = _ |- _ ] =>
          rewrite <- H; clear H
      end.
      assumption.
    }

    (* --- carry phase --- *)
    remember (rev [0;1;2;3;4;5;6;7;8;9;0])%nat as is; simpl in Heqis.
    destruct (fun pf pf2 => carry_sequence_rep is _ _ pf pf2 Hh). {
      subst is. clear. intros. simpl in *. firstorder.
    } {
      reflexivity.
    }
    remember (carry_sequence is [h0; h1; h2; h3; h4; h5; h6; h7; h8; h9]) as r; subst is.

    (* unroll the carry loop, create a separate variable for each of the 10 list elements *)
    cbv [GF25519Base25Point5.carry_sequence fold_right rev app] in Heqr.
    repeat match goal with
    | [H1: ?a = ?b, H2: ?b = ?c |- _ ] => subst a
    | [H: context[GF25519Base25Point5.carry ?i (?x::?xs)] |- _ ] =>
        let cr := fresh "cr" in
        remember (GF25519Base25Point5.carry i (x::xs)) as cr;
        match goal with [ Heq : cr = ?crdef |- _ ] =>
            cbv [GF25519Base25Point5.carry GF25519Base25Point5.carry_simple GF25519Base25Point5.carry_and_reduce] in Heq;
            simpl eq_nat_dec in Heq; cbv iota beta in Heq;
            cbv [set_nth nth_default nth_error value GF25519Base25Point5.add_to_nth] in Heq;
            let Heql := fresh "Heql" in
              assert (length cr = length crdef) as Heql by (subst cr; reflexivity);
              simpl length in Heql; expand_list cr; clear Heql;
            expand_list_equalities
        end
    end.

    (* compute the human-meaningful froms of constants used during carrying *)
    cbv [GF25519Base25Point5.cap Base25Point5_10limbs.base GF25519Base25Point5Params.k] in *.
    simpl eq_nat_dec in *; cbv iota in *.
    repeat match goal with
    | [H: _ |- _ ] =>
      rewrite (map_nth_default _ _ _ _ 0%nat 0%Z) in H by (abstract (clear; rewrite seq_length; firstorder))
    end.
    simpl two_p in *.
    repeat rewrite two_power_pos_equiv in *.
    repeat rewrite <- Z.pow_sub_r in * by (abstract (clear; firstorder)).
    simpl Z.sub in *;
    rewrite Zdiv_1_r in *.

    (* replace division and Z.modulo with bit operations *)
    remember (2 ^ 25)%Z as t25 in *.
    remember (2 ^ 26)%Z as t26 in *.
    repeat match goal with [H1: ?a = ?b, H2: ?b = ?c |- _ ] => subst a end.
    subst t25. subst t26.
    rewrite <- Z.land_ones in * by (abstract (clear; firstorder)).
    rewrite <- Z.shiftr_div_pow2 in * by (abstract (clear; firstorder)).

    (* evaluate the constant arguments to bit operations *)
    remember (Z.ones 25) as m25 in *. compute in Heqm25. subst m25.
    remember (Z.ones 26) as m26 in *. compute in Heqm26. subst m26.
    unfold GF25519Base25Point5Params.c in *.

    (* This tactic takes in [r], a variable that we want to use to instantiate an existential.
     * We find one other variable mentioned in [r], with its own equality in the hypotheses.
     * That equality is then switched into a [let] in [r]'s defining equation. *)
    Ltac letify r :=
      match goal with
      | [ H : ?x = ?e |- _ ] =>
        is_var x;
        match goal with
        | [ H' : r = _ |- _ ] =>
          pattern x in H';
            match type of H' with
            | (fun z => r = @?e' z) x =>
              let H'' := fresh "H" in assert (H'' : r = let x := e in e' x) by congruence;
                clear H'; subst x; rename H'' into H'; cbv beta in H'
            end
        end
      end.

    (* To instantiate an existential, give a variable with a defining equation to this tactic.
     * We instantiate with a [let]-ified version of that equation. *)
    Ltac existsFromEquations r := repeat letify r;
                                 match goal with
                                 | [ _ : r = ?e |- context[?u] ] => unify u e
                                 end.

    clear HmulRef Hh Hf Hg.
    existsFromEquations r.
    split; auto; congruence.

    (* Here's the tactic code I added at this point at the end of the old version.
     * Erase after reading, since it isn't needed anymore.

    replace ([r0; r1; r2; r3; r4; r5; r6; r7; r8; r9]) with r; unfold rep; auto.

    subst r.

    Ltac rsubstBoth := repeat (match goal with [ |- ?a = ?b] => subst a; subst b; repeat progress f_equal || reflexivity end).
    Ltac t := f_equal; abstract rsubstBoth || (try t).

    Time t.
    

    (* But there's a nicer way! *)
    Undo 2.

    (* This tactic finds an [x := e] hypothesis and adds a matching [x = e] hypothesis. *)
    Ltac letToEquality :=
      match goal with
      | [ x := ?e |- _ ] =>
        match goal with
        | [ _ : x = e |- _ ] => fail 1 (* To avoid infinite loop, make sure we didn't already do this one! *)
        | _ => assert (x = e) by reflexivity
        end
      end.

    (* Repeated introduction of those equalities enables [congruence] to solve the goal. *)
    Ltac smarter_congruence := repeat letToEquality; congruence.

    Time smarter_congruence.*)
  Defined.
End GF25519Base25Point5Formula.

Extraction "/tmp/test.ml" GF25519Base25Point5_mul_reduce_formula.
(* It's easy enough to use extraction to get the proper nice-looking formula.
 * More Ltac acrobatics will be needed to get out that formula for further use in Coq.
 * The easiest fix will be to make the proof script above fully automated,
 * using [abstract] to contain the proof part. *)
