Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Require Import Crypto.Algebra Crypto.Algebra.
Require Import Crypto.Util.Notations Crypto.Util.Decidable Crypto.Util.Tactics.

(* TODO: move *)
Lemma not_exfalso (P:Prop) (H:P->False) : not P. auto with nocore. Qed.

Global Instance Symmetric_not {T:Type} (R:T->T->Prop)
       {SymmetricR:Symmetric R} : Symmetric (fun a b => not (R a b)).
Proof. cbv [Symmetric] in *; repeat intro; eauto. Qed.

Section ReflectiveNsatzSideConditionProver.
  Context {R eq zero one opp add sub mul }
          {ring:@Algebra.ring R eq zero one opp add sub mul}
          {zpzf:@Algebra.is_zero_product_zero_factor R eq zero mul}.
  Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "+" := add.  Local Infix "-" := sub. Local Infix "*" := mul.
  
  Import BinInt BinNat BinPos.
  Axiom ZtoR : Z -> R.
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
  Lemma CtoZ_correct c : ZtoR (CtoZ c) = denote c.
  Proof.
  Admitted.

  Section WithChar.
    Context C (char_gt_C:forall p, Pos.le p C -> ZtoR (Zpos p) <> zero).
    Fixpoint is_nonzero (c:coef) : bool :=
      match c with
      | Coef_opp c => is_nonzero c
      | Coef_mul c1 c2 => andb (is_nonzero c1) (is_nonzero c2)
      | _ =>
        match CtoZ c with
        | Z0 => false
        | Zpos p => Pos.leb p C
        | Zneg p => Pos.leb p C
        end
      end.
    Lemma is_nonzero_correct c (refl:Logic.eq (is_nonzero c) true) : denote c <> zero.
    Proof.
      induction c;
        repeat match goal with
               | _ => progress (unfold is_nonzero in *; fold is_nonzero in *)
               | _ => progress change (denote Coef_one) with one in *
               | _ => progress change (denote (Coef_opp c)) with (opp (denote c)) in *
               | _ => progress change (denote (Coef_mul c1 c2)) with (denote c1 * denote c2) in *
               | _ => rewrite Pos.leb_le in *
               | _ => rewrite <-Pos2Z.opp_pos in *
               | H: Logic.eq match ?x with _ => _ end true |- _ => destruct x eqn:?
               | H: _ |- _ => unique pose proof (C_lt_char _ H)
               | H:_ |- _ => unique pose proof (proj1 (Bool.andb_true_iff _ _) H)
               | H:_/\_|- _ => unique pose proof (proj1 H)
               | H:_/\_|- _ => unique pose proof (proj2 H)
               | H: _ |- _ => unique pose proof (z_nonzero_correct _ H)
               | |- _ * _ <> zero => eapply Ring.nonzero_product_iff_nonzero_factor
               | |- opp _ <> zero => eapply Ring.opp_nonzero_nonzero
               | |- _ => solve [eauto | discriminate]
               end.
      { admit. }
      { rewrite <-CtoZ_correct, Heqz. auto. }
      { rewrite <-CtoZ_correct, Heqz. admit. }
    Admitted.
  End WithChar.
End ReflectiveNsatzSideConditionProver.

Ltac debuglevel := constr:(1%nat).
     
Ltac assert_as_by_debugfail G n tac :=
  (
    assert G as n by tac
  ) || 
    let dbg := debuglevel in
    match dbg with
    | O => idtac
    | _ => idtac "couldn't prove" G
    end.

Ltac solve_debugfail tac :=
  match goal with
    |- ?G => let H := fresh "H" in
             assert_as_by_debugfail G H tac; exact H
  end.

Ltac _reify one opp add mul x :=
  match x with
  | one => constr:(Coef_one)
  | opp ?a =>
    let a := _reify one opp add mul a in
    constr:(Coef_opp a)
  | add ?a ?b =>
    let a := _reify one opp add mul a in
    let b := _reify one opp add mul b in
    constr:(Coef_add a b)
  | mul ?a ?b =>
    let a := _reify one opp add mul a in
    let b := _reify one opp add mul b in
    constr:(Coef_mul a b)
  end.

Ltac solve_nsatz_nonzero :=
  match goal with (* TODO: change this match to a typeclass resolution *)
  |H:forall p:BinPos.positive, BinPos.Pos.le p ?C -> not (?eq (?ZtoR (BinInt.Z.pos p)) ?zero) |- not (?eq ?x ?zero) =>
   let refl_ok' := fresh "refl_ok" in
   pose (is_nonzero_correct(eq:=eq)(zero:=zero)(*TODO:ZtoR*) _ H) as refl_ok';
   let refl_ok := (eval cbv delta [refl_ok'] in refl_ok') in
   clear refl_ok';
   match refl_ok with
     is_nonzero_correct(R:=?R)(one:=?one)(opp:=?opp)(add:=?add)(mul:=?mul)(ring:=?rn)(zpzf:=?zpzf) _ _ =>
     solve_debugfail ltac:(
       let x' := _reify one opp add mul x in
       let x' := constr:(@denote R one opp add mul x') in
       change (not (eq x' zero)); apply refl_ok; vm_decide
     )
   end
  end.

Ltac goal_to_field_equality fld :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  match goal with
  | [ |- eq _ _] => idtac
  | [ |- not (eq ?x ?y) ] => apply not_exfalso; intro; goal_to_field_equality fld
  | _ => exfalso;
         match goal with
         | H: not (eq _ _) |- _ => apply not_exfalso in H; apply H
         | _ => apply (field_is_zero_neq_one(field:=fld))
         end
  end.

Ltac _introduce_inverse fld d d_nz :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let mul := match type of fld with Algebra.field(mul:=?mul) => mul end in
  let one := match type of fld with Algebra.field(one:=?one) => one end in
  let inv := match type of fld with Algebra.field(inv:=?inv) => inv end in
  match goal with [H: eq (mul d _) one |- _ ] => fail 1 | _ => idtac end;
  let d_i := fresh "i" in
  unique pose proof (Field.right_multiplicative_inverse(H:=fld) _ d_nz);
  set (inv d) as d_i in *;
  clearbody d_i.

Ltac inequalities_to_inverses fld :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let zero := match type of fld with Algebra.field(zero:=?zero) => zero end in
  let div := match type of fld with Algebra.field(div:=?div) => div end in
  let sub := match type of fld with Algebra.field(sub:=?sub) => sub end in
  repeat match goal with
         | [H: not (eq _ _) |- _ ] =>
           lazymatch type of H with
           | not (eq ?d zero) => _introduce_inverse fld d H
           | not (eq zero ?d) => _introduce_inverse fld d (symmetry(R:=fun a b => not (eq a b)) H)
           | not (eq ?x ?y) => _introduce_inverse fld (sub x y) (Ring.neq_sub_neq_zero _ _ H)
           end
         end.

Ltac _division_to_inverse_by fld n d tac :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let zero := match type of fld with Algebra.field(zero:=?zero) => zero end in
  let one := match type of fld with Algebra.field(one:=?one) => one end in
  let mul := match type of fld with Algebra.field(mul:=?mul) => mul end in
  let div := match type of fld with Algebra.field(div:=?div) => div end in
  let inv := match type of fld with Algebra.field(inv:=?inv) => inv end in
  let d_nz := fresh "nz" in
  assert_as_by_debugfail constr:(not (eq d zero)) d_nz tac;
  rewrite (field_div_definition(field:=fld) n d) in *;
  lazymatch goal with
  | H: eq (mul ?di d) one |- _ => rewrite <-!(Field.left_inv_unique(H:=fld) _ _ H) in *
  | H: eq (mul d ?di) one |- _ => rewrite <-!(Field.right_inv_unique(H:=fld) _ _ H) in *
  | _ => _introduce_inverse constr:(fld) constr:(d) d_nz
  end;
  clear d_nz.

Ltac _nonzero_tac fld :=
  solve [trivial | goal_to_field_equality fld; nsatz; solve_nsatz_nonzero].

Ltac divisions_to_inverses_step fld :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let zero := match type of fld with Algebra.field(zero:=?zero) => zero end in
  let div := match type of fld with Algebra.field(div:=?div) => div end in
  match goal with
  | [H: context[div ?n ?d] |- _ ] => _division_to_inverse_by fld n d ltac:(_nonzero_tac fld)
  | |- context[div ?n ?d] => _division_to_inverse_by fld n d ltac:(_nonzero_tac fld)
  end.

Ltac divisions_to_inverses fld :=
  repeat divisions_to_inverses_step fld.

Ltac fsatz :=
  let fld := Algebra.guess_field in
  goal_to_field_equality fld;
  inequalities_to_inverses fld;
  divisions_to_inverses fld;
  nsatz; solve_nsatz_nonzero.

Section Edwards.
  Context {F eq zero one opp add sub mul inv div}
          {field:@Algebra.field F eq zero one opp add sub mul inv div}
          {eq_dec:DecidableRel eq}.

  Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero.  Local Notation "1" := one.
  Local Infix "+" := add. Local Infix "*" := mul.
  Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "x ^ 2" := (x*x).

  Context (a:F) (a_nonzero : a<>0) (a_square : exists sqrt_a, sqrt_a^2 = a).
  Context (d:F) (d_nonsquare : forall sqrt_d, sqrt_d^2 <> d).
  Context (char_gt_2:forall p, BinPos.Pos.le p 2 -> ZtoR (BinInt.Zpos p) <> zero).

  Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).
  Lemma onCurve_zero : onCurve 0 1. nsatz. Qed.

  Section Addition.
    Context (x1 y1:F) (P1onCurve: onCurve x1 y1).
    Context (x2 y2:F) (P2onCurve: onCurve x2 y2).
    Lemma denominator_nonzero : (d*x1*x2*y1*y2)^2 <> 1.
    Proof.
      destruct a_square as [sqrt_a], (dec(sqrt_a*x2+y2 = 0)), (dec(sqrt_a*x2-y2 = 0));
        try match goal with [H: ?f (sqrt_a * x2) y2 <> 0 |- _ ]
            => pose proof (d_nonsquare ((f (sqrt_a * x1) (d * x1 * x2 * y1 * y2 * y1))
                                       /(f (sqrt_a * x2) y2     *   x1 * y1        )))
            end; fsatz.
    Qed.

    Lemma denominator_nonzero_x : 1 + d*x1*x2*y1*y2 <> 0.
    Proof. pose proof denominator_nonzero. fsatz. Qed.
    Lemma denominator_nonzero_y : 1 - d*x1*x2*y1*y2 <> 0.
    Proof. pose proof denominator_nonzero. fsatz. Qed.
    Lemma onCurve_add : onCurve ((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2)).
    Proof. pose proof denominator_nonzero. fsatz. Qed.
  End Addition.
End Edwards.