Require Import Spec.ModularArithmetic.

Require Import Eqdep_dec.
Require Import Tactics.VerdiTactics.
Require Import BinInt Zdiv Znumtheory NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.Classes.Morphisms Setoid.
Require Export Ring_theory Field_theory Field_tac.

Theorem F_eq: forall {m} (x y : F m), x = y <-> FieldToZ x = FieldToZ y.
Proof.
  destruct x, y; intuition; simpl in *; try congruence.
  subst_max.
  f_equal.
  eapply UIP_dec, Z.eq_dec.
Qed.

(* Fails iff the input term does some arithmetic with mod'd values. *)
Ltac notFancy E :=
match E with
| - (_ mod _) => idtac
| context[_ mod _] => fail 1
| _ => idtac
end.

Lemma Zplus_neg : forall n m, n + -m = n - m.
Proof.
  auto.
Qed.

Lemma Zmod_eq : forall a b n, a = b -> a mod n = b mod n.
Proof.
  intros; rewrite H; trivial.
Qed.

(* Remove redundant [mod] operations from the conclusion. *)
Ltac demod :=
  repeat match goal with
         | [ |- context[(?x mod _ + _) mod _] ] =>
           notFancy x; rewrite (Zplus_mod_idemp_l x)
         | [ |- context[(_ + ?y mod _) mod _] ] =>
           notFancy y; rewrite (Zplus_mod_idemp_r y)
         | [ |- context[(?x mod _ - _) mod _] ] =>
           notFancy x; rewrite (Zminus_mod_idemp_l x)
         | [ |- context[(_ - ?y mod _) mod _] ] =>
           notFancy y; rewrite (Zminus_mod_idemp_r _ y)
         | [ |- context[(?x mod _ * _) mod _] ] =>
           notFancy x; rewrite (Zmult_mod_idemp_l x)
         | [ |- context[(_ * (?y mod _)) mod _] ] =>
           notFancy y; rewrite (Zmult_mod_idemp_r y)
         | [ |- context[(?x mod _) mod _] ] =>
           notFancy x; rewrite (Zmod_mod x)
         | _ => rewrite Zplus_neg in * || rewrite Z.sub_diag in *
         end.

(* Remove exists under equals: we do this a lot *)
Ltac eq_remove_proofs := lazymatch goal with
| [ |- @eq (F _) ?a ?b ] =>
    assert (Q := F_eq a b);
    simpl in *; apply Q; clear Q
end.
            
Ltac Fdefn :=
  intros;
  unfold unfoldFm;
  rewrite ?F_opp_spec;
  repeat match goal with [ x : F _ |- _ ] => destruct x end;
  try eq_remove_proofs;
  demod;
  rewrite ?Z.mul_1_l;
  intuition; demod; try solve [ f_equal; intuition ].

Local Open Scope F_scope.

Section FEquality.
  Context {m:Z}.

  (** Equality **)
  Definition F_eqb (x y : F m) : bool :=  Z.eqb x y.

  Lemma F_eqb_eq x y : F_eqb x y = true -> x = y.
  Proof.
    unfold F_eqb; Fdefn; apply Z.eqb_eq; trivial.
  Qed.

  Lemma F_eqb_complete : forall x y: F m, x = y -> F_eqb x y = true.
  Proof.
    intros; subst; apply Z.eqb_refl.
  Qed.

  Lemma F_eqb_refl : forall x, F_eqb x x = true.
  Proof.
    intros; apply F_eqb_complete; trivial.
  Qed.

  Lemma F_eqb_neq x y : F_eqb x y = false -> x <> y.
  Proof.
    intuition; subst y.
    pose proof (F_eqb_refl x).
    congruence.
  Qed.

  Lemma F_eqb_neq_complete x y : x <> y -> F_eqb x y = false.
  Proof.
    intros.
    case_eq (F_eqb x y); intros; trivial.
    pose proof (F_eqb_eq x y); intuition.
  Qed.

  Lemma F_eq_dec : forall x y : F m, {x = y} + {x <> y}.
  Proof.
    intros; case_eq (F_eqb x y); [left|right]; auto using F_eqb_eq, F_eqb_neq.
  Qed.

  Lemma if_F_eq_dec_if_F_eqb : forall {T} x y (a b:T), (if F_eq_dec x y then a else b) = (if F_eqb x y then a else b).
  Proof.
    intros; intuition; break_if.
    - rewrite F_eqb_complete; trivial.
    - rewrite F_eqb_neq_complete; trivial.
  Defined.
End FEquality.

Section FandZ.
  Local Set Printing Coercions.
  Context {m:Z}.

  Lemma ZToField_small_nonzero : forall z, (0 < z < m)%Z -> ZToField z <> (0:F m).
  Proof.
    intuition; find_inversion; rewrite ?Z.mod_0_l, ?Z.mod_small in *; intuition.
  Qed.

  Lemma ZToField_0 : @ZToField m 0 = 0.
  Proof.
    Fdefn.
  Qed.

  Lemma FieldToZ_ZToField : forall z, FieldToZ (@ZToField m z) = z mod m.
  Proof.
    Fdefn.
  Qed.

  Lemma mod_FieldToZ : forall x,  (@FieldToZ m x) mod m = FieldToZ x.
  Proof.
    Fdefn.
  Qed.

  (** ZToField distributes over operations **)
  Lemma ZToField_add : forall (x y : Z),
      @ZToField m (x + y) = ZToField x + ZToField y.
  Proof.
    Fdefn.
  Qed.

  Lemma FieldToZ_add : forall x y : F m,
      FieldToZ (x + y) = ((FieldToZ x + FieldToZ y) mod m)%Z.
  Proof.
    Fdefn.
  Qed.

  Lemma mod_plus_zero_subproof a b : 0 mod m = (a + b) mod m ->
                                     b mod m =  (- a)  mod m.
  Admitted.

  Lemma FieldToZ_opp' : forall x, FieldToZ (@opp m x) mod m = -x mod m.
  Proof.
    intros.
    pose proof (FieldToZ_add x (opp x)) as H.
    rewrite F_opp_spec, FieldToZ_ZToField in H.
    auto using mod_plus_zero_subproof.
  Qed.

  Lemma FieldToZ_opp : forall x, FieldToZ (@opp m x) = -x mod m.
  Proof.
    intros.
    pose proof (FieldToZ_opp' x) as H; rewrite mod_FieldToZ in H; trivial.
  Qed.

  (* Compatibility between inject and subtraction *)
  Lemma ZToField_sub : forall (x y : Z),
      @ZToField m (x - y) = ZToField x - ZToField y.
  Proof.
    repeat progress Fdefn.
    rewrite Zplus_mod, FieldToZ_opp', FieldToZ_ZToField.
    demod; reflexivity.
  Qed.

  (* Compatibility between inject and multiplication *)
  Lemma ZToField_mul : forall (x y : Z),
      @ZToField m (x * y) = ZToField x * ZToField y.
  Proof.
    Fdefn.
  Qed.

  (* Compatibility between inject and GFtoZ *)
  Lemma ZToField_idempotent : forall (x : F m), ZToField x = x.
  Proof.
    Fdefn.
  Qed.

  (* Compatibility between inject and mod *)
  Lemma ZToField_mod : forall x, @ZToField m x = ZToField (x mod m).
  Proof.
    Fdefn.
  Qed.
End FandZ.

Section RingModuloPre.
  Context {m:Z}.
  (* Substitution to prove all Compats *)
  Ltac compat := repeat intro; subst; trivial.

  Instance Fplus_compat : Proper (eq==>eq==>eq) (@add m).
  Proof.
    compat.
  Qed.

  Instance Fminus_compat : Proper (eq==>eq==>eq) (@sub m).
  Proof.
    compat.
  Qed.

  Instance Fmult_compat : Proper (eq==>eq==>eq) (@mul m).
  Proof.
    compat.
  Qed.

  Instance Fopp_compat : Proper (eq==>eq) (@opp m).
  Proof.
    compat.
  Qed.

  Instance Finv_compat : Proper (eq==>eq) (@inv m).
  Proof.
    compat.
  Qed.

  Instance Fdiv_compat : Proper (eq==>eq==>eq) (@div m).
  Proof.
    compat.
  Qed.

  (***** Ring Theory *****)
  Definition Fring_theory : ring_theory 0%F 1%F (@add m) (@mul m) (@sub m) (@opp m) eq.
  Proof.
    constructor; Fdefn.
  Qed.

  Lemma pow_pow_N (x : F m) : forall (n : N), (x ^ id n)%F = pow_N 1%F mul x n.
  Proof.
    destruct (F_pow_spec x) as [HO HS].
  Admitted.

  (***** Power theory *****)
  Lemma Fpower_theory : power_theory 1%F (@mul m) eq id (@pow m).
  Proof.
    constructor; apply pow_pow_N.
  Qed.

  (***** Division Theory *****)
  Definition Fquotrem(a b: F m): F m * F m :=
    let '(q, r) := (Z.quotrem a b) in (ZToField q, ZToField r).
  Lemma Fdiv_theory : div_theory eq (@add m) (@mul m) (@id _) Fquotrem.
  Proof.
    constructor; intros; unfold Fquotrem, id.

    replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b) by
      try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).

    Fdefn; rewrite <-Z.quot_rem'; trivial.
  Qed.

  Lemma Z_mod_opp : forall x m, (- x) mod m = (- (x mod m)) mod m.
  Admitted.

  (* Define a "ring morphism" between GF and Z, i.e. an equivalence
   * between 'inject (ZFunction (X))' and 'GFFunction (inject (X))'.
   *
   * Doing this allows us to do our coefficient manipulations in Z
   * rather than GF, because we know it's equivalent to inject the
   * result afterward.
   *)
  Lemma Fring_morph:
      ring_morph 0%F 1%F (@add m) (@mul m) (@sub m) (@opp m) eq
                 0%Z 1%Z Z.add    Z.mul    Z.sub    Z.opp  Z.eqb
                 (@ZToField m).
  Proof.
    constructor; intros; try Fdefn; unfold id, unfoldFm;
      try (apply gf_eq; simpl; intuition).

    - rewrite FieldToZ_opp, FieldToZ_ZToField; demod; trivial.
    - rewrite FieldToZ_opp, FieldToZ_ZToField, Z_mod_opp; trivial.
    - rewrite (proj1 (Z.eqb_eq x y)); trivial.
  Qed.

  (* Redefine our division theory under the ring morphism *)
  Lemma Fmorph_div_theory: 
      div_theory eq Zplus Zmult (@ZToField m) Z.quotrem.
  Proof.
    constructor; intros; intuition.
    replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b);
      try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).

    eq_remove_proofs; demod;
      rewrite <- (Z.quot_rem' a b);
      destruct a; simpl; trivial.
  Qed.

  Lemma ZToField_1 : @ZToField m 1 = 1.
  Proof.
    Fdefn.
  Qed.
End RingModuloPre.

Module Type Modulus.
  Parameter modulus : Z.
End Modulus.

Module RingModulo (Export M : Modulus).
  (* Add our ring with all the fixin's *)
  Definition ring_theory_modulo := @Fring_theory modulus.
  Definition ring_morph_modulo := @Fring_morph modulus.
  Definition morph_div_theory_modulo := @Fmorph_div_theory modulus.
  Definition power_theory_modulo := @Fpower_theory modulus.

  Ltac Fexp_tac t := Ncst t.

  (* Expose the carrier in constants so field can simplify them *)
  Ltac Fpreprocess := rewrite <-?ZToField_0, ?ZToField_1.

  (* Split up the equation (because field likes /\, then
   * change back all of our GFones and GFzeros. *)
  Ltac Fpostprocess :=
    repeat split;
		repeat match goal with [ |- context[exist ?a ?b (Pre.Z_mod_mod ?x ?q)] ] =>
			replace (exist a b (Pre.Z_mod_mod x)) with (@ZToField q x%Z) by reflexivity
		end;
    rewrite ?ZToField_0, ?ZToField_1.

  (* Tactic to passively convert from GF to Z in special circumstances *)
  Ltac Fconstant t :=
    match t with
    | @ZToField _ ?x => x
    | _ => NotConstant
    end.
  
  Add Ring GFring_Z : ring_theory_modulo
    (morphism ring_morph_modulo,
     constants [Fconstant],
     div morph_div_theory_modulo,
     power_tac power_theory_modulo [Fexp_tac]). 
End RingModulo.