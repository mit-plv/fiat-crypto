Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.Pre.

Require Import Eqdep_dec.
Require Import Tactics.VerdiTactics.
Require Import BinInt Zdiv Znumtheory NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.Classes.Morphisms Setoid.
Require Export Ring_theory Field_theory Field_tac.

Section ModularArithmeticPreliminaries.
  Context {m:Z}.
  Local Coercion ZToFm := ZToField : BinNums.Z -> F m. Hint Unfold ZToFm.

  Theorem F_eq: forall (x y : F m), x = y <-> FieldToZ x = FieldToZ y.
  Proof.
    destruct x, y; intuition; simpl in *; try congruence.
    subst_max.
    f_equal.
    eapply UIP_dec, Z.eq_dec.
  Qed.
  
  Lemma F_opp_spec : forall (a:F m), add a (opp a) = 0.
    intros a.
    pose (@opp_with_spec m) as H.
    change (@opp m) with (proj1_sig H). 
    destruct H; eauto.
  Qed.
  
  Lemma F_pow_spec : forall (a:F m),
      pow a 0%N = 1%F /\ forall x, pow a (1 + x)%N = mul a (pow a x).
  Proof.
    intros a.
    pose (@pow_with_spec m) as H.
    change (@pow m) with (proj1_sig H). 
    destruct H; eauto.
  Qed.
End ModularArithmeticPreliminaries.

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

  Lemma FieldToZ_mul : forall x y : F m,
      FieldToZ (x * y) = ((FieldToZ x * FieldToZ y) mod m)%Z.
  Proof.
    Fdefn.
  Qed.

  Lemma FieldToZ_pow_Zpow_mod : forall (x : F m) n,
    (FieldToZ x ^ Z.of_N n mod m = FieldToZ (x ^ n)%F)%Z.
  Proof.
    intros.
    induction n using N.peano_ind;
      destruct (F_pow_spec x) as [pow_0 pow_succ] . {
      rewrite pow_0.
      rewrite Z.pow_0_r; auto.
    } {
      rewrite N2Z.inj_succ.
      rewrite Z.pow_succ_r by apply N2Z.is_nonneg.
      rewrite <- N.add_1_l.
      rewrite pow_succ.
      rewrite <- Zmult_mod_idemp_r.
      rewrite IHn.
      apply FieldToZ_mul.
    }
  Qed.

  Lemma FieldToZ_pow_efficient : forall (x : F m) n, FieldToZ (x^n) = powmod m (FieldToZ x) n.
  Proof.
    intros.
    rewrite powmod_Zpow_mod.
    rewrite <-FieldToZ_pow_Zpow_mod.
    reflexivity.
  Qed.

  Lemma mod_plus_zero_subproof a b : 0 mod m = (a + b) mod m ->
                                     b mod m =  (- a)  mod m.
  Proof.
    rewrite <-Z.sub_0_l; intros.
    replace (0-a)%Z with (b-(a + b))%Z by omega.
    rewrite Zminus_mod.
    rewrite <- H.
    rewrite Zmod_0_l.
    replace (b mod m - 0)%Z with (b mod m) by omega.
    rewrite Zmod_mod.
    reflexivity.
  Qed.

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
  
  Lemma sub_intersperse_modulus : forall x y, ((x - y) mod m = (x + (m - y)) mod m)%Z.
  Proof.
    intros.
    replace (x + (m - y))%Z with (m+(x-y))%Z by omega.
    rewrite Zplus_mod.
    rewrite Z_mod_same_full; simpl Z.add.
    rewrite Zmod_mod.
    reflexivity.
  Qed.

  (* Compatibility between inject and subtraction *)
  Lemma ZToField_sub : forall (x y : Z),
      @ZToField m (x - y) = ZToField x - ZToField y.
  Proof.
    Fdefn.
    apply sub_intersperse_modulus.
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
  Definition ZToField_FieldToZ := ZToField_idempotent. (* alias *)

  (* Compatibility between inject and mod *)
  Lemma ZToField_mod : forall x, @ZToField m x = ZToField (x mod m).
  Proof.
    Fdefn.
  Qed.
 
  (* Compatibility between inject and pow *)
  Lemma ZToField_pow : forall x n,
    @ZToField m x ^ n = ZToField (x ^ (Z.of_N n) mod m).
  Proof.
    intros.
    induction n using N.peano_ind;
      destruct (F_pow_spec (@ZToField m x)) as [pow_0 pow_succ] . {
      rewrite pow_0.
      Fdefn.
    } {
      rewrite N2Z.inj_succ.
      rewrite Z.pow_succ_r by apply N2Z.is_nonneg.
      rewrite <- N.add_1_l.
      rewrite pow_succ.
      rewrite IHn.
      Fdefn.
    }
  Qed.
End FandZ.

Section RingModuloPre.
  Context {m:Z}.
  Local Coercion ZToFm := ZToField : Z -> F m. Hint Unfold ZToFm.
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

  Lemma F_mul_1_r:
    forall x : F m, x * 1 = x.
  Proof.
    Fdefn; rewrite Z.mul_1_r; auto.
  Qed.
    
  Lemma F_mul_assoc:
    forall x y z : F m, x * (y * z) = x * y * z.
  Proof.
    Fdefn.
  Qed.  

  Lemma F_pow_pow_N (x : F m) : forall (n : N), (x ^ id n)%F = pow_N 1%F mul x n.
  Proof.
    destruct (F_pow_spec x) as [HO HS]; intros.
    destruct n; auto; unfold id.
    rewrite Pre.N_pos_1plus at 1.
    rewrite HS.
    simpl.
    induction p using Pos.peano_ind.
    - simpl. rewrite HO; apply F_mul_1_r.
    - rewrite (@pow_pos_succ (F m) (@mul m) eq _ _ F_mul_assoc x).
      rewrite <-IHp, Pos.pred_N_succ, Pre.N_pos_1plus, HS.
      f_equal.
  Qed.

  (***** Power theory *****)
  Lemma Fpower_theory : power_theory 1%F (@mul m) eq id (@pow m).
  Proof.
    constructor; apply F_pow_pow_N.
  Qed.

  (***** Division Theory *****)
  Definition Fquotrem(a b: F m): F m * F m := 
    let '(q, r) := (Z.quotrem a b) in (q : F m, r : F m).
  Lemma Fdiv_theory : div_theory eq (@add m) (@mul m) (@id _) Fquotrem.
  Proof.
    constructor; intros; unfold Fquotrem, id.

    replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b) by
      try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).

    Fdefn; rewrite <-Z.quot_rem'; trivial.
  Qed.

  Lemma Z_opp_opp : forall x : Z, (-(-x)) = x.
    destruct x; auto.
  Qed.

  Lemma Z_mod_opp : forall x m, (- x) mod m = (- (x mod m)) mod m.
    intros.
    apply Pre.mod_opp_equiv.
    rewrite Z_opp_opp.
    demod; auto.
  Qed.

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
    constructor; intros; try Fdefn; unfold id;
      try (apply gf_eq; simpl; intuition).

    - apply sub_intersperse_modulus.
    - rewrite Zminus_mod, Z_mod_same_full; simpl. apply Z_mod_opp.
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
  
Ltac Fconstant t := match t with @ZToField _ ?x => x | _ => NotConstant end.
Ltac Fexp_tac t := Ncst t.
Ltac Fpreprocess := rewrite <-?ZToField_0, ?ZToField_1.
Ltac Fpostprocess := repeat split;
  repeat match goal with [ |- context[exist ?a ?b (Pre.Z_mod_mod ?x ?q)] ] =>
    change (exist a b (Pre.Z_mod_mod x q)) with (@ZToField q x%Z) end;
  rewrite ?ZToField_0, ?ZToField_1.

Module Type Modulus.
  Parameter modulus : Z.
End Modulus.

(* Example of how to instantiate the ring tactic *)
Module RingModulo (Export M : Modulus).
  Definition ring_theory_modulo := @Fring_theory modulus.
  Definition ring_morph_modulo := @Fring_morph modulus.
  Definition morph_div_theory_modulo := @Fmorph_div_theory modulus.
  Definition power_theory_modulo := @Fpower_theory modulus.
  
  Add Ring GFring_Z : ring_theory_modulo
    (morphism ring_morph_modulo,
     constants [Fconstant],
     div morph_div_theory_modulo,
     power_tac power_theory_modulo [Fexp_tac]). 
End RingModulo.

Section VariousModulo.
  Context {m:Z}.
  
  Add Ring GFring_Z : (@Fring_theory m)
    (morphism (@Fring_morph m),
     constants [Fconstant],
     div (@Fmorph_div_theory m),
     power_tac (@Fpower_theory m) [Fexp_tac]). 

  Lemma F_mul_0_l : forall x : F m, 0 * x = 0.
  Proof.
    intros; ring.
  Qed.
  
  Lemma F_mul_0_r : forall x : F m, x * 0 = 0.
  Proof.
    intros; ring.
  Qed.
  
  Lemma F_mul_nonzero_l : forall a b : F m, a*b <> 0 -> a <> 0.
    intros; intuition; subst.
    assert (0 * b = 0) by ring; intuition.
  Qed.
  
  Lemma F_mul_nonzero_r : forall a b : F m, a*b <> 0 -> b <> 0.
    intros; intuition; subst.
    assert (a * 0 = 0) by ring; intuition.
  Qed.
  
  Lemma F_pow_distr_mul : forall (x y:F m) z, (0 <= z)%N ->
    (x ^ z) * (y ^ z) = (x * y) ^ z.
  Proof.
    intros.
    replace z with (Z.to_N (Z.of_N z)) by apply N2Z.id.
    apply natlike_ind with (x := Z.of_N z); simpl; [ ring | | 
      replace 0%Z with (Z.of_N 0%N) by auto; apply N2Z.inj_le; auto].
    intros z' z'_nonneg IHz'.
    rewrite Z2N.inj_succ by auto.
    rewrite <-N.add_1_l.
    rewrite !(proj2 (@F_pow_spec m _) _).
    rewrite <- IHz'.
    ring.
  Qed.
  
  Lemma F_opp_swap : forall x y : F m, opp x = y <-> x = opp y.
  Proof.
    split; intro; subst; ring.
  Qed.

  Lemma F_opp_involutive : forall x : F m, opp (opp x) = x.
  Proof.
    intros; ring.
  Qed.

  Lemma F_add_0_r : forall x : F m, (x + 0)%F = x.
  Proof.
    intros; ring.
  Qed.

  Lemma F_add_0_l : forall x : F m, (0 + x)%F = x.
  Proof.
    intros; ring.
  Qed.
  
  Lemma F_add_reg_r : forall x y z : F m, y + x = z + x -> y = z.
  Proof.
    intros ? ? ? A.
    replace y with (y + x - x) by ring.
    rewrite A; ring.
  Qed.

  Lemma F_add_reg_l : forall x y z : F m, x + y = x + z -> y = z.
  Proof.
    intros ? ? ? A.
    replace y with (x + y - x) by ring.
    rewrite A; ring.
  Qed.

  Lemma F_sub_0_r : forall x : F m, (x - 0)%F = x.
  Proof.
    intros; ring.
  Qed.

  Lemma F_sub_0_l : forall x : F m, (0 - x)%F = opp x.
  Proof.
    intros; ring.
  Qed.

  Lemma F_mul_1_l : forall x : F m, (1 * x)%F = x.
  Proof.
    intros; ring.
  Qed.

  Lemma F_ZToField_m : ZToField m = @ZToField m 0.
  Proof.
    Fdefn.
    rewrite Zmod_0_l.
    apply Z_mod_same_full.
  Qed.

  Lemma F_sub_m_l : forall x : F m, opp x = ZToField m - x.
  Proof.
    rewrite F_ZToField_m.
    symmetry.
    apply F_sub_0_l.
  Qed.

  Lemma opp_ZToField : forall x : Z, opp (ZToField x) = @ZToField m (m - x).
  Proof.
    Fdefn.
  Qed.

  Lemma F_pow_add : forall (x : F m) k j, x ^ j * x ^ k = x ^ (j + k).
  Proof.
    intros.
    destruct (F_pow_spec x) as [exp_zero exp_succ].
    induction j using N.peano_ind.
    + rewrite exp_zero.
      ring_simplify; eauto.
    +
    rewrite N.add_succ_l.
    do 2 rewrite <- N.add_1_l.
    do 2 rewrite exp_succ by apply N.neq_succ_0.
    rewrite <- IHj.
    ring.
  Qed.

  Lemma F_pow_compose : forall (x : F m) k j, (x ^ j) ^ k = x ^ (k * j).
  Proof.
    intros.
    induction k using N.peano_ind; [rewrite Nmult_0_l; ring | ].
    rewrite Nmult_Sn_m.
    rewrite <- F_pow_add.
    rewrite <- IHk.
    rewrite <- N.add_1_l.
    rewrite (proj2 (F_pow_spec _)).
    ring.
  Qed.

  Lemma F_sub_add_swap : forall w x y z : F m, w - x = y - z <-> w + z = y + x.
  Proof.
    split; intro A;
      [ replace w with (w - x + x) by ring
      | replace w with (w + z - z) by ring ]; rewrite A; ring. 
  Qed.

  Definition isSquare (x : F m) := exists sqrt_x, sqrt_x ^ 2 = x.

  Lemma square_Zmod_F : forall (a : F m), isSquare a <->
    (exists b : Z, ((b * b) mod m)%Z = a).
  Proof.
    split; intro A; destruct A as [sqrt_a sqrt_a_id]. {
      exists sqrt_a.
      rewrite <- FieldToZ_mul.
      apply F_eq.
      ring_simplify; auto.
    } {
      exists (ZToField sqrt_a).
      rewrite ZToField_pow.
      replace (Z.of_N 2) with 2%Z by auto.
      rewrite Z.pow_2_r.
      rewrite sqrt_a_id.
      apply ZToField_FieldToZ.
    }
  Qed.

  Lemma FieldToZ_range : forall x : F m, 0 < m -> 0 <= x < m.
  Proof.
    intros.
    rewrite <- mod_FieldToZ.
    apply Z.mod_pos_bound.
    omega.
  Qed.

  Lemma FieldToZ_nonzero_range : forall x : F m, (x <> 0) -> 0 < m ->
    (1 <= x < m)%Z.
  Proof.
    intros.
    pose proof (FieldToZ_range x).
    unfold not in *.
    rewrite F_eq in H.
    replace (FieldToZ 0) with 0%Z in H by auto.
    omega.
  Qed.

End VariousModulo.
