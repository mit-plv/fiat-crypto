Require Import Coq.ZArith.ZArith.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Util.ZUtil Crypto.Util.LetIn Crypto.Util.CPSUtil Crypto.Util.Tactics.
Require Import Crypto.Arithmetic.Core. Import B. Import Positional.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.IdfunWithAlt.
Local Open Scope Z_scope.

Section Karatsuba.
Context (weight : nat -> Z)
        (weight_0 : weight 0%nat = 1%Z)
        (weight_nonzero : forall i, weight i <> 0).
  (* [tuple Z n] is the "half-length" type,
     [tuple Z n2] is the "full-length" type *)
  Context {n n2 : nat} (n_nonzero : n <> 0%nat) (n2_nonzero : n2 <> 0%nat).
  Let T := tuple Z n.
  Let T2 := tuple Z n2.

  (*
     If x = x0 + sx1 and y = y0 + sy1, then xy = s^2 * z2 + s * z1 + s * z0,
     with:

     z2 = x1y1
     z0 = x0y0
     z1 = (x1+x0)(y1+y0) - (z2 + z0)

     Computing z1 one operation at a time:
     sum_z = z0 + z2
     sum_x = x1 + x0
     sum_y = y1 + y0
     mul_sumxy = sum_x * sum_y
     z1 = mul_sumxy - sum_z
  *)
  Definition karatsuba_mul_cps s (x y : T2) {R} (f:T2->R) :=
    split_cps (n:=n2) (m1:=n) (m2:=n) weight s x
      (fun x0_x1 => split_cps weight s y
      (fun y0_y1 => mul_cps weight (fst x0_x1) (fst y0_y1)
      (fun z0 => mul_cps weight(snd x0_x1) (snd y0_y1)
      (fun z2 => add_cps weight z0 z2
      (fun sum_z => add_cps weight (fst x0_x1) (snd x0_x1)
      (fun sum_x => add_cps weight (fst y0_y1) (snd y0_y1)
      (fun sum_y => mul_cps weight sum_x sum_y
      (fun mul_sumxy => unbalanced_sub_cps weight mul_sumxy sum_z
      (fun z1 => scmul_cps weight s z1
      (fun sz1 => scmul_cps weight (s^2) z2
      (fun s2z2 => add_cps weight s2z2 sz1
      (fun add_s2z2_sz1 => add_cps weight add_s2z2_sz1 z0 f)))))))))))).

  Definition karatsuba_mul s x y := @karatsuba_mul_cps s x y _ id.
  Lemma karatsuba_mul_id s x y R f :
    @karatsuba_mul_cps s x y R f = f (karatsuba_mul s x y).
  Proof.
    cbv [karatsuba_mul karatsuba_mul_cps].
    repeat autounfold.
    autorewrite with cancel_pair push_id uncps.
    reflexivity.
  Qed.

  Lemma eval_karatsuba_mul s x y (s_nonzero:s <> 0) :
    eval weight (karatsuba_mul s x y) = eval weight x * eval weight y.
  Proof.
    cbv [karatsuba_mul karatsuba_mul_cps]; repeat autounfold.
    autorewrite with cancel_pair push_id uncps push_basesystem_eval.
    repeat match goal with
           | _ => rewrite <-eval_to_associational
           | |- context [(to_associational ?w ?x)] =>
             rewrite <-(Associational.eval_split
                          s (to_associational w x)) by assumption
           | _ => rewrite <-Associational.eval_split by assumption
           | _ => setoid_rewrite Associational.eval_nil
           end.
    ring_simplify.
    nsatz.
  Qed.

  (* These definitions are intended to make bounds analysis go through
    for karatsuba. Essentially, we provide a version of the code to
    actually run and a version to bounds-check, along with a proof
    that they are exactly equal. This works around cases where the
    bounds proof requires high-level reasoning. *)
  Local Notation id_with_alt_bounds := id_tuple_with_alt.
  Local Notation id_with_alt_bounds_and_proof := id_tuple_with_alt_proof.

  (*
    If:
        s^2 mod p = (s + 1) mod p
        x = x0 + sx1
        y = y0 + sy1
    Then, with z0 and z2 as before (x0y0 and x1y1 respectively), let z1 = ((x0 + x1) * (y0 + y1)) - z0.

    Computing xy one operation at a time:
    sum_z = z0 + z2
    sum_x = x0 + x1
    sum_y = y0 + y1
    mul_sumxy = sum_x * sum_y
    z1 = mul_sumxy - z0
    sz1 = s * z1
    xy = sum_z - sz1

    The subtraction in the computation of z1 presents issues for
    bounds analysis. In particular, just analyzing the upper and lower
    bounds of the values would indicate that it could underflow--we
    know it won't because

    mul_sumxy -z0 = ((x0+x1) * (y0+y1)) - x0y0
                  = (x0y0 + x1y0 + x0y1 + x1y1) - x0y0
                  = x1y0 + x0y1 + x1y1

    Therefore, we use id_with_alt_bounds to indicate that the
    bounds-checker should check the non-subtracting form.

   *)

  Definition goldilocks_mul_cps_for_bounds_checker
             s (xs ys : T2) {R} (f:T2->R) :=
    split_cps (m1:=n) (m2:=n) weight s xs
      (fun x0_x1 => split_cps weight s ys
      (fun y0_y1 => mul_cps weight (fst x0_x1) (snd y0_y1)
      (fun x0_y1 => mul_cps weight (snd x0_x1) (fst y0_y1)
      (fun x1_y0 => mul_cps weight (fst x0_x1) (fst y0_y1)
      (fun z0 => mul_cps weight (snd x0_x1) (snd y0_y1)
      (fun z2 => add_cps weight z0 z2
      (fun sum_z => add_cps weight x0_y1 x1_y0
      (fun z1' => add_cps weight z1' z2
      (fun z1 => scmul_cps weight s z1
      (fun sz1 => add_cps weight sum_z sz1 f)))))))))).

  Definition goldilocks_mul_cps s (xs ys : T2) {R} (f:T2->R) :=
    split_cps (m1:=n) (m2:=n) weight s xs
      (fun x0_x1 => split_cps weight s ys
      (fun y0_y1 => mul_cps weight (fst x0_x1) (fst y0_y1)
      (fun z0 => mul_cps weight (snd x0_x1) (snd y0_y1)
      (fun z2 => add_cps weight z0 z2
      (fun sum_z => add_cps weight (fst x0_x1) (snd x0_x1)
      (fun sum_x => add_cps weight (fst y0_y1) (snd y0_y1)
      (fun sum_y => mul_cps weight sum_x sum_y
      (fun mul_sumxy => unbalanced_sub_cps weight mul_sumxy z0
      (fun z1 => scmul_cps weight s z1
      (fun sz1 => add_cps weight sum_z sz1 f)))))))))).


  Lemma to_list_left_append {A N} t0 (t : tuple A N) :
    to_list (S N) (left_append t0 t) = (to_list N t ++ t0 :: nil)%list.
  Proof.
    induction N;
      repeat match goal with
             | _ => destruct x
             | _ => rewrite (subst_append (left_append t0 t));
                      rewrite (subst_append t); rewrite !to_list_append;
                        rewrite <-!subst_append
             | _ => progress (rewrite ?hd_left_append, ?tl_left_append)
             | _ => rewrite IHN
             | _ => reflexivity
             end.
  Qed.

  Lemma seq_S_snoc len : forall start,
    List.seq start (S len) = (List.seq start len ++ (len + start)%nat :: nil)%list.
  Proof.
    induction len; intros; [reflexivity|].
    transitivity (start :: List.seq (S start) (S len))%list;
      [reflexivity|]. rewrite (IHlen (S start)).
    simpl List.seq; rewrite plus_Snm_nSm.
    apply List.app_comm_cons.
  Qed.

  Require Import Crypto.Util.ListUtil.
  Require Import Coq.Lists.List.
  Lemma repeat_left_append {A N} (a : A) :
    Tuple.repeat a (S N) = left_append a (Tuple.repeat a N).
  Admitted.

  Lemma from_to_associational_id wt N x :
    from_associational wt N (to_associational wt x) = x.
  Proof.
      cbv [from_associational to_associational from_associational_cps to_associational_cps].
      autorewrite with push_id uncps.
    induction N.
    { destruct x. reflexivity. }
    {
      rewrite (subst_left_append x).
      rewrite to_list_left_append.
      rewrite seq_S_snoc, plus_0_r.
      rewrite map_app, map_cons, map_nil.
      rewrite combine_app_samelength by distr_length.
      rewrite combine_cons, combine_nil_r.
      rewrite fold_right_app.
  Admitted.

  Local Infix "**" := Associational.mul (at level 40).

  Local Definition multerm terms :=
    Associational.multerm (fst terms) (snd terms).

  Lemma mul_power_equiv (p q : list limb) :
    Permutation.permutation
      (p ** q)
      (List.map multerm (list_prod p q)).
  Admitted.

  Lemma permutation_from_associational (p q : list limb) :
    Permutation.permutation p q -> forall wt N,
    from_associational wt N p = from_associational wt N q.
  Admitted.

  Lemma prod_append_binary_expansion {A : Type} {B : Set} (f:(A*A)->B)
        (ws xs ys zs : list A) :
    @Permutation.permutation B
      (map f (list_prod (ws ++ xs) (ys ++ zs)))
      (map f ((list_prod ws ys) ++ (list_prod ws zs) ++ (list_prod xs ys) ++ (list_prod xs zs))).
  Admitted.

  Lemma to_from_associational_append wt N p q :
    to_associational wt (from_associational wt N (p ++ q))
    = to_associational wt (from_associational wt N p) ++ to_associational wt (from_associational wt N q).
  Admitted.

  Lemma binary_expansion wt N a b c d :
    let to_from x := to_associational wt (from_associational wt N x) in
    (to_from ((a ++ b) ** (c ++ d)) = to_from (to_from (a ** c) ++ (to_from (to_from (a ** d) ++ (to_from (b ** c))) ++ to_from (b ** d))))%list.
  Proof.
    intro.
    pose proof (prod_append_binary_expansion multerm a b c d).
    pose proof (mul_power_equiv (a ++ b) (c ++ d)).
    let P := fresh "P" in
    remember (fun w z x y H => Permutation.permutation_app_comp _ w z (x ** y) (map multerm (list_prod x y)) H (mul_power_equiv _ _)) as P;
      pose proof (P _ _ b d (P _ _ b c (P _ _ a d (mul_power_equiv a c))));
      subst P.
    rewrite !map_app, !app_assoc_reverse in *.
    let H := fresh "H" in
    match goal with
      HA : Permutation.permutation ?x ?y,
           HB : Permutation.permutation ?z ?x,
                HC : Permutation.permutation ?w ?y |- _ =>
      assert (Permutation.permutation z w) as H by
            eauto using Permutation.permutation_sym, Permutation.permutation_trans;
        clear HA HB HC
    end; apply permutation_from_associational with (wt := wt) (N := N) in H.
    subst to_from. cbv beta.
    f_equal. etransitivity; [eassumption|].
    rewrite !to_from_associational_append.
    rewrite !from_to_associational_id.
    rewrite <-!to_from_associational_append.
    rewrite !from_to_associational_id.
    rewrite !app_assoc_reverse.
    reflexivity.
   Qed.

  Local Notation from := (from_associational weight).
  Local Notation to := (to_associational weight).

  Lemma subtraction_id N p q :
    from N ((p ++ Associational.negate_snd p) ++ q) = from N q.
  Admitted.

  Lemma goldilocks_mul_equiv' x0 x1 y0 y1 :
    let X0 := to (from n x0) in
    let X1 := to (from n x1) in
    let Y0 := to (from n y0) in
    let Y1 := to (from n y1) in
    from n2
         (to (from n2 (to (from n2 (X0 ** Y1)) ++ to (from n2 (X1 ** Y0)))) ++ to (from n2 (X1 ** Y1))) =
    from n2
         (to (from n2 (to (from n (X0 ++ X1)) ** to (from n (Y0 ++ Y1)))) ++ Associational.negate_snd (to (from n2 (X0 ** Y0)))).
  Proof.
    intros.
    repeat match goal with
           | _ => progress
                    (rewrite !to_from_associational_append,
                     !from_to_associational_id)
           | _ => progress
                    (rewrite <-!to_from_associational_append,
                     !from_to_associational_id)
           | _ => rewrite app_assoc_reverse
           | _ => rewrite binary_expansion
           | _ => subst X0 X1 Y0 Y1
           end.
    match goal with
    | |- _ = from ?n (?a ++ ?b ++ ?c ++ ?d ++ Associational.negate_snd ?a) =>
      transitivity (from n ((a ++ Associational.negate_snd a) ++ b ++ c ++ d));
        [|remember a as A; remember b as B; remember c as C; remember d as D; remember (Associational.negate_snd A) as negA]

    end.
    Focus 2.
    { rewrite app_assoc_reverse.
      apply permutation_from_associational.
      replace (A ++ B ++ C ++ D ++ negA) with (A ++ (B ++ C ++ D) ++ negA).
      auto using app_assoc, app_assoc_reverse.
      rewrite !app_assoc_reverse; reflexivity. } Unfocus.
    rewrite subtraction_id.
    repeat match goal with
           | _ => progress
                    (rewrite <-!to_from_associational_append,
                     !from_to_associational_id)
           | _ => rewrite app_assoc_reverse
           end.
    reflexivity.
  Qed.

  Lemma goldilocks_mul_equiv s xs ys {R} f:
    @goldilocks_mul_cps s xs ys R f =
    @goldilocks_mul_cps_for_bounds_checker s xs ys R f.
  Proof.
    cbv [goldilocks_mul_cps_for_bounds_checker goldilocks_mul_cps].
    repeat autounfold.
    autorewrite with cancel_pair push_id uncps.
    apply f_equal.
    repeat match goal with
             |- context [Associational.mul ?x ?y] =>
             let m := fresh "m" in
             remember (Associational.mul x y) as m end.
    apply f_equal.
    apply f_equal.
    apply f_equal.
    apply f_equal.
    subst m m0 m1 m2.
    apply f_equal2; try reflexivity.
    apply f_equal.
    symmetry.
    apply goldilocks_mul_equiv'.
  Qed.

  Definition goldilocks_mul s xs ys :=
    id_with_alt_bounds_and_proof
      (pf := goldilocks_mul_equiv _ _ _ _)
      (@goldilocks_mul_cps s xs ys _ id)
      (@goldilocks_mul_cps_for_bounds_checker s xs ys _ id).
  Lemma goldilocks_mul_id s xs ys {R} f :
    @goldilocks_mul_cps s xs ys R f = f (goldilocks_mul s xs ys).
  Proof.
    cbv [goldilocks_mul goldilocks_mul_cps]; rewrite !unfold_id_tuple_with_alt_proof.
    repeat autounfold.
    autorewrite with cancel_pair push_id uncps.
    reflexivity.
  Qed.

  Local Existing Instances Z.equiv_modulo_Reflexive
        RelationClasses.eq_Reflexive Z.equiv_modulo_Symmetric
        Z.equiv_modulo_Transitive Z.mul_mod_Proper Z.add_mod_Proper
        Z.modulo_equiv_modulo_Proper.

  Lemma goldilocks_mul_correct (p : Z) (p_nonzero : p <> 0) s (s_nonzero : s <> 0) (s2_modp : (s^2) mod p = (s+1) mod p) xs ys :
    (eval weight (goldilocks_mul s xs ys)) mod p = (eval weight xs * eval weight ys) mod p.
  Proof.
    cbv [goldilocks_mul goldilocks_mul_cps]; rewrite !unfold_id_tuple_with_alt_proof.
    Zmod_to_equiv_modulo.
    repeat autounfold; autorewrite with push_id cancel_pair uncps push_basesystem_eval.
    repeat match goal with
           | _ => rewrite <-eval_to_associational
           | |- context [(to_associational ?w ?x)] =>
             rewrite <-(Associational.eval_split
                          s (to_associational w x)) by assumption
           | _ => rewrite <-Associational.eval_split by assumption
           | _ => setoid_rewrite Associational.eval_nil
           end.

    ring_simplify.
    setoid_rewrite s2_modp.
    apply f_equal2; nsatz.
  Qed.
End Karatsuba.
