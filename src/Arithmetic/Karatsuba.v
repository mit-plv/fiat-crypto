Require Import Coq.ZArith.ZArith.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Util.ZUtil Crypto.Util.LetIn Crypto.Util.CPSUtil.
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

  (*
  Definition goldilocks_mul_cps_for_bounds_checker
             s (xs ys : T2) {R} (f:T2->R) :=
    split_cps (m1:=n) (m2:=n) weight s xs
      (fun x0_x1 => split_cps weight s ys

      (fun z1 => Positional.to_associational_cps weight z1
      (fun z1 => Associational.mul_cps (pair s 1::nil) z1
      (fun sz1 => Positional.from_associational_cps weight n2 sz1
      (fun sz1 => add_cps weight sum_z sz1 f)))))))))))).
   *)

  Let T3 := tuple Z (n2+n).
  Definition goldilocks_mul_cps s (xs ys : T2) {R} (f:T3->R) :=
    split_cps (m1:=n) (m2:=n) weight s xs
      (fun x0_x1 => split_cps weight s ys
      (fun y0_y1 => mul_cps weight (fst x0_x1) (fst y0_y1)
      (fun z0 => mul_cps weight (snd x0_x1) (snd y0_y1)
      (fun z2 => add_cps weight z0 z2
      (fun sum_z : tuple _ n2 => add_cps weight (fst x0_x1) (snd x0_x1)
      (fun sum_x => add_cps weight (fst y0_y1) (snd y0_y1)
      (fun sum_y => mul_cps weight sum_x sum_y
      (fun mul_sumxy =>

      dlet z1 := id_with_alt_bounds (unbalanced_sub_cps weight mul_sumxy z0 id) (

      (mul_cps weight (fst x0_x1) (snd y0_y1)
      (fun x0_y1 => mul_cps weight (snd x0_x1) (fst y0_y1)
      (fun x1_y0 => mul_cps weight (fst x0_x1) (fst y0_y1)
      (fun z0 => mul_cps weight (snd x0_x1) (snd y0_y1)
      (fun z2 => add_cps weight z0 z2
      (fun sum_z => add_cps weight x0_y1 x1_y0
      (fun z1' => add_cps weight z1' z2 id))))))))  in

                 Positional.to_associational_cps weight z1
      (fun z1 => Associational.mul_cps (pair s 1::nil) z1
      (fun sz1 => Positional.to_associational_cps weight sum_z
      (fun sum_z => Positional.from_associational_cps weight _ (sum_z++sz1) f
      ))))))))))).

  Definition goldilocks_mul s xs ys := goldilocks_mul_cps s xs ys id.
  Lemma goldilocks_mul_id s xs ys R f :
    @goldilocks_mul_cps s xs ys R f = f (goldilocks_mul s xs ys).
  Proof.
    cbv [goldilocks_mul goldilocks_mul_cps id_with_alt_bounds Let_In].
    repeat autounfold. autorewrite with uncps push_id.
    reflexivity.
  Qed.
  Hint Opaque goldilocks_mul : uncps.
  Hint Rewrite goldilocks_mul_id : uncps.

  Local Existing Instances Z.equiv_modulo_Reflexive
        RelationClasses.eq_Reflexive Z.equiv_modulo_Symmetric
        Z.equiv_modulo_Transitive Z.mul_mod_Proper Z.add_mod_Proper
        Z.modulo_equiv_modulo_Proper.

  Lemma goldilocks_mul_correct (p : Z) (p_nonzero : p <> 0) s (s_nonzero : s <> 0) (s2_modp : (s^2) mod p = (s+1) mod p) xs ys :
    (eval weight (goldilocks_mul s xs ys)) mod p = (eval weight xs * eval weight ys) mod p.
  Proof.
    cbv [goldilocks_mul_cps goldilocks_mul Let_In].
    Zmod_to_equiv_modulo.
    progress autounfold.
    progress autorewrite with push_id cancel_pair uncps push_basesystem_eval.
    rewrite !unfold_id_tuple_with_alt.
    repeat match goal with
    | _ => rewrite <-eval_to_associational
    | |- context [(to_associational ?w ?x)] =>
      rewrite <-(Associational.eval_split
                   s (to_associational w x)) by assumption
    | _ => rewrite <-Associational.eval_split by assumption
    | _ => setoid_rewrite Associational.eval_nil
    end.
    progress autorewrite with push_id cancel_pair uncps push_basesystem_eval.
    repeat (rewrite ?eval_from_associational, ?eval_to_associational).
    progress autorewrite with push_id cancel_pair uncps push_basesystem_eval.
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
    assumption. assumption. omega.
  Qed.
End Karatsuba.
Hint Opaque goldilocks_mul : uncps.
Hint Rewrite goldilocks_mul_id : uncps.
