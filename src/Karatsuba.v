Require Import Coq.ZArith.ZArith.
Require Import Crypto.Tactics.Algebra_syntax.Nsatz.
Require Import Crypto.Util.ZUtil Crypto.Util.LetIn Crypto.Util.CPSUtil.
Local Open Scope Z_scope.

Section Karatsuba.
  Context {T : Type} (eval : T -> Z)
          (sub_cps : T -> T -> forall {R}, (T->R)->R)
          (sub : T -> T -> T)
          (sub_id : forall x y {R} f, @sub_cps x y R f = f (sub x y)) 
          (eval_sub : forall x y, eval (sub x y) = eval x - eval y)
          (mul_cps : T -> T -> forall {R}, (T->R)->R)
          (mul : T -> T -> T)
          (mul_id : forall x y {R} f, @mul_cps x y R f = f (mul x y)) 
          (eval_mul : forall x y, eval (mul x y) = eval x * eval y)
          (add_cps : T -> T -> forall {R}, (T->R)->R)
          (add : T -> T -> T)
          (add_id : forall x y {R} f, @add_cps x y R f = f (add x y)) 
          (eval_add : forall x y, eval (add x y) = eval x + eval y)
          (scmul_cps : Z -> T -> forall {R}, (T->R)->R)
          (scmul : Z -> T -> T)
          (scmul_id : forall z x {R} f, @scmul_cps z x R f = f (scmul z x))
          (eval_scmul : forall c x, eval (scmul c x) = c * eval x)
          (split_cps : Z -> T -> forall {R}, ((T * T)->R)->R)
          (split : Z -> T -> T * T)
          (split_id : forall s x R f, @split_cps s x R f = f (split s x))
          (eval_split : forall s x, s <> 0 -> eval (fst (split s x)) + s * (eval (snd (split s x))) = eval x)
  .

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
  Definition karatsuba_mul_cps s (x y : T) {R} (f:T->R) :=
    split_cps s x _
      (fun x0_x1 => split_cps s y _
      (fun y0_y1 => mul_cps (fst x0_x1) (fst y0_y1) _
      (fun z0 => mul_cps (snd x0_x1) (snd y0_y1) _
      (fun z2 => add_cps z0 z2 _
      (fun sum_z => add_cps (fst x0_x1) (snd x0_x1) _
      (fun sum_x => add_cps (fst y0_y1) (snd y0_y1) _
      (fun sum_y => mul_cps sum_x sum_y _
      (fun mul_sumxy => sub_cps mul_sumxy sum_z _
      (fun z1 => scmul_cps s z1 _
      (fun sz1 => scmul_cps (s^2) z2 _
      (fun s2z2 => add_cps s2z2 sz1 _
      (fun add_s2z2_sz1 => add_cps add_s2z2_sz1 z0 _ f)))))))))))).

  Definition karatsuba_mul s x y := @karatsuba_mul_cps s x y _ id.
  Lemma karatsuba_mul_id s x y R f :
    @karatsuba_mul_cps s x y R f = f (karatsuba_mul s x y).
  Proof.
    cbv [karatsuba_mul karatsuba_mul_cps].
    repeat progress rewrite ?sub_id, ?mul_id, ?add_id, ?scmul_id, ?split_id.
    reflexivity.
  Qed.

  Lemma eval_karatsuba_mul s x y (s_nonzero:s <> 0) :
    eval (karatsuba_mul s x y) = eval x * eval y.
  Proof.
    cbv [karatsuba_mul karatsuba_mul_cps].
    repeat progress rewrite ?sub_id, ?mul_id, ?add_id, ?scmul_id, ?split_id.
    repeat rewrite push_id.
    repeat progress rewrite ?eval_sub, ?eval_mul, ?eval_add, ?eval_scmul.
    rewrite <-(eval_split s x), <-(eval_split s y) by assumption; ring.
  Qed.

  (*
    If:
        s^2 mod p = (s + 1) mod p
        x = x0 + sx1
        y = y0 + sy1
    Then, with z0 and z2 as before and z1 = ((a + b) * (c + d)) - z0,
        xy = z0 + z2 + sz1
    
    Computing xy one operation at a time:
    sum_z = z0 + z2
    sum_x = x0 + x1
    sum_y = y0 + y1
    mul_sumxy = sum_x * sum_y
    z1 = mul_sumxy - z0
    sz1 = s * z1
    xy = sum_z - sz1
   
  *)
  Definition goldilocks_mul s (xs ys : T) : T :=
    let a_b := split s xs in
    let c_d := split s ys in
    let ac := mul (fst a_b) (fst c_d) in
    (add (add ac (mul (snd a_b) (snd c_d)))
         (scmul s (sub (mul (add (fst a_b) (snd a_b)) (add (fst c_d) (snd c_d))) ac))).

  Local Existing Instances Z.equiv_modulo_Reflexive RelationClasses.eq_Reflexive Z.equiv_modulo_Symmetric Z.equiv_modulo_Transitive Z.mul_mod_Proper Z.add_mod_Proper Z.modulo_equiv_modulo_Proper.

  Lemma goldilocks_mul_correct (p : Z) (p_nonzero : p <> 0) s (s_nonzero : s <> 0) (s2_modp : (s^2) mod p = (s+1) mod p) xs ys :
    (eval (goldilocks_mul s xs ys)) mod p = (eval xs * eval ys) mod p.
  Proof. cbv [goldilocks_mul]; Zmod_to_equiv_modulo.
    repeat rewrite ?eval_mul, ?eval_add, ?eval_sub, ?eval_scmul, <-?(eval_split s xs), <-?(eval_split s ys) by assumption; ring_simplify.
    setoid_rewrite s2_modp.
    apply f_equal2; nsatz. Qed.
End Karatsuba.
