Require Import Coq.ZArith.ZArith.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Util.ZUtil Crypto.Util.LetIn Crypto.Util.CPSUtil.
Local Open Scope Z_scope.

Section Karatsuba.
  (* T is the "half-length" type, T2 is the "full-length" type *)
  Context {T T2 : Type} (eval : T -> Z) (eval2 : T2 -> Z).

  (* multiplication takes half-length inputs to full-length output *)
  Context {mul_cps : T -> T -> forall {R}, (T2->R)->R}
          {mul : T -> T -> T2}
          {mul_id : forall x y {R} f, @mul_cps x y R f = f (mul x y)}
          {eval_mul : forall x y, eval2 (mul x y) = eval x * eval y}.

  (* splitting takes full-length input to half-length outputs *)
  Context {split_cps : Z -> T2 -> forall {R}, ((T * T)->R)->R}
          {split : Z -> T2 -> T * T}
          {split_id : forall s x R f, @split_cps s x R f = f (split s x)}
          {eval_split : forall s x, s <> 0 -> eval (fst (split s x)) + s * (eval (snd (split s x))) = eval2 x}.

  (* half-length add *)
  Context {add_cps : T -> T -> forall {R}, (T->R)->R}
          {add : T -> T -> T}
          {add_id : forall x y {R} f, @add_cps x y R f = f (add x y)}
          {eval_add : forall x y, eval (add x y) = eval x + eval y}.

  (* full-length operations: sub, add, scmul *)
  Context {sub2_cps : T2 -> T2 -> forall {R}, (T2->R)->R}
          {sub2 : T2 -> T2 -> T2}
          {sub2_id : forall x y {R} f, @sub2_cps x y R f = f (sub2 x y)} 
          {eval_sub2 : forall x y, eval2 (sub2 x y) = eval2 x - eval2 y}
          {add2_cps : T2 -> T2 -> forall {R}, (T2->R)->R}
          {add2 : T2 -> T2 -> T2}
          {add2_id : forall x y {R} f, @add2_cps x y R f = f (add2 x y)} 
          {eval_add2 : forall x y, eval2 (add2 x y) = eval2 x + eval2 y}
          {scmul2_cps : Z -> T2 -> forall {R}, (T2->R)->R}
          {scmul2 : Z -> T2 -> T2}
          {scmul2_id : forall z x {R} f, @scmul2_cps z x R f = f (scmul2 z x)}
          {eval_scmul2 : forall c x, eval2 (scmul2 c x) = c * eval2 x}.

  Local Ltac rewrite_id :=
    repeat progress rewrite ?mul_id, ?split_id, ?add_id, ?sub2_id, ?add2_id, ?scmul2_id.
  Local Ltac rewrite_eval :=
    repeat progress rewrite ?eval_mul, ?eval_split, ?eval_add, ?eval_sub2, ?eval_add2, ?eval_scmul2.

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
    split_cps s x _
      (fun x0_x1 => split_cps s y _
      (fun y0_y1 => mul_cps (fst x0_x1) (fst y0_y1) _
      (fun z0 => mul_cps (snd x0_x1) (snd y0_y1) _
      (fun z2 => add2_cps z0 z2 _
      (fun sum_z => add_cps (fst x0_x1) (snd x0_x1) _
      (fun sum_x => add_cps (fst y0_y1) (snd y0_y1) _
      (fun sum_y => mul_cps sum_x sum_y _
      (fun mul_sumxy => sub2_cps mul_sumxy sum_z _
      (fun z1 => scmul2_cps s z1 _
      (fun sz1 => scmul2_cps (s^2) z2 _
      (fun s2z2 => add2_cps s2z2 sz1 _
      (fun add_s2z2_sz1 => add2_cps add_s2z2_sz1 z0 _ f)))))))))))).

  Definition karatsuba_mul s x y := @karatsuba_mul_cps s x y _ id.
  Lemma karatsuba_mul_id s x y R f :
    @karatsuba_mul_cps s x y R f = f (karatsuba_mul s x y).
  Proof.
    cbv [karatsuba_mul karatsuba_mul_cps]. rewrite_id.
    reflexivity.
  Qed.

  Lemma eval_karatsuba_mul s x y (s_nonzero:s <> 0) :
    eval2 (karatsuba_mul s x y) = eval2 x * eval2 y.
  Proof.
    cbv [karatsuba_mul karatsuba_mul_cps]. rewrite_id.
    repeat rewrite push_id. rewrite_eval.
    rewrite <-(eval_split s x), <-(eval_split s y) by assumption; ring.
  Qed.

  (*
    If:
        s^2 mod p = (s + 1) mod p
        x = x0 + sx1
        y = y0 + sy1
    Then, with z0 and z2 as before and z1 = ((a + b) * (c + d)) - z0,
        xy mod p = (z0 + z2 + sz1) mod p
    
    Computing xy one operation at a time:
    sum_z = z0 + z2
    sum_x = x0 + x1
    sum_y = y0 + y1
    mul_sumxy = sum_x * sum_y
    z1 = mul_sumxy - z0
    sz1 = s * z1
    xy = sum_z - sz1
   
  *)
  Definition goldilocks_mul_cps s (xs ys : T2) {R} (f:T2->R) :=
    split_cps s xs _
      (fun x0_x1 => split_cps s ys _
      (fun y0_y1 => mul_cps (fst x0_x1) (fst y0_y1) _
      (fun z0 => mul_cps (snd x0_x1) (snd y0_y1) _
      (fun z2 => add2_cps z0 z2 _
      (fun sum_z => add_cps (fst x0_x1) (snd x0_x1) _
      (fun sum_x => add_cps (fst y0_y1) (snd y0_y1) _
      (fun sum_y => mul_cps sum_x sum_y _
      (fun mul_sumxy => sub2_cps mul_sumxy z0 _
      (fun z1 => scmul2_cps s z1 _
      (fun sz1 => add2_cps sum_z sz1 _ f)))))))))).

  Definition goldilocks_mul s xs ys := @goldilocks_mul_cps s xs ys _ id.
  Lemma goldilocks_mul_id s xs ys {R} f :
    @goldilocks_mul_cps s xs ys R f = f (goldilocks_mul s xs ys).
  Proof.
    cbv [goldilocks_mul goldilocks_mul_cps]. rewrite_id.
    reflexivity.
  Qed.
    
  Local Existing Instances Z.equiv_modulo_Reflexive
        RelationClasses.eq_Reflexive Z.equiv_modulo_Symmetric
        Z.equiv_modulo_Transitive Z.mul_mod_Proper Z.add_mod_Proper
        Z.modulo_equiv_modulo_Proper.

  Lemma goldilocks_mul_correct (p : Z) (p_nonzero : p <> 0) s (s_nonzero : s <> 0) (s2_modp : (s^2) mod p = (s+1) mod p) xs ys :
    (eval2 (goldilocks_mul s xs ys)) mod p = (eval2 xs * eval2 ys) mod p.
  Proof.
    cbv [goldilocks_mul_cps goldilocks_mul]; Zmod_to_equiv_modulo.
    rewrite_id. rewrite push_id. rewrite_eval.
    repeat progress rewrite <-?(eval_split s xs), <-?(eval_split s ys) by assumption; ring_simplify.
    setoid_rewrite s2_modp.
    apply f_equal2; nsatz.
  Qed.
End Karatsuba.
