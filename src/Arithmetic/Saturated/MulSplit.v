Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.LetIn Crypto.Util.CPSUtil.

(* Defines bignum multiplication using a two-output multiply operation. *)
Module B.
  Module Associational.
    Section Associational.
      Context {mul_split : Z -> Z -> Z -> Z * Z} (* first argument is where to split output; [mul_split s x y] gives ((x * y) mod s, (x * y) / s) *)
              {mul_split_mod : forall s x y,
                  fst (mul_split s x y)  = (x * y) mod s}
              {mul_split_div : forall s x y,
                  snd (mul_split s x y)  = (x * y) / s}
              .

      Definition sat_multerm_cps s (t t' : B.limb) {T} (f:list B.limb ->T) :=
      dlet xy := mul_split s (snd t) (snd t') in
      f ((fst t * fst t', fst xy) :: (fst t * fst t' * s, snd xy) :: nil).

      Definition sat_multerm s t t' := sat_multerm_cps s t t' id.
      Lemma sat_multerm_id s t t' T f :
      @sat_multerm_cps s t t' T f = f (sat_multerm s t t').
      Proof. reflexivity. Qed.
      Hint Opaque sat_multerm : uncps.
      Hint Rewrite sat_multerm_id : uncps.

      Definition sat_mul_cps s (p q : list B.limb) {T} (f : list B.limb -> T) :=
      flat_map_cps (fun t => @flat_map_cps _ _ (sat_multerm_cps s t) q) p f.

      Definition sat_mul s p q := sat_mul_cps s p q id.
      Lemma sat_mul_id s p q T f : @sat_mul_cps s p q T f = f (sat_mul s p q).
      Proof. cbv [sat_mul sat_mul_cps]. autorewrite with uncps. reflexivity. Qed.
      Hint Opaque sat_mul : uncps.
      Hint Rewrite sat_mul_id : uncps.

      Lemma eval_map_sat_multerm s a q (s_nonzero:s<>0):
      B.Associational.eval (flat_map (sat_multerm s a) q) = fst a * snd a * B.Associational.eval q.
      Proof.
      cbv [sat_multerm sat_multerm_cps Let_In]; induction q;
      repeat match goal with
              | _ => progress (autorewrite with uncps push_id cancel_pair push_basesystem_eval in * )
              | _ => progress simpl flat_map
              | _ => progress rewrite ?IHq, ?mul_split_mod, ?mul_split_div
              | _ => rewrite Z.mod_eq by assumption
              | _ => ring_simplify; omega
              end.
      Qed.
      Hint Rewrite eval_map_sat_multerm using (omega || assumption)
      : push_basesystem_eval.

      Lemma eval_sat_mul s p q (s_nonzero:s<>0):
      B.Associational.eval (sat_mul s p q) = B.Associational.eval p * B.Associational.eval q.
      Proof.
      cbv [sat_mul sat_mul_cps]; induction p; [reflexivity|].
      repeat match goal with
              | _ => progress (autorewrite with uncps push_id push_basesystem_eval in * )
              | _ => progress simpl flat_map
              | _ => rewrite IHp
              | _ => progress change (fun x => sat_multerm_cps s a x id)  with (sat_multerm s a)
              | _ => ring_simplify; omega
              end.
      Qed.
      Hint Rewrite eval_sat_mul : push_basesystem_eval.
    End Associational.
  End Associational.
End B.
Hint Opaque B.Associational.sat_mul B.Associational.sat_multerm : uncps.
Hint Rewrite @B.Associational.sat_mul_id @B.Associational.sat_multerm_id : uncps.
Hint Rewrite @B.Associational.eval_sat_mul @B.Associational.eval_map_sat_multerm using (omega || assumption) : push_basesystem_eval.

