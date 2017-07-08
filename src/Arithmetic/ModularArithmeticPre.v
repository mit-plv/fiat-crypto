Require Import Coq.ZArith.BinInt Coq.NArith.BinNat Coq.Numbers.BinNums Coq.ZArith.Zdiv Coq.ZArith.Znumtheory.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.omega.Omega.
Require Import Crypto.Util.NumTheoryUtil.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.BreakMatch.

Lemma Z_mod_mod x m : x mod m = (x mod m) mod m.
  symmetry.
  destruct (BinInt.Z.eq_dec m 0).
  - subst; rewrite !Zdiv.Zmod_0_r; reflexivity.
  - apply BinInt.Z.mod_mod; assumption.
Qed.

Lemma exist_reduced_eq: forall (m : Z) (a b : Z), a = b -> forall pfa pfb,
    exist (fun z : Z => z = z mod m) a pfa =
    exist (fun z : Z => z = z mod m) b pfb.
Proof.
  intuition; simpl in *; try congruence.
  subst.
  f_equal.
  eapply UIP_dec, Z.eq_dec.
Qed.

Definition mulmod m := fun a b => a * b mod m.
Definition powmod_pos m := Pos.iter_op (mulmod m).
Definition powmod m a x := match x with N0 => 1 mod m | Npos p => powmod_pos m p (a mod m) end.

Lemma mulmod_assoc:
  forall m x y z : Z, mulmod m x (mulmod m y z) = mulmod m (mulmod m x y) z.
Proof.
  unfold mulmod; intros.
  rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; f_equal.
  apply Z.mul_assoc.
Qed.

Lemma powmod_1plus:
      forall m a : Z,
        forall x : N, powmod m a (1 + x) = (a * (powmod m a x mod m)) mod m.
Proof.
  intros m a x.
  rewrite N.add_1_l.
  cbv beta delta [powmod N.succ].
  destruct x. simpl; rewrite ?Zdiv.Zmult_mod_idemp_r, Z.mul_1_r; auto.
  unfold powmod_pos.
  rewrite Pos.iter_op_succ by (apply mulmod_assoc).
  unfold mulmod.
  rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; f_equal.
Qed.


Lemma N_pos_1plus : forall p, (N.pos p = 1 + (N.pred (N.pos p)))%N.
  intros.
  rewrite <-N.pos_pred_spec.
  rewrite N.add_1_l.
  rewrite N.pos_pred_spec.
  rewrite N.succ_pred; eauto.
  discriminate.
Qed.

Lemma powmod_Zpow_mod : forall m a n, powmod m a n = (a^Z.of_N n) mod m.
Proof.
  induction n as [|n IHn] using N.peano_ind; [auto|].
  rewrite <-N.add_1_l.
  rewrite powmod_1plus.
  rewrite IHn.
  rewrite Zmod_mod.
  rewrite N.add_1_l.
  rewrite N2Z.inj_succ.
  rewrite Z.pow_succ_r by (apply N2Z.is_nonneg).
  rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; f_equal.
Qed.

Local Obligation Tactic := idtac.

Program Definition pow_impl_sig {m} (a:{z : Z | z = z mod m}) (x:N) : {z : Z | z = z mod m}
  := powmod m (proj1_sig a) x.
Next Obligation.
  intros m a x; destruct x; [simpl; rewrite Zmod_mod; reflexivity|].
  rewrite N_pos_1plus.
  rewrite powmod_1plus.
  rewrite Zmod_mod; reflexivity.
Qed.

Program Definition pow_impl {m} :
   {pow0
   : {z : BinNums.Z | z = z mod m} -> BinNums.N -> {z : BinNums.Z | z = z mod m}
   |
   forall a : {z : BinNums.Z | z = z mod m},
   pow0 a 0%N =
   exist (fun z : BinNums.Z => z = z mod m) (1 mod m) (Z_mod_mod 1 m) /\
   (forall x : BinNums.N,
    pow0 a (1 + x)%N =
    exist (fun z : BinNums.Z => z = z mod m)
      ((proj1_sig a * proj1_sig (pow0 a x)) mod m)
      (Z_mod_mod (proj1_sig a * proj1_sig (pow0 a x)) m))} := pow_impl_sig.
Next Obligation.
  split; intros; apply exist_reduced_eq;
    rewrite ?powmod_1plus, ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r; reflexivity.
Qed.

Program Definition mod_inv_sig {m} (a:{z : Z | z = z mod m}) : {z : Z | z = z mod m} :=
  let (a, _) := a in
  match a return _ with
  | 0%Z => 0 (* m = 2 *)
  | _ => powmod m a (Z.to_N (m-2))
  end.
Next Obligation.
  intros; break_match; rewrite ?powmod_Zpow_mod, ?Zmod_mod, ?Zmod_0_l; reflexivity.
Qed.

Program Definition inv_impl {m : BinNums.Z} :
   {inv0 : {z : BinNums.Z | z = z mod m} -> {z : BinNums.Z | z = z mod m} |
   inv0 (exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m)) =
   exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m) /\
   (Znumtheory.prime m ->
    forall a : {z : BinNums.Z | z = z mod m},
    a <> exist (fun z : BinNums.Z => z = z mod m) (0 mod m) (Z_mod_mod 0 m) ->
    exist (fun z : BinNums.Z => z = z mod m)
      ((proj1_sig (inv0 a) * proj1_sig a) mod m)
      (Z_mod_mod (proj1_sig (inv0 a) * proj1_sig a) m) =
    exist (fun z : BinNums.Z => z = z mod m) (1 mod m) (Z_mod_mod 1 m))}
     := mod_inv_sig.
Next Obligation.
  intros m; split.
  { apply exist_reduced_eq; rewrite Zmod_0_l; reflexivity. }
  intros Hm [a pfa] Ha'. apply exist_reduced_eq.
  assert (Hm':0 <= m - 2) by (pose proof prime_ge_2 m Hm; omega).
  assert (Ha:a mod m<>0) by (intro; apply Ha', exist_reduced_eq; congruence).
  cbv [proj1_sig mod_inv_sig].
  transitivity ((a*powmod m a (Z.to_N (m - 2))) mod m); [destruct a; f_equal; ring|].
  rewrite !powmod_Zpow_mod.
  rewrite Z2N.id by assumption.
  rewrite Zmult_mod_idemp_r.
  rewrite <-Z.pow_succ_r by assumption.
  replace (Z.succ (m - 2)) with (m-1) by omega.
  rewrite (Zmod_small 1) by omega.
  apply (fermat_little m Hm a Ha).
Qed.
