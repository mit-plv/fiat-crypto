(** NUtil that doesn't depend on ZUtil stuff *)
(** Should probably come up with a better organization of this stuff *)
Require Import Coq.NArith.NArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.Util.NatUtil Crypto.Util.Decidable.

Module N.
  Lemma size_le a b : (a <= b -> N.size a <= N.size b)%N.
  Proof.
    destruct (dec (a=0)%N), (dec (b=0)%N); subst; auto using N.le_0_l.
    { destruct a; auto. }
    { rewrite !N.size_log2 by assumption.
      rewrite <-N.succ_le_mono.
      apply N.log2_le_mono. }
  Qed.

  Lemma N_le_1_l : forall p, (1 <= N.pos p)%N.
  Proof.
    destruct p; cbv; congruence.
  Qed.

  Lemma Pos_land_upper_bound_l : forall a b, (Pos.land a b <= N.pos a)%N.
  Proof.
    induction a as [a IHa|a IHa|]; destruct b as [b|b|]; try solve [cbv; congruence];
      simpl; specialize (IHa b); case_eq (Pos.land a b); intro p; simpl;
      try (apply N_le_1_l || apply N.le_0_l); intro land_eq;
      rewrite land_eq in *; unfold N.le, N.compare in *;
      rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO;
      try assumption.
    destruct (p ?=a)%positive; cbv; congruence.
  Qed.

  Lemma le_to_nat a b : (a <= b)%N <-> (N.to_nat a <= N.to_nat b)%nat.
  Proof.
    rewrite <-N.lt_succ_r.
    rewrite <-Nat.lt_succ_r.
    rewrite <-Nnat.N2Nat.inj_succ.
    rewrite <-NatUtil.Nat2N_inj_lt.
    rewrite !Nnat.N2Nat.id.
    reflexivity.
  Qed.

  Lemma size_nat_equiv : forall n, N.size_nat n = N.to_nat (N.size n).
  Proof.
    destruct n as [|p]; auto; simpl; induction p as [p IHp|p IHp|]; simpl; auto; rewrite IHp, Pnat.Pos2Nat.inj_succ; reflexivity.
  Qed.

  Lemma size_nat_le a b : (a <= b)%N -> (N.size_nat a <= N.size_nat b)%nat.
  Proof.
    rewrite !size_nat_equiv.
    rewrite <-le_to_nat.
    apply size_le.
  Qed.
End N.
