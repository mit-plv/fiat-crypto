From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Bool.
From Coq Require Import Btauto.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Testbit.
Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma land_lxor_distr_l : forall a b c, (Z.lxor a b) &' c = (Z.lxor (a &' c) b) &' c.
  Proof. intros; apply Z.bits_inj; intro; autorewrite with Ztestbit; btauto. Qed.
  Lemma land_lxor_distr_r : forall a b c, (Z.lxor a b) &' c = (Z.lxor a (b &' c)) &' c.
  Proof. intros; apply Z.bits_inj; intro; autorewrite with Ztestbit; btauto. Qed.
  Lemma land_lxor_distr_both : forall a b c, (Z.lxor a b) &' c = (Z.lxor (a &' c) (b &' c)) &' c.
  Proof. intros; apply Z.bits_inj; intro; autorewrite with Ztestbit; btauto. Qed.
  (** Branch-free selection: [a ^ ((a ^ b) & mask)] picks bits of [b] where [mask] is set and bits of [a] elsewhere. *)
  Lemma lxor_land_lxor_select : forall a b mask, Z.lxor a ((Z.lxor a b) &' mask) = (Z.lnot mask &' a) |' (mask &' b).
  Proof.
    intros; apply Z.bits_inj'; intros n Hn.
    rewrite Z.lxor_spec, Z.lor_spec, !Z.land_spec, Z.lxor_spec, Z.lnot_spec by assumption.
    btauto.
  Qed.
End Z.
