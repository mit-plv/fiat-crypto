Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.btauto.Btauto.
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
End Z.
