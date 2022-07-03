Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma land_same_r : forall a b, (a &' b) &' b = a &' b.
  Proof.
    intros a b; apply Z.bits_inj'; intros n H.
    rewrite !Z.land_spec.
    case_eq (Z.testbit b n); intros;
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
  Qed.

  Lemma land_m1'_l a : Z.land (-1) a = a.
  Proof. apply Z.land_m1_l. Qed.
  Hint Rewrite Z.land_m1_l land_m1'_l : zsimplify_const zsimplify zsimplify_fast.

  Lemma land_m1'_r a : Z.land a (-1) = a.
  Proof. apply Z.land_m1_r. Qed.
  Hint Rewrite Z.land_m1_r land_m1'_r : zsimplify_const zsimplify zsimplify_fast.

  Lemma sub_1_lt_le x y : (x - 1 < y) <-> (x <= y).
  Proof. lia. Qed.
End Z.
