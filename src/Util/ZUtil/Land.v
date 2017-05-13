Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Notations.
Local Open Scope Z_scope.

Module Z.
  Lemma land_same_r : forall a b, (a &' b) &' b = a &' b.
  Proof.
    intros; apply Z.bits_inj'; intros.
    rewrite !Z.land_spec.
    case_eq (Z.testbit b n); intros;
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
  Qed.
End Z.
