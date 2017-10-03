Require Import Coq.ZArith.ZArith Coq.Classes.RelationClasses.

Local Open Scope Z_scope.

Module Z.
  Lemma ge_refl x : x >= x.
  Proof. rewrite !Z.ge_le_iff; reflexivity. Qed.
  Lemma ge_trans n m p : n >= m -> m >= p -> n >= p.
  Proof. rewrite !Z.ge_le_iff; eauto using Z.le_trans. Qed.

  Global Instance ge_preorder : PreOrder Z.ge.
  Proof. constructor; hnf; [ apply ge_refl | apply ge_trans ]. Defined.
End Z.
