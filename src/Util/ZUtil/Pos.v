From Stdlib Require Import ZArith Lia.
Require Import Crypto.Util.Pos.
Local Open Scope Z_scope.
#[local] Coercion Z.of_N : N >-> Z.

Module Z.
  Lemma pos_of_N n : Z.pos (Pos.of_N n) = Z.max 1 (Z.of_N n).
  Proof. case n; cbn; lia. Qed.

  Import ZifyClasses.
  #[global] Instance Op_Pos_of_N : UnOp Pos.of_N.
  Proof. refine ({| TUOp x := Z.max 1 x ; TUOpInj x := _ |}). exact (pos_of_N x). Defined.
  Add Zify UnOp Op_Pos_of_N.

  Lemma pos_of_N_pos (n : N) : Z.lt 0 n -> Z.pos (Pos.of_N n) = n.
  Proof. lia. Qed.
End Z.
