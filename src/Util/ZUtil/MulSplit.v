Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Local Open Scope Z_scope.

Module Z.
  Lemma mul_split_mod s x y : fst (Z.mul_split s x y)  = (x * y) mod s.
  Proof. reflexivity. Qed.
  Lemma mul_split_div s x y : snd (Z.mul_split s x y)  = (x * y) / s.
  Proof. reflexivity. Qed.
End Z.
