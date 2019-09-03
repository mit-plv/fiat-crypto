Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Local Open Scope Z_scope.

Module Z.
  Lemma truncating_shiftl_correct bw x y
  : Z.truncating_shiftl bw x y = (x << y) mod 2^bw.
  Proof. reflexivity. Qed.
End Z.
