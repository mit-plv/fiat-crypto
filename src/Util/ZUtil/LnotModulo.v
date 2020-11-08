Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Local Open Scope Z_scope.

Module Z.
  Lemma lnot_modulo_correct x m : Z.lnot_modulo x m = Z.lnot x mod m.
  Proof. reflexivity. Qed.
End Z.
