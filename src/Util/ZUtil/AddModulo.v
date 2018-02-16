Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Local Open Scope Z_scope.

Module Z.
  Lemma add_modulo_correct x y modulus :
    Z.add_modulo x y modulus =  if (modulus <=? x + y) then (x + y) - modulus else (x + y).
  Proof. reflexivity. Qed.
End Z.