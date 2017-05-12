Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Notations.
Local Open Scope Z_scope.

Module Z.
  Definition pow2_mod n i := (n &' (Z.ones i)).
End Z.
