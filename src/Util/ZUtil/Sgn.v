Require Import Coq.ZArith.ZArith Coq.omega.Omega.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma div_abs_sgn_nonneg a b : 0 <= Z.sgn (Z.abs a / Z.abs b).
  Proof.
    generalize (Zdiv_sgn (Z.abs a) (Z.abs b)).
    destruct a, b; simpl; omega.
  Qed.
  Hint Resolve div_abs_sgn_nonneg : zarith.
End Z.
