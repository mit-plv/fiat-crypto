Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma div_abs_sgn_nonneg a b : 0 <= Z.sgn (Z.abs a / Z.abs b).
  Proof.
    generalize (Zdiv_sgn (Z.abs a) (Z.abs b)).
    destruct a, b; simpl; lia.
  Qed.
  Global Hint Resolve div_abs_sgn_nonneg : zarith.
End Z.

Module Export Hints.
  Export Crypto.Util.FixCoqMistakes.
  Export Crypto.Util.ZUtil.Hints.Core.
  Global Hint Resolve Z.div_abs_sgn_nonneg : zarith.
End Hints.
