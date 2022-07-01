Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
  Proof. lia. Qed.
  Hint Rewrite opp_eq_0_iff : zsimplify.
End Z.
