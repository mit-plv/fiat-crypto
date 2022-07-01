(** Basic lemmas about [Z.div] for bootstrapping various tactics *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma div_0_r_eq a b : b = 0 -> a / b = 0.
  Proof. intro; subst; auto with zarith. Qed.
  Global Hint Resolve div_0_r_eq : zarith.
  Hint Rewrite div_0_r_eq using assumption : zsimplify.
End Z.
