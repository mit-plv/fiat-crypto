Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Local Open Scope Z_scope.

Module Z.
  Lemma divideb_divide x y : Z.divideb x y = true <-> Z.divide x y.
  Proof.
    cbv [Z.divideb].
    pose proof (Z.mod_divide y x).
    destruct (x =? 0) eqn:H'; intuition repeat (lia || reflect_hyps || subst || rewrite Z.eqb_eq || auto).
    all: cbv [Z.divide] in *.
    { exists 0; reflexivity. }
    { destruct_head'_ex; lia. }
  Qed.

  #[global] Instance divideb_spec : reflect_rel Z.divide Z.divideb | 10.
  Proof.
    intros x y; pose proof (divideb_divide x y); destruct Z.divideb; constructor.
    all: intuition congruence.
  Qed.
End Z.
