From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import List.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma fold_right_land_m1_cps v ls
    : fold_right Z.land v ls
      = Z.land (fold_right Z.land (-1) ls) v.
  Proof.
    induction ls as [|?? IH]; cbn [fold_right].
    { now rewrite Z.land_m1'_l. }
    { rewrite <- !Z.land_assoc, IH; reflexivity. }
  Qed.

  Lemma fold_right_land_ones_id sz ls
    : Z.land (fold_right Z.land (Z.ones sz) ls) (Z.ones sz)
      = Z.land (fold_right Z.land (-1) ls) (Z.ones sz).
  Proof.
    rewrite fold_right_land_m1_cps, <- Z.land_assoc, Z.land_diag.
    reflexivity.
  Qed.
End Z.
