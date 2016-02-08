Require Import Znumtheory BinInt BinNums.

Lemma Z_mod_mod x m : x mod m = (x mod m) mod m.
  symmetry.
  destruct (BinInt.Z.eq_dec m 0).
  - subst; rewrite !Zdiv.Zmod_0_r; reflexivity.
  - apply BinInt.Z.mod_mod; assumption.
Qed.
