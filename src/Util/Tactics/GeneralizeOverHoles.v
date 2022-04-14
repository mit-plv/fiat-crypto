Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.Zeta1.
Require Import Coq.ssr.ssreflect.

Ltac generalize_over_holes tac :=
  zeta1 (ltac:(let H := fresh in
               (pose H := ltac:(let v := tac () in refine v));
               exact H)).
