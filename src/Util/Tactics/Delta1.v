Require Export Crypto.Util.FixCoqMistakes.

Ltac delta1 x :=
  eval cbv delta [x] in x.
