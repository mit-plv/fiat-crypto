Require Export Crypto.Util.FixCoqMistakes.
Ltac get_goal :=
  match goal with |- ?G => G end.
