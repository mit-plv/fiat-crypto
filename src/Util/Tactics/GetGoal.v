Require Export Crypto.Util.GlobalSettings.
Ltac get_goal :=
  match goal with |- ?G => G end.
