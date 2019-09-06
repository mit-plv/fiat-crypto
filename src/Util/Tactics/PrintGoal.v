Require Import Crypto.Util.Tactics.PrintContext.

Ltac print_goal _ :=
  lazymatch goal with |- ?G => idtac G end.

Ltac print_context_and_goal _ :=
  print_context ();
  idtac "============================";
  print_goal ().
