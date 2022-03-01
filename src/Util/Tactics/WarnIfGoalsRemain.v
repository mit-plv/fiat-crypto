Require Import Crypto.Util.Tactics.PrintGoal.

Ltac warn_if_goals_remain _ :=
  [ > idtac "WARNING: Remaining goal:"; print_context_and_goal () .. ].

Ltac fail_if_goals_remain _ :=
  warn_if_goals_remain (); fail 0 "A goal remains".
