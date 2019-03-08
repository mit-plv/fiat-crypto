Ltac gprogress tac :=
  [ > progress tac | tac.. ]
  + [ > | gprogress tac.. ].
Tactic Notation "gprogress" tactic3(tac) := gprogress tac.
Ltac gtry tac := tac + idtac.
Tactic Notation "gtry" tactic3(tac) := gtry tac.
Ltac grepeat tac := gtry (gprogress tac; grepeat tac).
Tactic Notation "grepeat" tactic3(tac) := grepeat tac.
