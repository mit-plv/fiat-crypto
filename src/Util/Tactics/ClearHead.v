Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Tactics.Head.

Ltac clear_one_head T :=
  match goal with
  | [ H : ?HT |- _ ]
    => lazymatch head HT with
       | T => clear H
       end
  end.
Ltac clear_head T := repeat clear_one_head T.
