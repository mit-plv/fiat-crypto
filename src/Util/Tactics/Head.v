Require Export Crypto.Util.FixCoqMistakes.

(** find the head of the given expression *)
Ltac head expr :=
  match expr with
  | ?f _ => head f
  | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.
