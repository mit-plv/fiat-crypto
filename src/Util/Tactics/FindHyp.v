Require Export Crypto.Util.FixCoqMistakes.

Ltac find_hyp_eq a b := match goal with _ => constr_eq_nounivs a b end.
(* Work around https://github.com/coq/coq/issues/15554 *)
Ltac find_hyp T :=
  lazymatch T with
  | T
    => (* we're not in https://github.com/coq/coq/issues/15554 *)
      multimatch goal with
      | [ H : T |- _ ] => H
      end
  | _
    => (* https://github.com/coq/coq/issues/15554 *)
      multimatch goal with
      | [ H : ?T' |- _ ] => let __ := find_hyp_eq T T' in
                            H
      end
  end.

Ltac find_hyp_with_body body :=
  lazymatch body with
  | body
    => (* we're not in https://github.com/coq/coq/issues/15554 *)
      multimatch goal with
      | [ H := body |- _ ] => H
      end
  | _
    => (* https://github.com/coq/coq/issues/15554 *)
      multimatch goal with
      | [ H := ?body' |- _ ] => let __ := find_hyp_eq body body' in
                                H
      end
  end.
