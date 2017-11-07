Require Export Crypto.Util.FixCoqMistakes.

(** find the head of the given expression, underneath [fun] and [forall] *)
Ltac head_under_binders_gen redtac expr :=
  let expr := redtac expr in
  match expr with
  | ?f _ => head_under_binders_gen redtac f
  | fun x : ?T => @?f x
    => lazymatch constr:(fun x : T
                         => ltac:(let f' := (eval cbv beta in (f x)) in
                                  let h := head_under_binders_gen redtac f' in
                                  exact h)) with
       | fun _ => ?f => f
       | ?f => f
       end
  | forall x, @?f x
    => head_under_binders_gen redtac f
  | ?expr => expr
  end.

Ltac head_under_binders expr := head_under_binders_gen ltac:(fun e => e) expr.
Ltac head_hnf_under_binders expr := head_under_binders_gen ltac:(fun e => eval hnf in e) expr.
