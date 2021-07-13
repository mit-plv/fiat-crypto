Require Export Crypto.Util.FixCoqMistakes.

Ltac count_binders_gen eval_tac v :=
  let v := eval_tac v in
  lazymatch v with
  | fun x : ?T => ?F
    => let x' := fresh in
       lazymatch constr:(fun x' : T => ltac:(let f := constr:(match x' return _ with x => F end) in
                                             let v := count_binders_gen eval_tac f in
                                             exact (S v))) with
       | fun _ => ?v => v
       | ?val => fail 0 "Cannot eliminate functional dependencies of" val
       end
  | forall x, @?F x => count_binders_gen eval_tac F
  | _ => O
  end.

Ltac count_binders_hnf v := count_binders_gen ltac:(fun v => eval hnf in v) v.
Ltac count_binders v := count_binders_gen ltac:(fun v => v) v.
