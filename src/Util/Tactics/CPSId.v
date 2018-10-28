(** * [cps_id] is a scaffold for writing tactics that convert to cps normal form (where the continuation is the identity *)

Ltac ensure_complex_continuation allow_option k :=
  lazymatch k with
  | @id _ => fail
  | (fun x => x) => fail
  | _
    => lazymatch allow_option with
       | true => lazymatch k with
                 | @Some _ => fail
                 | (fun x => Some x) => fail
                 | _ => idtac
                 end
       | false => idtac
       | ?ao => fail 100 "Argument allow_option to ensure_complex_continuation must be true or false, not" ao
       end
  end.

Ltac cps_id_step allow_option lem :=
  let lem := open_constr:(lem) in
  lazymatch type of lem with
  | ?T -> _ => cps_id_step allow_option open_constr:(lem _)
  | ?lhs = ?k ?rhs
    => match goal with
       | [ |- context[?e] ]
         => (* take advantage of lazymatch treating evars as holes/wildcards *)
         lazymatch e with
         | lhs
           => let lem := constr:(lem : e = _) in
              ensure_complex_continuation allow_option k;
              rewrite lem
         end
       | [ H : context[?e] |- _ ]
         => (* take advantage of lazymatch treating evars as holes/wildcards *)
         lazymatch e with
         | lhs
           => let lem := constr:(lem : e = _) in
              ensure_complex_continuation allow_option k;
              rewrite lem in H
         end
       end
  end.

Ltac cps_id allow_option lem := repeat cps_id_step allow_option lem.
Tactic Notation "cps_id_with_option" uconstr(lem) := cps_id true lem.
Tactic Notation "cps_id_no_option" uconstr(lem) := cps_id false lem.
