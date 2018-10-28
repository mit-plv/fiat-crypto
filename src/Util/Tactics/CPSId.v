(** * [cps_id] is a scaffold for writing tactics that convert to cps normal form (where the continuation is the identity *)

Ltac ensure_complex_continuation allow_option k :=
  lazymatch k with
  | id => fail
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

Ltac cps_id_step allow_option match_to_cont_lem :=
  match goal with
  | [ |- context[?e] ]
    => let res := match_to_cont_lem e in
       lazymatch res with
       | (?k, ?lem)
         => ensure_complex_continuation allow_option k;
            (* sometimes reduction mismatches happen, so we cast [lem] to fix them *)
            (rewrite lem || rewrite (lem : e = _))
       end
  | [ H : context[?e] |- _ ]
    => let res := match_to_cont_lem e in
       lazymatch res with
       | (?k, ?lem)
         => ensure_complex_continuation allow_option k;
            (* sometimes reduction mismatches happen, so we cast [lem] to fix them *)
            (rewrite lem in H || rewrite (lem : e = _) in H)
       end
  end.

Ltac cps_id allow_option match_to_cont_lem := repeat cps_id_step allow_option match_to_cont_lem.
Ltac cps_id_with_option match_to_cont_lem := cps_id true match_to_cont_lem.
Ltac cps_id_no_option match_to_cont_lem := cps_id false match_to_cont_lem.
