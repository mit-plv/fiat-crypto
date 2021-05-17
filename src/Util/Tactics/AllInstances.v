Require Import Crypto.Util.Tactics.AllSuccesses.
Require Import Crypto.Util.Tactics.CountBinders.
Require Import Crypto.Util.Tactics.AppendUnderscores.

Ltac all_instances_of tc :=
  (eval cbv zeta in
      (ltac:(let v := all_successes ltac:(fun _ => let tc := open_constr:(tc) in
                                                   let H := fresh in
                                                   let __ := multimatch goal with
                                                             | _ => simple notypeclasses refine (let H : tc := _ in _);
                                                                    [ typeclasses eauto | ]
                                                             end in
                                                   let v := (eval cbv delta [H] in H) in
                                                   let __ := match goal with _ => clear H end in
                                                   v)
                                           () in
             exact v))).
Ltac all_instances_of_family F :=
  let T := type of F in
  let underscores := count_binders_hnf T in
  let F := append_underscores F underscores in
  all_instances_of F.
