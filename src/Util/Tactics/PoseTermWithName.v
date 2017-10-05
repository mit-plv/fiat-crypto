Ltac pose_term_with tac name :=
  let name := fresh name in
  let v := tac () in
  let dummy := match goal with
               | _ => pose v as name
               end in
  name.

Ltac pose_term_with_type type tac name :=
  pose_term_with ltac:(fun u => let v := tac u in constr:(v : type)) name.
