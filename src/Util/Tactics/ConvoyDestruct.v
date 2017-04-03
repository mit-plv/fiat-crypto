Require Import Crypto.Util.Tactics.GetGoal.

(** Destruct the convoy pattern ([match e as x return x = e -> _ with _ => _ end eq_refl] *)
Ltac convoy_destruct_gen T change_in :=
  let e' := fresh in
  let H' := fresh in
  match T with
  | context G[?f eq_refl]
    => match f with
       | match ?e with _ => _ end
         => pose e as e';
            match f with
            | context F[e]
              => let F' := context F[e'] in
                 first [ pose (eq_refl : e = e') as H';
                         let G' := context G[F' H'] in
                         change_in G';
                         clearbody H' e'
                       | pose (eq_refl : e' = e) as H';
                         let G' := context G[F' H'] in
                         change_in G';
                         clearbody H' e' ]
            end
       end;
       destruct e'
  end.

Ltac convoy_destruct_in H :=
  let T := type of H in
  convoy_destruct_gen T ltac:(fun T' => change T' in H).
Ltac convoy_destruct :=
  let T := get_goal in
  convoy_destruct_gen T ltac:(fun T' => change T').
