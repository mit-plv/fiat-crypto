(** If [tac_in H] operates in [H] and leaves side-conditions before
    the original goal, then
    [side_conditions_before_to_side_conditions_after tac_in H] does
    the same thing to [H], but leaves side-conditions after the
    original goal. *)
Ltac side_conditions_before_to_side_conditions_after tac_in H :=
  let HT := type of H in
  let HTT := type of HT in
  let H' := fresh in
  rename H into H';
  let HT' := fresh in
  evar (HT' : HTT);
  cut HT';
  [ subst HT'; intro H
  | tac_in H';
    [ ..
    | subst HT'; eexact H' ] ];
  instantiate; (* required in 8.4 for the [move] to succeed, because evar dependencies *)
  [ (* We preserve the order of the hypotheses.  We need to do this
       here, after evars are instantiated, and not above. *)
    move H after H'; clear H'
  | .. ].
