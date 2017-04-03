(** [forward H] specializes non-dependent binders in a hypothesis [H]
    with side-conditions.  Side-conditions come after the main goal,
    like with [replace] and [rewrite].

    [eforward H] is like [forward H], but also specializes dependent
    binders with evars.

    Both tactics do nothing on hypotheses they cannot handle. *)
Ltac forward_step H :=
  match type of H with
  | ?A -> ?B => let a := fresh in cut A; [ intro a; specialize (H a); clear a | ]
  end.
Ltac eforward_step H :=
  match type of H with
  | _ => forward_step H
  | forall x : ?A, _
    => let x_or_fresh := fresh x in
       evar (x_or_fresh : A);
       specialize (H x_or_fresh); subst x_or_fresh
  end.
Ltac forward H := try (forward_step H; [ forward H | .. ]).
Ltac eforward H := try (eforward_step H; [ eforward H | .. ]).
