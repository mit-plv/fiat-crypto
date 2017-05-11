(** [simplify_projections] reduces terms of the form [fst (_, _)] (for
    any projection from [prod], [sig], [sigT], or [and]) *)
Ltac pre_simplify_projection proj proj' uproj' :=
  pose proj as proj';
  pose proj as uproj';
  unfold proj in uproj';
  change proj with proj'.
Ltac do_simplify_projection_2Targ_4carg_step proj proj' uproj' construct :=
  change proj' with uproj' at 1;
  lazymatch goal with
  | [ |- context[uproj' _ _ (construct _ _ _ _)] ]
    => cbv beta iota delta [uproj']
  | _ => change uproj' with proj
  end.
Ltac do_simplify_projection_2Targ_4carg proj proj' uproj' construct :=
  repeat do_simplify_projection_2Targ_4carg_step proj proj' uproj' construct.
Ltac simplify_projection_2Targ_4carg proj construct :=
  let proj' := fresh "proj" in
  let uproj' := fresh "proj" in
  pre_simplify_projection proj proj' uproj';
  do_simplify_projection_2Targ_4carg proj proj' uproj' construct;
  clear proj' uproj'.

Ltac simplify_projections :=
  repeat (simplify_projection_2Targ_4carg @fst @pair
          || simplify_projection_2Targ_4carg @snd @pair
          || simplify_projection_2Targ_4carg @proj1_sig @exist
          || simplify_projection_2Targ_4carg @proj2_sig @exist
          || simplify_projection_2Targ_4carg @projT1 @existT
          || simplify_projection_2Targ_4carg @projT2 @existT
          || simplify_projection_2Targ_4carg @proj1 @conj
          || simplify_projection_2Targ_4carg @proj2 @conj).
