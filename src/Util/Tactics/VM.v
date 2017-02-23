(* Code by Jason Gross for COQBUG 4637: vm_compute in _ makes Defined slow *)

(** First, work around COQBUG 4494, https://coq.inria.fr/bugs/show_bug.cgi?id=4494 (replace is slow and broken under binders *)
Ltac replace_with_at_by x y set_tac tac :=
  let H := fresh in
  let x' := fresh in
  set_tac x' x;
  assert (H : y = x') by (subst x'; tac);
  clearbody x'; induction H.

Ltac replace_with_at x y set_tac :=
  let H := fresh in
  let x' := fresh in
  set_tac x' x;
  cut (y = x');
  [ intro H; induction H
  | subst x' ].

Ltac replace_with_vm_compute c :=
  let c' := (eval vm_compute in c) in
  (* we'd like to just do: *)
  (* replace c with c' by (clear; abstract (vm_compute; reflexivity)) *)
  (* but [set] is too slow in 8.4, so we write our own version (see COQBUG https://coq.inria.fr/bugs/show_bug.cgi?id=3280#c13 *)
  let set_tac := (fun x' x
                  => pose x as x';
                     change x with x') in
  replace_with_at_by c c' set_tac ltac:(clear; vm_cast_no_check (eq_refl c')).

Ltac replace_with_vm_compute_in c H :=
  let c' := (eval vm_compute in c) in
  (* By constrast [set ... in ...] seems faster than [change .. with ... in ...] in 8.4?! *)
  replace_with_at_by c c' ltac:(fun x' x => set (x' := x) in H ) ltac:(clear; vm_cast_no_check (eq_refl c')).
