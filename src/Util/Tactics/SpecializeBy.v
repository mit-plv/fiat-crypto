Require Export Crypto.Util.FixCoqMistakes.

Ltac transparent_specialize_one H arg :=
  first [ let test := eval unfold H in H in idtac;
          let H' := fresh in rename H into H'; pose (H' arg) as H; subst H'
         | specialize (H arg) ].

(** try to specialize all non-dependent hypotheses using [tac], maintaining transparency *)
Ltac guarded_specialize_by' tac guard_tac :=
  idtac;
  match goal with
  | [ H : ?A -> ?B |- _ ]
    => guard_tac H;
       let H' := fresh in
       assert (H' : A) by tac;
       transparent_specialize_one H H';
       try clear H' (* if [H] was transparent, [H'] will remain *)
  end.
Ltac specialize_by' tac := guarded_specialize_by' tac ltac:(fun _ => idtac).

Ltac specialize_by tac := repeat specialize_by' tac.

(** [specialize_by auto] should not mean [specialize_by ( auto
    with * )]!!!!!!! (see
    https://coq.inria.fr/bugs/show_bug.cgi?id=4966) We fix this design
    flaw. *)
Tactic Notation "specialize_by" tactic3(tac) := specialize_by tac.

(** A marginally faster version of [specialize_by assumption] *)
Ltac specialize_by_assumption :=
  repeat match goal with
         | [ H : ?T, H' : (?T -> ?U)%type |- _ ]
           => lazymatch goal with
              | [ _ : context[H'] |- _ ] => fail
              | [ |- context[H'] ] => fail
              | _ => specialize (H' H)
              end
         end.
