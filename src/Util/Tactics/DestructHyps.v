Require Export Crypto.Util.FixCoqMistakes.

(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].

    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac do_one_match_then matcher do_tac tac :=
  idtac;
  match goal with
  | [ H : ?T |- _ ]
    => matcher T; do_tac H;
       try match type of H with
           | T => clear H
           end;
       tac
  end.

Ltac do_all_matches_then matcher do_tac tac :=
  repeat do_one_match_then matcher do_tac tac.

Ltac destruct_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => destruct H) tac.
Ltac destruct_one_match_then matcher tac :=
  do_one_match_then matcher ltac:(fun H => destruct H) tac.

Ltac inversion_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => inversion H; subst) tac.
Ltac inversion_one_match_then matcher tac :=
  do_one_match_then matcher ltac:(fun H => inversion H; subst) tac.

Ltac destruct_all_matches matcher :=
  destruct_all_matches_then matcher ltac:( simpl in * ).
Ltac destruct_one_match matcher := destruct_one_match_then matcher ltac:( simpl in * ).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

Ltac inversion_all_matches matcher := inversion_all_matches_then matcher ltac:( simpl in * ).
Ltac inversion_one_match matcher := inversion_one_match_then matcher ltac:( simpl in * ).
Ltac inversion_all_matches' matcher := inversion_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
  | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).
