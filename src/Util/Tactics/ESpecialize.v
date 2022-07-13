Require Export Crypto.Util.FixCoqMistakes.
(** Like [specialize] but allows holes that get filled with evars. *)
Tactic Notation "especialize" open_constr(H) := specialize H.
