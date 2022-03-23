Require Import Coq.Lists.List.
Require Import Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Module List.
  Lemma concat_map_singleton A (ls : list A) : concat (map (fun x => [x]) ls) = ls.
  Proof. induction ls; cbn; congruence. Qed.
End List.
