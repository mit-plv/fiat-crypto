Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Open Scope list_scope.

Lemma split_alt {A B} ls : @split A B ls = (List.map fst ls, List.map snd ls).
Proof.
  induction ls as [|[? ?]? IH]; cbn; [ reflexivity | now rewrite IH ].
Qed.
