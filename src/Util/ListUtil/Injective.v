From Coq Require Import List.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Module List.
  Lemma map_inj A B f g xs ys : (forall x y, f x = g y -> x = y) -> @map A B f xs = @map A B g ys -> xs = ys.
  Proof.
    intro H; revert ys; induction xs as [|?? IH], ys; cbn; try reflexivity.
    all: inversion 1; f_equal; eauto.
  Qed.
End List.
