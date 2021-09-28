Require Import Coq.Bool.Bool.
(* Compat for Coq 8.9 *)
Module Export Coq.
  Module Export Bool.
    Module Bool.
      Definition le (b1 b2 : bool) := if b1 then b2 = true else True.
      Lemma le_implb : forall b1 b2, le b1 b2 <-> implb b1 b2 = true.
      Proof.
        destr_bool; intuition.
      Qed.
      Lemma implb_true_r : forall b:bool, implb b true = true.
      Proof.
        destr_bool.
      Qed.
    End Bool.
  End Bool.
End Coq.
