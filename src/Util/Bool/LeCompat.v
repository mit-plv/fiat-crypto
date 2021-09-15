Require Import Coq.Bool.Bool.
(* Compat for Coq 8.9 *)
Module Export Coq.
  Module Export Bool.
    Module Bool.
      Definition le (b1 b2 : bool) := if b1 then b2 = true else True.
    End Bool.
  End Bool.
End Coq.
