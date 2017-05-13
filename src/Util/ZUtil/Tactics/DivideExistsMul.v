Require Import Coq.ZArith.ZArith Coq.omega.Omega.
Local Open Scope Z_scope.

Module Z.
  Ltac divide_exists_mul := let k := fresh "k" in
  match goal with
  | [ H : (?a | ?b) |- _ ] => apply Z.mod_divide in H; try apply Zmod_divides in H;
                              match type of H with
                              | ex _ => destruct H as [k H]
                              | _ => destruct H
                              end
  | [ |- (?a | ?b) ] => apply Z.mod_divide; try apply Zmod_divides
  end; (omega || auto).
End Z.
