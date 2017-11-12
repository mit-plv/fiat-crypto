Require Import Coq.Compat.AdmitAxiom.
Require Import Crypto.Util.SideConditions.CorePackages.

Definition admit_package (P : Prop) := P.

Ltac autosolve else_tac :=
  lazymatch goal with
  | [ |- admit_package ?P ]
    => change P; admit
  | _ => else_tac ()
  end.
