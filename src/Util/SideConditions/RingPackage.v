Require Import Coq.ZArith.ZArith.
Require Import Coq.setoid_ring.Ring_tac.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Export Crypto.Util.FixCoqMistakes.

Definition eq_by_Zring_prod_package (P : Prop) := P.

Ltac auto_split_prod_step _ :=
  match goal with
  | [ H : prod _ _ |- _ ] => destruct H
  | [ |- forall a, _ ] => let a := fresh in intro a; compute in a
  | [ |- pair _ _ = pair _ _ ] => apply f_equal2
  | [ |- @eq (prod _ _) _ _ ] => apply path_prod
  end.

Ltac Zring_prod_eq_tac _ :=
  cbv -[Z.add Z.sub Z.mul Z.div Z.pow Z.opp Z.log2 Z.land Z.lor Z.log2_up Z.abs];
  repeat match goal with
         | _ => auto_split_prod_step ()
         | [ |- @eq Z _ _ ] => ring
         end.

Ltac autosolve else_tac :=
  lazymatch goal with
  | [ |- eq_by_Zring_prod_package _ ]
    => solve [ Zring_prod_eq_tac () ]
  | _ => else_tac ()
  end.
