Require Import Coq.ZArith.ZArith.
Require Import Coq.setoid_ring.Ring_tac.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Export Crypto.Util.FixCoqMistakes.

Definition eq_by_Zring_prod_package (P : Prop) := P.

Ltac auto_split_prod_step_early special_ring_intros_tac :=
  match goal with
  | _ => progress hnf
  | _ => progress special_ring_intros_tac ()
  | [ H : prod _ _ |- _ ] => destruct H
  | [ |- forall a, _ ] => let a := fresh in intro a; compute in a
  end.

Ltac auto_split_prod_step special_ring_intros_tac :=
  match goal with
  | _ => auto_split_prod_step_early special_ring_intros_tac
  | [ |- pair _ _ = pair _ _ ] => apply f_equal2
  | [ |- @eq (prod _ _) _ _ ] => apply path_prod
  end.

Ltac Zring_prod_eq_tac_gen special_ring_intros_tac :=
  repeat auto_split_prod_step_early special_ring_intros_tac;
  cbv -[Z.add Z.sub Z.mul Z.div Z.pow Z.opp Z.log2 Z.land Z.lor Z.log2_up Z.abs];
  repeat match goal with
         | _ => auto_split_prod_step special_ring_intros_tac
         | [ |- @eq Z _ _ ] => ring
         end.

Ltac default_ring_intros_tac _ := fail.

Ltac Zring_prod_eq_tac _ := Zring_prod_eq_tac_gen default_ring_intros_tac.

Ltac autosolve_gen_intros special_ring_intros_tac else_tac :=
  lazymatch goal with
  | [ |- eq_by_Zring_prod_package _ ]
    => abstract Zring_prod_eq_tac_gen special_ring_intros_tac
  | _ => else_tac ()
  end.

Ltac autosolve else_tac := autosolve_gen_intros default_ring_intros_tac else_tac.
