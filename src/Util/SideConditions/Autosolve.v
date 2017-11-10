Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Util.SideConditions.RingPackage.

Ltac autosolve_gen autosolve_tac else_tac :=
  CorePackages.preautosolve ();
  CorePackages.Internal.autosolve ltac:(fun _ =>
  ReductionPackages.autosolve autosolve_tac ltac:(fun _ =>
  RingPackage.autosolve ltac:(fun _ =>
  CorePackages.autosolve else_tac
                                       ))).

Ltac autosolve else_tac :=
  autosolve_gen autosolve else_tac.
