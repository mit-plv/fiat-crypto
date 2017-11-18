Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.AdmitPackage.
Require Import Crypto.Util.SideConditions.ModInvPackage.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Util.SideConditions.RingPackage.

Ltac autosolve_gen autosolve_tac ring_intros_tac else_tac :=
  CorePackages.preautosolve ();
  CorePackages.Internal.autosolve ltac:(fun _ =>
  AdmitPackage.autosolve ltac:(fun _ =>
  ModInvPackage.autosolve ltac:(fun _ =>
  ReductionPackages.autosolve autosolve_tac ltac:(fun _ =>
  RingPackage.autosolve_gen_intros ring_intros_tac ltac:(fun _ =>
  CorePackages.autosolve else_tac
                                       ))))).

Ltac autosolve_gen_intros ring_intros_tac else_tac :=
  autosolve_gen ltac:(autosolve_gen_intros ring_intros_tac) ring_intros_tac else_tac.

Ltac autosolve else_tac := autosolve_gen_intros default_ring_intros_tac else_tac.
