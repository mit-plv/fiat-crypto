Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.ModularBaseSystemInterface.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Require Import Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Crypto.Util.Notations.
Local Open Scope Z.

(* BEGIN PseudoMersenneBaseParams instance construction. *)

Definition modulus : Z := 2^255 - 19.
Lemma prime_modulus : prime modulus. Admitted.
Definition int_width := 32%Z.

Instance params25519 : PseudoMersenneBaseParams modulus.
  construct_params prime_modulus 10%nat 255.
Defined.

Definition mul2modulus := Eval compute in (construct_mul2modulus params25519).

Instance subCoeff : SubtractionCoefficient modulus params25519.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus).
  cbv; auto.
  cbv [ModularBaseSystem.decode].
  apply ZToField_eqmod.
  cbv; reflexivity.
Defined.

Definition freezePreconditions25519 : freezePreconditions params25519 int_width.
Proof.
  constructor; compute_preconditions.
Defined.

(* END PseudoMersenneBaseParams instance construction. *)

(* Precompute k and c *)
Definition k_ := Eval compute in k.
Definition c_ := Eval compute in c.
Definition k_subst : k = k_ := eq_refl k_.
Definition c_subst : c = c_ := eq_refl c_.
Definition fe25519 : Type := Eval cbv in fe.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Let_In.

Definition add_sig (f g : fe25519) :
  { fg : fe25519 | fg = ModularBaseSystemInterface.add f g}.
Proof.
  cbv [fe25519] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  eexists.
  cbv.
  reflexivity.
Defined.

Definition add (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  let '(f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) := f in
  let '(g0,g1,g2,g3,g4,g5,g6,g7,g8,g9) := g in
  proj1_sig (add_sig (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) (g0,g1,g2,g3,g4,g5,g6,g7,g8,g9)).

Definition add_correct (f g : fe25519)
  : add f g = ModularBaseSystemInterface.add f g :=
  let '(f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) := f in
  let '(g0,g1,g2,g3,g4,g5,g6,g7,g8,g9) := g in
  proj2_sig (add_sig (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) (g0,g1,g2,g3,g4,g5,g6,g7,g8,g9)).

Definition sub_sig (f g : fe25519) :
  { fg : fe25519 | fg = ModularBaseSystemInterface.sub f g}.
Proof.
  cbv [fe25519] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  eexists.
  cbv.
  reflexivity.
Defined.

Definition sub (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  let '(f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) := f in
  let '(g0,g1,g2,g3,g4,g5,g6,g7,g8,g9) := g in
  proj1_sig (sub_sig (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) (g0,g1,g2,g3,g4,g5,g6,g7,g8,g9)).

Definition sub_correct (f g : fe25519)
  : sub f g = ModularBaseSystemInterface.sub f g :=
  let '(f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) := f in
  let '(g0,g1,g2,g3,g4,g5,g6,g7,g8,g9) := g in
  proj2_sig (sub_sig (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) (g0,g1,g2,g3,g4,g5,g6,g7,g8,g9)).

Definition mul_sig (f g : fe25519) :
  { fg : fe25519 | fg = ModularBaseSystemInterface.mul (k_ := k_) (c_ := c_) f g}.
Proof.
  cbv [fe25519] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  eexists.
  cbv.
  autorewrite with zsimplify.
  reflexivity.
Defined.

Definition mul (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_sig] in
  let '(f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) := f in
  let '(g0,g1,g2,g3,g4,g5,g6,g7,g8,g9) := g in
  proj1_sig (mul_sig (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) (g0,g1,g2,g3,g4,g5,g6,g7,g8,g9)).

Definition mul_correct (f g : fe25519)
  : mul f g = ModularBaseSystemInterface.mul (k_ := k_) (c_ := c_) f g :=
  let '(f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) := f in
  let '(g0,g1,g2,g3,g4,g5,g6,g7,g8,g9) := g in
  proj2_sig (mul_sig (f0,f1,f2,f3,f4,f5,f6,f7,f8,f9) (g0,g1,g2,g3,g4,g5,g6,g7,g8,g9)).

Import Morphisms.

Lemma field25519 : @field fe25519 eq zero one opp add sub mul inv div.
Proof.
  pose proof (Equivalence_Reflexive : Reflexive eq).
  eapply (Field.equivalent_operations_field (fieldR := modular_base_system_field k_subst c_subst)).
  Grab Existential Variables.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros; rewrite mul_correct; reflexivity.
  + intros; rewrite sub_correct; reflexivity.
  + intros; rewrite add_correct; reflexivity.
  + reflexivity.
  + reflexivity.
Qed.


(*
Local Transparent Let_In.
Eval cbv iota beta delta [proj1_sig mul Let_In] in (fun f0 f1 f2 f3 f4  g0 g1 g2 g3 g4 => proj1_sig (mul (f4,f3,f2,f1,f0) (g4,g3,g2,g1,g0))).
*)

(* TODO: This file should eventually contain the following operations:
   toBytes
   fromBytes
   inv
   opp
   sub
   zero
   one
   eq
*)