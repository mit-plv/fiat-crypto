Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.ModularBaseSystemInterface.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.
Local Infix "<<" := Z.shiftr.
Local Infix "&" := Z.land.

(* BEGIN PseudoMersenneBaseParams instance construction. *)

Definition modulus : Z := 2^130 - 5.
Lemma prime_modulus : prime modulus. Admitted.
Definition int_width := 32%Z.

Instance params1305 : PseudoMersenneBaseParams modulus.
  construct_params prime_modulus 5%nat 130.
Defined.

Definition mul2modulus := Eval compute in (construct_mul2modulus params1305).

Instance subCoeff : SubtractionCoefficient modulus params1305.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus).
  cbv; auto.
  cbv [ModularBaseSystem.decode].
  apply ZToField_eqmod.
  cbv; reflexivity.
Defined.

Definition freezePreconditions1305 : freezePreconditions params1305 int_width.
Proof.
  constructor; compute_preconditions.
Defined.

(* END PseudoMersenneBaseParams instance construction. *)

(* Precompute k and c *)
Definition k_ := Eval compute in k.
Definition c_ := Eval compute in c.
Definition k_subst : k = k_ := eq_refl k_.
Definition c_subst : c = c_ := eq_refl c_.

Definition fe1305 : Type := Eval cbv in fe.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Let_In phi.

Definition add_formula (f g:fe1305) : { fg | phi fg = @ModularArithmetic.add modulus (phi f) (phi g) }.
Proof.
  cbv [fe1305] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  eexists.
  rewrite <-add_phi.
  cbv.
  apply f_equal.
  reflexivity.
Qed.
Definition add f g := proj1_sig (add_formula f g).

Definition sub_formula (f g:fe1305) : { fg | phi fg = @ModularArithmetic.sub modulus (phi f) (phi g) }.
Proof.
  cbv [fe1305] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  eexists.
  rewrite <-sub_phi.
  cbv.
  apply f_equal.
  reflexivity.
Qed.
Definition sub f g := proj1_sig (sub_formula f g).

Definition mul_formula (f g:fe1305) : { fg | phi fg = @ModularArithmetic.mul modulus (phi f) (phi g) }.
Proof.
  cbv [fe1305] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  eexists.
  rewrite <-(mul_phi (c_ := c_) (k_ := k_)) by auto using k_subst,c_subst.
  cbv.
  apply f_equal.
  autorewrite with zsimplify.
  repeat match goal with |- appcontext[?a * 1] => rewrite (Z.mul_1_r a) end.
  reflexivity.
Qed.
Definition mul f g := proj1_sig (mul_formula f g).

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
