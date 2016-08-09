Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.ModularBaseSystemField.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
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

Definition fe1305 := Eval compute in (tuple Z (length limb_widths)).

Definition mul2modulus : fe1305 :=
  Eval compute in (from_list_default 0%Z (length limb_widths) (construct_mul2modulus params1305)).

Instance subCoeff : SubtractionCoefficient modulus params1305.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus).
  vm_decide.
Defined.

Instance carryChain : CarryChain limb_widths.
  apply Build_CarryChain with (carry_chain := ([0;1;2;3;4;0])%nat).
  intros;
    repeat (destruct H as [|H]; [subst; vm_compute; repeat constructor | ]).
  contradiction H.
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

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Let_In.

Definition app_5 (f : fe1305) (P : fe1305 -> fe1305) : fe1305.
Proof.
  cbv [fe1305] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Definition app_5_correct f (P : fe1305 -> fe1305) : app_5 f P = P f.
Proof.
  intros.
  cbv [fe1305] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  reflexivity.
Qed.

Definition appify2 (op : fe1305 -> fe1305 -> fe1305) (f g : fe1305):= 
  app_5 f (fun f0 => (app_5 g (fun g0 => op f0 g0))).

Lemma appify2_correct : forall op f g, appify2 op f g = op f g.
Proof.
  intros. cbv [appify2].
  etransitivity; apply app_5_correct.
Qed.

Definition add_sig (f g : fe1305) :
  { fg : fe1305 | fg = add_opt f g}.
Proof.
  eexists.
  rewrite <-appify2_correct.
  cbv.
  reflexivity.
Defined.

Definition add (f g : fe1305) : fe1305 :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj1_sig (add_sig f g).

Definition add_correct (f g : fe1305)
  : add f g = add_opt f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (add_sig f g).

Definition sub_sig (f g : fe1305) :
  { fg : fe1305 | fg = sub_opt f g}.
Proof.
  eexists.
  rewrite <-appify2_correct.
  cbv.
  reflexivity.
Defined.

Definition sub (f g : fe1305) : fe1305 :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj1_sig (sub_sig f g).

Definition sub_correct (f g : fe1305)
  : sub f g = sub_opt f g :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj2_sig (sub_sig f g).

(* For multiplication, we add another layer of definition so that we can
   rewrite under the [let] binders. *)
Definition mul_simpl_sig (f g : fe1305) :
  { fg : fe1305 | fg = carry_mul_opt k_ c_ f g}.
Proof.
  cbv [fe1305] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv.
  autorewrite with zsimplify.
  reflexivity.
Defined.

Definition mul_simpl (f g : fe1305) : fe1305 :=
  Eval cbv beta iota delta [proj1_sig mul_simpl_sig] in
  proj1_sig (mul_simpl_sig f g).

Definition mul_simpl_correct (f g : fe1305)
  : mul_simpl f g = carry_mul_opt k_ c_ f g :=
  Eval cbv beta iota delta [proj1_sig mul_simpl_sig] in
  proj2_sig (mul_simpl_sig f g).

Definition mul_sig (f g : fe1305) :
  { fg : fe1305 | fg = carry_mul_opt k_ c_ f g}.
Proof.
  eexists.
  rewrite <-mul_simpl_correct.
  rewrite <-appify2_correct.
  cbv.
  reflexivity.
Defined.

Definition mul (f g : fe1305) : fe1305 :=
  Eval cbv beta iota delta [proj1_sig mul_sig] in
    proj1_sig (mul_sig f g).

Definition mul_correct (f g : fe1305)
  : mul f g = carry_mul_opt k_ c_ f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (mul_sig f g).

Import Morphisms.

Lemma field1305 : @field fe1305 eq zero one opp add sub mul inv div.
Proof.
  pose proof (Equivalence_Reflexive : Reflexive eq).
  eapply (Field.equivalent_operations_field (fieldR := modular_base_system_field k_ c_ k_subst c_subst)).
  Grab Existential Variables.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros; rewrite mul_correct. reflexivity.
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
