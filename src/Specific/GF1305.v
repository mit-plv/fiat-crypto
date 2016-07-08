Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemInterface.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.
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
  apply Build_SubtractionCoefficient with (coeff := mul2modulus); cbv; auto.
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

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Let_In.

Definition mul (f g:fe1305) : { fg | fg = @ModularBaseSystemInterface.mul _ _ k_ c_ f g }.
  (* NOTE: beautiful example of reduction slowness: stack overflow if [f] [g] are not destructed first *)
  cbv [fe1305] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  eexists.
  cbv.
  autorewrite with zsimplify.
  reflexivity.
Defined.

(*
Local Transparent Let_In.
Eval cbv iota beta delta [proj1_sig mul Let_In] in (fun f0 f1 f2 f3 f4  g0 g1 g2 g3 g4 => proj1_sig (mul (f4,f3,f2,f1,f0) (g4,g3,g2,g1,g0))).
*)

Local Open Scope nat_scope.
Lemma GF1305Base26_mul_reduce_formula :
  forall f0 f1 f2 f3 f4 g0 g1 g2 g3 g4,
    {ls | forall f g, rep [f0;f1;f2;f3;f4] f
                      -> rep [g0;g1;g2;g3;g4] g
                      -> rep ls (f*g)%F}.
Proof.
  eexists; intros ? ? Hf Hg.
  pose proof (carry_mul_opt_rep k_ c_ (eq_refl k) c_subst _ _ _ _ Hf Hg) as Hfg.
  compute_formula.
  exact Hfg.
Defined.

Lemma GF1305Base26_add_formula :
  forall f0 f1 f2 f3 f4 g0 g1 g2 g3 g4,
    {ls | forall f g, rep [f0;f1;f2;f3;f4] f
                   -> rep [g0;g1;g2;g3;g4] g
                   -> rep ls (f + g)%F}.
Proof.
  eexists; intros ? ? Hf Hg.
  pose proof (add_opt_rep _ _ _ _ Hf Hg) as Hfg.
  compute_formula.
  exact Hfg.
Defined.

Lemma GF1305Base26_sub_formula :
  forall f0 f1 f2 f3 f4 g0 g1 g2 g3 g4,
    {ls | forall f g, rep [f0;f1;f2;f3;f4] f
                   -> rep [g0;g1;g2;g3;g4] g
                   -> rep ls (f - g)%F}.
Proof.
  eexists.
  intros f g Hf Hg.
  pose proof (sub_opt_rep _ _ _ _ Hf Hg) as Hfg.
  compute_formula.
  exact Hfg.
Defined.

Lemma GF1305Base26_freeze_formula :
  forall f0 f1 f2 f3 f4,
    {ls | forall x, rep [f0;f1;f2;f3;f4] x
                 -> rep ls x}.
Proof.
  eexists.
  intros x Hf.
  pose proof (freeze_opt_preserves_rep _ c_subst freezePreconditions1305 _ _ Hf) as Hfreeze_rep.
  compute_formula.
  exact Hfreeze_rep.
Defined.
