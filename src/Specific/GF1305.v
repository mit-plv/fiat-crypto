Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseRep.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

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
Definition c_subst : c = c_ := eq_refl c_.

(* Makes Qed not take forever *)
Opaque Z.shiftr Pos.iter Z.div2 Pos.div2 Pos.div2_up Pos.succ Z.land
  Z.of_N Pos.land N.ldiff Pos.pred_N Pos.pred_double Z.opp Z.mul Pos.mul
  Let_In digits Z.add Pos.add Z.pos_sub andb Z.eqb Z.ltb.

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
