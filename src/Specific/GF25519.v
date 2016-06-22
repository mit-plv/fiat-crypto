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

Definition modulus : Z := 2^255 - 19.
Lemma prime_modulus : prime modulus. Admitted.
Definition int_width := 32%Z.

Instance params25519 : PseudoMersenneBaseParams modulus.
  construct_params prime_modulus 10%nat 255.
Defined.

Definition mul2modulus := Eval compute in (construct_mul2modulus params25519).

Instance subCoeff : SubtractionCoefficient modulus params25519.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus); cbv; auto.
Defined.

Definition freezePreconditions25519 : freezePreconditions params25519 int_width.
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
Lemma GF25519Base25Point5_mul_reduce_formula :
  forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
    {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                      -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                      -> rep ls (f*g)%F}.
Proof.
  eexists; intros ? ? Hf Hg.
  pose proof (carry_mul_opt_rep k_ c_ (eq_refl k_) c_subst _ _ _ _ Hf Hg) as Hfg.
  compute_formula.
  exact Hfg.
(*Time*) Defined.

(* Uncomment this to see a pretty-printed mulmod
Local Transparent Let_In.
Infix "<<" := Z.shiftr (at level 50).
Infix "&" := Z.land (at level 50).
Eval cbv beta iota delta [proj1_sig GF25519Base25Point5_mul_reduce_formula Let_In] in
  fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 => proj1_sig (
    GF25519Base25Point5_mul_reduce_formula f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
                                           g0 g1 g2 g3 g4 g5 g6 g7 g8 g9).
Local Opaque Let_In.
*)


Extraction "/tmp/test.ml" GF25519Base25Point5_mul_reduce_formula.
(* It's easy enough to use extraction to get the proper nice-looking formula.
 * More Ltac acrobatics will be needed to get out that formula for further use in Coq.
 * The easiest fix will be to make the proof script above fully automated,
 * using [abstract] to contain the proof part. *)


Lemma GF25519Base25Point5_add_formula :
  forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
    {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                   -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                   -> rep ls (f + g)%F}.
Proof.
  eexists.
  intros f g Hf Hg.
  pose proof (add_opt_rep _ _ _ _ Hf Hg) as Hfg.
  compute_formula.
  exact Hfg.
Defined.

Lemma GF25519Base25Point5_sub_formula :
  forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
    {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                   -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                   -> rep ls (f - g)%F}.
Proof.
  eexists.
  intros f g Hf Hg.
  pose proof (sub_opt_rep _ _ _ _ Hf Hg) as Hfg.
  compute_formula.
  exact Hfg.
Defined.

Lemma GF25519Base25Point5_freeze_formula :
  forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9,
    {ls | forall x, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] x
                 -> rep ls x}.
Proof.
  eexists.
  intros x Hf.
  pose proof (freeze_opt_preserves_rep _ c_subst freezePreconditions25519 _ _ Hf) as Hfreeze_rep.
  compute_formula.
  exact Hfreeze_rep.
Defined.

(* Uncomment the below to see pretty-printed freeze function *)
(*
Set Printing Depth 1000.
Local Transparent Let_In.
Infix "<<" := Z.shiftr (at level 50).
Infix "&" := Z.land (at level 50).
Eval cbv beta iota delta [proj1_sig GF25519Base25Point5_freeze_formula Let_In] in
  fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 => proj1_sig (
    GF25519Base25Point5_freeze_formula f0 f1 f2 f3 f4 f5 f6 f7 f8 f9).
*)