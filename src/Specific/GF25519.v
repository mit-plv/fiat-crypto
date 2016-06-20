Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseRep.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Require Import Crypto.Rep.
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

Definition F25519Rep := (Z * Z * Z * Z * Z  *  Z * Z * Z * Z * Z)%type.

Definition F25519toRep (x:F (2^255 - 19)) : F25519Rep := (0, 0, 0, 0, 0,  0, 0, 0, 0, FieldToZ x)%Z.
Definition F25519unRep (rx:F25519Rep) :=
  let '(x9, x8, x7, x6, x5, x4, x3, x2, x1, x0) := rx in
                ModularBaseSystem.decode [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9].

Global Instance F25519RepConversions : RepConversions (F (2^255 - 19)) F25519Rep :=
  {
    toRep := F25519toRep;
    unRep := F25519unRep
  }.

Lemma F25519RepConversionsOK : RepConversionsOK F25519RepConversions.
Proof.
  unfold F25519RepConversions, RepConversionsOK, unRep, toRep, F25519toRep, F25519unRep; intros.
  change (ModularBaseSystem.decode (ModularBaseSystem.encode x) = x).
  eauto using ModularBaseSystemProofs.rep_decode, ModularBaseSystemProofs.encode_rep.
Qed.

Definition F25519Rep_mul (f g:F25519Rep) : F25519Rep.
  refine (
  let '(f9, f8, f7, f6, f5, f4, f3, f2, f1, f0) := f in
  let '(g9, g8, g7, g6, g5, g4, g3, g2, g1, g0) := g in _).
  (* FIXME: the r should not be present in generated code *)
  pose (r := proj1_sig (GF25519Base25Point5_mul_reduce_formula f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
                                                             g0 g1 g2 g3 g4 g5 g6 g7 g8 g9)).
  simpl in r.
  unfold F25519Rep.
  repeat let t' := (eval cbv beta delta [r] in r) in
    lazymatch t' with Let_In ?arg ?f =>
                      let x := fresh "x" in
                      refine (let x := arg in _);
                        let t'' := (eval cbv beta in (f x)) in
                        change (Let_In arg f) with t'' in r
    end.
  let t' := (eval cbv beta delta [r] in r) in
  lazymatch t' with [?r0;?r1;?r2;?r3;?r4;?r5;?r6;?r7;?r8;?r9] =>
                    clear r;
                    exact (r9, r8, r7, r6, r5, r4, r3, r2, r1, r0)
  end.
(*Time*) Defined.

Lemma F25519_mul_OK : RepBinOpOK F25519RepConversions ModularArithmetic.mul F25519Rep_mul.
  cbv iota beta delta [RepBinOpOK F25519RepConversions F25519Rep_mul toRep unRep F25519toRep F25519unRep].
  destruct x as [[[[[[[[[x9 x8] x7] x6] x5] x4] x3] x2] x1] x0].
  destruct y as [[[[[[[[[y9 y8] y7] y6] y5] y4] y3] y2] y1] y0].
  let E := constr:(GF25519Base25Point5_mul_reduce_formula x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) in
  transitivity (ModularBaseSystem.decode (proj1_sig E)); [|solve[simpl; apply f_equal; reflexivity]];
    destruct E as [? r]; cbv [proj1_sig].
  cbv [rep ModularBaseSystem.rep PseudoMersenneBase modulus] in r; edestruct r; eauto.
Qed.

Definition F25519Rep_add (f g:F25519Rep) : F25519Rep.
  refine (
  let '(f9, f8, f7, f6, f5, f4, f3, f2, f1, f0) := f in
  let '(g9, g8, g7, g6, g5, g4, g3, g2, g1, g0) := g in _).
  let t' := (eval simpl in (proj1_sig (GF25519Base25Point5_add_formula f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
                                                                       g0 g1 g2 g3 g4 g5 g6 g7 g8 g9))) in
  lazymatch t' with [?r0;?r1;?r2;?r3;?r4;?r5;?r6;?r7;?r8;?r9] =>
                    exact (r9, r8, r7, r6, r5, r4, r3, r2, r1, r0)
  end.
Defined.

Definition F25519Rep_sub (f g:F25519Rep) : F25519Rep.
  refine (
  let '(f9, f8, f7, f6, f5, f4, f3, f2, f1, f0) := f in
  let '(g9, g8, g7, g6, g5, g4, g3, g2, g1, g0) := g in _).
  let t' := (eval simpl in (proj1_sig (GF25519Base25Point5_sub_formula f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
                                                                       g0 g1 g2 g3 g4 g5 g6 g7 g8 g9))) in
  lazymatch t' with [?r0;?r1;?r2;?r3;?r4;?r5;?r6;?r7;?r8;?r9] =>
                    exact (r9, r8, r7, r6, r5, r4, r3, r2, r1, r0)
  end.
Defined.

Lemma F25519_add_OK : RepBinOpOK F25519RepConversions ModularArithmetic.add F25519Rep_add.
  cbv iota beta delta [RepBinOpOK F25519RepConversions F25519Rep_add toRep unRep F25519toRep F25519unRep].
  destruct x as [[[[[[[[[x9 x8] x7] x6] x5] x4] x3] x2] x1] x0].
  destruct y as [[[[[[[[[y9 y8] y7] y6] y5] y4] y3] y2] y1] y0].
  let E := constr:(GF25519Base25Point5_add_formula x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) in
  transitivity (ModularBaseSystem.decode (proj1_sig E)); [|solve[simpl; apply f_equal; reflexivity]];
    destruct E as [? r]; cbv [proj1_sig].
  cbv [rep ModularBaseSystem.rep PseudoMersenneBase modulus] in r; edestruct r; eauto.
Qed.

Lemma F25519_sub_OK : RepBinOpOK F25519RepConversions ModularArithmetic.sub F25519Rep_sub.
  cbv iota beta delta [RepBinOpOK F25519RepConversions F25519Rep_sub toRep unRep F25519toRep F25519unRep].
  destruct x as [[[[[[[[[x9 x8] x7] x6] x5] x4] x3] x2] x1] x0].
  destruct y as [[[[[[[[[y9 y8] y7] y6] y5] y4] y3] y2] y1] y0].
  let E := constr:(GF25519Base25Point5_sub_formula x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) in
  transitivity (ModularBaseSystem.decode (proj1_sig E)); [|solve[simpl; apply f_equal; reflexivity]];
    destruct E as [? r]; cbv [proj1_sig].
  cbv [rep ModularBaseSystem.rep PseudoMersenneBase modulus] in r; edestruct r; eauto.
Qed.
