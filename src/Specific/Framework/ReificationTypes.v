Require Import Coq.ZArith.ZArith.
Require Import Coq.romega.ROmega.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Decidable.

Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.

Ltac pose_local_limb_widths wt sz limb_widths :=
  pose_term_with
    ltac:(fun _ => (eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz))))
           limb_widths.

Ltac get_b_of upper_bound_of_exponent :=
  constr:(fun exp => {| lower := 0 ; upper := upper_bound_of_exponent exp |}%Z). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)

(* The definition [bounds_exp] is a tuple-version of the limb-widths,
   which are the [exp] argument in [b_of] above, i.e., the approximate
   base-2 exponent of the bounds on the limb in that position. *)
Ltac pose_local_bounds_exp sz limb_widths bounds_exp :=
  pose_term_with_type
    (Tuple.tuple Z sz)
    ltac:(fun _ => eval compute in
               (Tuple.from_list sz limb_widths eq_refl))
           bounds_exp.

Ltac pose_local_bounds sz upper_bound_of_exponent bounds_exp bounds :=
  let b_of := get_b_of upper_bound_of_exponent in
  pose_term_with_type
    (Tuple.tuple zrange sz)
    ltac:(fun _ => eval compute in
               (Tuple.map (fun e => b_of e) bounds_exp))
           bounds.

Ltac pose_bound1 r bound1 :=
  cache_term_with_type_by
    zrange
    ltac:(exact {| lower := 0 ; upper := Z.pos r-1 |})
           bound1.

Ltac pose_local_lgbitwidth limb_widths lgbitwidth :=
  pose_term_with
    ltac:(fun _ => eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))))
           lgbitwidth.

Ltac pose_local_adjusted_bitwidth' lgbitwidth adjusted_bitwidth' :=
  pose_term_with
    ltac:(fun _ => eval compute in (2^lgbitwidth)%nat)
           adjusted_bitwidth'.
Ltac pose_adjusted_bitwidth adjusted_bitwidth' adjusted_bitwidth :=
  cache_term adjusted_bitwidth' adjusted_bitwidth.

Ltac pose_local_feZ sz feZ :=
  pose_term_with
    ltac:(fun _ => constr:(tuple Z sz))
           feZ.

Ltac pose_feW sz lgbitwidth feW :=
  cache_term_with_type_by
    Type
    ltac:(let v := eval cbv [lgbitwidth] in (tuple (wordT lgbitwidth) sz) in exact v)
           feW.
Ltac pose_feW_bounded feW bounds feW_bounded :=
  cache_term_with_type_by
    (feW -> Prop)
    ltac:(let v := eval cbv [bounds] in (fun w : feW => is_bounded_by None bounds (map wordToZ w)) in exact_no_check v)
           feW_bounded.
Ltac pose_feBW sz adjusted_bitwidth' bounds feBW :=
  cache_term_with_type_by
    Type
    ltac:(let v := eval cbv [adjusted_bitwidth' bounds] in (BoundedWord sz adjusted_bitwidth' bounds) in exact v)
           feBW.

Lemma feBW_bounded_helper'
      sz adjusted_bitwidth' bounds
      (feBW := BoundedWord sz adjusted_bitwidth' bounds)
      (wt : nat -> Z)
      (Hwt : forall i, 0 <= wt i)
  : forall (a : feBW),
    B.Positional.eval wt (map lower bounds)
    <= B.Positional.eval wt (BoundedWordToZ sz adjusted_bitwidth' bounds a)
    <= B.Positional.eval wt (map upper bounds).
Proof.
  let a := fresh "a" in
  intro a;
    destruct a as [a H]; unfold BoundedWordToZ, proj1_sig.
  destruct sz as [|sz].
  { cbv -[Z.le Z.lt Z.mul]; lia. }
  { cbn [tuple map] in *.
    revert dependent wt; induction sz as [|sz IHsz]; intros.
    { cbv -[Z.le Z.lt wordToZ Z.mul Z.pow Z.add lower upper Nat.log2 wordT] in *.
      repeat match goal with
             | [ |- context[@wordToZ ?n ?x] ]
               => generalize dependent (@wordToZ n x); intros
             | [ H : forall j, 0 <= wt j |- context[wt ?i] ]
               => pose proof (H i); generalize dependent (wt i); intros
             end.
      nia. }
    { pose proof (Hwt 0%nat).
      cbn [tuple' map'] in *.
      destruct a as [a' a], bounds as [bounds b], H as [H [H' _]].
      cbn [fst snd] in *.
      setoid_rewrite (@B.Positional.eval_step (S _)).
      specialize (IHsz bounds a' H (fun i => wt (S i)) (fun i => Hwt _)).
      nia. } }
Qed.
Lemma feBW_bounded_helper
      sz adjusted_bitwidth' bounds
      (feBW := BoundedWord sz adjusted_bitwidth' bounds)
      (wt : nat -> Z)
      (Hwt : forall i, 0 <= wt i)
      l u
  : l <= B.Positional.eval wt (map lower bounds)
    /\ B.Positional.eval wt (map upper bounds) < u
    -> forall (a : feBW),
      l <= B.Positional.eval wt (BoundedWordToZ sz adjusted_bitwidth' bounds a) < u.
Proof.
  intros [Hl Hu] a; split;
    [ eapply Z.le_trans | eapply Z.le_lt_trans ];
    [ | eapply feBW_bounded_helper' | eapply feBW_bounded_helper' | ];
    assumption.
Qed.

Ltac pose_feBW_bounded wt sz feBW adjusted_bitwidth' bounds m wt_nonneg feBW_bounded :=
  cache_proof_with_type_by
    (forall a : feBW, 0 <= B.Positional.eval wt (BoundedWordToZ sz adjusted_bitwidth' bounds a) < 2 * Z.pos m)
    ltac:(apply (@feBW_bounded_helper sz adjusted_bitwidth' bounds wt wt_nonneg);
          vm_compute; clear; split; congruence)
           feBW_bounded.

Ltac pose_phiW feW m wt phiW :=
  cache_term_with_type_by
    (feW -> F m)
    ltac:(exact (fun x : feW => B.Positional.Fdecode wt (Tuple.map wordToZ x)))
           phiW.
Ltac pose_phiBW feBW m wt phiBW :=
  cache_term_with_type_by
    (feBW -> F m)
    ltac:(exact (fun x : feBW => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x)))
           phiBW.
