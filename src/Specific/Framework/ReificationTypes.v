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

Ltac pose_limb_widths wt sz limb_widths :=
  pose_term_with
    ltac:(fun _ => (eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz))))
           limb_widths.

Ltac get_b_of upper_bound_of_exponent :=
  constr:(fun exp => {| lower := 0 ; upper := upper_bound_of_exponent exp |}%Z). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)

(* The definition [bounds_exp] is a tuple-version of the limb-widths,
   which are the [exp] argument in [b_of] above, i.e., the approximate
   base-2 exponent of the bounds on the limb in that position. *)
Ltac pose_bounds_exp sz limb_widths bounds_exp :=
  pose_term_with_type
    (Tuple.tuple Z sz)
    ltac:(fun _ => eval compute in
               (Tuple.from_list sz limb_widths eq_refl))
           bounds_exp.

Ltac pose_bounds sz b_of bounds_exp bounds :=
  pose_term_with_type
    (Tuple.tuple zrange sz)
    ltac:(fun _ => eval compute in
               (Tuple.map (fun e => b_of e) bounds_exp))
           bounds.

Ltac pose_lgbitwidth limb_widths lgbitwidth :=
  pose_term_with
    ltac:(fun _ => eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))))
           lgbitwidth.

Ltac pose_bitwidth lgbitwidth bitwidth :=
  pose_term_with
    ltac:(fun _ => eval compute in (2^lgbitwidth)%nat)
           bitwidth.

Ltac pose_feZ sz feZ :=
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
Ltac pose_feBW sz bitwidth bounds feBW :=
  cache_term_with_type_by
    Type
    ltac:(let v := eval cbv [bitwidth bounds] in (BoundedWord sz bitwidth bounds) in exact v)
           feBW.

Lemma feBW_bounded_helper'
      sz bitwidth bounds
      (feBW := BoundedWord sz bitwidth bounds)
      (wt : nat -> Z)
      (Hwt : forall i, 0 <= wt i)
  : forall (a : feBW),
    B.Positional.eval wt (map lower bounds)
    <= B.Positional.eval wt (BoundedWordToZ sz bitwidth bounds a)
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
      sz bitwidth bounds
      (feBW := BoundedWord sz bitwidth bounds)
      (wt : nat -> Z)
      (Hwt : forall i, 0 <= wt i)
      l u
  : l <= B.Positional.eval wt (map lower bounds)
    /\ B.Positional.eval wt (map upper bounds) < u
    -> forall (a : feBW),
      l <= B.Positional.eval wt (BoundedWordToZ sz bitwidth bounds a) < u.
Proof.
  intros [Hl Hu] a; split;
    [ eapply Z.le_trans | eapply Z.le_lt_trans ];
    [ | eapply feBW_bounded_helper' | eapply feBW_bounded_helper' | ];
    assumption.
Qed.

Ltac pose_feBW_bounded wt sz feBW bitwidth bounds m wt_nonneg feBW_bounded :=
  cache_proof_with_type_by
    (forall a : feBW, 0 <= B.Positional.eval wt (BoundedWordToZ sz bitwidth bounds a) < 2 * Z.pos m)
    ltac:(apply (@feBW_bounded_helper sz bitwidth bounds wt wt_nonneg);
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

Ltac get_ReificationTypes_package wt sz m wt_nonneg upper_bound_of_exponent :=
  let limb_widths := fresh "limb_widths" in
  let bounds_exp := fresh "bounds_exp" in
  let bounds := fresh "bounds" in
  let lgbitwidth := fresh "lgbitwidth" in
  let bitwidth := fresh "bitwidth" in
  let feZ := fresh "feZ" in
  let feW := fresh "feW" in
  let feW_bounded := fresh "feW_bounded" in
  let feBW := fresh "feBW" in
  let feBW_bounded := fresh "feBW_bounded" in
  let phiW := fresh "phiW" in
  let phiBW := fresh "phiBW" in
  let limb_widths := pose_limb_widths wt sz limb_widths in
  let b_of := get_b_of upper_bound_of_exponent in
  let bounds_exp := pose_bounds_exp sz limb_widths bounds_exp in
  let bounds := pose_bounds sz b_of bounds_exp bounds in
  let lgbitwidth := pose_lgbitwidth limb_widths lgbitwidth in
  let bitwidth := pose_bitwidth lgbitwidth bitwidth in
  let feZ := pose_feZ sz feZ in
  let feW := pose_feW sz lgbitwidth feW in
  let feW_bounded := pose_feW_bounded feW bounds feW_bounded in
  let feBW := pose_feBW sz bitwidth bounds feBW in
  let feBW_bounded := pose_feBW_bounded wt sz feBW bitwidth bounds m wt_nonneg feBW_bounded in
  let phiW := pose_phiW feW m wt phiW in
  let phiBW := pose_phiBW feBW m wt phiBW in
  constr:((feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW)).
Ltac make_ReificationTypes_package wt sz m wt_nonneg upper_bound_of_exponent :=
  lazymatch goal with
  | [ |- { T : _ & T } ] => eexists
  | [ |- _ ] => idtac
  end;
  let pkg := get_ReificationTypes_package wt sz m wt_nonneg upper_bound_of_exponent in
  exact pkg.

Module Type ReificationTypesPrePackage.
  Parameter ReificationTypes_package' : { T : _ & T }.
  Parameter ReificationTypes_package : projT1 ReificationTypes_package'.
End ReificationTypesPrePackage.

Module MakeReificationTypes (RP : ReificationTypesPrePackage).
  Ltac get_ReificationTypes_package _ := eval hnf in RP.ReificationTypes_package.
  Ltac RT_reduce_proj x :=
    eval cbv beta iota zeta in x.
  (**
<<
terms = 'feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW'
for i in terms.split(', '):
    print("  Ltac get_%s _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(%s) := pkg in %s)." % (i, terms, i))
    print("  Notation %s := (ltac:(let v := get_%s () in exact v)) (only parsing)." % (i, i))
>> *)
  Ltac get_feZ _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW) := pkg in feZ).
  Notation feZ := (ltac:(let v := get_feZ () in exact v)) (only parsing).
  Ltac get_feW _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW) := pkg in feW).
  Notation feW := (ltac:(let v := get_feW () in exact v)) (only parsing).
  Ltac get_feW_bounded _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW) := pkg in feW_bounded).
  Notation feW_bounded := (ltac:(let v := get_feW_bounded () in exact v)) (only parsing).
  Ltac get_feBW _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW) := pkg in feBW).
  Notation feBW := (ltac:(let v := get_feBW () in exact v)) (only parsing).
  Ltac get_feBW_bounded _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW) := pkg in feBW_bounded).
  Notation feBW_bounded := (ltac:(let v := get_feBW_bounded () in exact v)) (only parsing).
  Ltac get_phiW _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW) := pkg in phiW).
  Notation phiW := (ltac:(let v := get_phiW () in exact v)) (only parsing).
  Ltac get_phiBW _ := let pkg := get_ReificationTypes_package () in RT_reduce_proj (let '(feZ, feW, feW_bounded, feBW, feBW_bounded, phiW, phiBW) := pkg in phiBW).
  Notation phiBW := (ltac:(let v := get_phiBW () in exact v)) (only parsing).
End MakeReificationTypes.
