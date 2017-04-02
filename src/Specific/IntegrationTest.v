Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Import ListNotations.

Require Import Crypto.Reflection.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 10)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
  (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)
  Let bounds_exp : Tuple.tuple Z length_lw
    := Eval compute in
        Tuple.from_list length_lw limb_widths eq_refl.
  Let bounds : Tuple.tuple zrange length_lw
    := Eval compute in
        Tuple.map (fun e => b_of e) bounds_exp.

  Let feZ : Type := tuple Z 10.
  Let feW : Type := tuple word32 10.
  Let feBW : Type := BoundedWord 10 32 bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (* TODO : change this to field once field isomorphism happens *)
  Definition add :
    { add : feBW -> feBW -> feBW
    | forall a b, phi (add a b) = F.add (phi a) (phi b) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b, ?phi (f a b) = @?rhs a b } ]
      => apply lift2_sig with (P:=fun a b f => phi f = rhs a b)
    end.
    intros. eexists ?[add]. cbv [phi].
    rewrite <- (proj2_sig add_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_addZ := fun a b => proj1_sig carry_sig (proj1_sig add_sig a b)).
    change (proj1_sig carry_sig (proj1_sig add_sig ?a ?b)) with (carry_addZ a b).
    cbv beta iota delta [proj1_sig add_sig carry_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz] in carry_addZ.
    cbn beta iota delta [fst snd] in carry_addZ.
    apply f_equal.
    (* jgross start here! *)
    Set Ltac Profiling.
    Time refine_reflectively.
    Show Ltac Profile.
  Time Defined.

End BoundedField25p5.
