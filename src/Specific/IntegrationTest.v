Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Notations Crypto.Util.ZRange.
Import ListNotations.

Section Pre.
  Definition BoundedWord n (bitwidth : nat)
             (bounds : tuple zrange n) : Type :=
    { x : tuple (wordT bitwidth) n
    | is_bounded_by (Some (Z.of_nat bitwidth)) bounds
                    (map wordToZ x)}.

  Definition BoundedWordToZ n w b (BW :BoundedWord n w b)
    : tuple Z n :=  map wordToZ (proj1_sig BW).
End Pre.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 10)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
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
  Definition mul :
    { mul : feBW -> feBW -> feBW
    | forall a b, phi (mul a b) = (phi a * phi b)%F }.
  Proof.
    eexists ?[mul]; intros. cbv [phi].
    rewrite <- (proj2_sig mul_sig).
    set (mulZ := proj1_sig mul_sig).
    cbv beta iota delta [proj1_sig mul_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr] in mulZ.
    apply f_equal.
    (* jgross start here! *)

  Admitted.

End BoundedField25p5.
