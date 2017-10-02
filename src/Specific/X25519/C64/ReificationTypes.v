Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.

Section BoundedField.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := P.upper_bound_of_exponent exp |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
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

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Definition feW : Type := Eval cbv [lgbitwidth] in tuple (wordT lgbitwidth) sz.
  Definition feW_bounded : feW -> Prop
    := Eval cbv [bounds] in fun w => is_bounded_by None bounds (map wordToZ w).
  Definition feBW : Type := Eval cbv [bitwidth bounds] in BoundedWord sz bitwidth bounds.

  Lemma feBW_bounded (a : feBW)
    : 0 <= B.Positional.eval wt (BoundedWordToZ sz bitwidth bounds a) < 2 * Z.pos m.
  Proof.
    destruct a as [a H]; unfold BoundedWordToZ, proj1_sig.
    revert H.
    cbv -[Z.le Z.add Z.mul Z.lt fst snd wordToZ wt]; cbn [fst snd].
    repeat match goal with
           | [ |- context[wt ?n] ]
             => let v := (eval compute in (wt n)) in change (wt n) with v
           end.
    intro; destruct_head'_and.
    omega.
  Qed.
End BoundedField.
