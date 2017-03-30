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

  (* TODO(jgross) : what goes here? *)
  Let bounds: tuple zrange 10 := repeat (Build_zrange 0 (2^32)) 10.
  
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
    eexists; intros. cbv [phi].
    destruct mul_sig as [mulZ phi_mulZ].
    rewrite <-phi_mulZ.
    apply f_equal.
    (* jgross start here! *)
  Admitted.

End BoundedField25p5.