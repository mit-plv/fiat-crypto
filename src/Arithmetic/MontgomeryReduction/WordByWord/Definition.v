(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [list ℤ]. *)
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Definition.

Section redc.
  (** TODO: pick better names for the arguments to this definition. *)
  Definition redc_cps {r : positive} {R_numlimbs : nat} (N A B : T) (k : Z) {cpsT} (rest : T -> cpsT) : cpsT
    := @redc_cps T numlimbs zero divmod r (@scmul (Z.pos r)) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N A B k cpsT rest.
End redc.
