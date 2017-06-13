(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [list ℤ].  We follow
    "Fast Prime Field Elliptic Curve Cryptography with 256 Bit
    Primes", https://eprint.iacr.org/2013/816.pdf. *)
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Definition.

Section redc.
  (** XXX TODO: Figure out how to fill in these context variables *)
  Context {mul_split : Z -> Z -> Z -> Z * Z} (* first argument is where to split output; [mul_split s x y] gives ((x * y) mod s, (x * y) / s) *).

  (** XXX TODO: pick better names for the arguments to this definition. *)
  Definition redc {r : positive} {R_numlimbs : nat} (N A B : T) (k : Z) : T
    := @redc T numlimbs zero divmod r (@scmul (Z.pos r) mul_split) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N A B k.
End redc.
