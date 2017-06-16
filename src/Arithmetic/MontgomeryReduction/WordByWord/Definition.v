(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [list ℤ].  See
    https://github.com/mit-plv/fiat-crypto/issues/157 for a discussion
    of the algorithm; note that it may be that none of the algorithms
    there exactly match what we're doing here. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Definition.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.

Local Open Scope Z_scope.

Section WordByWordMontgomery.
  Local Coercion Z.pos : positive >-> Z.
  (** TODO: pick better names for the arguments to this definition. *)
  Context
    {r : positive}
    {R_numlimbs : nat}
    (N : T).

  Definition redc_body_no_cps (B : T) (k : Z) (A_S : T * T) : T * T
    := @redc_body T divmod r (@scmul (Z.pos r)) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N B k A_S.
  Definition redc_loop_no_cps (B : T) (k : Z) (count : nat) (A_S : T * T) : T * T
    := @redc_loop T divmod r (@scmul (Z.pos r)) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N B k count A_S.
  Definition redc_no_cps (A B : T) (k : Z) : T
    := @redc T numlimbs zero divmod r (@scmul (Z.pos r)) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N A B k.

  Definition redc_body_cps (A B : T) (k : Z) (S' : T) {cpsT} (rest : T * T -> cpsT) : cpsT
    := divmod_cps A (fun '(A, a) =>
       @scmul_cps r a B _ (fun aB => @add_cps r S' aB _ (fun S1 =>
       divmod_cps S1 (fun '(_, s) =>
       dlet q := s * k mod r in
       @scmul_cps r q N _ (fun qN => @add_cps r S1 qN _ (fun S2 =>
       divmod_cps S2 (fun '(S3, _) =>
       @drop_high_cps (S R_numlimbs) S3 _ (fun S4 => rest (A, S4))))))))).

  Section loop.
    Context (A B : T) (k : Z) {cpsT : Type}.
    Fixpoint redc_loop_cps (count : nat) (rest : T * T -> cpsT) : T * T -> cpsT
      := match count with
         | O => rest
         | S count' => fun '(A, S') => redc_body_cps A B k S' (redc_loop_cps count' rest)
         end.

    Definition redc_cps (rest : T -> cpsT) : cpsT
      := redc_loop_cps (numlimbs A) (fun '(A, S') => rest S') (A, zero (1 + numlimbs B)).
  End loop.

  Definition redc_body (A B : T) (k : Z) (S' : T) : T * T := redc_body_cps A B k S' id.
  Definition redc_loop (B : T) (k : Z) (count : nat) : T * T -> T * T := redc_loop_cps B k count id.
  Definition redc (A B : T) (k : Z) : T := redc_cps A B k id.
End WordByWordMontgomery.

Hint Opaque redc redc_body redc_loop : uncps.
