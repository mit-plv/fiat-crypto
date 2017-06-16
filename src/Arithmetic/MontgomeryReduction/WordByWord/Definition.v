(*** Word-By-Word Montgomery Multiplication *)
(** This file implements Montgomery Form, Montgomery Reduction, and
    Montgomery Multiplication on an abstract [ℤⁿ].  See
    https://github.com/mit-plv/fiat-crypto/issues/157 for a discussion
    of the algorithm; note that it may be that none of the algorithms
    there exactly match what we're doing here. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Definition.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.

Local Open Scope Z_scope.

Section WordByWordMontgomery.
  Local Coercion Z.pos : positive >-> Z.
  (** TODO: pick better names for the arguments to this definition. *)
  Context
    {r : positive}
    {R_numlimbs : nat}
    (N' : T R_numlimbs).
  (** TODO(andreser): Add a comment here about why we take in [N : T
       R_numlimbs]; we need [N : T (S R_numlimbs)] so that the limb
       arithmetic works out exactly (so that we can add [q * N] of
       length [S (S R_numlimbs)] to [S1] of length [S (S R_numlimbs)]
       and then do [divmod] to get something of length [S
       R_numlimbs]. *)
  Local Notation N := (join0 N').

  Definition redc_body_no_cps (B : T R_numlimbs) (k : Z) {pred_A_numlimbs} (A_S : T (S pred_A_numlimbs) * T (S R_numlimbs))
    : T pred_A_numlimbs * T (S R_numlimbs)
    := @redc_body T (@divmod) r R_numlimbs (@scmul (Z.pos r)) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N B k _ A_S.
  Definition redc_loop_no_cps (B : T R_numlimbs) (k : Z) (count : nat) (A_S : T count * T (S R_numlimbs))
    : T 0 * T (S R_numlimbs)
    := @redc_loop T (@divmod) r R_numlimbs (@scmul (Z.pos r)) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N B k count A_S.
  Definition redc_no_cps {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) : T (S R_numlimbs)
    := @redc T (@zero) (@divmod) r R_numlimbs (@scmul (Z.pos r)) (@add (Z.pos r)) (@drop_high (S R_numlimbs)) N _ A B k.

  Definition redc_body_cps {pred_A_numlimbs} (A : T (S pred_A_numlimbs)) (B : T R_numlimbs) (k : Z) (S' : T (S R_numlimbs))
             {cpsT} (rest : T pred_A_numlimbs * T (S R_numlimbs) -> cpsT)
    : cpsT
    := divmod_cps A (fun '(A, a) =>
       @scmul_cps r _ a B _ (fun aB => @add_cps r _ S' aB _ (fun S1 =>
       divmod_cps S1 (fun '(_, s) =>
       dlet q := s * k mod r in
       @scmul_cps r _ q N _ (fun qN => @add_cps r _ S1 qN _ (fun S2 =>
       divmod_cps S2 (fun '(S3, _) =>
       @drop_high_cps (S R_numlimbs) S3 _ (fun S4 => rest (A, S4))))))))).

  Section loop.
    Context {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) {cpsT : Type}.
    Fixpoint redc_loop_cps (count : nat) (rest : T 0 * T (S R_numlimbs) -> cpsT) : T count * T (S R_numlimbs) -> cpsT
      := match count with
         | O => rest
         | S count' => fun '(A, S') => redc_body_cps A B k S' (redc_loop_cps count' rest)
         end.

    Definition redc_cps (rest : T (S R_numlimbs) -> cpsT) : cpsT
      := redc_loop_cps A_numlimbs (fun '(A, S') => rest S') (A, zero).
  End loop.

  Definition redc_body {pred_A_numlimbs} (A : T (S pred_A_numlimbs)) (B : T R_numlimbs) (k : Z) (S' : T (S R_numlimbs))
    : T pred_A_numlimbs * T (S R_numlimbs)
    := redc_body_cps A B k S' id.
  Definition redc_loop (B : T R_numlimbs) (k : Z) (count : nat) : T count * T (S R_numlimbs) -> T 0 * T (S R_numlimbs)
    := redc_loop_cps B k count id.
  Definition redc {A_numlimbs} (A : T A_numlimbs) (B : T R_numlimbs) (k : Z) : T (S R_numlimbs)
    := redc_cps A B k id.
End WordByWordMontgomery.

Hint Opaque redc redc_body redc_loop : uncps.
