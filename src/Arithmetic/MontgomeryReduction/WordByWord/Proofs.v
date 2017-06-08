(*** Word-By-Word Montgomery Multiplication Proofs *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.omega.Omega.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope Z_scope.

Section montgomery.
  Context {T : Type} {length : T -> nat}
          {divmod : T -> T * Z} (* returns lowest limb and all-but-lowest-limb *)
          {scmul : Z -> T -> T} (* uses double-output multiply *)
          {add : T -> T -> T * Z} (* produces carry *)
          {join : T * Z -> T}
          {zero : nat -> T}
          {to_Z : T -> Z}
          (A B : T)
          (bound : Z)
          (N : T)
          (k : Z) (* [(-1 mod N) mod bound] *)
          (divmod_div : forall v, to_Z (fst (divmod v)) = to_Z v / bound)
          (divmod_mod : forall v, snd (divmod v) = to_Z v mod bound)
          (scmul_correct : forall a v, to_Z (scmul a v) = a * to_Z v)
          (join_add_correct : forall a b, to_Z (join (add a b)) = to_Z a * to_Z b)
          (length_divmod_div : forall v, length (fst (divmod v)) = pred (length v))
          (length_join : forall v, length (join v) = S (length (fst v)))
          (length_add : forall a b, length (fst (add a b)) = max (length a) (length b))
          (length_scmul : forall a v, 0 <= a < bound -> length (scmul a v) = S (length v))
          (bound_pos : 0 < bound).
  Local Infix "≡" := (Z.equiv_modulo bound).

  Local Notation redc_body := (@redc_body T divmod scmul add join B N k).

  Local Ltac start :=
    unfold redc_body;
    repeat match goal with
           | [ H : _ * _ |- _ ] => destruct H
           | [ |- context[match ?x with pair _ _ => _ end] ]
             => rewrite (surjective_pairing x); simpl
           end.

  Hint Rewrite divmod_div divmod_mod join_add_correct scmul_correct : rew_db.
  Hint Rewrite length_add length_divmod_div length_scmul length_join : rew_db.
  Hint Rewrite Max.max_idempotent : rew_db.

  Lemma redc_body_small A_S
    : to_Z (snd A_S) < to_Z N + to_Z B
      -> to_Z (snd (redc_body A_S)) < to_Z N + to_Z B.
  Proof.
    start; repeat autorewrite with rew_db.
  Admitted.

  Lemma fst_redc_body_length A_S
    : length (fst (redc_body A_S)) = pred (length (fst A_S)).
  Proof.
    start; autorewrite with rew_db; reflexivity.
  Qed.
  Lemma snd_redc_body_length A_S
    : length (snd A_S) = S (max (length B) (length N))
      -> length (snd (redc_body A_S)) = S (max (length B) (length N)).
  Proof.
    apply Max.max_case_strong; intro Hm;
      start; intro H;
        repeat first [ progress autorewrite with rew_db
                     | rewrite H
                     | reflexivity
                     | apply Z.mod_pos_bound; assumption
                     | match goal with
                       | [ |- context[max ?x ?y] ]
                         => first [ rewrite (Max.max_l x y) by omega
                                  | rewrite (Max.max_r x y) by omega ]
                       end ].
  Qed.

  (*Lemma redc_body_value A_S *)
End montgomery.
