Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.DestructHead.

Module ZRange.
  Import Operations.ZRange.
  Local Open Scope zrange_scope.

  Local Notation eta v := r[ lower v ~> upper v ].

  Local Ltac t :=
    repeat first [ reflexivity
                 | progress destruct_head' zrange
                 | progress cbv -[Z.min Z.max Z.le Z.lt Z.ge Z.gt]
                 | progress split_min_max
                 | match goal with
                   | [ |- _ = _ :> zrange ] => apply f_equal2
                   end
                 | omega
                 | solve [ auto ] ].


  Lemma flip_flip v : flip (flip v) = v.
  Proof. destruct v; reflexivity. Qed.

  Lemma normalize_flip v : normalize (flip v) = normalize v.
  Proof. t. Qed.

  Lemma normalize_idempotent v : normalize (normalize v) = normalize v.
  Proof. t. Qed.

  Definition normalize_or v : normalize v = v \/ normalize v = flip v.
  Proof. t. Qed.
End ZRange.
