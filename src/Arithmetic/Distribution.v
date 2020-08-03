Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Notations.
Import ListNotations Weight. Local Open Scope Z_scope.

Module Positional.
  Export Core.Positional.
  Section __.
    Context weight
            (n : nat)
            (s : Z)
            (c : list (Z * Z))
            {wprops : @weight_properties weight}.

    Local Notation eval := (eval weight) (only parsing).

    (** Sometimes we want to ensure that each limb of our encoded
        number [x] is larger than the corresponding limb of a given
        bound [minvalues].  We can ensure this by encoding [x -
        minvalues] in a way that ensures each limb is non-negative,
        and then adding back [minvalues].  We extend [minvalues] with
        zeros for convenience, so we don't need a proof that [length
        minvalues = n] for the proofs about [encode_distributed]. *)
    Definition encode_distributed (minvalues : list Z) (x : Z) : list Z
      := let minvalues := List.firstn n (minvalues ++ List.repeat 0 n) in
         (add weight n)
           (Partition.partition weight n ((x - Positional.eval weight n minvalues) mod (s - Associational.eval c)))
           minvalues.

    Lemma eval_encode_distributed minvalues x
      : 0 < s - Associational.eval c <= weight n
        -> eval n (encode_distributed minvalues x) mod (s - Associational.eval c)
           = x mod (s - Associational.eval c).
    Proof using wprops.
      intros; cbv [encode_distributed]; rewrite eval_add, eval_partition by (auto; distr_length).
      assert (forall x, x mod (s - Associational.eval c) < s - Associational.eval c) by auto with zarith.
      rewrite (Z.mod_small (_ mod (s - _)) (weight _)) by now eauto using Z.lt_le_trans with zarith.
      pull_Zmod; now autorewrite with zsimplify_fast.
    Qed.
    Hint Rewrite eval_encode_distributed : push_eval.
    Lemma length_encode_distributed minvalues x
      : length (encode_distributed minvalues x) = n.
    Proof using Type. cbv [encode_distributed]; repeat distr_length. Qed.
    Hint Rewrite length_encode_distributed : distr_length.
    Lemma nth_default_encode_distributed_bounded'
          (** We add an extra hypothesis that is too bulky to prove *)
          (Hadd : forall x y, length x = n -> length y = n -> add weight n x y = map2 Z.add x y)
          minvalues x i d' d
          (Hmin : (i < length minvalues)%nat)
          (Hn : (i < n)%nat)
      : nth_default d' minvalues i <= nth_default d (encode_distributed minvalues x) i.
    Proof using wprops.
      cbv [encode_distributed].
      rewrite (nth_default_in_bounds 0 d') by lia.
      rewrite (nth_default_in_bounds 0 d) by repeat distr_length.
      rewrite Hadd by repeat distr_length.
      rewrite nth_default_map2 with (d1:=0) (d2:=0);
        autorewrite with push_nth_default distr_length.
      rewrite Nat.min_assoc, Nat.min_id, (Nat.min_l n (_ + n)) by lia.
      break_innermost_match; try lia;
        autorewrite with simpl_nth_default;
        try solve [ destruct_head'_or; try lia ].
      match goal with |- ?x <= ?y + ?x => cut (0 <= y); [ lia | ] end.
      auto with zarith.
    Qed.
    (** We would like to prove this general lemma, but since we're
        using [Positional.add] rather than [List.map2 Z.add], it's
        kind-of annoying to prove, so we skip it. *)
    Lemma nth_default_encode_distributed_bounded
          minvalues x i d' d
          (Hmin : (i < length minvalues)%nat)
          (Hn : (i < n)%nat)
      : nth_default d' minvalues i <= nth_default d (encode_distributed minvalues x) i.
    Proof using wprops.
      apply nth_default_encode_distributed_bounded'; auto.
    Abort.
  End __.
End Positional.
Hint Rewrite @Positional.eval_encode_distributed using solve [auto; lia] : push_eval.
Hint Rewrite @Positional.length_encode_distributed : distr_length.
