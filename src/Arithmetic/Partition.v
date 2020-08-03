Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.

Require Import Crypto.Util.Notations.
Import ListNotations Weight. Local Open Scope Z_scope.

(* extra name wrapper so partition won't be confused with List.partition *)
Module Partition.
  Definition partition (weight : nat -> Z) n x :=
    map (fun i => (x mod weight (S i)) / weight i) (seq 0 n).
End Partition.

Section PartitionProofs.
  Context weight {wprops : @weight_properties weight}.
  Local Notation partition := (Partition.partition weight).

  Lemma partition_step n x :
    partition (S n) x = partition n x ++ [(x mod weight (S n)) / weight n].
  Proof using Type.
    cbv [partition]. rewrite seq_snoc.
    autorewrite with natsimplify push_map. reflexivity.
  Qed.

  Lemma length_partition n x : length (partition n x) = n.
  Proof using Type. cbv [partition]; distr_length. Qed.
  Hint Rewrite length_partition : distr_length.

  Lemma eval_partition n x :
    Positional.eval weight n (partition n x) = x mod (weight n).
  Proof using wprops.
    induction n; intros.
    { cbn. rewrite (weight_0); auto with zarith. }
    { rewrite (Z.div_mod (x mod weight (S n)) (weight n)) by auto with zarith.
      rewrite <-Znumtheory.Zmod_div_mod by (try apply Z.mod_divide; auto with zarith).
      rewrite partition_step, Positional.eval_snoc with (n:=n) by distr_length.
      lia. }
  Qed.

  Lemma partition_Proper n :
    Proper (Z.equiv_modulo (weight n) ==> eq) (partition n).
  Proof using wprops.
    cbv [Proper Z.equiv_modulo respectful].
    intros x y Hxy; induction n; intros.
    { reflexivity. }
    { assert (Hxyn : x mod weight n = y mod weight n).
      { erewrite (Znumtheory.Zmod_div_mod _ (weight (S n)) x), (Znumtheory.Zmod_div_mod _ (weight (S n)) y), Hxy
          by (try apply Z.mod_divide; auto with zarith);
          reflexivity. }
      rewrite !partition_step, IHn by eauto.
      rewrite (Z.div_mod (x mod weight (S n)) (weight n)), (Z.div_mod (y mod weight (S n)) (weight n)) by auto with zarith.
      rewrite <-!Znumtheory.Zmod_div_mod by (try apply Z.mod_divide; auto with zarith).
      rewrite Hxy, Hxyn; reflexivity. }
  Qed.

  (* This is basically a shortcut for:
       apply partition_Proper; [ | cbv [Z.equiv_modulo] *)
  Lemma partition_eq_mod x y n :
    x mod weight n = y mod weight n ->
    partition n x = partition n y.
  Proof using wprops. apply partition_Proper. Qed.

  Lemma nth_default_partition d n x i :
    (i < n)%nat ->
    nth_default d (partition n x) i = x mod weight (S i) / weight i.
  Proof using Type.
    cbv [partition]; intros.
    rewrite map_nth_default with (x:=0%nat) by distr_length.
    autorewrite with push_nth_default natsimplify. reflexivity.
  Qed.

  Lemma nth_default_partition_full d n x i :
    nth_default d (partition n x) i = if lt_dec i n then x mod weight (S i) / weight i else d.
  Proof using Type.
    break_innermost_match;
      try now rewrite nth_default_out_of_bounds by distr_length.
    now rewrite nth_default_partition by lia.
  Qed.

  Fixpoint recursive_partition n i x :=
    match n with
    | O => []
    | S n' => x mod (weight (S i) / weight i) :: recursive_partition n' (S i) (x / (weight (S i) / weight i))
    end.

  Lemma recursive_partition_equiv' n : forall x j,
      map (fun i => x mod weight (S i) / weight i) (seq j n) = recursive_partition n j (x / weight j).
  Proof using wprops.
    induction n; [reflexivity|].
    intros; cbn. rewrite IHn.
    pose proof (@weight_positive _ wprops j).
    pose proof (@weight_divides _ wprops j).
    f_equal;
      repeat match goal with
             | _ => rewrite Z.mod_pull_div by auto with zarith
             | _ => rewrite weight_multiples by auto with zarith
             | _ => progress autorewrite with zsimplify_fast zdiv_to_mod pull_Zdiv
             | _ => reflexivity
             end.
  Qed.

  Lemma recursive_partition_equiv n x :
    partition n x = recursive_partition n 0%nat x.
  Proof using wprops.
    cbv [partition]. rewrite recursive_partition_equiv'.
    rewrite weight_0 by auto; autorewrite with zsimplify_fast.
    reflexivity.
  Qed.

  Lemma length_recursive_partition n : forall i x,
      length (recursive_partition n i x) = n.
  Proof using Type.
    induction n; cbn [recursive_partition]; [reflexivity | ].
    intros; distr_length; auto.
  Qed.

  Lemma drop_high_to_length_partition n m x :
    (n <= m)%nat ->
    Positional.drop_high_to_length n (partition m x) = partition n x.
  Proof using Type.
    cbv [Positional.drop_high_to_length partition]; intros.
    autorewrite with push_firstn.
    rewrite Nat.min_l by lia.
    reflexivity.
  Qed.

  Lemma partition_0 n : partition n 0 = Positional.zeros n.
  Proof.
    cbv [partition].
    erewrite Positional.zeros_ext_map with (p:=seq 0 n) by distr_length.
    apply map_ext; intros.
    autorewrite with zsimplify; reflexivity.
  Qed.

End PartitionProofs.
Hint Rewrite length_partition length_recursive_partition : distr_length.
Hint Rewrite eval_partition using (solve [auto; distr_length]) : push_eval.
Hint Rewrite nth_default_partition_full : push_nth_default.
