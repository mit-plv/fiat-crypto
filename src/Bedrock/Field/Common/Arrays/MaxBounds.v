Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Datatypes.List.
Require Import bedrock2.Syntax.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Common.Arrays.MakeAccessSizes.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Local Open Scope Z_scope.
Import ListNotations.

Section MaxBounds.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.
  Context (n : nat).

  (* TODO: make Expr.v import this *)
  Definition max_range : ZRange.zrange :=
    {|ZRange.lower:=0; ZRange.upper:=2^width-1|}.
  Definition max_bounds : list (option ZRange.zrange) :=
    repeat (Some max_range) n.

  Lemma max_bounds_range_iff x :
    let bytes := (Memory.bytes_per
                    (width:=width) access_size.word) in
    list_Z_bounded_by max_bounds x <->
    (length x = n /\
     Forall
       (fun z : Z =>
          0 <= z < 2 ^ (Z.of_nat bytes * 8)) x).
  Proof.
    cbv [max_bounds max_range list_Z_bounded_by].
    replace (Z.of_nat (Memory.bytes_per access_size.word) * 8) with width
      by (destruct Bitwidth.width_cases; subst width; exact eq_refl).
    generalize n as m.
    induction x; destruct m; split;
      cbn [FoldBool.fold_andb_map repeat]; try congruence; intros;
        repeat match goal with
               | _ => progress cleanup
               | _ => progress cbn [length ZRange.lower ZRange.upper] in *
               | |- Forall _ [] => solve [constructor]
               | |- Forall _ (_ :: _) => constructor
               | H: Forall _ (_ :: _) |- _ =>
                 inversion H; clear H; subst
               | |- (_ && _)%bool = true =>
                 apply Bool.andb_true_iff; split
               | H: (_ && _)%bool = true |- _ =>
                 apply Bool.andb_true_iff in H; destruct H
               | H : context [iff] |- _ => eapply H; solve [eauto]
               | H : context [iff] |- _ =>
                 rewrite H; auto; congruence
               | |- _ /\ _ => split
               | |- S _ = S _ => f_equal
               | _ => progress Z.ltb_to_lt
               | _ => congruence
               | _ => lia
               end.
  Qed.


  Lemma map_word_wrap_bounded' r x m :
    ZRange.is_tighter_than_bool r max_range = true ->
    list_Z_bounded_by (repeat (Some r) m) x ->
    map word.wrap x = x.
  Proof.
    intros.
    pose proof length_list_Z_bounded_by _ x ltac:(eassumption).
    cbv [max_bounds max_range list_Z_bounded_by
                    ZRange.is_tighter_than_bool] in *.
    rewrite repeat_length in *.
    generalize dependent m.
    generalize dependent x; induction x; destruct m;
      repeat match goal with
             | _ => progress intros
             | _ => progress cleanup
             | _ => progress
                      cbn [length FoldBool.fold_andb_map
                                  ZRange.upper ZRange.lower
                                  repeat map] in *
             | H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H
             | IH : context [map word.wrap ?x = ?x] |- _ =>
               rewrite IH with (m:=m) by (try eassumption; lia)
             | _ => progress Z.ltb_to_lt
             | |- word.wrap ?x :: ?y = ?x :: ?y =>
               cbv [word.wrap]; Z.rewrite_mod_small;
                 reflexivity
             | _ => congruence
             end.
  Qed.

  Lemma map_word_wrap_bounded x :
    list_Z_bounded_by max_bounds x ->
    map word.wrap x = x.
  Proof.
    intros. eapply map_word_wrap_bounded'; [ | eassumption ].
    apply ZRange.is_tighter_than_bool_Reflexive.
  Qed.

  Lemma byte_unsigned_within_max_bounds x :
    length x = n ->
    list_Z_bounded_by max_bounds (map Byte.byte.unsigned x).
  Proof.
    intros; apply max_bounds_range_iff; split;
      [ rewrite ?map_length; solve [auto] | ].
    eapply Forall_impl;
      [ | apply Forall_map_byte_unsigned ].
    cbv beta; intros.
    pose proof Z.pow_le_mono_r 2 8 width ltac:(lia) width_ge_8.
    replace (Z.of_nat (Memory.bytes_per access_size.word) * 8) with width
      by (destruct Bitwidth.width_cases; subst width; exact eq_refl).
    lia.
  Qed.

  Lemma partition_max_range :
    forall x,
      let bytes := (Memory.bytes_per
                      (width:=width) access_size.word) in
      Forall (fun z => 0 <= z < 2^(Z.of_nat bytes * 8))
             (Partition.partition
                (UniformWeight.uweight width) n x).
  Proof.
    pose proof word.width_pos. cbv zeta.
    induction n; intros; [ solve [constructor] | ].
    rewrite partition_step. apply Forall_snoc; auto; [ ].
    rewrite UniformWeight.uweight_S by lia.
    rewrite <-Z.mod_pull_div by auto with zarith.
    replace (Z.of_nat (Memory.bytes_per access_size.word) * 8) with width
      by (destruct Bitwidth.width_cases; subst width; exact eq_refl).
    apply Z.mod_pos_bound; auto with zarith.
  Qed.

  Lemma partition_bounded_by x :
    list_Z_bounded_by
      max_bounds
      (Partition.partition (UniformWeight.uweight width) n x).
  Proof.
    apply max_bounds_range_iff; split;
      auto using partition_max_range, length_partition.
  Qed.
End MaxBounds.
