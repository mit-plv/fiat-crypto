Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Byte.
Require Import bedrock2.Syntax.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Local Open Scope Z_scope.
Import ListNotations.
Import Partition.

Section ByteBounds.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.
  Context (n : nat).

  Definition byte_range : ZRange.zrange :=
    {|ZRange.lower:=0; ZRange.upper:=2^8-1|}.
  Definition byte_bounds : list (option ZRange.zrange) :=
    repeat (Some byte_range) n.

  (* TODO: consider refactoring this lemma into lemmas about Forall, Forall2,
     and fold_andb_map *)
  Lemma byte_bounds_range_iff x :
    list_Z_bounded_by byte_bounds x <->
    (length x = n /\
     Forall (fun z : Z => 0 <= z < 2 ^ 8) x).
  Proof.
    cbv [byte_bounds byte_range list_Z_bounded_by].
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

  Lemma map_byte_wrap_bounded' r x m :
    ZRange.is_tighter_than_bool r byte_range = true ->
    list_Z_bounded_by (repeat (Some r) m) x ->
    map byte.wrap x = x.
  Proof.
    intros.
    pose proof length_list_Z_bounded_by _ x ltac:(eassumption).
    cbv [byte_bounds byte_range list_Z_bounded_by
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
             | IH : context [map byte.wrap ?x = ?x] |- _ =>
               rewrite IH with (m:=m) by (try eassumption; lia)
             | _ => progress Z.ltb_to_lt
             | |- byte.wrap ?x :: ?y = ?x :: ?y =>
               cbv [byte.wrap]; Z.rewrite_mod_small;
                 reflexivity
             | _ => congruence
             end.
  Qed.

  Lemma map_byte_wrap_bounded x :
    list_Z_bounded_by byte_bounds x ->
    map byte.wrap x = x.
  Proof.
    intros. eapply map_byte_wrap_bounded'; [ | eassumption ].
    apply ZRange.is_tighter_than_bool_Reflexive.
  Qed.

  Lemma byte_map_unsigned_of_Z x :
    map byte.unsigned (map byte.of_Z x) = map byte.wrap x.
  Proof.
    rewrite map_map. apply map_ext. exact byte.unsigned_of_Z.
  Qed.

  (* TODO: this should be upstreamed (maybe move to Util for now) *)
  Lemma byte_of_Z_unsigned b : byte.of_Z (byte.unsigned b) = b.
  Proof.
    apply byte.unsigned_inj.
    rewrite byte.unsigned_of_Z.
    apply byte.wrap_unsigned.
  Qed.

  Lemma byte_map_of_Z_unsigned x :
    map byte.of_Z (map byte.unsigned x) = x.
  Proof.
    rewrite map_map.
    erewrite map_ext; [ apply map_id | ].
    auto using byte_of_Z_unsigned.
  Qed.

  Lemma partition_bytes_range :
    forall x,
      Forall (fun z => 0 <= z < 2^8)
             (partition (ModOps.weight 8 1) n x).
  Proof.
    induction n; intros; [ solve [constructor] | ].
    rewrite partition_step. apply Forall_snoc; auto; [ ].
    fold (UniformWeight.uweight 8).
    rewrite UniformWeight.uweight_S by lia.
    rewrite <-Z.mod_pull_div by auto with zarith.
    apply Z.mod_pos_bound; auto with zarith.
  Qed.

  Lemma partition_bounded_by x :
    list_Z_bounded_by byte_bounds (partition (ModOps.weight 8 1) n x).
  Proof.
    apply byte_bounds_range_iff; split;
      auto using partition_bytes_range, length_partition.
  Qed.
End ByteBounds.
