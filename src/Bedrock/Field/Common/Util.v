Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.List.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Coq.Lists.List. (* after SeparationLogic *)
Import ListNotations.

Import AbstractInterpretation.Compilers.

Section Maps.
  Local Hint Mode map.map - - : typeclass_instances.
  Context {key value} {key_eqb}
          {map : map.map key value}
          {key_eq_dec :
             forall x y : key,
               BoolSpec (x = y) (x <> y) (key_eqb x y)}
          {map_ok : map.ok map}.

  Lemma only_differ_empty m :
    map.only_differ m PropSet.empty_set m.
  Proof. right; reflexivity. Qed.

  Lemma only_differ_sym m1 m2 ks :
    map.only_differ m1 ks m2 ->
    map.only_differ m2 ks m1.
  Proof. firstorder congruence. Qed.

  Lemma only_differ_trans m1 m2 m3 ks1 ks2 :
    map.only_differ m2 ks1 m1 ->
    map.only_differ m3 ks2 m2 ->
    map.only_differ m3 (union ks1 ks2) m1.
  Proof. firstorder congruence. Qed.

  Global Instance Proper_only_differ :
    Proper (eq ==> sameset ==> eq ==> iff) map.only_differ.
  Proof. firstorder congruence. Qed.

  Global Instance Proper_undef_on :
    Proper (eq ==> sameset ==> iff) map.undef_on.
  Proof. firstorder congruence. Qed.

  Lemma only_differ_put m k v :
    map.only_differ (map.put m k v) (singleton_set k) m.
  Proof.
    cbv [map.only_differ elem_of singleton_set].
    intro x; destr (key_eqb k x); subst;
      rewrite ?map.get_put_same, ?map.get_put_diff by congruence;
      tauto.
  Qed.

  Lemma putmany_of_list_zip_app_l m ks1 ks2 vs :
    map.putmany_of_list_zip (ks1 ++ ks2) vs m =
    Option.bind
      (map.putmany_of_list_zip
         ks1 (List.firstn (Datatypes.length ks1) vs) m)
      (map.putmany_of_list_zip
         ks2 (List.skipn (Datatypes.length ks1) vs)).
  Proof.
    revert m ks2 vs; induction ks1; destruct vs;
      rewrite ?app_nil_l, <-?app_comm_cons;
      try reflexivity; [ ].
    apply IHks1.
  Qed.

  Lemma putmany_of_list_zip_None ks vs m :
    map.putmany_of_list_zip ks vs m = None <->
    length ks <> length vs.
  Proof.
    revert m vs; induction ks; destruct vs;
      cbn [map.putmany_of_list_zip length];
      split; intros; try congruence;
        match goal with
        | H : _ |- _ => apply IHks in H; lia
        | _ => apply IHks; lia
        end.
  Qed.

  Lemma putmany_of_list_zip_combine m ks vs :
    length ks = length vs ->
    map.putmany_of_list_zip ks vs m =
    Some (map.putmany_of_list (combine ks vs) m).
  Proof.
    revert m vs; induction ks; destruct vs; intros;
      cbn [length] in *; try lia; try reflexivity; [ ].
    cbn [map.putmany_of_list_zip map.putmany_of_list combine].
    rewrite IHks; auto.
  Qed.

  Lemma put_put_comm k1 k2 v1 v2 m :
    k1 <> k2 ->
    map.put (map.put m k1 v1) k2 v2 =
    map.put (map.put m k2 v2) k1 v1.
  Proof.
    intros.
    apply map.map_ext; intro k;
      destruct (key_eq_dec k1 k);
      destruct (key_eq_dec k2 k);
      subst; try congruence;
        repeat first [ rewrite map.get_put_same
                     | rewrite map.get_put_diff by congruence
                     | reflexivity ].
  Qed.

  Lemma putmany_of_list_put_comm kv k v m :
    ~ In k (List.map fst kv) ->
    map.putmany_of_list kv (map.put m k v) =
    map.put (map.putmany_of_list kv m) k v.
  Proof.
    revert m k v; induction kv; intros;
      [ reflexivity | ].
    cbn [map.putmany_of_list]. break_match.
    cbn [List.map In fst] in *.
    match goal with H : _ |- _ =>
                    apply Decidable.not_or in H; destruct H end.
    rewrite <-IHkv by auto.
    rewrite put_put_comm by congruence.
    reflexivity.
  Qed.

  Lemma putmany_of_list_comm kv1 kv2 m :
    NoDup (List.map fst (kv1 ++ kv2)) ->
    map.putmany_of_list kv1 (map.putmany_of_list kv2 m) =
    map.putmany_of_list kv2 (map.putmany_of_list kv1 m).
  Proof.
    revert kv2 m; induction kv1; destruct kv2; intros;
      try reflexivity; [ ].
    rewrite map_app in *. cbn [List.map] in *.
    cbn [map.putmany_of_list]. break_match.
    repeat match goal with
           | H : NoDup (_ ++ _) |- _ =>
             apply NoDup_app_iff in H
           | H : _ /\ _ |- _ => destruct H
           | H : NoDup (_ :: _) |- _ => inversion H; subst; clear H
           end.
    cbn [In fst] in *.
    rewrite !putmany_of_list_put_comm by firstorder idtac.
    rewrite put_put_comm by firstorder idtac.
    rewrite IHkv1; [ reflexivity | ].
    rewrite map_app. apply NoDup_app_iff.
    firstorder idtac.
  Qed.

  Lemma putmany_of_list_zip_bind_comm ks1 ks2 vs1 vs2 m :
    NoDup (ks1 ++ ks2) ->
    Option.bind
      (map.putmany_of_list_zip ks1 vs1 m)
      (map.putmany_of_list_zip ks2 vs2) =
    Option.bind
      (map.putmany_of_list_zip ks2 vs2 m)
      (map.putmany_of_list_zip ks1 vs1).
  Proof.
    intros.
    destruct (Nat.eq_dec (length ks1) (length vs1));
      destruct (Nat.eq_dec (length ks2) (length vs2));
      try solve [
            cbv [Option.bind]; break_match; try reflexivity;
            repeat match goal with
                   | H : _ = Some _ |- _ =>
                     apply map.putmany_of_list_zip_sameLength in H
                   | H : _ = None |- _ =>
                     apply putmany_of_list_zip_None in H
                   | _ => apply putmany_of_list_zip_None
                   | _ => symmetry; apply putmany_of_list_zip_None
                   | _ => congruence
                   end ]; [ ].
    repeat match goal with
           | _ => rewrite putmany_of_list_zip_combine by auto
           | _ => progress cbn [Option.bind]
           end.
    rewrite <-putmany_of_list_comm; [ reflexivity | ].
    rewrite <-combine_app_samelength by congruence.
    rewrite map_fst_combine.
    rewrite firstn_all2 by (rewrite !app_length; lia).
    assumption.
  Qed.

  Lemma getmany_of_tuple_empty sz keys :
    sz <> 0%nat ->
    map.getmany_of_tuple (sz:=sz) map.empty keys = None.
  Proof.
    destruct sz; try congruence.
    cbn; intros. rewrite map.get_empty. reflexivity.
  Qed.

  Lemma undef_on_None m k ks :
    map.undef_on m ks ->
    elem_of k ks ->
    map.get m k = None.
  Proof.
    intros.
    match goal with H : map.undef_on _ _ |- _ =>
                    specialize (H _ ltac:(eassumption));
                      rewrite map.get_empty in H
    end.
    congruence.
  Qed.

  Lemma undef_on_empty ks :
    map.undef_on map.empty ks.
  Proof. firstorder idtac. Qed.

  Lemma get_only_differ_undef m1 m2 ks k v :
    map.only_differ m1 ks m2 ->
    map.undef_on m1 ks ->
    map.get m1 k = Some v ->
    map.get m2 k = Some v.
  Proof.
    repeat match goal with
           | _ => progress intros
           | H : map.only_differ _ _ _ |- _ =>
             specialize (H k); destruct H
           | H1 : map.undef_on _ ?ks, H2 : elem_of ?k ?ks |- _ =>
             eapply undef_on_None in H2; [ | eassumption .. ]
           | _ => congruence
           end.
  Qed.

  Lemma only_differ_union_undef_l m1 m2 k1 k2 :
    map.only_differ m1 (union k1 k2) m2 ->
    map.undef_on m1 k2 ->
    map.undef_on m2 k2 ->
    map.only_differ m1 k1 m2.
  Proof.
    intros.
    match goal with H : map.only_differ _ _ _ |- map.only_differ _ _ _ =>
                    let x := fresh "x" in intro x; specialize (H x);
                                            destruct H
    end; [ | tauto ].
    match goal with H : elem_of _ (union _ _) |- _ =>
                    destruct H end;
      erewrite ?undef_on_None by eauto; tauto.
  Qed.

  Lemma undef_on_subset m k1 k2 :
    subset k1 k2 ->
    map.undef_on m k2 ->
    map.undef_on m k1.
  Proof. firstorder congruence. Qed.

  Lemma only_differ_disjoint_undef_on m1 m2 ks s :
    map.only_differ m1 ks m2 ->
    disjoint ks s ->
    map.undef_on m1 s ->
    map.undef_on m2 s.
  Proof. firstorder congruence. Qed.

  Lemma undef_on_union_iff m k1 k2 :
    map.undef_on m (union k1 k2) <->
    (map.undef_on m k1 /\ map.undef_on m k2).
  Proof.
    cbv [map.undef_on map.agree_on union elem_of].
    repeat split; intros; destruct_head'_or; destruct_head'_and; eauto.
  Qed.

  Lemma put_undef_on k v m s :
    map.undef_on m s ->
    ~ s k ->
    map.undef_on (map.put m k v) s.
  Proof.
    cbv [map.undef_on map.agree_on elem_of].
    intros. rewrite map.get_empty.
    match goal with H : context [map.empty] |- _ =>
                    setoid_rewrite map.get_empty in H end.
    match goal with H1 : ~ ?s ?k1, H2 : ?s ?k2 |- _ =>
                    destruct (key_eq_dec k1 k2); subst;
                      [ tauto | ]
    end.
    rewrite map.get_put_diff by congruence. eauto.
  Qed.

  Lemma of_list_zip_app ks1 ks2 vs1 vs2 :
    length ks1 = length vs1 ->
    length ks2 = length vs2 ->
    (exists l,
        map.of_list_zip (ks1 ++ ks2) (vs1 ++ vs2) = Some l).
  Proof.
    intros. apply map.sameLength_putmany_of_list.
    rewrite !app_length; lia.
  Qed.

  Lemma putmany_of_list_zip_undef_on ks vs m1 m2 s :
    map.putmany_of_list_zip ks vs m1 = Some m2 ->
    disjoint (of_list ks) s ->
    map.undef_on m1 s ->
    map.undef_on m2 s.
  Proof.
    revert vs m1 m2 s; induction ks; destruct vs;
      cbn [map.putmany_of_list_zip]; intros;
        try match goal with H : Some _ = Some _ |- _ =>
                            inversion H; subst; clear H
            end; try congruence; eauto; [ ].
    match goal with H : _ |- _ =>
                    symmetry in H; apply disjoint_cons in H
    end.
    destruct_head'_and.
    eapply IHks; eauto.
    { symmetry; eauto. }
    { apply put_undef_on; eauto.
      eapply disjoint_singleton_r_iff; eauto. }
  Qed.

  Lemma of_list_zip_undef_on ks vs m s :
    map.of_list_zip ks vs = Some m ->
    disjoint (of_list ks) s ->
    map.undef_on m s.
  Proof.
    cbv [map.of_list_zip]; intros.
    eapply putmany_of_list_zip_undef_on; eauto.
    cbv [map.undef_on map.agree_on]; reflexivity.
  Qed.

  Lemma only_differ_notin k ks m m' :
    map.only_differ m ks m' ->
    ~ ks k ->
    map.get m' k = map.get m k.
  Proof.
    cbv [map.only_differ PropSet.elem_of].
    let H := fresh in
    intro H; specialize (H k); destruct H.
    { tauto. }
    { auto. }
  Qed.
End Maps.

(* proofs about list_Z_bounded_by *)
Section ListZBoundedBy.
  Lemma relax_list_Z_bounded_by r1 r2 x :
    ZRange.type.option.is_tighter_than
      (t:=type.base (base.type.list (base.type.type_base base.type.Z)))
      (Some r1) (Some r2) = true ->
    list_Z_bounded_by r1 x ->
    list_Z_bounded_by r2 x.
  Proof.
    cbn in r1, r2 |- *. intros.
    pose proof length_list_Z_bounded_by _ x ltac:(eassumption).
    match goal with H : FoldBool.fold_andb_map _ _ _ = true |- _ =>
                    pose proof H;
                      apply FoldBool.fold_andb_map_length in H
    end.
    generalize dependent r1; generalize dependent r2.
    generalize dependent x; induction x; cbn [length].
    { destruct r2; cbn [length]; intros; [ | lia].
      reflexivity. }
    { destruct r1, r2; cbn [length]; intros; try lia; [ ].
      cbv [list_Z_bounded_by] in *. cbn [FoldBool.fold_andb_map] in *.
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             | H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H
             end.
      apply Bool.andb_true_iff; split.
      { break_innermost_match; [ | reflexivity].
        break_innermost_match_hyps; [ | congruence ].
        cbv [ZRange.is_tighter_than_bool] in *.
        repeat match goal with
               | H : _ /\ _ |- _ => destruct H
               | H : (_ && _)%bool = true |- _ =>
                 apply Bool.andb_true_iff in H
               end.
        apply Bool.andb_true_iff; split; Z.ltb_to_lt; lia. }
      { eapply IHx;
          match goal with
          | |- length _ = length _ =>
            idtac (* no eassumption on length goals *)
          | _ => try eassumption
          end; lia. } }
  Qed.

  Lemma list_Z_bounded_by_Forall x r m :
    list_Z_bounded_by (repeat (Some r) m) x ->
    Forall (fun z : Z => ZRange.lower r <= z <= ZRange.upper r)%Z x.
  Proof.
    intros.
    pose proof length_list_Z_bounded_by _ x ltac:(eassumption).
    cbv [list_Z_bounded_by] in *.
    rewrite repeat_length in *.
    generalize dependent x.
    generalize dependent m.
    induction m; intros;
      destruct x; intros; cbn [length] in *; subst;
        try lia; [ | ]; constructor;
          [ | apply IHm; [ | lia] ].
    all: cbn [repeat FoldBool.fold_andb_map] in *.
    all: repeat match goal with
                | H : _ /\ _ |- _ => destruct H
                | H : (_ && _)%bool = true |- _ =>
                  apply Bool.andb_true_iff in H
                | _ => progress Z.ltb_to_lt
                | _ => solve [auto]
                | _ => lia
                end.
  Qed.

  Lemma list_Z_bounded_by_cons b0 bs x0 xs:
    list_Z_bounded_by (b0 :: bs) (x0 :: xs) <->
    (match b0 with
     | Some r =>
       ZRange.is_bounded_by_bool x0 r = true
     | None => True
     end /\ list_Z_bounded_by bs xs).
  Proof.
    cbv [list_Z_bounded_by]. cbn [FoldBool.fold_andb_map].
    cbv [ZRange.is_bounded_by_bool].
    split; destruct b0; intros;
      repeat match goal with
             | H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H
             | |- (_ && _)%bool = true => apply Bool.andb_true_iff
             | H : _ /\ _ |- _ => destruct H
             | |- _ /\ _ => split
             | _ => assumption
             | _ => tauto
             end.
  Qed.

  Lemma list_Z_tighter_than_cons b1 b2 b1s b2s :
    list_Z_tighter_than (b1 :: b1s) (b2 :: b2s) <->
    (match b1 with
     | Some r1 =>
       match b2 with
       | Some r2 =>
         (ZRange.lower r2 <= ZRange.lower r1
          /\ ZRange.upper r1 <= ZRange.upper r2)%Z
       | None => True
       end
     | None => match b2 with
               | Some _ => False
               | None => True
               end
     end /\ list_Z_tighter_than b1s b2s).
  Proof.
    cbv [list_Z_tighter_than]. cbn [FoldBool.fold_andb_map].
    split; destruct b1, b2; intros;
      repeat match goal with
             | H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H
             | |- (_ && _)%bool = true => apply Bool.andb_true_iff
             | H : _ /\ _ |- _ => destruct H
             | |- _ /\ _ => split
             | _ => progress Z.ltb_to_lt
             | _ => assumption
             | _ => tauto
             | _ => congruence
             end.
  Qed.

  Lemma list_Z_bounded_by_snoc b0 bs x0 xs:
    list_Z_bounded_by (bs ++ [b0]) (xs ++ [x0]) <->
    (match b0 with
     | Some r =>
       ZRange.is_bounded_by_bool x0 r = true
     | None => True
     end /\ list_Z_bounded_by bs xs).
  Proof.
    cbv [list_Z_bounded_by].
    rewrite FoldBool.fold_andb_map_snoc.
    cbv [ZRange.is_bounded_by_bool].
    split; destruct b0; intros;
      repeat match goal with
             | H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H
             | |- (_ && _)%bool = true => apply Bool.andb_true_iff
             | H : _ /\ _ |- _ => destruct H
             | |- _ /\ _ => split
             | _ => assumption
             | _ => tauto
             end.
  Qed.

  Lemma relax_to_bounded_upperbounds bs upperbounds x :
    list_Z_bounded_by
      (map (fun v : Z => Some {| ZRange.lower := 0; ZRange.upper := v |})
           upperbounds) x ->
    Forall (fun r =>
              match r with
              | Some r => ZRange.lower r = 0%Z
              | None => True end) bs ->
    list_Z_bounded_by bs upperbounds ->
    list_Z_bounded_by bs x.
  Proof.
    intros.
    pose proof length_list_Z_bounded_by bs _ ltac:(eassumption).
    pose proof length_list_Z_bounded_by _ x ltac:(eassumption).
    rewrite map_length in *.
    generalize dependent bs. generalize dependent upperbounds.
    generalize dependent x.
    induction x; destruct upperbounds; destruct bs;
      cbn [map length] in *; try congruence; intros; [ ].
    repeat match goal with
           | _ => progress cbv [ZRange.is_bounded_by_bool] in *
           | _ => progress cbn [ZRange.lower ZRange.upper] in *
           | H : _ = 0 |- _ => rewrite H in *
           | H : Forall _ (_ :: _) |- _ =>
             inversion H; subst; clear H
           | H : (_ && _)%bool = true |- _ =>
             apply Bool.andb_true_iff in H
           | H : list_Z_bounded_by (_ :: _) (_ :: _) |- _ =>
             apply list_Z_bounded_by_cons in H; destruct H
           | |- list_Z_bounded_by (_ :: _) (_ :: _) =>
             apply list_Z_bounded_by_cons; split
           | |- (_ && _)%bool = true => apply Bool.andb_true_iff
           | H : _ /\ _ |- _ => destruct H
           | |- _ /\ _ => split
           | _ => progress break_match
           | _ => solve [auto]
           | _ => Z.ltb_to_lt; lia
           | H : _ |- list_Z_bounded_by _ _ => eapply H; solve [eauto]
           end.
  Qed.

  Lemma tighter_than_if_upper_bounded_by lo uppers bs :
    list_Z_bounded_by bs uppers ->
    Forall (fun b =>
              exists r,
                b = Some r /\ ZRange.lower r = lo) bs ->
    list_Z_tighter_than
      (map (fun v : Z => Some {| ZRange.lower := lo; ZRange.upper := v |})
           uppers) bs.
  Proof.
    clear; revert bs; induction uppers; intros;
      lazymatch goal with
      | H : list_Z_bounded_by _ _ |- _ =>
        pose proof H; apply length_list_Z_bounded_by in H
      end; (destruct bs; cbn [length] in *; try auto with lia); [ ].
    repeat lazymatch goal with
           | H : list_Z_bounded_by (_::_) (_::_) |- _ =>
             rewrite list_Z_bounded_by_cons in H
           | |- list_Z_tighter_than (map _ (_ :: _)) (_ :: _) =>
             cbn [map]; rewrite list_Z_tighter_than_cons
           | H : ZRange.is_bounded_by_bool _ _ = true |- _ =>
             apply Bool.andb_true_iff in H; destruct H;
               Z.ltb_to_lt
           | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
           | H : exists _, _ |- _ => destruct H; subst
           | H : _ /\ _ |- _ => destruct H; subst
           end.
    progress cbn [ZRange.lower ZRange.upper].
    split; auto with lia.
  Qed.

  Lemma partition_bounded_by_partition_ones x lg2s nb :
    (0 <= x < 2 ^ lg2s)%Z ->
    list_Z_bounded_by
      (map (fun v : Z => Some {| ZRange.lower := 0; ZRange.upper := v |})
           (Partition.Partition.partition
              (ModOps.weight 8 1) nb (2 ^ lg2s - 1)))
      (Partition.Partition.partition (ModOps.weight 8 1) nb x).
  Proof.
    clear.
    induction nb; [ reflexivity | ].
    rewrite !Partition.partition_step.
    rewrite map_last, list_Z_bounded_by_snoc.
    split; [ | solve [auto] ]. cbv [ZRange.is_bounded_by_bool].
    cbn [ZRange.lower ZRange.upper].
    apply Bool.andb_true_iff; split; Z.ltb_to_lt;
      [ ZeroBounds.Z.zero_bounds;
        solve [auto using Core.weight_positive, ModOps.wprops
                 with zarith] | ].
    apply Z.div_le_mono;
      [ solve [auto using Core.weight_positive, ModOps.wprops
                 with zarith] | ].
    cbv [ModOps.weight]. rewrite Nat2Z.inj_succ.
    autorewrite with zsimplify_fast. clear IHnb.
    destruct (Z_lt_dec lg2s ((8 * Z.of_nat nb + 8)%Z));
      [ assert (2 ^ lg2s < 2 ^ (8 * Z.of_nat nb + 8))%Z | ].
    1:auto with zarith.
    1:rewrite !Z.mod_small; auto with zarith.
    replace (2 ^ lg2s - 1)%Z with (Z.ones lg2s)
      by (rewrite Z.ones_equiv; auto with zarith).
    rewrite Z.ones_mod_pow2 by auto with zarith.
    lazymatch goal with
      |- context [(x mod ?m)%Z] =>
      pose proof Z.mod_pos_bound x m ltac:(auto with zarith)
    end.
    rewrite Z.ones_equiv; auto with zarith.
  Qed.
End ListZBoundedBy.

Section Bytes.
  Context {width : Z} {word : word width} {word_ok : word.ok word}.
  Local Notation bytes_per_word := (Z.to_nat (Memory.bytes_per_word width)).

  Definition eval_bytes bs := map le_combine (chunk bytes_per_word bs).

  Definition encode_bytes (xs : list word) : list Byte.byte :=
    flat_map (fun w => le_split bytes_per_word (word.unsigned w)) xs.

  Lemma bytes_per_word_nz : bytes_per_word <> 0%nat.
  Proof.
    pose proof word.width_pos.
    cbv [Memory.bytes_per]. change 0%nat with (Z.to_nat 0).
    rewrite Z2Nat.inj_iff by (try apply Z.div_pos; lia).
    apply not_eq_sym. apply Z.lt_neq, Z.div_str_pos.
    lia.
  Qed.

  Lemma eval_bytes_length bs n :
    length bs = (n * bytes_per_word)%nat ->
    length (eval_bytes bs) = n.
  Proof.
    intro Hlength.
    pose proof bytes_per_word_nz.
    rewrite <-(Nat.div_mul n bytes_per_word) by trivial.
    cbv [eval_bytes]; rewrite map_length, length_chunk by trivial.
    rewrite Hlength, Nat.div_up_exact, Nat.div_mul; trivial.
  Qed.

  Lemma Forall_map_byte_unsigned x :
    Forall (fun z : Z => 0 <= z < 2 ^ 8)%Z (map Byte.byte.unsigned x).
  Proof.
    induction x; cbn [length] in *; constructor; eauto; [ ].
    apply Byte.byte.unsigned_range.
  Qed.

  Context {bits_per_word_eq_width : (Z.of_nat bytes_per_word * 8 = width)%Z}.

  Lemma eval_bytes_range bs :
    Forall (fun z : Z => (0 <= z < 2 ^ width)%Z) (eval_bytes bs).
  Proof.
    pose proof bytes_per_word_nz as Hnz.
    apply Forall_map_iff, Forall_nth; intros.
    split; try eapply Z.lt_le_trans; try apply le_combine_bound.
    eapply Z.pow_le_mono_r; [cbv;trivial|].
    rewrite length_chunk in H by trivial.
    erewrite nth_error_nth in *; [|eapply nth_error_chunk; trivial].
    rewrite firstn_length, skipn_length.

    change 8%Z with (Z.of_nat 8).
    rewrite <-Nat2Z.inj_mul, <-Nat.mul_min_distr_l, Nat2Z.inj_min, Nat.mul_comm.
    rewrite Nat2Z.inj_mul.
    setoid_rewrite bits_per_word_eq_width.
    eapply Z.le_min_l.
  Qed.
End Bytes.

Section Scalars.
  Context
  {width: Z} {BW: Bitwidth.Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}
  {locals: map.map String.string word}
  {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}
  {ext_spec: bedrock2.Semantics.ExtSpec}
  {varname_gen : nat -> String.string}
  {word_ok : word.ok word} {mem_ok : map.ok mem}
  {locals_ok : map.ok locals}
  {env_ok : map.ok env}
  {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Local Notation bytes_per_word :=
    (@Memory.bytes_per_word width).

  Lemma scalar_to_bytes (a x : word) :
    Lift1Prop.iff1
      (scalar a x)
      (array ptsto (word.of_Z 1) a
             (LittleEndianList.le_split (Z.to_nat bytes_per_word)
             (word.unsigned x))).
  Proof.
    unfold scalar, truncated_word, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
    rewrite HList.tuple.to_list_of_list; reflexivity.
  Qed.

  Lemma truncated_scalar_one_ptsto_iff1 :
    forall (addr : word) x,
      Lift1Prop.iff1
        (truncated_scalar access_size.one addr x)
        (ptsto addr (Byte.byte.of_Z x)).
  Proof. intros.
    unfold scalar, truncated_word, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
    rewrite HList.tuple.to_list_of_list. unfold Memory.bytes_per, le_split, array.
    cancel.
  Qed.

  Lemma array_truncated_scalar_scalar_iff1 :
    forall xs (start : word) size,
      Lift1Prop.iff1
        (array (truncated_scalar access_size.word)
               size start (map word.unsigned xs))
        (array scalar size start xs).
  Proof.
    induction xs; cbn [array map]; intros; [ reflexivity | ].
    rewrite IHxs by auto. reflexivity.
  Qed.

  Lemma array_truncated_scalar_ptsto_iff1 :
    forall xs (start : word) size,
      Lift1Prop.iff1
        (array (truncated_scalar access_size.one)
               size start xs)
        (array ptsto size start (map Byte.byte.of_Z xs)).
  Proof.
    induction xs; cbn [array map]; intros; [ reflexivity | ].
    rewrite IHxs by auto. rewrite truncated_scalar_one_ptsto_iff1.
    cancel.
  Qed.
End Scalars.

Section Words.
  Local Hint Mode word.word - : typeclass_instances.
  Context {width} {word : word.word width} {ok : word.ok word}.

  Lemma map_of_Z_unsigned x :
    map word.of_Z (map word.unsigned x) = x.
  Proof.
    rewrite map_map.
    rewrite map_ext with (g:=id);
      [ solve [apply map_id] | ].
    intros. rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  Lemma map_unsigned_of_Z x :
    map word.unsigned (map word.of_Z x) = map word.wrap x.
  Proof.
    rewrite map_map. apply map_ext.
    exact word.unsigned_of_Z.
  Qed.

  Lemma Forall_map_unsigned x :
    Forall (fun z : Z => (0 <= z < 2 ^ width)%Z)
           (map word.unsigned x).
  Proof.
    induction x; intros; cbn [map]; constructor;
      auto using word.unsigned_range.
  Qed.

  Local Notation bytes_per_word := (Z.to_nat (Memory.bytes_per_word width)).
  Lemma Forall_word_unsigned_within_access_size
    {bits_per_word_eq_width : (Z.of_nat bytes_per_word * 8 = width)%Z} x :
    Forall
      (fun z : Z =>
         0 <= z < 2 ^ (Z.of_nat (Memory.bytes_per (width:=width) access_size.word) * 8))%Z
      (map word.unsigned x).
  Proof.
    intros.
    eapply Forall_impl; [ | apply Forall_map_unsigned ].
      cbv beta; intros.
    setoid_rewrite bits_per_word_eq_width; assumption.
  Qed.
End Words.

(* These lemmas should be moved to bedrock2, not coqutil *)
Section Separation.
  Local Hint Mode map.map - - : typeclass_instances.
  Context `{map_ok : map.ok}
           {key_eqb : forall H H0 : key, bool}
           {key_eq_dec :
              forall x y : key,
                BoolSpec (x = y) (x <> y) (key_eqb x y)}.
  Lemma sep_empty_iff (q r : map.rep -> Prop) :
    sep q r map.empty <-> q map.empty /\ r map.empty.
  Proof.
    cbv [sep].
    repeat match goal with
           | _ => progress (intros; subst)
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : _ |- _ => apply map.split_empty in H
           | _ => rewrite map.split_empty
           | _ => exists map.empty
           | _ => tauto
           | _ => split
           end.
  Qed.

  Lemma iff1_sep_cancel_both p1 p2 q1 q2 :
    Lift1Prop.iff1 p1 p2 ->
    Lift1Prop.iff1 q1 q2 ->
    Lift1Prop.iff1 (sep p1 q1) (sep p2 q2).
  Proof.
    intros Hp Hq. rewrite Hp, Hq. reflexivity.
  Qed.
End Separation.

(* These lemmas should be moved to bedrock2, not coqutil *)
Section WeakestPrecondition.
  Import Bitwidth bedrock2.WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  (* "expr" should not be Compilers.expr; can remove once upstreamed *)
  Local Notation expr := WeakestPrecondition.expr.

  Section Load.
    Lemma load_empty :
      forall s (m:mem) a post,
        load s map.empty a post -> load s m a post.
    Proof.
      intros *.
      cbv [load Memory.load Memory.load_Z Memory.load_bytes].
      rewrite getmany_of_tuple_empty; intros;
        repeat match goal with
               | H : exists _, _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
               | _ => congruence
               end.
      cbv [Memory.bytes_per]; break_match; try congruence.
      change 0%nat with (Z.to_nat 0).
      pose proof word.width_pos.
      rewrite Z2Nat.inj_iff by (try apply Z.div_pos; lia).
      rewrite Z.eq_sym_iff.
      apply Z.lt_neq, Z.div_str_pos; lia.
    Qed.
  End Load.

  Section Get.
    Lemma get_put_same (l : locals) x y (post:_->Prop) :
      post y -> get (map.put l x y) x post.
    Proof.
      cbv [get]; intros.
      exists y; rewrite map.get_put_same; tauto.
    Qed.

    Lemma get_put_diff (l : locals) x1 x2 y (post:_->Prop) :
      x1 <> x2 ->
      get l x1 post ->
      get (map.put l x2 y) x1 post.
    Proof.
      cbv [get]; intros.
      match goal with H : exists _, _ |- _ =>
                      destruct H end.
      eexists; rewrite map.get_put_diff; eauto.
    Qed.

    (* TODO: make module around Maps to stop name collision *)
    Lemma WP_get_only_differ_undef :
      forall e vset (locals locals' : locals) post,
        map.only_differ locals vset locals' ->
        map.undef_on locals vset ->
        get locals e post ->
        get locals' e post.
    Proof.
      cbv [get]; intros.
      match goal with H : exists _, _ |- _ => destruct H end.
      destruct_head'_and. eexists; split; try eassumption; eapply get_only_differ_undef; eauto.
    Qed.
  End Get.

  Section Expr.
    Lemma expr_empty :
      forall e m (locals : locals) post,
        expr map.empty locals e post ->
        expr m locals e post.
    Proof.
      induction e;
        cbn [expr expr_body];
        cbv [dlet.dlet literal get];
        intros; eauto.
      { eapply IHe; eauto.
        eapply Proper_expr; [ repeat intro | eassumption ].
        eauto using load_empty. }
      { eapply IHe1; eauto.
        eapply Proper_expr; [ repeat intro | eassumption ].
        cbv beta in *. eapply IHe2; eauto. }
      { eapply IHe1; eauto.
        eapply Proper_expr; [ repeat intro | eassumption ].
        cbv beta in *.
        destr (word.eqb a (word.of_Z 0)); eauto. }
    Qed.

    Lemma expr_untouched mem1 mem2 (l1 l2 : locals) vars v P :
      map.only_differ l2 vars l1 ->
      ~ vars v ->
      expr mem1 l1 (expr.var v) P <->
      expr mem2 l2 (expr.var v) P.
    Proof.
      cbv [map.only_differ
             elem_of
             expr
             expr_body
             get].
      let H := fresh in
      intro H; specialize (H v).
      split; intros;
        repeat match goal with
               | H : exists _, _ |- _ => destruct H
               | H : _ \/ _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
               | H : map.get _ _ = map.get _ _ |- _ =>
                 rewrite H in *
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | _ => eassumption
               | _ => tauto
               end.
    Qed.

    Lemma expr_only_differ_undef :
      forall e m vset (locals locals' : locals) post,
        map.only_differ locals vset locals' ->
        map.undef_on locals vset ->
        expr m locals e post ->
        expr m locals' e post.
    Proof.
      induction e;
        cbn [expr expr_body]; cbv [dlet.dlet literal];
        intros; eauto using WP_get_only_differ_undef.
      { eapply IHe1; eauto.
        eapply Proper_expr; [ repeat intro | eassumption ].
        cbv beta in *. eapply IHe2; eauto. }
      { eapply IHe1; eauto.
        eapply Proper_expr; [ repeat intro | eassumption ].
        cbv beta in *. destr (word.eqb a (word.of_Z 0)); eauto. }
    Qed.
  End Expr.

  Section ListMap.
    Context {A B} (f : A -> (B -> Prop) -> Prop)
            (f_ext :
               forall a H1 H2,
                 (forall b, H1 b <-> H2 b) ->
                 f a H1 <-> f a H2).
    Lemma list_map_app_iff xs ys post :
      list_map f (xs ++ ys) post <->
      list_map
        f xs (fun xx =>
                list_map
                  f ys (fun yy => post (xx ++ yy))).
    Proof.
      revert ys post; induction xs;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [list_map
                                      list_map_body] in *
               | _ => rewrite app_nil_l
               | _ => rewrite <-app_comm_cons
               | |- f _ _ <-> f _ _ => apply f_ext
               | _ => reflexivity
               end.
      apply IHxs.
    Qed.

    Lemma list_map_cons_iff x xs post :
      list_map f (x :: xs) post <->
      f x (fun y => list_map f xs (fun ys => post (y :: ys))).
    Proof. reflexivity. Qed.
  End ListMap.

  Section Dexpr.
    Lemma dexpr_equiv m (l : locals) n x1 x2 :
      dexpr m l (expr.var n) x1 ->
      dexpr m l (expr.var n) x2 ->
      x1 = x2.
    Proof.
      destruct 1; destruct 1; destruct_head'_and; congruence.
    Qed.

    Lemma dexpr_put_same m (l : locals) n x :
      dexpr m (map.put l n x) (expr.var n) x.
    Proof. eexists; rewrite map.get_put_same; tauto. Qed.

    Lemma dexpr_put_diff m (l : locals) n1 n2 x y :
      n1 <> n2 ->
      dexpr m l (expr.var n1) x ->
      dexpr m (map.put l n2 y) (expr.var n1) x.
    Proof.
      destruct 2; intros; eexists; rewrite map.get_put_diff; eauto.
    Qed.
  End Dexpr.

  (* TODO: some of these may be unused *)
  Section Dexprs.
    Local Ltac peel_expr :=
      progress (
          repeat
            progress match goal with
                     | H : expr ?m ?l ?e _ |- _ =>
                       match goal with
                       | |- expr m l e _ => idtac
                       | _ =>
                         apply expr_sound with (mc:=MetricLogging.EmptyMetricLog) in H;
                         destruct H as [? [_ [_ H] ] ]
                       end
                     end).

    Local Ltac propers_step :=
      match goal with
      | H : get ?l ?x _
        |- get ?l ?x _ =>
        eapply Proper_get
      | H : expr ?m ?l ?e _
        |- expr ?m ?l ?e _ =>
        eapply Proper_expr
      | H : list_map ?f ?xs _
        |- list_map ?f ?xs _ =>
        eapply Proper_list_map
      end; [ repeat intro .. | eassumption ]; cbv beta in *.

    Local Ltac propers :=
      propers_step;
      match goal with
      | _ => solve [propers]
      | H : _ |- _ => apply H; solve [eauto]
      | _ => congruence
      end.

    Lemma dexprs_cons_iff m (l : locals) e es v vs :
      dexprs m l (e :: es) (v :: vs) <->
      (expr m l e (eq v)
       /\ dexprs m l es vs).
    Proof.
      cbv [dexprs].
      revert es v vs; induction es; split; intros;
        repeat match goal with
               | _ => progress cbn [list_map
                                      list_map_body] in *
               | _ => progress cbv beta in *
               | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
               | |- _ /\ _ => split
               | _ => progress destruct_head'_and
               | _ => solve [propers]
               | _ => reflexivity
               | _ => peel_expr
               end.
      eapply IHes with (vs := tl vs).
      propers_step. peel_expr.
      destruct vs; cbn [tl]; propers.
    Qed.

    Lemma dexprs_cons_nil m (l : locals) e es :
      dexprs m l (e :: es) [] -> False.
    Proof.
      cbv [dexprs].
      induction es; intros;
        repeat match goal with
               | _ => progress cbn [list_map
                                      list_map_body] in *
               | _ => congruence
               | _ => solve [propers]
               | _ => apply IHes
               | _ => peel_expr
               end.
      propers_step. peel_expr. propers.
    Qed.

    Lemma dexprs_app_l m (l : locals) es1 :
      forall es2 vs,
        dexprs m l (es1 ++ es2) vs ->
        (dexprs m l es1 (firstn (length es1) vs)) /\
        (dexprs m l es2 (skipn (length es1) vs)).
    Proof.
      induction es1; intros.
      { cbn [Datatypes.length skipn firstn]; rewrite app_nil_l in *.
        split; eauto; reflexivity. }
      { destruct vs; rewrite <-app_comm_cons in *;
          [ match goal with H : _ |- _ => apply dexprs_cons_nil in H; tauto end | ].
        cbn [Datatypes.length skipn firstn].
        rewrite !dexprs_cons_iff in *.
        destruct_head'_and.
        repeat split; try eapply IHes1; eauto. }
    Qed.

    Lemma dexprs_length m (l : locals) :
      forall vs es,
        dexprs m l es vs ->
        length es = length vs.
    Proof.
      induction vs; destruct es; intros;
        repeat match goal with
               | _ => progress cbn [Datatypes.length]
               | _ => progress destruct_head'_and
               | H : _ |- _ => apply dexprs_cons_nil in H; tauto
               | H : _ |- _ => apply dexprs_cons_iff in H
               | _ => reflexivity
               | _ => congruence
               end.
      rewrite IHvs; auto.
    Qed.
  End Dexprs.
End WeakestPrecondition.
