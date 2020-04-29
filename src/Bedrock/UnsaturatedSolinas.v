Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Import Language.Compilers.
Import Types Types.Notations.
Existing Instances rep.Z rep.listZ_mem.

(* TODO: this is copy-pasted from Stringification; put in a common location *)
Section with_parameters.
  Context {p : Types.parameters}.
  Context {inname_gen outname_gen : nat -> string}.

  Fixpoint make_names
           (name_gen : nat -> string) (nextn : nat) (t : base.type)
    : nat * base_ltype t :=
    match t as t0 return nat * base_ltype t0 with
    | base.type.prod a b =>
      let resa := make_names name_gen nextn a in
      let resb := make_names name_gen (fst resa) b in
      (fst resb, (snd resa, snd resb))
    | base_listZ =>
      (S nextn, name_gen nextn)
    | _ =>
      (S nextn, name_gen nextn)
    end.
  Fixpoint make_innames' (nextn : nat) (t : API.type)
    : nat * type.for_each_lhs_of_arrow ltype t :=
    match t as t0 return
          nat * type.for_each_lhs_of_arrow ltype t0 with
    | type.base _ => (nextn, tt)
    | type.arrow (type.base s) d =>
      let ress := make_names inname_gen nextn s in
      let resd := make_innames' (fst ress) d in
      (fst resd, (snd ress, snd resd))
    | type.arrow _ d =>
      let resd := make_innames' nextn d in
      (fst resd, (tt, snd resd))
    end.
  Definition make_innames t : type.for_each_lhs_of_arrow ltype t :=
    snd (make_innames' 0 t).
  Definition make_outnames t : base_ltype t :=
    snd (make_names outname_gen 0 t).

  Fixpoint list_lengths_repeat_base (n : nat) t : base_listonly nat t :=
    match t as t0 return base_listonly nat t0 with
    | base.type.prod a b =>
      (list_lengths_repeat_base n a, list_lengths_repeat_base n b)
    | base_listZ => n
    | _ => tt
    end.
  Fixpoint list_lengths_repeat_args (n : nat) t
    : type.for_each_lhs_of_arrow list_lengths t :=
    match t as t0 return type.for_each_lhs_of_arrow list_lengths t0 with
    | type.base b => tt
    | type.arrow (type.base s) d =>
      (list_lengths_repeat_base n s, list_lengths_repeat_args n d)
    | type.arrow s d => (tt, list_lengths_repeat_args n d)
    end.
End with_parameters.

Import Language.Compilers.
Import Language.Wf.Compilers.
Import Associational Positional.

Require Import Crypto.Util.Notations.
Import Types.Notations ListNotations.
Import QArith_base.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

(* Strategy for varnames:
   - Take in generator function for innames/outnames
   - Make separate files with varname generators and proofs about them
     * Include a prefix-based generator
     * Include an easy proof that if the prefixes aren't equal the generators don't collide

   For the synthesis, there should be two levels
   - This level, where you get an end-to-end proof specialized to the function but lots of other things (the varname generation and machine wordsize, for instance) are left unspecified
     * If you want to do something special or custom, you would access this level directly
   - Another ltac-based level on top, the "easy mode", where you're not specialized to compile-time parameters like n or machine_wordsize, but varname generation is plugged in for you and there's automation to prove most of the subgoals of calling this level, so ideally you just plug in your parameters and get a record type with the functions and their proofs


   Steps:
   - finish up with carry_mul (except maybe the bytes<->Bignum proofs)
   - make the ltac just for carry_mul and test it out
   - create examples using the ltac

 *)

Section __.
  Context {p : Types.parameters}
          {inname_gen outname_gen : nat -> string}
          (n : nat) (s : Z) (c : list (Z * Z)).

  Definition make_bedrock_func {t} (res : API.Expr t) :=
    fst (translate_func res (make_innames (inname_gen:=inname_gen) _)
                        (list_lengths_repeat_args n _)
                        (make_outnames (outname_gen:=outname_gen) _)).

  Definition carry_mul
             (res : API.Expr (type.arrow type_listZ
                                         (type.arrow type_listZ
                                                     type_listZ)))
    : bedrock_func :=
    ("carry_mul", make_bedrock_func res).

  Definition max_bounds : list (option ZRange.zrange) :=
    repeat (Some {|ZRange.lower:=0; ZRange.upper:=2^Semantics.width-1|}) n.

  Section Proofs.
    Context {ok : Types.ok}.
    Existing Instance semantics_ok.

    Local Notation M := (s - Associational.eval c)%Z.
    Local Notation wt :=
      (ModOps.weight
         (Qnum (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))
         (QDen (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))).
    Local Notation eval := (eval wt n).
    Local Notation loose_bounds := (UnsaturatedSolinas.loose_bounds n s c).
    Local Notation tight_bounds := (UnsaturatedSolinas.tight_bounds n s c).

    Context
      (* loose_bounds_ok could be proven in parameterized form, but is a pain
      and is easily computable with parameters plugged in. So for now, leaving
      as a precondition. *)
      (loose_bounds_ok :
         ZRange.type.option.is_tighter_than
           (t:=type_listZ) (Some loose_bounds) (Some max_bounds) = true)
      (check_args_ok :
         check_args n s c Semantics.width (ErrorT.Success tt)
         = ErrorT.Success tt).

    Context (inname_gen_varname_gen_ok :
               forall n m, inname_gen n <> varname_gen m)
            (outname_gen_varname_gen_ok :
               forall n m, outname_gen n <> varname_gen m)
            (outname_gen_inname_gen_ok :
               forall n m, outname_gen n <> inname_gen m).
    (* TODO: make record type for varname generators *)
    Context (inname_gen_unique :
               forall i j : nat, inname_gen i = inname_gen j <-> i = j)
            (outname_gen_unique :
               forall i j : nat, outname_gen i = outname_gen j <-> i = j).

    Definition Bignum (addr : Semantics.word) (xs : list Z) :
      Semantics.mem -> Prop :=
      array scalar (word.of_Z word_size_in_bytes)
            addr (map word.of_Z xs).

    (* TODO: move to ListUtil or somewhere else common *)
    Fixpoint partition_equal_size' {T}
             (n : nat) (xs acc : list T) (i : nat)
      : list (list T) :=
      match xs with
      | [] => match i with
              | O => [acc]
              | S _ => [] (* if the last acc is incomplete, drop it *)
              end
      | x :: xs' =>
        match i with
        | O => acc :: partition_equal_size' n xs' [x] (n-1)
        | S i' => partition_equal_size' n xs' (acc ++ [x])%list i'
        end
      end.
    Definition partition_equal_size {T} (n : nat) (xs : list T) :=
      partition_equal_size' n xs [] n.

    Definition eval_bytes (bs : list Byte.byte) : list Z :=
      map (fun l => LittleEndian.combine _ (HList.tuple.of_list l))
          (partition_equal_size (Z.to_nat word_size_in_bytes) bs).

    Definition encode_bytes (xs : list Semantics.word) : list Byte.byte :=
      flat_map
        (fun x => HList.tuple.to_list
                    (LittleEndian.split (Z.to_nat word_size_in_bytes)
                                        (word.unsigned x)))
        xs.

    Lemma scalar_to_bytes a x :
      Lift1Prop.iff1
        (array ptsto (word.of_Z 1) a
               (HList.tuple.to_list
                  (LittleEndian.split (Z.to_nat word_size_in_bytes)
                                      (word.unsigned x))))
        (scalar a x).
    Admitted.

    (* TODO: move upstream *)
    Lemma scalar_of_bytes
          a l (H : length l = Z.to_nat word_size_in_bytes) :
      Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                     (scalar a (word.of_Z
                                  (LittleEndian.combine
                                     _ (HList.tuple.of_list l)))).
    Admitted. (* TODO *)

    Lemma Bignum_of_bytes addr bs :
      length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
      Lift1Prop.iff1 (array ptsto (word.of_Z 1) addr bs)
                     (Bignum addr (eval_bytes bs)).
    Admitted. (* TODO *)

    Lemma Bignum_to_bytes addr x :
      list_Z_bounded_by max_bounds x ->
      Lift1Prop.iff1
        (array ptsto (word.of_Z 1) addr (encode_bytes (map word.of_Z x)))
        (Bignum addr x).
    Admitted. (* TODO *)

    (* TODO: clean up and move *)
    Lemma relax_list_Z_bounded_by r1 r2 x :
      ZRange.type.option.is_tighter_than
        (t:=type_listZ) (Some r1) (Some r2) = true ->
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
               | _ => progress cleanup
               | H : _ && _ = true |- _ =>
                 apply Bool.andb_true_iff in H
               end.
        apply Bool.andb_true_iff; split.
        { break_innermost_match; [ | reflexivity].
          break_innermost_match_hyps; [ | congruence ].
          cbv [ZRange.is_tighter_than_bool] in *.
          repeat match goal with
                 | _ => progress cleanup
                 | H : _ && _ = true |- _ =>
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

    Lemma relax_to_max_bounds x :
      list_Z_bounded_by loose_bounds x ->
      list_Z_bounded_by max_bounds x.
    Proof. apply relax_list_Z_bounded_by; auto. Qed.

    (* TODO: maybe upstream? *)
    Lemma list_Z_bounded_by_Forall x r m :
      list_Z_bounded_by (repeat (Some r) m) x ->
      Forall (fun z : Z => ZRange.lower r <= z <= ZRange.upper r) x.
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
               | _ => progress cleanup
               | _ => progress Z.ltb_to_lt
               | H : _ && _ = true |- _ =>
                 apply Bool.andb_true_iff in H
               | _ => solve [auto]
               | _ => lia
               end.
    Qed.

    Lemma max_bounds_range x :
      list_Z_bounded_by max_bounds x ->
      Forall (fun z : Z => 0 <= z < 2^Semantics.width) x.
    Proof.
      cbv [max_bounds]; intros.
      eapply Forall_impl;
        [ | eapply list_Z_bounded_by_Forall; eassumption ].
      cbn [ZRange.lower ZRange.upper].
      intros. lia.
    Qed.

    Lemma bounded_by_loose_bounds_length x :
      list_Z_bounded_by loose_bounds x -> length x = n.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite length_loose_bounds in *. lia.
    Qed.

    (* TODO: move *)
    Lemma length_partition_equal_size' {A} :
      forall n (xs : list A) acc i,
        n <> 0%nat -> (i <= n)%nat ->
        length (partition_equal_size' n xs acc i) = ((length xs + (n-i)) / n)%nat.
    Proof.
      induction xs; destruct i; cbn [partition_equal_size' length];
        intros; rewrite ?IHxs by lia; autorewrite with natsimplify;
          repeat match goal with
                 | _ => rewrite Nat.div_same by lia
                 | _ => rewrite Nat.div_small by lia
                 | _ => rewrite NatUtil.div_minus, Nat.add_1_r by lia
                 | |- (_ / ?x)%nat = (_ / ?x)%nat => repeat (f_equal; try lia)
                 | |- S _ = S _ => repeat (f_equal; try lia)
                 | _ => lia
                 end.
    Qed.

    (* TODO: move *)
    Lemma length_partition_equal_size {A} :
      forall n (xs : list A),
        n <> 0%nat ->
        length (partition_equal_size n xs) = (length xs / n)%nat.
    Proof.
      cbv [partition_equal_size]; intros.
      rewrite length_partition_equal_size' by lia.
      autorewrite with natsimplify. reflexivity.
    Qed.

    (* TODO: move *)
    Lemma partition_equal_size'_equal_size {A} :
      forall n (xs : list A) acc i,
        n <> 0%nat -> (length acc = n - i)%nat -> (i <= n)%nat ->
        Forall (fun l => length l = n) (partition_equal_size' n xs acc i).
    Proof.
      induction xs; destruct i; cbn [partition_equal_size']; intros;
          repeat match goal with
                 | _ => apply Forall_nil
                 | _ => apply Forall_cons
                 | _ => lia
                 | _ => progress autorewrite with natsimplify in *
                 end.
      { eapply Forall_impl; [ | apply IHxs; cbn [length]; lia ].
        intros; lia. }
      { eapply Forall_impl; [ | apply IHxs; rewrite ?app_length;
                                cbn [length]; lia ].
        intros; lia. }
    Qed.

    (* TODO: move *)
    Lemma partition_equal_size_equal_size {A} :
      forall n (xs : list A),
        n <> 0%nat ->
        Forall (fun l => length l = n) (partition_equal_size n xs).
    Proof.
      intros.
      apply partition_equal_size'_equal_size; cbn [length]; lia.
    Qed.

    Lemma eval_bytes_length bs :
      length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
      length (eval_bytes bs) = n.
    Proof.
      intro Hlength. pose proof word_size_in_bytes_pos.
      assert (Z.to_nat word_size_in_bytes <> 0%nat)
        by (rewrite <-Z2Nat.inj_0, Z2Nat.inj_iff; lia).
      rewrite <-(Nat.div_mul n (Z.to_nat word_size_in_bytes)) by lia.
      cbv [eval_bytes]. rewrite <-Hlength, map_length.
      apply length_partition_equal_size; lia.
    Qed.

    Lemma eval_bytes_range bs :
      Forall (fun z : Z => 0 <= z < 2 ^ Semantics.width) (eval_bytes bs).
    Proof.
      pose proof word_size_in_bytes_pos.
      assert (Z.to_nat word_size_in_bytes <> 0%nat)
        by (rewrite <-Z2Nat.inj_0, Z2Nat.inj_iff; lia).
      cbv [eval_bytes]. apply Forall_map_iff.
      eapply Forall_impl;
        [ | apply partition_equal_size_equal_size; solve [auto] ].
      cbv beta; intros.
      rewrite word_size_in_bytes_eq.
      match goal with
      | |- context [LittleEndian.combine ?n ?t] =>
        pose proof LittleEndian.combine_bound t
      end.
      match goal with
      | H : length ?x = Z.to_nat ?y |- _ =>
        assert (Z.of_nat (length x) = y)
          by (rewrite H, Z2Nat.id; lia)
      end.
      congruence.
    Qed.

    Lemma make_names_no_collision name_gen1 name_gen2 t :
      (forall n m : nat, name_gen1 n <> name_gen2 m) ->
      forall nextn n,
        ~ varname_set_base (snd (make_names name_gen1 nextn t))
          (name_gen2 n).
    Proof.
      intro Hdisjoint; induction t; intros;
        cbn [varname_set_base rep.varname_set rep.Z rep.listZ_mem
                              make_names fst snd ];
        repeat match goal with
               | _ => progress cbn [fst snd]
               | |- ~ PropSet.singleton_set _ _ =>
                 apply disjoint_singleton_r_iff;
                   solve [auto using disjoint_singleton_singleton]
               | |- ~ PropSet.union _ _ _ =>
                 apply Util.not_union_iff; split; solve [auto]
               | _ => progress break_innermost_match
               end.
    Qed.

    (* TODO: when make_innames is moved, move this too *)
    Lemma make_innames'_varname_gen_disjoint t :
      forall nextn n,
        ~ varname_set_args
          (snd (make_innames' (inname_gen:=inname_gen) nextn t))
          (varname_gen n).
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress
                        cbn [fst snd make_innames'
                                 varname_set_args] in *
               | |- ~ PropSet.empty_set _ => cbv [PropSet.empty_set]; tauto
               | |- ~ PropSet.union _ _ _ =>
                 apply Util.not_union_iff; split
               | _ => progress break_innermost_match
               | _ => solve [auto using make_names_no_collision]
               end.
    Qed.

    (* TODO: when make_innames is moved, move this too *)
    Lemma make_innames_varname_gen_disjoint t :
      forall n,
        ~ varname_set_args (make_innames (inname_gen:=inname_gen) t)
          (varname_gen n).
    Proof. apply make_innames'_varname_gen_disjoint. Qed.

    (* TODO: when make_outnames is moved, move this too *)
    Lemma make_outnames_varname_gen_disjoint t :
      forall n,
        ~ varname_set_base (make_outnames (outname_gen:=outname_gen) t)
          (varname_gen n).
    Proof. apply make_names_no_collision; auto. Qed.

    (* TODO: when make_names is moved, move this too *)
    Lemma fst_make_names_lower_bound name_gen t :
      forall nextn, (nextn <= fst (make_names name_gen nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_names] in *
               | _ => progress break_innermost_match
               | _ => lia
               end; [ ].
      eapply Nat.le_trans; [ | solve [eauto] ]. eauto.
    Qed.

    (* TODO: when make_names is moved, move this too *)
    Lemma flatten_make_names_range name_gen t :
      forall x nextn,
        In x (Flatten.flatten_base_ltype
                (snd (make_names name_gen nextn t))) ->
        exists n, x = name_gen n
                  /\ (nextn <= n < fst (make_names name_gen nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_names
                                        Flatten.flatten_base_ltype] in *
               | H : _ /\ _ |- _ => destruct H
               | H : In _ [_] |- _ => inversion H; clear H
               | H : In _ [] |- _ => solve [inversion H]
               | H : In _ (_ ++ _) |- _ =>
                 apply in_app_iff in H; destruct H
               | H : name_gen ?x = ?y |- exists n, ?y = name_gen n /\ _ =>
                 exists x; split; [ congruence | ]
               | H : ?y = name_gen ?x |- exists n, ?y = name_gen n /\ _ =>
                 exists x; split; [ assumption | ]
               | _ => specialize (IHt1 _ _ ltac:(eassumption));
                        destruct IHt1
               | _ => specialize (IHt2 _ _ ltac:(eassumption));
                        destruct IHt2
               | _ => progress break_innermost_match
               | _ => lia
              end; [ | ];
          pose proof fst_make_names_lower_bound name_gen t1 nextn;
          pose proof fst_make_names_lower_bound
               name_gen t2 (fst (make_names name_gen nextn t1));
          lia.
    Qed.

    (* TODO: when make_names is moved, move this too *)
    Lemma flatten_make_names_NoDup name_gen t :
      (forall i j, name_gen i = name_gen j <-> i = j) ->
      forall nextn,
        NoDup (Flatten.flatten_base_ltype
                 (snd (make_names name_gen nextn t))).
    Proof.
      intro name_gen_unique.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_names
                                        Flatten.flatten_base_ltype]
               | H : In _ _ |- _ => apply flatten_make_names_range in H;
                                      destruct H
               | H : _ /\ _ |- _ => destruct H
               | H1 : ?x = name_gen ?n1, H2 : ?x = name_gen ?n2 |- _ =>
                 pose proof (proj1 (name_gen_unique n1 n2)
                                   ltac:(congruence)); clear H1 H2
               | _ => apply NoDup_cons
               | |- NoDup (_ ++ _) => apply NoDup_app_iff
               | |- _ /\ _ => split
               | |- ~ In _ _ => try apply in_nil; intro
               | _ => progress break_innermost_match
               | _ => solve [auto using in_nil, NoDup_nil]
               | _ => lia
               end.
    Qed.

    (* TODO: when make_innames is moved, move this too *)
    Lemma fst_make_innames'_lower_bound t :
      forall nextn,
        (nextn <= fst (make_innames' (inname_gen:=inname_gen) nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_innames'] in *
               | _ => progress break_innermost_match
               | _ => progress break_innermost_match_hyps
               | _ => lia
               | _ => solve [eauto]
               end; [ ].
      eapply Nat.le_trans; [ apply fst_make_names_lower_bound | ].
      eauto.
    Qed.

    (* TODO: when make_innames is moved, move this too *)
    Lemma flatten_make_innames'_range t :
      forall x nextn,
        In x (Flatten.flatten_argnames
                (snd (make_innames' (inname_gen:=inname_gen) nextn t))) ->
        exists n,
          x = inname_gen n
          /\ (nextn <= n < fst (make_innames' (inname_gen:=inname_gen)
                                              nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_innames'
                                        Flatten.flatten_argnames] in *
               | H : _ /\ _ |- _ => destruct H
               | H : In _ [] |- _ => solve [inversion H]
               | H : In _ (_ ++ _) |- _ =>
                 apply in_app_iff in H; destruct H
               | H : In _ _ |- _ => apply flatten_make_names_range in H;
                                      destruct H
               | H : ?y = inname_gen ?x
                 |- exists n, ?y = inname_gen n /\ _ =>
                 exists x; split; [ assumption | ]
               | _ => specialize (IHt2 _ _ ltac:(eassumption));
                        destruct IHt2
               | _ => progress break_innermost_match
               | _ => lia
               end; [ | ].
      { pose proof fst_make_innames'_lower_bound t2 (fst (make_names inname_gen nextn t)).
        lia. }
      { pose proof fst_make_names_lower_bound inname_gen t nextn.
        lia. }
    Qed.

    (* TODO: when make_innames is moved, move this too *)
    Lemma flatten_make_innames'_NoDup t :
      forall nextn,
        NoDup
          (Flatten.flatten_argnames
             (snd (make_innames' (inname_gen:=inname_gen) nextn t))).
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_innames'
                                        Flatten.flatten_argnames]
               | _ => apply NoDup_nil
               | H : _ /\ _ |- _ => destruct H
               | H : In _ _ |- _ => apply flatten_make_names_range in H;
                                      destruct H
               | H : In _ _ |- _ => apply flatten_make_innames'_range in H;
                                      destruct H
               | H1 : ?x = inname_gen ?n1, H2 : ?x = inname_gen ?n2 |- _ =>
                 pose proof (proj1 (inname_gen_unique n1 n2)
                                   ltac:(congruence)); clear H1 H2
               | |- NoDup (_ ++ _) => apply NoDup_app_iff
               | |- _ /\ _ => split
               | |- ~ In _ _ => intro
               | _ => progress break_innermost_match
               | _ => solve [ auto using flatten_make_names_NoDup]
               | _ => lia
               end.
    Qed.

    (* TODO: when make_innames is moved, move this too *)
    Lemma flatten_make_innames_NoDup t :
      NoDup
        (Flatten.flatten_argnames
           (make_innames (inname_gen:=inname_gen) t)).
    Proof. apply flatten_make_innames'_NoDup. Qed.

    Lemma flatten_make_innames_exists t x :
      In x (Flatten.flatten_argnames
              (make_innames (inname_gen:=inname_gen) t)) ->
      exists n : nat, x = inname_gen n.
    Proof.
      cbv [make_innames]; intros.
      destruct (flatten_make_innames'_range t _ _ ltac:(eassumption)).
      cleanup. eexists; eauto.
    Qed.

    Lemma flatten_make_outnames_exists t x :
      In x (Flatten.flatten_base_ltype
              (make_outnames (outname_gen:=outname_gen) t)) ->
      exists n : nat, x = outname_gen n.
    Proof.
      cbv [make_outnames]; intros.
      destruct (flatten_make_names_range
                  outname_gen t _ _ ltac:(eassumption)).
      cleanup. eexists; eauto.
    Qed.

    (* TODO: when make_innames is moved, move this too *)
    Lemma make_innames_make_outnames_disjoint t1 t2 :
      PropSet.disjoint
        (varname_set_args (make_innames (inname_gen:=inname_gen) t1))
        (varname_set_base (make_outnames (outname_gen:=outname_gen) t2)).
    Proof.
      rewrite Flatten.varname_set_args_flatten.
      rewrite Flatten.varname_set_flatten.
      apply NoDup_disjoint, NoDup_app_iff.
      ssplit;
        repeat match goal with
               | _ => progress intros
               | H : In _ _ |- _ => apply flatten_make_innames_exists in H;
                                      destruct H
               | H : In _ _ |- _ => apply flatten_make_outnames_exists in H;
                                      destruct H
               | H1 : ?x = inname_gen ?n1, H2 : ?x = outname_gen ?n2 |- _ =>
                 specialize (outname_gen_inname_gen_ok n2 n1); congruence
               | |- ~ In _ _ => intro
               | _ => solve [eauto using flatten_make_innames_NoDup,
                             flatten_make_names_NoDup]
               end.
    Qed.

    (* For out, you can get an array of bytes from a bignum using
       Bignum_to_bytes. *)
    Instance spec_of_carry_mul : spec_of "carry_mul" :=
      fun functions =>
        forall x y px py pout bs t m
               (Ra Rr : Semantics.mem -> Prop),
          list_Z_bounded_by loose_bounds x ->
          list_Z_bounded_by loose_bounds y ->
          length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
          sep (sep (Bignum px x) (Bignum py y)) Ra m ->
          sep (array ptsto (word.of_Z 1) pout bs) Rr m ->
          WeakestPrecondition.call
            (p:=semantics)
            functions "carry_mul" t m
            (px :: py :: pout :: nil)
            (fun t' m' rets =>
               t = t' /\
               rets = []%list /\
               Lift1Prop.ex1
                 (fun out =>
                    sep
                      (sep (emp (eval out mod M = (eval x * eval y) mod M
                                 /\ list_Z_bounded_by tight_bounds out))
                             (Bignum pout out)) Rr) m').

    Lemma carry_mul_correct :
      forall carry_mul_res :
               API.Expr (type_listZ -> type_listZ -> type_listZ),
        UnsaturatedSolinas.carry_mul n s c Semantics.width
        = ErrorT.Success carry_mul_res ->
        expr.Wf3 carry_mul_res ->
        valid_func (carry_mul_res (fun _ : API.type => unit)) ->
        forall functions,
          spec_of_carry_mul
            (("carry_mul", make_bedrock_func carry_mul_res) :: functions).
    Proof.
      cbv [spec_of_carry_mul]; intros.
      cbv [make_bedrock_func].

      match goal with H : _ = ErrorT.Success _ |- _ =>
                      apply UnsaturatedSolinas.carry_mul_correct in H;
                        [ | assumption ]
      end.

      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=(x, (y, tt))) (flat_args := [px; py]) ].
      { repeat intro.
        match goal with
          H : context [sep _ _ ?m] |- context [_ ?m] =>
          cbn in H
        end.
        sepsimpl_hyps.
        ssplit; [ congruence | congruence | ].

        eexists.
        sepsimpl;
          try match goal with
              | H : context [Solinas.carry_mul_correct] |- _ =>
               apply H; eauto
              end; [ ].
        cbv [Bignum expr.Interp].
        match goal with
        | H : literal (word.unsigned _) (eq (word.of_Z _)) |- _ =>
          let H' := fresh in
          cbv [literal] in H; inversion H as [H']; clear H;
            rewrite ?word.of_Z_unsigned in H';
            rewrite <-H'
        end.
        assumption. }

      (* now we prove translate_func preconditions *)
      all: try assumption.
      all: try reflexivity.

      { cbn. rewrite !bounded_by_loose_bounds_length by auto.
        reflexivity. }
      { apply make_innames_varname_gen_disjoint. }
      { (* arg pointers are correct *)
        cbn; sepsimpl.
        exists 1%nat; sepsimpl;
          cbn [firstn skipn];
          [ solve [eauto using firstn_length_le] | ].
        exists (word.unsigned px); sepsimpl.
        { apply max_bounds_range;
            auto using relax_to_max_bounds. }
        { apply word.unsigned_range. }
        { apply word.unsigned_range. }
        { reflexivity. }
        exists 1%nat; sepsimpl;
          cbn [firstn skipn];
          [ solve [eauto using firstn_length_le] | ].
        exists (word.unsigned py); sepsimpl.
        { apply max_bounds_range;
            auto using relax_to_max_bounds. }
        { apply word.unsigned_range. }
        { apply word.unsigned_range. }
        { reflexivity. }
        { reflexivity. }
        cbv [Bignum] in *.
        rewrite !word.of_Z_unsigned.
        ecancel_assumption. }
      { (* no duplicates in argnames *)
        apply flatten_make_innames_NoDup. }
      { apply make_outnames_varname_gen_disjoint. }
      { (* no duplicates in outnames *)
        apply flatten_make_names_NoDup; auto. }
      { apply make_innames_make_outnames_disjoint. }
      { cbn. sepsimpl.
        match goal with
        | H : context [array ptsto _ _ ?bs] |- _ =>
          seprewrite_in Bignum_of_bytes H; [ assumption | ];
            exists (eval_bytes bs)
        end.
        sepsimpl.
        { match goal with
          | H : context [Solinas.carry_mul_correct _ _ _ _ _ ?e] |- _ =>
            specialize (H x y ltac:(eauto) ltac:(eauto));
              cleanup;
              pose proof length_list_Z_bounded_by _ (e x y)
                   ltac:(eassumption)
          end.
          rewrite eval_bytes_length by lia.
          rewrite length_tight_bounds in *.
          cbv [expr.Interp] in *. congruence. }
        (* todo: tactic for this pattern, used in args above as well *)
        exists (word.unsigned pout); sepsimpl.
        { apply eval_bytes_range. }
        { apply word.unsigned_range. }
        { apply word.unsigned_range. }
        { rewrite word.of_Z_unsigned. eexists.
          rewrite ?map.get_put_diff, map.get_put_same by congruence.
          ssplit; reflexivity. }
        { rewrite !word.of_Z_unsigned.
          cbv [Bignum] in *.
          ecancel_assumption. } }
    Qed.
  End Proofs.
End __.
