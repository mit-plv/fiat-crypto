Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import coqutil.Byte.
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
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Require Import Crypto.Bedrock.Field.Common.Arrays.MakeAccessSizes.
Require Import Crypto.Bedrock.Field.Common.Arrays.MakeListLengths.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.Bedrock.Field.Common.Names.MakeNames.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Field.Translation.Func.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Existing Instances rep.Z rep.listZ_mem.

Import Language.Compilers.
Import Associational Positional.

Require Import Crypto.Util.Notations.
Import Types.Notations ListNotations.
Import QArith_base.
Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Declare Scope sep_scope.
Local Delimit Scope sep_scope with sep.
Local Infix "*" := sep : sep_scope.

Ltac apply_correctness_in H :=
  match type of H with
  | context [WordByWordMontgomery.mul] =>
    eapply WordByWordMontgomery.mul_correct in H
  | context [WordByWordMontgomery.square] =>
    eapply WordByWordMontgomery.square_correct in H
  | context [WordByWordMontgomery.add] =>
    eapply WordByWordMontgomery.add_correct in H
  | context [WordByWordMontgomery.sub] =>
    eapply WordByWordMontgomery.sub_correct in H
  | context [WordByWordMontgomery.opp] =>
    eapply WordByWordMontgomery.opp_correct in H
  | context [WordByWordMontgomery.to_montgomery] =>
    eapply WordByWordMontgomery.to_montgomery_correct in H
  | context [WordByWordMontgomery.from_montgomery] =>
    eapply WordByWordMontgomery.from_montgomery_correct in H
  | context [WordByWordMontgomery.nonzero] =>
    eapply WordByWordMontgomery.nonzero_correct in H
  | context [WordByWordMontgomery.selectznz] =>
    eapply Primitives.selectznz_correct in H
  | context [WordByWordMontgomery.to_bytes] =>
    eapply WordByWordMontgomery.to_bytes_correct in H
  | context [WordByWordMontgomery.from_bytes] =>
    eapply WordByWordMontgomery.from_bytes_correct in H
  | context [WordByWordMontgomery.encode] =>
    eapply WordByWordMontgomery.encode_correct in H
  | context [WordByWordMontgomery.zero] =>
    eapply WordByWordMontgomery.zero_correct in H
  | context [WordByWordMontgomery.one] =>
    eapply WordByWordMontgomery.one_correct in H
  end.

Section __.
  Context
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}
          {inname_gen outname_gen : nat -> string}
          (m : Z).
  Local Notation is_correct := (is_correct (parameters_sentinel:=parameters_sentinel) (inname_gen:=inname_gen) (outname_gen:=outname_gen)).
  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.
  Local Notation n := (WordByWordMontgomery.n m width).
  Local Notation n_bytes := (WordByWordMontgomery.n_bytes m).
  Local Notation bounds :=
    (WordByWordMontgomery.bounds m width).
  Local Notation montgomery_domain_bounds :=
    (WordByWordMontgomery.montgomery_domain_bounds m width).
  Local Notation non_montgomery_domain_bounds :=
    (WordByWordMontgomery.non_montgomery_domain_bounds m width).
  Local Notation prime_bounds :=
    (WordByWordMontgomery.prime_bounds m width).
  Local Notation prime_bytes_bounds :=
    (WordByWordMontgomery.prime_bytes_bounds m).
  Local Notation saturated_bounds :=
    (Primitives.saturated_bounds n width).
  Local Notation eval :=
    (@WordByWordMontgomery.WordByWordMontgomery.eval width n).

  Ltac select_access_size b :=
    lazymatch b with
    | Some bounds => constr:(access_size.word)
    | Some montgomery_domain_bounds => constr:(access_size.word)
    | Some non_montgomery_domain_bounds => constr:(access_size.word)
    | Some saturated_bounds => constr:(access_size.word)
    | Some prime_bounds => constr:(access_size.word)
    | Some prime_bytes_bounds => constr:(access_size.one)
    | ?b => fail "unable to select access size for bound" b
    end.

  Ltac select_length b :=
    lazymatch b with
    | Some bounds => constr:(n)
    | Some montgomery_domain_bounds => constr:(n)
    | Some non_montgomery_domain_bounds => constr:(n)
    | Some saturated_bounds => constr:(n)
    | Some prime_bounds => constr:(n)
    | Some prime_bytes_bounds => constr:(n_bytes)
    | ?b => fail "unable to select array length for bound" b
    end.

  Ltac sizes_from_bounds := map_bounds_listonly select_access_size.
  Ltac lengths_from_bounds := map_bounds_listonly select_length.

  Ltac prove_operation_correctness :=
    intros;
    let Hcorrect :=
        lazymatch goal with H : _ = ErrorT.Success _ |- _ => H end in
    apply_correctness_in Hcorrect; [ | eassumption .. ];
    specialize_to_args Hcorrect;
    postcondition_from_correctness.

  Ltac make_operation out :=
    let inbounds := (eval cbv beta in (Pipeline.arg_bounds_of_pipeline out)) in
    let outbounds := (eval cbv beta in (Pipeline.out_bounds_of_pipeline out)) in
    let t := lazymatch goal with |- operation ?t => t end in
    let insizes := sizes_from_bounds inbounds in
    let outsizes := sizes_from_bounds outbounds in
    let inlengths := lengths_from_bounds inbounds in
    let outlengths := lengths_from_bounds outbounds in
    eapply (Build_operation
              t inbounds insizes outsizes inlengths outlengths)
    with (pipeline_out:=out)
         (check_args_ok:=
            check_args m machine_wordsize [] (ErrorT.Success tt)
            = ErrorT.Success tt).

  Definition mul
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.mul m width).
    prove_operation_correctness.
  Defined.

  Definition square
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.square m width).
    prove_operation_correctness.
  Defined.

  Definition add
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.add m width).
    prove_operation_correctness.
  Defined.

  Definition sub
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.sub m width).
    prove_operation_correctness.
  Defined.

  Definition opp
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.opp m width).
    prove_operation_correctness.
  Defined.

  Definition to_montgomery
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.to_montgomery m width).
    prove_operation_correctness.
  Defined.

  Definition from_montgomery
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.from_montgomery m width).
    prove_operation_correctness.
  Defined.

  Definition nonzero
    : operation (type_listZ -> type_Z).
  Proof.
    make_operation (WordByWordMontgomery.nonzero m width).
    prove_operation_correctness.
  Defined.

  Definition selectznz
    : operation (type_Z -> type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.selectznz m width).
    prove_operation_correctness.
    Unshelve.
    { apply width. }
  Defined.

  Definition to_bytes
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.to_bytes m width).
    prove_operation_correctness.
  Defined.

  Definition from_bytes
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (WordByWordMontgomery.from_bytes m width).
    prove_operation_correctness.
  Defined.

  Definition spec_of_mul name : spec_of name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Rx Ry Rout : mem -> Prop),
        let op := mul in
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n py wy * Ry)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: py :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_square name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := square in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_add name : spec_of name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Rx Ry Rout : mem -> Prop),
        let op := add in
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n py wy * Ry)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: py :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_sub name : spec_of name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Rx Ry Rout : mem -> Prop),
        let op := sub in
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n py wy * Ry)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: py :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_opp name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := opp in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_to_montgomery name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := to_montgomery in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_from_montgomery name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := from_montgomery in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_nonzero name : spec_of name :=
    fun functions =>
      forall wx px t m
             (Rx Rout : mem -> Prop),
        let op := nonzero in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        Rout m ->
        WeakestPrecondition.call
          functions name t m
          (px :: nil)
          (fun t' m' rets =>
             t = t' /\
             length rets = 1%nat /\
             Rout m' /\
             let out := hd (word.of_Z 0) rets in
             op.(postcondition) args (word.unsigned out)).

  Definition spec_of_selectznz name : spec_of name :=
    fun functions =>
      forall wc wx px wy py pout wold_out t m
             (Rx Ry Rout : mem -> Prop),
        let op := selectznz in
        let args := (word.unsigned wc,
                     (map word.unsigned wx, (map word.unsigned wy, tt))) in
        let c := word.unsigned wc in
        ZRange.is_bounded_by_bool c bit_range = true ->
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n py wy * Ry)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: wc :: px :: py :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_to_bytes name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := to_bytes in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (EncodedBignum n_bytes pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (EncodedBignumSuchThat
                      n_bytes pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_from_bytes name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := from_bytes in
        let args := (map byte.unsigned wx, tt) in
        op.(precondition) args ->
        (EncodedBignum n_bytes px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      n pout wout (op.(postcondition) args))
                   Rout m').

  Hint Unfold mul square add sub opp to_montgomery from_montgomery
       nonzero selectznz to_bytes from_bytes : defs.

  Hint Unfold
       spec_of_mul
       spec_of_square
       spec_of_add
       spec_of_sub
       spec_of_opp
       spec_of_to_montgomery
       spec_of_from_montgomery
       spec_of_nonzero
       spec_of_selectznz
       spec_of_to_bytes
       spec_of_from_bytes : specs.

  Section Proofs.
    Context {ok : Types.ok}.

    Context (inname_gen_varname_gen_ok : disjoint inname_gen varname_gen)
            (outname_gen_varname_gen_ok : disjoint outname_gen varname_gen)
            (outname_gen_inname_gen_ok : disjoint outname_gen inname_gen).
    Context (inname_gen_unique : unique inname_gen)
            (outname_gen_unique : unique outname_gen).

    Lemma relax_to_max_bounds x :
      list_Z_bounded_by bounds x ->
      list_Z_bounded_by (@max_bounds width n) x.
    Proof.
      apply relax_list_Z_bounded_by. cbn.
      cbv [bounds Primitives.saturated_bounds Primitives.word_bound max_bounds list_Z_tighter_than].
      induction n; [ reflexivity | ].
      cbn [repeat FoldBool.fold_andb_map ZRange.lower ZRange.upper max_range].
      apply Bool.andb_true_iff. split; [ | solve [ auto ] ].
      apply Bool.andb_true_iff. split; Z.ltb_to_lt; lia.
    Qed.

    (* TODO: move to coqutil.Datatypes.List *)
    Lemma Forall_repeat : forall {A} (R : A -> Prop) n x,
      R x -> Forall R (repeat x n).
    Proof using. clear.
      intros; induction n; intros; cbn [repeat];
      constructor; auto.
    Qed.

    Lemma relax_prime_bounds x :
      list_Z_bounded_by prime_bounds x ->
      list_Z_bounded_by bounds x.
    Proof.
      cbv [prime_bounds prime_upperbound_list].
      intros; eapply relax_to_bounded_upperbounds;
        eauto; [ | solve [apply MaxBounds.partition_bounded_by] ].
      apply Forall_repeat. reflexivity.
    Qed.

    Lemma relax_to_byte_bounds x :
      list_Z_bounded_by prime_bytes_bounds x ->
      list_Z_bounded_by (byte_bounds n_bytes) x.
    Proof.
      cbv [prime_bytes_bounds prime_bytes_upperbound_list].
      intros; eapply relax_to_bounded_upperbounds;
        eauto using ByteBounds.partition_bounded_by; [ ].
      apply Forall_repeat. reflexivity.
    Qed.

    Lemma length_bounds : length bounds = n.
    Proof. apply repeat_length. Qed.

    Lemma bounded_by_bounds_length x :
      list_Z_bounded_by bounds x -> length x = n.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite <-length_bounds. cbn - [bounds]. congruence.
    Qed.

    Lemma length_saturated_bounds : length saturated_bounds = n.
    Proof. apply repeat_length. Qed.

    Lemma bounded_by_saturated_bounds_length x :
      list_Z_bounded_by saturated_bounds x -> length x = n.
    Proof.
      cbv [max_bounds].
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite Primitives.length_saturated_bounds in *. lia.
    Qed.

    Lemma bounded_by_prime_bounds_length x :
      list_Z_bounded_by prime_bounds x -> length x = n.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      cbv [prime_bounds prime_upperbound_list] in *.
      rewrite map_length, length_partition in *. lia.
    Qed.

    Lemma bounded_by_prime_bytes_bounds_length x :
      list_Z_bounded_by prime_bytes_bounds x -> length x = n_bytes.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      cbv [prime_bytes_bounds prime_bytes_upperbound_list] in *.
      rewrite map_length, length_partition in *. lia.
    Qed.

    Lemma bounded_by_byte_bounds_length x :
      list_Z_bounded_by (byte_bounds n_bytes) x -> length x = n_bytes.
    Proof. eapply byte_bounds_range_iff. Qed.

    Lemma valid_bounded_by_prime_bounds x :
      (check_args m width [] (ErrorT.Success tt)
       = ErrorT.Success tt) ->
      WordByWordMontgomery.valid width n m x ->
      list_Z_bounded_by prime_bounds x.
    Proof.
      intros; unshelve eapply bounded_by_prime_bounds_of_valid; eauto.
    Qed.

    Lemma valid_bounded_by_prime_bytes_bounds x :
      (check_args m width [] (ErrorT.Success tt)
       = ErrorT.Success tt) ->
      WordByWordMontgomery.valid 8 n_bytes m x ->
      list_Z_bounded_by prime_bytes_bounds x.
    Proof.
      intros; eapply bounded_by_prime_bytes_bounds_of_bytes_valid; eauto.
    Qed.

    (* TODO: maybe make a generalized prove_bounds tactic that takes a list of
    bounds? *)
    Ltac assert_bounds x :=
      match goal with
      | H: list_Z_bounded_by ?bs x |- _ => idtac
      | _ =>
        assert (WordByWordMontgomery.valid width n m x)
               by prove_bounds_direct;
        assert (list_Z_bounded_by prime_bounds x)
               by (apply valid_bounded_by_prime_bounds; auto)
      | _ =>
        assert (WordByWordMontgomery.valid 8 n_bytes m x)
               by prove_bounds_direct;
        assert (list_Z_bounded_by prime_bytes_bounds x)
               by (apply valid_bounded_by_prime_bytes_bounds; auto)
      | _ => assert (list_Z_bounded_by bounds x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by prime_bytes_bounds x)
          by prove_bounds_direct
      | _ => assert (list_Z_bounded_by (max_bounds n) x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by (byte_bounds n_bytes) x) by prove_bounds_direct
      | _ => fail "could not determine known bounds of" x
      end.
    (* looks for the following combinations of tighter/looser bounds:
       - prime_bounds/bounds
       - prime_bounds/saturated_bounds
       - prime_bytes_bounds/byte_bounds
    *)
    Ltac prove_bounds :=
      match goal with |- list_Z_bounded_by ?bs ?x => assert_bounds x end;
      match goal with
      | H : list_Z_bounded_by ?b1 ?x |- list_Z_bounded_by ?b2 ?x =>
        first [ unify b1 b2; apply H
              | unify b1 prime_bounds; unify b2 bounds;
                apply relax_prime_bounds; apply H
              | unify b1 prime_bounds; unify b2 saturated_bounds;
                apply relax_to_max_bounds, relax_prime_bounds; apply H
              | unify b1 prime_bytes_bounds; unify b2 (byte_bounds n_bytes);
                apply relax_to_byte_bounds; apply H ]
      end.

    (* special for to_bytes, because bounds are not included in the
       postcondition as with all other operations *)
    Ltac assert_to_bytes_bounds :=
      match goal with
      | H : postcondition ?op _ ?e |- _ =>
        unify op to_bytes;
        assert (list_Z_bounded_by (byte_bounds n_bytes) e)
          by (cbn [fst snd postcondition to_bytes] in H;
              rewrite H by prove_bounds;
              apply ByteBounds.partition_bounded_by)
      end.

    Ltac prove_output_length :=
      ssplit;
      match goal with
      | |- length _ = n =>
        apply bounded_by_bounds_length; prove_bounds
      | |- length _ = n =>
        apply bounded_by_saturated_bounds_length; prove_bounds
      | |- length _ = n =>
        apply bounded_by_prime_bounds_length; prove_bounds
      | |- length _ = n_bytes =>
        apply bounded_by_byte_bounds_length; prove_bounds
      | |- length _ = n_bytes =>
        apply bounded_by_prime_bytes_bounds_length; prove_bounds
      | |- n = length _ =>
        symmetry; prove_output_length
      | |- n_bytes = length _ =>
        symmetry; prove_output_length
      | |- tt = tt => reflexivity
      | |- ?x => fail "could not prove output length :" x
      end.

    Ltac setup :=
      autounfold with defs specs;
      begin_proof;
      match goal with
        H1 : precondition _ _, H2 : precondition _ _ -> _ |- _ =>
        specialize (H2 H1); autounfold with defs in H1;
        cbn [precondition] in H1; cleanup
      end;
      try assert_to_bytes_bounds;
      assert_output_length prove_output_length.

    Ltac prove_length :=
      lazymatch goal with
      | H : map _ ?x = ?y |- length ?x = length ?y =>
        rewrite <-H, !map_length; congruence
      | H : length ?x = ?n |- length (map _ ?x) = ?n =>
        rewrite map_length; solve [apply H]
      | H : length (map _ ?x) = ?n |- length ?x = ?n =>
        rewrite map_length in H; solve [apply H]
      | |- length ?x = length ?y =>
        rewrite ?map_length in *; congruence
      | H1 : length ?x = ?n, H2 : map _ ?y = ?x |- length ?y = ?n =>
        rewrite <-H1, <-H2, ?map_length; reflexivity
      | _ => idtac
      end.

    Ltac use_translate_func_correct Rout arg_ptrs out_array_ptrs :=
      apply_translate_func_correct Rout arg_ptrs out_array_ptrs;
      [ post_sufficient;
        cbv [Bignum EncodedBignum] in *; sepsimpl;
        prove_length; canonicalize_arrays; ecancel_assumption
      | .. ].

    Ltac solve_lists_reserved out_array_ptrs :=
      lazymatch out_array_ptrs with
      | [] => sepsimpl; solve [auto]
      | _ =>
        exists_all_placeholders out_array_ptrs;
        cbv [Bignum EncodedBignum] in *; sepsimpl;
        lazymatch goal with
        | |- length _ = _ => prove_length
        | |- WeakestPrecondition.get _ _ _ =>
          eexists; rewrite ?map.get_put_diff by eauto;
          rewrite map.get_put_same; solve [eauto]
        | |- sep _ _ _ => canonicalize_arrays; ecancel_assumption
        end
      end.

    Ltac prove_is_correct Rout :=
      let args := lazymatch goal with
                  | H : postcondition _ ?args _ |- _ => args end in
      let arg_ptrs := get_bedrock2_arglist args in
      let all_ptrs := lazymatch goal with
                      | |- call _ _ _ _ ?in_ptrs _ => in_ptrs end in
      let out_ptrs := get_out_array_ptrs arg_ptrs all_ptrs in
      use_translate_func_correct Rout arg_ptrs out_ptrs;
      solve_translate_func_subgoals prove_bounds prove_output_length;
      [ repeat next_argument; [ .. | reflexivity ];
        cbv [Bignum EncodedBignum] in *; sepsimpl;
        canonicalize_arrays; ecancel_assumption
      | setup_lists_reserved; solve_lists_reserved out_ptrs ].

    Context (check_args_ok :
               check_args m width [] (ErrorT.Success tt)
               = ErrorT.Success tt).

    Lemma mul_correct name :
      is_correct
        (WordByWordMontgomery.mul m width)
        mul (spec_of_mul name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma square_correct name :
      is_correct
        (WordByWordMontgomery.square m width)
        square (spec_of_square name).
    Proof. setup. prove_is_correct Rout. Qed.

    Lemma add_correct name :
      is_correct
        (WordByWordMontgomery.add m width)
        add (spec_of_add name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma sub_correct name :
      is_correct
        (WordByWordMontgomery.sub m width)
        sub (spec_of_sub name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma opp_correct name :
      is_correct
        (WordByWordMontgomery.opp m width)
        opp (spec_of_opp name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma to_montgomery_correct name :
      is_correct
        (WordByWordMontgomery.to_montgomery m width)
        to_montgomery (spec_of_to_montgomery name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma from_montgomery_correct name :
      is_correct
        (WordByWordMontgomery.from_montgomery m width)
        from_montgomery (spec_of_from_montgomery name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma nonzero_correct name :
      is_correct
        (WordByWordMontgomery.nonzero m width)
        nonzero (spec_of_nonzero name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma selectznz_correct name :
      is_correct
        (WordByWordMontgomery.selectznz m width)
        selectznz (spec_of_selectznz name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma to_bytes_correct name :
      is_correct
        (WordByWordMontgomery.to_bytes m width)
        to_bytes (spec_of_to_bytes name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma from_bytes_correct name :
      is_correct
        (WordByWordMontgomery.from_bytes m width)
        from_bytes (spec_of_from_bytes name).
    Proof. setup; prove_is_correct Rout. Qed.
  End Proofs.
End __.
Hint Unfold mul square add sub opp to_montgomery from_montgomery
     nonzero selectznz to_bytes from_bytes : defs.
Hint Unfold
     spec_of_mul
     spec_of_square
     spec_of_add
     spec_of_sub
     spec_of_opp
     spec_of_to_montgomery
     spec_of_from_montgomery
     spec_of_nonzero
     spec_of_selectznz
     spec_of_to_bytes
     spec_of_from_bytes : specs.
