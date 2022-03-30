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
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
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
  | context [UnsaturatedSolinas.carry_mul] =>
    eapply UnsaturatedSolinas.carry_mul_correct in H
  | context [UnsaturatedSolinas.carry_square] =>
    eapply UnsaturatedSolinas.carry_square_correct in H
  | context [UnsaturatedSolinas.carry] =>
    eapply UnsaturatedSolinas.carry_correct in H
  | context [UnsaturatedSolinas.add] =>
    eapply UnsaturatedSolinas.add_correct in H
  | context [UnsaturatedSolinas.sub] =>
    eapply UnsaturatedSolinas.sub_correct in H
  | context [UnsaturatedSolinas.opp] =>
    eapply UnsaturatedSolinas.opp_correct in H
  | context [UnsaturatedSolinas.selectznz] =>
    eapply Primitives.selectznz_correct in H
  | context [UnsaturatedSolinas.to_bytes] =>
    eapply UnsaturatedSolinas.to_bytes_correct in H
  | context [UnsaturatedSolinas.from_bytes] =>
    eapply UnsaturatedSolinas.from_bytes_correct in H
  | context [UnsaturatedSolinas.carry_scmul_const] =>
    eapply UnsaturatedSolinas.carry_scmul_const_correct in H
  | context [UnsaturatedSolinas.encode] =>
    eapply UnsaturatedSolinas.encode_correct in H
  | context [UnsaturatedSolinas.zero] =>
    eapply UnsaturatedSolinas.zero_correct in H
  | context [UnsaturatedSolinas.one] =>
    eapply UnsaturatedSolinas.one_correct in H
  end.

(** We need to tell [check_args] that we are requesting these functions in order to get the relevant properties out *)
Notation necessary_requests := ["to_bytes"; "from_bytes"]%string (only parsing).

Section __.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}
          {inname_gen outname_gen : nat -> string}
          (n : nat) (s : Z) (c : list (Z * Z)).
  Local Notation is_correct :=
    (is_correct (parameters_sentinel:=parameters_sentinel) (inname_gen:=inname_gen) (outname_gen:=outname_gen)).
  Local Notation loose_bounds :=
    (UnsaturatedSolinasHeuristics.loose_bounds n s c).
  Local Notation tight_bounds :=
    (UnsaturatedSolinasHeuristics.tight_bounds n s c).
  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.
  Local Notation saturated_bounds :=
    (Primitives.saturated_bounds n width).
  Local Notation prime_bytes_bounds :=
    (UnsaturatedSolinas.prime_bytes_bounds s).
  Local Notation n_bytes := (UnsaturatedSolinas.n_bytes s).
  Local Notation M := (UnsaturatedSolinas.m s c).
  Definition weight :=
    (ModOps.weight
       (Qnum (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))
       (QDen (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))).
  Local Notation eval := (eval weight n).

  Ltac select_access_size bounds :=
    lazymatch bounds with
    | Some saturated_bounds => constr:(access_size.word)
    | Some loose_bounds => constr:(access_size.word)
    | Some tight_bounds => constr:(access_size.word)
    | Some prime_bytes_bounds => constr:(access_size.one)
    | ?b => fail "unable to select access size for bound" b
    end.

  Ltac select_length bounds :=
    lazymatch bounds with
    | Some saturated_bounds => constr:(n)
    | Some loose_bounds => constr:(n)
    | Some tight_bounds => constr:(n)
    | Some prime_bytes_bounds => constr:(n_bytes)
    | ?b => fail "unable to select array length for bound" b
    end.

  Ltac sizes_from_bounds := map_bounds_listonly select_access_size.
  Ltac lengths_from_bounds := map_bounds_listonly select_length.

  Ltac prove_operation_correctness :=
    intros;
    let Hcorrect :=
        lazymatch goal with H : _ = ErrorT.Success _ |- _ => H end in
    apply_correctness_in Hcorrect; [ | eassumption + refine (eq_refl true) .. ];
    fold weight in *; specialize_to_args Hcorrect;
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
            check_args n s c machine_wordsize necessary_requests (ErrorT.Success tt)
            = ErrorT.Success tt).

  Definition carry_mul
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.carry_mul n s c width).
    prove_operation_correctness.
  Defined.

  Definition carry_square
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.carry_square n s c width).
    prove_operation_correctness.
  Defined.

  Definition carry
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.carry n s c width).
    prove_operation_correctness.
  Defined.

  Definition add
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.add n s c width).
    prove_operation_correctness.
  Defined.

  Definition sub
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.sub n s c width).
    prove_operation_correctness.
  Defined.

  Definition opp
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.opp n s c width).
    prove_operation_correctness.
  Defined.

  Definition selectznz
    : operation (type_Z -> type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.selectznz n width).
    prove_operation_correctness.
    Unshelve.
    { apply width. }
  Defined.

  Definition to_bytes
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.to_bytes n s c width).
    prove_operation_correctness.
  Defined.

  Definition from_bytes
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.from_bytes n s c width).
    prove_operation_correctness.
  Defined.

  Definition carry_scmul_const (x : Z)
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (UnsaturatedSolinas.carry_scmul_const n s c width x).
    prove_operation_correctness.
  Defined.

  Definition spec_of_carry_mul name : spec_of name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Rx Ry Rout : mem -> Prop),
        let op := carry_mul in
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n py wy * Ry)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px :: py ::  nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_carry_square name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := carry_square in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px ::  nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_carry name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := carry in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px ::  nil)
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
          (pout :: px :: py ::  nil)
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
          (pout :: px :: py ::  nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_opp name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Ry Rout : mem -> Prop),
        let op := opp in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px ::  nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

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
          (pout :: wc :: px :: py ::  nil)
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
          (pout :: px ::  nil)
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
          (pout :: px ::  nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      n pout wout (op.(postcondition) args))
                   Rout m').

  Definition spec_of_carry_scmul_const (z : Z) (name : string)
    : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Rx Rout : mem -> Prop),
        let op := carry_scmul_const z in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum n px wx * Rx)%sep m ->
        (Bignum n pout wold_out * Rout)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (pout :: px ::  nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat n pout wout (op.(postcondition) args))
                   Rout m').

  Hint Unfold carry_mul carry_square carry add sub opp selectznz
       to_bytes from_bytes carry_scmul_const : defs.
  Hint Unfold
       spec_of_carry_mul
       spec_of_carry_square
       spec_of_carry
       spec_of_add
       spec_of_sub
       spec_of_opp
       spec_of_selectznz
       spec_of_to_bytes
       spec_of_from_bytes
       spec_of_carry_scmul_const : specs.

  Section Proofs.
    Context {ok : Types.ok}.

    (* loose_bounds_ok could be proven in parameterized form, but is a pain
      and is easily computable with parameters plugged in. So for now, leaving
      as a precondition. *)
    Context
      (loose_bounds_ok :
         ZRange.type.option.is_tighter_than
           (t:=type_listZ) (Some loose_bounds)
           (Some (@max_bounds width n)) = true).

    Context (inname_gen_varname_gen_ok : disjoint inname_gen varname_gen)
            (outname_gen_varname_gen_ok : disjoint outname_gen varname_gen)
            (outname_gen_inname_gen_ok : disjoint outname_gen inname_gen).
    Context (inname_gen_unique : unique inname_gen)
            (outname_gen_unique : unique outname_gen).

    Lemma relax_to_max_bounds x :
      list_Z_bounded_by loose_bounds x ->
      list_Z_bounded_by (@max_bounds width n) x.
    Proof. apply relax_list_Z_bounded_by; auto. Qed.

    (* TODO: move to coqutil.Datatypes.List *)
    Local Lemma Forall_repeat : forall {A} (R : A -> Prop) n x,
      R x -> Forall R (repeat x n).
    Proof using. clear.
    intros; induction n; intros; cbn [repeat];
    constructor; auto.
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

    Lemma bounded_by_loose_bounds_length x :
      list_Z_bounded_by loose_bounds x -> length x = n.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      autorewrite with distr_length in *; lia.
    Qed.

    Lemma bounded_by_saturated_bounds_length x :
      list_Z_bounded_by saturated_bounds x -> length x = n.
    Proof.
      cbv [max_bounds].
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite length_saturated_bounds in *. lia.
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

    (* TODO: maybe make a generalized prove_bounds tactic that takes a list of
    bounds? *)
    Ltac assert_bounds x :=
      match goal with
      | H: list_Z_bounded_by ?bs x |- _ => idtac
      | _ => assert (list_Z_bounded_by tight_bounds x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by loose_bounds x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by prime_bytes_bounds x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by (max_bounds n) x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by (byte_bounds n_bytes) x) by prove_bounds_direct
      | _ => fail "could not determine known bounds of" x
      end.
    (* looks for the following combinations of tighter/looser bounds:
       - tight_bounds/saturated_bounds
       - tight_bounds/loose_bounds
       - loose_bounds/saturated_bounds
       - prime_bytes_bounds/byte_bounds
    *)
    Ltac prove_bounds :=
      match goal with |- list_Z_bounded_by ?bs ?x => assert_bounds x end;
      match goal with
      | H : list_Z_bounded_by ?b1 ?x |- list_Z_bounded_by ?b2 ?x =>
        first [ unify b1 b2; apply H
              | unify b1 tight_bounds; unify b2 saturated_bounds;
                apply relax_to_max_bounds, relax_valid; apply H
              | unify b1 tight_bounds; unify b2 loose_bounds;
                apply relax_valid; apply H
              | unify b1 loose_bounds; unify b2 saturated_bounds;
                apply relax_to_max_bounds; apply H
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
        apply bounded_by_loose_bounds_length; prove_bounds
      | |- length _ = n =>
        apply bounded_by_saturated_bounds_length; prove_bounds
      | |- length _ = n_bytes =>
        apply bounded_by_byte_bounds_length; prove_bounds
      | |- length _ = n_bytes =>
        apply bounded_by_prime_bytes_bounds_length; prove_bounds
      | |- n = length _ =>
        symmetry; prove_output_length
      | |- n_bytes = length _ =>
        symmetry; prove_output_length
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
      | |- length ?x = length ?y =>
        rewrite ?map_length in *; congruence
      | _ => idtac
      end.

    Ltac use_translate_func_correct Rout arg_ptrs out_array_ptrs :=
      apply_translate_func_correct Rout arg_ptrs out_array_ptrs;
      [ post_sufficient;
        cbv [Bignum EncodedBignum] in *; sepsimpl;
        prove_length; canonicalize_arrays; ecancel_assumption
      | .. ].

    Ltac solve_lists_reserved out_array_ptrs :=
      exists_all_placeholders out_array_ptrs;
      cbv [Bignum EncodedBignum] in *; sepsimpl;
        lazymatch goal with
        | |- length _ = _ => prove_length
        | |- WeakestPrecondition.get _ _ _ =>
          eexists; rewrite ?map.get_put_diff by eauto;
          rewrite map.get_put_same; solve [eauto]
        | |- sep _ _ _ => canonicalize_arrays; ecancel_assumption
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
        cbv [Bignum EncodedBignum Memory.bytes_per] in *; sepsimpl;
        canonicalize_arrays; ecancel_assumption
      | setup_lists_reserved; solve_lists_reserved out_ptrs ].

    Context (check_args_ok :
               check_args n s c width necessary_requests (ErrorT.Success tt)
               = ErrorT.Success tt).

    Lemma carry_mul_correct name :
      is_correct
        (UnsaturatedSolinas.carry_mul n s c width)
        carry_mul (spec_of_carry_mul name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma carry_square_correct name :
      is_correct
        (UnsaturatedSolinas.carry_square n s c width)
        carry_square (spec_of_carry_square name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma carry_correct name :
      is_correct
        (UnsaturatedSolinas.carry n s c width)
        carry (spec_of_carry name).
    Proof. setup. prove_is_correct Rout. Qed.

    Lemma add_correct name :
      is_correct
        (UnsaturatedSolinas.add n s c width)
        add (spec_of_add name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma sub_correct name :
      is_correct
        (UnsaturatedSolinas.sub n s c width)
        sub (spec_of_sub name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma opp_correct name :
      is_correct
        (UnsaturatedSolinas.opp n s c width)
        opp (spec_of_opp name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma selectznz_correct name :
      is_correct
        (UnsaturatedSolinas.selectznz n width)
        selectznz (spec_of_selectznz name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma to_bytes_correct name :
      is_correct
        (UnsaturatedSolinas.to_bytes n s c width)
        to_bytes (spec_of_to_bytes name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma from_bytes_correct name :
      is_correct
        (UnsaturatedSolinas.from_bytes n s c width)
        from_bytes (spec_of_from_bytes name).
    Proof. setup; prove_is_correct Rout. Qed.

    Lemma carry_scmul_const_correct (x : Z) name :
      is_correct
        (UnsaturatedSolinas.carry_scmul_const n s c width x)
        (carry_scmul_const x) (spec_of_carry_scmul_const x name).
    Proof. setup; prove_is_correct Rout. Qed.
  End Proofs.
End __.
Hint Unfold carry_mul carry_square carry add sub opp selectznz
     to_bytes from_bytes carry_scmul_const : defs.
Hint Unfold
     spec_of_carry_mul
     spec_of_carry_square
     spec_of_carry
     spec_of_add
     spec_of_sub
     spec_of_opp
     spec_of_selectznz
     spec_of_to_bytes
     spec_of_from_bytes
     spec_of_carry_scmul_const : specs.
