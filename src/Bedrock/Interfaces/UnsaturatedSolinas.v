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
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.Arrays.ByteBounds.
Require Import Crypto.Bedrock.Arrays.MakeAccessSizes.
Require Import Crypto.Bedrock.Arrays.MakeListLengths.
Require Import Crypto.Bedrock.Arrays.MaxBounds.
Require Import Crypto.Bedrock.Names.MakeNames.
Require Import Crypto.Bedrock.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Parameters.Defaults.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Bedrock.Interfaces.Tactics.
Require Import Crypto.Bedrock.Interfaces.Operation.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Import Types.
Existing Instances rep.Z rep.listZ_mem.

Import Language.Compilers.
Import Language.Wf.Compilers.
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
    apply UnsaturatedSolinas.carry_mul_correct in H
  | context [UnsaturatedSolinas.carry_square] =>
    apply UnsaturatedSolinas.carry_square_correct in H
  | context [UnsaturatedSolinas.carry] =>
    apply UnsaturatedSolinas.carry_correct in H
  | context [UnsaturatedSolinas.add] =>
    apply UnsaturatedSolinas.add_correct in H
  | context [UnsaturatedSolinas.sub] =>
    apply UnsaturatedSolinas.sub_correct in H
  | context [UnsaturatedSolinas.opp] =>
    apply UnsaturatedSolinas.opp_correct in H
  | context [UnsaturatedSolinas.selectznz] =>
    eapply Primitives.selectznz_correct in H
  | context [UnsaturatedSolinas.to_bytes] =>
    apply UnsaturatedSolinas.to_bytes_correct in H
  | context [UnsaturatedSolinas.from_bytes] =>
    apply UnsaturatedSolinas.from_bytes_correct in H
  | context [UnsaturatedSolinas.carry_scmul_const] =>
    apply UnsaturatedSolinas.carry_scmul_const_correct in H
  | context [UnsaturatedSolinas.encode] =>
    apply UnsaturatedSolinas.encode_correct in H
  | context [UnsaturatedSolinas.zero] =>
    apply UnsaturatedSolinas.zero_correct in H
  | context [UnsaturatedSolinas.one] =>
    apply UnsaturatedSolinas.one_correct in H
  end.

Section Bignum.
  Context {p : Types.parameters}.
  Definition Bignum
    : Semantics.word -> list Semantics.word -> Semantics.mem -> Prop :=
    array scalar (word.of_Z word_size_in_bytes).

  Definition EncodedBignum
    : Semantics.word -> list Byte.byte -> Semantics.mem -> Prop :=
    array ptsto (word.of_Z 1).

  Section Proofs.
    Context {ok : Types.ok}.
    Existing Instance semantics_ok.

    Lemma Bignum_of_bytes n addr bs :
      length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
      Lift1Prop.iff1
        (array ptsto (word.of_Z 1) addr bs)
        (Bignum addr (map word.of_Z
                          (eval_bytes (width:=Semantics.width) bs))).
    Admitted. (* TODO *)

    Lemma Bignum_to_bytes n addr x :
      list_Z_bounded_by (max_bounds n) (map word.unsigned x) ->
      Lift1Prop.iff1
        (Bignum addr x)
        (array ptsto (word.of_Z 1) addr (encode_bytes x)).
    Admitted. (* TODO *)
  End Proofs.
End Bignum.
Notation BignumSuchThat :=
  (fun addr ws P =>
     let xs := map word.unsigned ws in
     sep (emp (P xs)) (Bignum addr ws)).
Notation EncodedBignumSuchThat :=
  (fun addr ws P =>
     let xs := map Byte.byte.unsigned ws in
     sep (emp (P xs)) (EncodedBignum addr ws)).

Section __.
  Context {p : Types.parameters}
          {inname_gen outname_gen : nat -> string}
          (n : nat) (s : Z) (c : list (Z * Z)).
  Local Notation is_correct :=
    (@is_correct p inname_gen outname_gen).
  Local Notation loose_bounds :=
    (UnsaturatedSolinasHeuristics.loose_bounds n s c).
  Local Notation tight_bounds :=
    (UnsaturatedSolinasHeuristics.tight_bounds n s c).
  (* TODO: maybe use Primitives.saturated_bounds instead, and unify this with
  max_bounds? *)
  Local Notation saturated_bounds := (max_bounds n).
  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.
  Local Notation M := (s - Associational.eval c)%Z.
  Definition weight :=
    (ModOps.weight
       (Qnum (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))
       (QDen (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))).
  Local Notation eval := (eval weight n).

  (* for to/from bytes *)
  Local Definition limbwidth :=
    (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
  Local Definition n_bytes :=
    (Freeze.bytes_n (Qnum limbwidth) (Qden limbwidth) n).
  Let prime_bytes_upperbound_list :=
    encode_no_reduce (ModOps.weight 8 1) n_bytes (s - 1).
  Let prime_bytes_bounds :=
    map (fun v : Z => Some {| ZRange.lower := 0; ZRange.upper := v |})
        prime_bytes_upperbound_list.

  Ltac select_access_size bounds :=
    lazymatch bounds with
    | Some saturated_bounds => constr:(access_size.word)
    | Some loose_bounds => constr:(access_size.word)
    | Some tight_bounds => constr:(access_size.word)
    | Some prime_bytes_bounds => constr:(access_size.one)
    | ?b => fail "unable to select access size for bound " b
    end.

  Ltac select_length bounds :=
    lazymatch bounds with
    | Some saturated_bounds => constr:(n)
    | Some loose_bounds => constr:(n)
    | Some tight_bounds => constr:(n)
    | Some prime_bytes_bounds => constr:(n_bytes)
    | ?b => fail "unable to select array length for bound " b
    end.

  Ltac sizes_from_bounds := map_bounds_listonly select_access_size.
  Ltac lengths_from_bounds := map_bounds_listonly select_length.

  Ltac prove_operation_correctness :=
    intros;
    let Hcorrect :=
        lazymatch goal with H : _ = ErrorT.Success _ |- _ => H end in
    apply_correctness_in Hcorrect; [ | eassumption .. ];
    fold weight in *; specialize_to_args Hcorrect;
    postcondition_from_correctness.

  Ltac make_operation inbounds outbounds out :=
    let t := lazymatch goal with |- operation ?t => t end in
    let insizes := sizes_from_bounds inbounds in
    let outsizes := sizes_from_bounds outbounds in
    let inlengths := lengths_from_bounds inbounds in
    let outlengths := lengths_from_bounds outbounds in
    eapply (Build_operation
              t inbounds insizes outsizes inlengths outlengths)
    with (pipeline_out:=out)
         (check_args_ok:=
            check_args n s c machine_wordsize (ErrorT.Success tt)
            = ErrorT.Success tt).

  Definition carry_mul
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (Some loose_bounds, (Some loose_bounds, tt))
                   (Some tight_bounds)
                   (UnsaturatedSolinas.carry_mul n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition carry_square
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (Some loose_bounds, tt)
                   (Some tight_bounds)
                   (UnsaturatedSolinas.carry_square n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition carry
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (Some loose_bounds, tt)
                   (Some tight_bounds)
                   (UnsaturatedSolinas.carry n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition add
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (Some loose_bounds, (Some loose_bounds, tt))
                   (Some tight_bounds)
                   (UnsaturatedSolinas.add n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition sub
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (Some tight_bounds, (Some tight_bounds, tt))
                   (Some loose_bounds)
                   (UnsaturatedSolinas.sub n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition opp
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (Some tight_bounds, tt)
                   (Some loose_bounds)
                   (UnsaturatedSolinas.opp n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition selectznz
    : operation (type_Z -> type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation (Some bit_range, (Some saturated_bounds, (Some saturated_bounds, tt)))
                   (Some loose_bounds)
                   (UnsaturatedSolinas.selectznz n Semantics.width).
    prove_operation_correctness.
    Unshelve.
    { apply Semantics.width. }
    { apply limbwidth. }
  Defined.

  Definition to_bytes
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (Some tight_bounds, tt)
                   (Some prime_bytes_bounds)
                   (UnsaturatedSolinas.to_bytes n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition from_bytes
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (Some prime_bytes_bounds, tt)
                   (Some tight_bounds)
                   (UnsaturatedSolinas.from_bytes n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition carry_scmul_const (x : Z)
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation (Some loose_bounds, tt)
                   (Some tight_bounds)
                   (UnsaturatedSolinas.carry_scmul_const n s c Semantics.width x).
    prove_operation_correctness.
  Defined.

  Definition spec_of_carry_mul name : spec_of name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := carry_mul in
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        op.(precondition) args ->
        (Bignum px wx * Bignum py wy * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_carry_square name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := carry_square in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum px wx  * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_carry name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := carry in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum px wx * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_add name : spec_of name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := add in
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        op.(precondition) args ->
        (Bignum px wx * Bignum py wy * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_sub name : spec_of name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := sub in
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        op.(precondition) args ->
        (Bignum px wx * Bignum py wy * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_opp name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := opp in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum px wx * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_selectznz name : spec_of name :=
    fun functions =>
      forall wc wx px wy py pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := selectznz in
        let args := (word.unsigned wc,
                     (map word.unsigned wx, (map word.unsigned wy, tt))) in
        let c := word.unsigned wc in
        ZRange.is_bounded_by_bool c bit_range = true ->
        op.(precondition) args ->
        (Bignum px wx * Bignum py wy * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (wc :: px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_to_bytes name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := to_bytes in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum px wx * Ra)%sep m ->
        (EncodedBignumSuchThat
           pout wold_out (fun l => length l = n_bytes) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (EncodedBignumSuchThat
                      pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_from_bytes name : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := from_bytes in
        let args := (map byte.unsigned wx, tt) in
        op.(precondition) args ->
        (EncodedBignum px wx  * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat
                      pout wout (op.(postcondition) args))
                   Rr m').

  Definition spec_of_carry_scmul_const (z : Z) (name : string)
    : spec_of name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let op := carry_scmul_const z in
        let args := (map word.unsigned wx, tt) in
        op.(precondition) args ->
        (Bignum px wx * Ra)%sep m ->
        (BignumSuchThat
           pout wold_out (fun l => length l = n) * Rr)%sep m ->
        WeakestPrecondition.call
          functions name t m
          (px :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout (op.(postcondition) args))
                   Rr m').

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

  (* TODO: assert length in Bignum to make output simpler *)
  (* TODO:
     try adding something called "precondition" to operation that constructs seplogic with bounds for each argument + output array given the list of pointers with which the function is called; can use exists for wx, wy
     make "postcondition" exclude these bounds preconditions, and have correctness say precondition -> postcondition *)

  Section Proofs.
    Context {ok : Types.ok}.
    Existing Instance semantics_ok.

    (* loose_bounds_ok could be proven in parameterized form, but is a pain
      and is easily computable with parameters plugged in. So for now, leaving
      as a precondition. *)
    Context
      (loose_bounds_ok :
         ZRange.type.option.is_tighter_than
           (t:=type_listZ) (Some loose_bounds)
           (Some (max_bounds n)) = true).

    Context (inname_gen_varname_gen_ok : disjoint inname_gen varname_gen)
            (outname_gen_varname_gen_ok : disjoint outname_gen varname_gen)
            (outname_gen_inname_gen_ok : disjoint outname_gen inname_gen).
    Context (inname_gen_unique : unique inname_gen)
            (outname_gen_unique : unique outname_gen).

    Lemma relax_to_max_bounds x :
      list_Z_bounded_by loose_bounds x ->
      list_Z_bounded_by (max_bounds n) x.
    Proof. apply relax_list_Z_bounded_by; auto. Qed.

    (* TODO : this proof is going to be way more annoying than it needed to be,
    since there doesn't appear to be any encode_no_reduce_partitions *)
    Lemma relax_to_byte_bounds x :
      list_Z_bounded_by prime_bytes_bounds x ->
      list_Z_bounded_by (byte_bounds n_bytes) x.
    Proof.
      cbv [prime_bytes_bounds byte_bounds prime_bytes_upperbound_list].
    Admitted.

    Lemma bounded_by_loose_bounds_length x :
      list_Z_bounded_by loose_bounds x -> length x = n.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite @length_loose_bounds in *. lia.
    Qed.

    Lemma bounded_by_saturated_bounds_length x :
      list_Z_bounded_by saturated_bounds x -> length x = n.
    Proof.
      cbv [saturated_bounds max_bounds].
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite repeat_length in *. lia.
    Qed.

    Lemma bounded_by_prime_bytes_bounds_length x :
      list_Z_bounded_by prime_bytes_bounds x -> length x = n_bytes.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      cbv [prime_bytes_bounds prime_bytes_upperbound_list] in *.
      rewrite map_length, length_encode_no_reduce in *. lia.
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
      | _ => fail "could not determine known bounds of " x
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
                apply relax_to_max_bounds, relax_correct; apply H
              | unify b1 tight_bounds; unify b2 loose_bounds;
                apply relax_correct; apply H
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
              apply partition_bounded_by)
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

    Ltac use_translate_func_correct Rin Rout arg_ptrs out_array_ptrs :=
      apply_translate_func_correct Rin Rout arg_ptrs out_array_ptrs;
      [ post_sufficient;
        cbv [Bignum EncodedBignum] in *;
        canonicalize_arrays; ecancel_assumption
      | .. ].

    Ltac solve_lists_reserved out_array_ptrs :=
      exists_all_placeholders out_array_ptrs;
      cbv [Bignum EncodedBignum] in *;
      canonicalize_arrays; ecancel_assumption.

    Ltac prove_is_correct Rin Rout :=
      let args := lazymatch goal with
                  | H : postcondition _ ?args _ |- _ => args end in
      let arg_ptrs := get_bedrock2_arglist args in
      let all_ptrs := lazymatch goal with
                      | |- call _ _ _ _ ?in_ptrs _ => in_ptrs end in
      let out_ptrs := get_out_array_ptrs arg_ptrs all_ptrs in
      use_translate_func_correct Rin Rout arg_ptrs out_ptrs;
      solve_translate_func_subgoals prove_bounds prove_output_length;
      [ exists_arg_pointers;
        cbv [Bignum EncodedBignum] in *;
        canonicalize_arrays; ecancel_assumption
      | setup_lists_reserved; solve_lists_reserved out_ptrs ].

    Context (check_args_ok :
               check_args n s c Semantics.width (ErrorT.Success tt)
               = ErrorT.Success tt).

    Lemma carry_mul_correct name :
      is_correct
        (UnsaturatedSolinas.carry_mul n s c Semantics.width)
        carry_mul (spec_of_carry_mul name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma carry_square_correct name :
      is_correct
        (UnsaturatedSolinas.carry_square n s c Semantics.width)
        carry_square (spec_of_carry_square name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma carry_correct name :
      is_correct
        (UnsaturatedSolinas.carry n s c Semantics.width)
        carry (spec_of_carry name).
    Proof. setup. prove_is_correct Ra Rr. Qed.

    Lemma add_correct name :
      is_correct
        (UnsaturatedSolinas.add n s c Semantics.width)
        add (spec_of_add name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma sub_correct name :
      is_correct
        (UnsaturatedSolinas.sub n s c Semantics.width)
        sub (spec_of_sub name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma opp_correct name :
      is_correct
        (UnsaturatedSolinas.opp n s c Semantics.width)
        opp (spec_of_opp name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma selectznz_correct name :
      is_correct
        (UnsaturatedSolinas.selectznz n Semantics.width)
        selectznz (spec_of_selectznz name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma to_bytes_correct name :
      is_correct
        (UnsaturatedSolinas.to_bytes n s c Semantics.width)
        to_bytes (spec_of_to_bytes name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma from_bytes_correct name :
      is_correct
        (UnsaturatedSolinas.from_bytes n s c Semantics.width)
        from_bytes (spec_of_from_bytes name).
    Proof. setup; prove_is_correct Ra Rr. Qed.

    Lemma carry_scmul_const_correct (x : Z) name :
      is_correct
        (UnsaturatedSolinas.carry_scmul_const n s c Semantics.width x)
        (carry_scmul_const x) (spec_of_carry_scmul_const x name).
    Proof. setup; prove_is_correct Ra Rr. Qed.
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
