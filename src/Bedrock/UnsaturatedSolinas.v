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
Require Import Crypto.Bedrock.ByteBounds.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.MakeAccessSizes.
Require Import Crypto.Bedrock.MakeNames.
Require Import Crypto.Bedrock.MakeListLengths.
Require Import Crypto.Bedrock.MaxBounds.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.VarnameGenerator.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Language.API.
Require Import Coq.Lists.List. (* after SeparationLogic *)

Import Language.Compilers.
Import Types Types.Notations.
Existing Instances rep.Z rep.listZ_mem.

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

Section __.
  Context {p : Types.parameters}
          {inname_gen outname_gen : nat -> string}
          (n : nat) (s : Z) (c : list (Z * Z)).
  Context (carry_mul_name add_name to_bytes_name : string).
  Local Notation loose_bounds := (UnsaturatedSolinas.loose_bounds n s c).
  Local Notation tight_bounds := (UnsaturatedSolinas.tight_bounds n s c).
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

  (* convenience notation for readability *)
  Local Notation foreach_arg F t :=
    (type.for_each_lhs_of_arrow F t) (only parsing).
  Local Notation foreach_ret F t :=
    (F (type.base (type.final_codomain t))) (only parsing).

  Definition make_bedrock_func_with_sizes
             {t} insizes outsizes inlengths (res : API.Expr t)
    : list string * list string * cmd.cmd :=
    fst (translate_func res
                        (make_innames (inname_gen:=inname_gen) _)
                        inlengths insizes
                        (make_outnames (outname_gen:=outname_gen) _)
                        outsizes).

  Record operation (t : API.type) :=
    { name : string;
      inbounds : foreach_arg ZRange.type.option.interp t;
      input_array_sizes : foreach_arg access_sizes t;
      output_array_sizes : foreach_ret access_sizes t;
      input_array_lengths : foreach_arg list_lengths t;
      output_array_lengths : foreach_ret list_lengths t;
      pipeline_out : Pipeline.ErrorT (API.Expr t);
      postcondition : foreach_arg API.interp_type t
                      -> foreach_ret API.interp_type t -> Prop;
      correctness :
        check_args
          n s c Semantics.width (ErrorT.Success tt) = ErrorT.Success tt ->
        forall res,
          pipeline_out = ErrorT.Success res ->
          forall args,
            postcondition args (type.app_curried (API.Interp res) args)
    }.
  Arguments name {_}.
  Arguments inbounds {_}.
  Arguments input_array_sizes {_}.
  Arguments output_array_sizes {_}.
  Arguments input_array_lengths {_}.
  Arguments output_array_lengths {_}.
  Arguments pipeline_out {_}.
  Arguments postcondition {_}.
  Arguments correctness {_}.

  Definition make_bedrock_func
             {t} (op : operation t) (res : API.Expr t)
    : bedrock_func :=
    (op.(name), make_bedrock_func_with_sizes
                  (op.(input_array_sizes)) (op.(output_array_sizes))
                  (op.(input_array_lengths)) res).

  Ltac select_access_size bounds :=
    lazymatch bounds with
    | Some loose_bounds => constr:(access_size.word)
    | Some tight_bounds => constr:(access_size.word)
    | Some prime_bytes_bounds => constr:(access_size.one)
    | ?b => fail "unable to select access size for bound " b
    end.

  Ltac sizes_from_bounds bounds :=
    lazymatch bounds with
    | (?a, ?b) =>
      let x := sizes_from_bounds a in
      let y := sizes_from_bounds b in
      constr:((x, y))
    | tt => constr:(tt)
    | ?b => lazymatch type of b with
            | option (list _) => select_access_size b
            | _ => constr:(tt)
            end
    end.

  Ltac select_length bounds :=
    lazymatch bounds with
    | Some loose_bounds => constr:(n)
    | Some tight_bounds => constr:(n)
    | Some prime_bytes_bounds => constr:(n_bytes)
    | ?b => fail "unable to select array length for bound " b
    end.

  Ltac lengths_from_bounds bounds :=
    lazymatch bounds with
    | (?a, ?b) =>
      let x := lengths_from_bounds a in
      let y := lengths_from_bounds b in
      constr:((x, y))
    | tt => constr:(tt)
    | ?b => lazymatch type of b with
            | option (list _) => select_length b
            | _ => constr:(tt)
            end
    end.

  Ltac apply_correctness_in H :=
    match type of H with
    | context [UnsaturatedSolinas.carry_mul] =>
      apply UnsaturatedSolinas.carry_mul_correct in H
    | context [UnsaturatedSolinas.add] =>
      apply UnsaturatedSolinas.add_correct in H
    | context [UnsaturatedSolinas.sub] =>
      apply UnsaturatedSolinas.sub_correct in H
    | context [UnsaturatedSolinas.opp] =>
      apply UnsaturatedSolinas.opp_correct in H
    | context [UnsaturatedSolinas.carry] =>
      apply UnsaturatedSolinas.carry_correct in H
    | context [UnsaturatedSolinas.encode] =>
      apply UnsaturatedSolinas.encode_correct in H
    | context [UnsaturatedSolinas.zero] =>
      apply UnsaturatedSolinas.zero_correct in H
    | context [UnsaturatedSolinas.one] =>
      apply UnsaturatedSolinas.one_correct in H
    | context [UnsaturatedSolinas.to_bytes] =>
      apply UnsaturatedSolinas.to_bytes_correct in H
    | context [UnsaturatedSolinas.from_bytes] =>
      apply UnsaturatedSolinas.from_bytes_correct in H
    end.
  Ltac apply_correctness :=
    match goal with H : _ = ErrorT.Success _ |- _ =>
                    apply_correctness_in H;
                    [ | assumption .. ]
    end.

  Ltac specialize_to_args Hcorrect :=
    let A := fresh "A" in
    let A' := fresh "A" in
    match goal with
      a : type.for_each_lhs_of_arrow API.interp_type _ |- _ =>
      cbn in a; set (A:=a)
    end;
    repeat match type of A with
             (?xt * ?yt)%type =>
             specialize (Hcorrect (fst A));
             set (A':=snd A); subst A;
             rename A' into A
           end;
    subst A.

  Ltac postcondition_from_correctness :=
    cbn [type.app_curried API.interp_type
                          Language.Compilers.base.interp
                          Compilers.base_interp] in *;
  lazymatch goal with
  | Hcorrect : context [?res] |- ?post ?args ?res =>
    let T := lazymatch type of Hcorrect with ?T => T end in
    let F := lazymatch (eval pattern res in T) with
               ?f _ => f end in
    let F := lazymatch (eval pattern args in F) with
               ?f _ => f end in
    let H := fresh in
    assert (F args res) as H by exact Hcorrect;
      exact H
  end.

  Ltac prove_operation_correctness :=
    intros;
    let Hcorrect :=
        lazymatch goal with H : _ = ErrorT.Success _ |- _ => H end in
    apply_correctness_in Hcorrect; fold weight in *;
    specialize_to_args Hcorrect; postcondition_from_correctness.

  Ltac make_operation name inbounds outbounds out :=
    let t := lazymatch goal with |- operation ?t => t end in
    let insizes := sizes_from_bounds inbounds in
    let outsizes := sizes_from_bounds outbounds in
    let inlengths := lengths_from_bounds inbounds in
    let outlengths := lengths_from_bounds outbounds in
    eapply (Build_operation
              t name inbounds
              insizes outsizes inlengths outlengths)
           with (pipeline_out:=out).

  Definition carry_mul
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation carry_mul_name
                   (Some loose_bounds, (Some loose_bounds, tt))
                   (Some tight_bounds)
                   (UnsaturatedSolinas.carry_mul n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition add
    : operation (type_listZ -> type_listZ -> type_listZ).
  Proof.
    make_operation add_name
                   (Some loose_bounds, (Some loose_bounds, tt))
                   (Some tight_bounds)
                   (UnsaturatedSolinas.add n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition to_bytes
    : operation (type_listZ -> type_listZ).
  Proof.
    make_operation to_bytes_name
                   (Some tight_bounds, tt)
                   (Some prime_bytes_bounds)
                   (UnsaturatedSolinas.to_bytes n s c Semantics.width).
    prove_operation_correctness.
  Defined.

  Definition Bignum
    : Semantics.word -> list Semantics.word -> Semantics.mem -> Prop :=
    array scalar (word.of_Z word_size_in_bytes).

  Definition EncodedBignum
    : Semantics.word -> list Byte.byte -> Semantics.mem -> Prop :=
    array ptsto (word.of_Z 1).

  Notation BignumSuchThat :=
    (fun addr ws P =>
       let xs := map word.unsigned ws in
       sep (emp (P xs)) (Bignum addr ws)).

  Notation EncodedBignumSuchThat :=
    (fun addr ws P =>
       let xs := map Byte.byte.unsigned ws in
       sep (emp (P xs)) (EncodedBignum addr ws)).

  Declare Scope sep_scope.
  Local Delimit Scope sep_scope with sep.
  Local Infix "*" := sep : sep_scope.

  Definition spec_of_carry_mul : spec_of carry_mul_name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        let X := BignumSuchThat px wx (list_Z_bounded_by loose_bounds) in
        let Y := BignumSuchThat py wy (list_Z_bounded_by loose_bounds) in
        let Out := BignumSuchThat pout wold_out (fun l => length l = n) in
        (X * Y * Ra)%sep m ->
        (Out * Rr)%sep m ->
        WeakestPrecondition.call
          functions carry_mul_name t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout
                                   (carry_mul.(postcondition) args))
                   Rr m').

  Definition spec_of_add : spec_of add_name :=
    fun functions =>
      forall wx wy px py pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let args := (map word.unsigned wx, (map word.unsigned wy, tt)) in
        let X := BignumSuchThat px wx (list_Z_bounded_by tight_bounds) in
        let Y := BignumSuchThat py wy (list_Z_bounded_by tight_bounds) in
        let Out := BignumSuchThat pout wold_out (fun l => length l = n) in
        (X * Y * Ra)%sep m ->
        (Out * Rr)%sep m ->
        WeakestPrecondition.call
          functions add_name t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (BignumSuchThat pout wout
                                   (add.(postcondition) args))
                   Rr m').

  Definition spec_of_to_bytes : spec_of add_name :=
    fun functions =>
      forall wx px pout wold_out t m
             (Ra Rr : Semantics.mem -> Prop),
        let args := (map word.unsigned wx, tt) in
        let X := BignumSuchThat px wx (list_Z_bounded_by tight_bounds) in
        let Out := EncodedBignumSuchThat
                     pout wold_out (fun l => length l = n_bytes) in
        (X  * Ra)%sep m ->
        (Out * Rr)%sep m ->
        WeakestPrecondition.call
          functions to_bytes_name t m
          (px :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             exists wout,
               sep (EncodedBignumSuchThat
                      pout wout (to_bytes.(postcondition) args))
                   Rr m').

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

    Lemma Bignum_of_bytes addr bs :
      length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
      Lift1Prop.iff1
        (array ptsto (word.of_Z 1) addr bs)
        (Bignum addr (map word.of_Z
                          (eval_bytes (width:=Semantics.width) bs))).
    Admitted. (* TODO *)

    Lemma Bignum_to_bytes addr x :
      list_Z_bounded_by (max_bounds n) (map word.unsigned x) ->
      Lift1Prop.iff1
        (Bignum addr x)
        (array ptsto (word.of_Z 1) addr (encode_bytes x)).
    Admitted. (* TODO *)

    Lemma relax_to_max_bounds x :
      list_Z_bounded_by loose_bounds x ->
      list_Z_bounded_by (max_bounds n) x.
    Proof. apply relax_list_Z_bounded_by; auto. Qed.

    Lemma bounded_by_loose_bounds_length x :
      list_Z_bounded_by loose_bounds x -> length x = n.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite length_loose_bounds in *. lia.
    Qed.

    (* TODO: move *)
    Lemma Forall_word_unsigned_within_access_size x :
      Forall
        (fun z : Z =>
           0 <= z < 2 ^ (Z.of_nat (Memory.bytes_per (width:=Semantics.width) access_size.word) * 8))
        (map word.unsigned x).
    Proof.
      eapply Forall_impl; [ | solve [apply Forall_map_unsigned] ];
        cbv beta; intros.
      rewrite bits_per_word_eq_width by auto using width_0mod_8; lia.
    Qed.

    Ltac crush_list_ptr_subgoals :=
      repeat match goal with
             | _ => progress cbv [WeakestPrecondition.literal]
             | _ => rewrite word.of_Z_unsigned
             | _ => rewrite map.get_put_diff by congruence
             | _ => rewrite map.get_put_same by auto
             | |- WeakestPrecondition.get _ _ _ => eexists
             | _ => solve [apply Forall_word_unsigned_within_access_size]
             | _ => solve [apply word.unsigned_range]
             | _ => solve [auto using eval_bytes_range]
             | _ => reflexivity
             end.
    Ltac exists_list_ptr p :=
      exists p; sepsimpl; [ ];
             eexists; sepsimpl;
             [ solve [crush_list_ptr_subgoals] .. | ];
             eexists; sepsimpl;
             [ solve [crush_list_ptr_subgoals] .. | ].
    Ltac next_argument :=
      (exists 1%nat); sepsimpl; cbn [firstn skipn];
      [ solve [eauto using firstn_length_le] | ].
    Ltac prove_bounds_direct :=
      match goal with
      | H : _ |- _ => apply H; solve [auto]
      end.
    Ltac assert_bounds x :=
      match goal with
      | H: list_Z_bounded_by ?bs x |- _ => idtac
      | _ => assert (list_Z_bounded_by tight_bounds x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by loose_bounds x) by prove_bounds_direct
      | _ => assert (list_Z_bounded_by (max_bounds n) x) by prove_bounds_direct
      | _ => fail "could not determine known bounds of " x
      end.
    Ltac prove_bounds :=
      match goal with |- list_Z_bounded_by ?bs ?x => assert_bounds x end;
      match goal with
      | H : list_Z_bounded_by ?b1 ?x |- list_Z_bounded_by ?b2 ?x =>
        first [ unify b1 b2; apply H
              | unify b1 tight_bounds; unify b2 (max_bounds n);
                apply relax_to_max_bounds, relax_correct; apply H
              | unify b1 tight_bounds; unify b2 loose_bounds;
                apply relax_correct; apply H
              | unify b1 loose_bounds; unify b2 (max_bounds n);
                apply relax_to_max_bounds; apply H ]
      end.

    Context (check_args_ok :
               check_args n s c Semantics.width (ErrorT.Success tt)
               = ErrorT.Success tt).

    Definition is_correct
               {t : API.type}
               (start : Pipeline.ErrorT (API.Expr t))
               (op : operation t)
               {name : string} (spec : spec_of name) : Prop :=
      (forall res : API.Expr t,
          start = ErrorT.Success res ->
          expr.Wf3 res ->
          valid_func (res (fun _ : API.type => unit)) ->
          forall functions,
            spec (make_bedrock_func op res :: functions)).

    Ltac setup :=
      match goal with
        |- is_correct _ ?def ?spec =>
        cbv [is_correct spec make_bedrock_func] in *; intros;
        sepsimpl;
        cbn [def name inbounds input_array_sizes output_array_sizes
                 input_array_lengths output_array_lengths
                 pipeline_out correctness] in *
      end;
      match goal with |- context [postcondition ?op ?args] =>
                      let H := fresh in
                      pose proof (correctness op) as H;
                      repeat specialize (H ltac:(assumption));
                      specialize (H args)
      end; cleanup.

    Ltac simplify_translate_func_postcondition :=
      match goal with
        H : context [sep _ _ ?m] |- context [_ ?m] =>
        cbn - [Memory.bytes_per translate_func] in H
      end;
    sepsimpl_hyps.

    Ltac ssubst :=
      repeat match goal with
             | H : literal (word.unsigned _) (eq _) |- _ =>
               inversion H as [H']; clear H;
               rewrite word.of_Z_unsigned in H'
             | H : word.unsigned _ = word.unsigned _ |- _ =>
               apply word.unsigned_inj in H
             end; subst.

    Lemma carry_mul_correct :
      is_correct
        (UnsaturatedSolinas.carry_mul n s c Semantics.width)
        carry_mul spec_of_carry_mul.
    Proof.
      setup.

      (* TODO: put something to this effect in [operation] to make it more
         uniform? *)
      (* fetch output length for convenience *)
      let out := lazymatch goal with
                 | H : postcondition _ _ ?out |- _ => out end in
      assert (length out = n)
        by (apply bounded_by_loose_bounds_length; prove_bounds).

      (* TODO: automate flat_args, out_ptrs? *)
      (* use translate_func_correct to get the translation postcondition *)
      let a := lazymatch goal with
               | H : postcondition _ ?args _ |- _ => args end in
      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=a) (flat_args := [px; py]) ].
      { (* prove that the translation postcondition is sufficient *)
        repeat intro.
        simplify_translate_func_postcondition.
        ssplit; [ congruence | congruence | eexists ].
        cbn [type.app_curried fst snd] in *; cbv [expr.Interp] in *.
        sepsimpl;
          [ match goal with H : map word.unsigned _ = _ |- _ =>
                            rewrite H; solve [eauto] end | ].
        ssubst. cbv [Bignum].
        rewrite word_size_in_bytes_eq.
        use_sep_assumption.
        rewrite array_truncated_scalar_scalar_iff1.
        cancel. }

      (* Now, we prove translate_func preconditions.
         First, take care of all the easy ones. *)
      all: auto using make_innames_varname_gen_disjoint,
           make_outnames_varname_gen_disjoint,
           make_innames_make_outnames_disjoint,
           flatten_make_innames_NoDup, flatten_make_outnames_NoDup.

      { (* list lengths are correct *)
        cbn.
        rewrite !bounded_by_loose_bounds_length by prove_bounds.
        reflexivity. }
      { (* arg pointers are correct *)
        cbn - [Memory.bytes_per]; sepsimpl.
        next_argument. exists_list_ptr px.
        next_argument. exists_list_ptr py.
        cbv [Bignum] in *.
        repeat seprewrite array_truncated_scalar_scalar_iff1.
        rewrite <-word_size_in_bytes_eq.
        ecancel_assumption. }
      { (* input access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* input access sizes are accurate *)
        cbn - [Memory.bytes_per]; ssplit; try tauto;
          eapply max_bounds_range_iff; prove_bounds. }
      { (* output access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* output access sizes are accurate *)
        cbn - [Memory.bytes_per].
        eapply max_bounds_range_iff; prove_bounds. }
      { (* space is reserved for output lists *)
        cbn - [Memory.bytes_per]. sepsimpl.
        cbv [expr.Interp] in *.
        cbn [fst snd type.app_curried Compilers.base_interp] in *.
        exists (map word.unsigned wold_out).
        sepsimpl;
          [ rewrite map_length in *; congruence | ].
        exists pout; sepsimpl; [ ].
        eexists.
        sepsimpl; [ reflexivity
                  | rewrite bits_per_word_eq_width
                    by auto using width_0mod_8;
                    solve [apply Forall_map_unsigned]
                  | ].
        eexists.
        sepsimpl; [ reflexivity
                  | eexists; rewrite ?map.get_put_diff by congruence;
                    rewrite map.get_put_same; split; reflexivity
                  | ].
        cbv [Bignum] in *.
        rewrite <-word_size_in_bytes_eq.
        repeat seprewrite array_truncated_scalar_scalar_iff1.
        ecancel_assumption. }
    Qed.

    Lemma add_correct :
      is_correct
        (UnsaturatedSolinas.add n s c Semantics.width)
        add spec_of_add.
    Proof.
      setup.

      (* TODO: put something to this effect in [operation] to make it more
         uniform? *)
      (* fetch output length for convenience *)
      let out := lazymatch goal with
                 | H : postcondition _ _ ?out |- _ => out end in
      assert (length out = n)
        by (apply bounded_by_loose_bounds_length; prove_bounds).

      (* TODO: automate flat_args, out_ptrs? *)
      (* use translate_func_correct to get the translation postcondition *)
      let a := lazymatch goal with
               | H : postcondition _ ?args _ |- _ => args end in
      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=a) (flat_args := [px; py]) ].
      { (* prove that the translation postcondition is sufficient *)
        repeat intro.
        simplify_translate_func_postcondition.
        ssplit; [ congruence | congruence | eexists ].
        cbn [type.app_curried fst snd] in *; cbv [expr.Interp] in *.
        sepsimpl;
          [ match goal with H : map word.unsigned _ = _ |- _ =>
                            rewrite H; solve [eauto] end | ].
        ssubst. cbv [Bignum].
        rewrite word_size_in_bytes_eq.
        use_sep_assumption.
        rewrite array_truncated_scalar_scalar_iff1.
        cancel. }

      (* Now, we prove translate_func preconditions.
         First, take care of all the easy ones. *)
      all: auto using make_innames_varname_gen_disjoint,
           make_outnames_varname_gen_disjoint,
           make_innames_make_outnames_disjoint,
           flatten_make_innames_NoDup, flatten_make_outnames_NoDup.

      { (* list lengths are correct *)
        cbn.
        rewrite !bounded_by_loose_bounds_length by prove_bounds.
        reflexivity. }
      { (* arg pointers are correct *)
        cbn - [Memory.bytes_per]; sepsimpl.
        next_argument. exists_list_ptr px.
        next_argument. exists_list_ptr py.
        cbv [Bignum] in *.
        repeat seprewrite array_truncated_scalar_scalar_iff1.
        rewrite <-word_size_in_bytes_eq.
        ecancel_assumption. }
      { (* input access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* input access sizes are accurate *)
        cbn - [Memory.bytes_per]; ssplit; try tauto;
          eapply max_bounds_range_iff; prove_bounds. }
      { (* output access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* output access sizes are accurate *)
        cbn - [Memory.bytes_per].
        eapply max_bounds_range_iff; prove_bounds. }
      { (* space is reserved for output lists *)
        cbn - [Memory.bytes_per]. sepsimpl.
        cbv [expr.Interp] in *.
        cbn [fst snd type.app_curried Compilers.base_interp] in *.
        exists (map word.unsigned wold_out).
        sepsimpl;
          [ rewrite map_length in *; congruence | ].
        exists pout; sepsimpl; [ ].
        eexists.
        sepsimpl; [ reflexivity
                  | rewrite bits_per_word_eq_width
                    by auto using width_0mod_8;
                    solve [apply Forall_map_unsigned]
                  | ].
        eexists.
        sepsimpl; [ reflexivity
                  | eexists; rewrite ?map.get_put_diff by congruence;
                    rewrite map.get_put_same; split; reflexivity
                  | ].
        cbv [Bignum] in *.
        rewrite <-word_size_in_bytes_eq.
        repeat seprewrite array_truncated_scalar_scalar_iff1.
        ecancel_assumption. }
    Qed.

    Lemma to_bytes_correct :
      is_correct
        (UnsaturatedSolinas.to_bytes n s c Semantics.width)
        to_bytes spec_of_to_bytes.
    Proof.
      setup.

      (* TODO: put something to this effect in [operation] to make it more
         uniform? *)
      (* fetch output length for convenience *)
      (* differs from add/mul:
        let out := lazymatch goal with
                    | H : postcondition _ _ ?out |- _ => out end in
        assert (length out = n)
            by (apply bounded_by_loose_bounds_length; prove_bounds). *)
      lazymatch goal with
      | H : postcondition ?op _ ?out |- _ =>
        assert (length out = n_bytes)
          by (erewrite <-Partition.length_partition;
              cbv [n_bytes limbwidth];
              cbn [fst snd postcondition op] in H;
              rewrite <-H by prove_bounds;
              reflexivity)
      end.

      (* assert output bounds for convenience *)
      match goal with
      | H : postcondition ?op _ ?e |- _ =>
        assert (list_Z_bounded_by (byte_bounds n_bytes) e)
          by (cbn [fst snd postcondition op] in H;
              rewrite H by prove_bounds;
              apply partition_bounded_by)
      end.
      (* end differ *)

      (* TODO: automate flat_args, out_ptrs? *)
      (* use translate_func_correct to get the translation postcondition *)
      (* differs from add/mul:
        let a := lazymatch goal with
                | H : postcondition _ ?args _ |- _ => args end in
        eapply Proper_call;
            [ | eapply translate_func_correct with
                    (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                    (args:=a) (flat_args := [px; py]) ]. *)
      let a := lazymatch goal with
               | H : postcondition _ ?args _ |- _ => args end in
      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=a) (flat_args := [px]) ].
      { (* prove that the translation postcondition is sufficient *)
        repeat intro.
        simplify_translate_func_postcondition.
        ssplit; [ congruence | congruence | eexists ].
        cbn [type.app_curried fst snd] in *; cbv [expr.Interp] in *.
        (* differs from add/mul:
            sepsimpl;
            [ match goal with H : map word.unsigned _ = _ |- _ =>
                                rewrite H; solve [eauto] end | ].
            ssubst. cbv [Bignum].
            rewrite word_size_in_bytes_eq. *)
        sepsimpl;
          [ erewrite byte_map_unsigned_of_Z, map_byte_wrap_bounded
            by (eapply byte_bounds_range_iff; eauto);
            match goal with H : _ |- _ => apply H; assumption end | ].
        ssubst. cbv [EncodedBignum].
        change (Z.of_nat (Memory.bytes_per access_size.one)) with 1 in *.
        match goal with H : map word.unsigned _ = expr.interp _ _ _ |- _ =>
                        rewrite <-H in * end.
        (* end differ *)
        use_sep_assumption.
        rewrite array_truncated_scalar_ptsto_iff1.
        cancel. }

      (* Now, we prove translate_func preconditions.
         First, take care of all the easy ones. *)
      all: auto using make_innames_varname_gen_disjoint,
           make_outnames_varname_gen_disjoint,
           make_innames_make_outnames_disjoint,
           flatten_make_innames_NoDup, flatten_make_outnames_NoDup.

      { (* list lengths are correct *)
        cbn.
        rewrite !bounded_by_loose_bounds_length by prove_bounds.
        reflexivity. }
      { (* arg pointers are correct *)
        cbn - [Memory.bytes_per]; sepsimpl.
        next_argument. exists_list_ptr px.
        (* differs from add/mul:
            next_argument. exists_list_ptr py.
         *)
        (* end differ *)
        cbv [Bignum] in *.
        repeat seprewrite array_truncated_scalar_scalar_iff1.
        rewrite <-word_size_in_bytes_eq.
        ecancel_assumption. }
      { (* input access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* input access sizes are accurate *)
        cbn - [Memory.bytes_per]; ssplit; try tauto;
          eapply max_bounds_range_iff; prove_bounds. }
      { (* output access sizes are legal *)
        (* differs from add/mul:
            pose proof bits_per_word_le_width.
            cbn - [Memory.bytes_per]; tauto. *)
         cbn. apply width_ge_8. (* end differ *) }
      { (* output access sizes are accurate *)
        cbn - [Memory.bytes_per].
        (* differs from add/mul:
           cbv [expr.Interp] in *.
           eapply max_bounds_range_iff; prove_bounds. *)
        cbn [type.app_curried fst snd] in *. cbv [expr.Interp] in *.
        eapply byte_bounds_range_iff. prove_bounds. (* end differ *)}
      { (* space is reserved for output lists *)
        cbn - [Memory.bytes_per]. sepsimpl.
        cbv [expr.Interp] in *.
        cbn [fst snd type.app_curried Compilers.base_interp] in *.
        (* differs from mul/add:
        exists (map word.unsigned wold_out). *)
        exists (map byte.unsigned wold_out).
        (* end differ *)
        sepsimpl; [ rewrite map_length in *; congruence | ].
        exists pout; sepsimpl; [ ].
        (* differs from mul/add:
        eexists.
        sepsimpl; [ reflexivity
                  | rewrite bits_per_word_eq_width
                    by auto using width_0mod_8;
                    solve [apply Forall_map_unsigned]
                  | ]. *)
        exists (map word.of_Z (map byte.unsigned wold_out)).
        sepsimpl;
          [ rewrite map_unsigned_of_Z;
            solve [eauto using map_word_wrap_bounded,
                   byte_unsigned_within_max_bounds]
          | solve [apply Forall_map_byte_unsigned] | ].
        (* end differ *)
        eexists.
        sepsimpl; [ reflexivity
                  | eexists; rewrite ?map.get_put_diff by congruence;
                    rewrite map.get_put_same; split; reflexivity
                  | ].
        (* differs from mul/add:
        cbv [Bignum] in *.
        rewrite <-word_size_in_bytes_eq.
        repeat seprewrite array_truncated_scalar_scalar_iff1. *)
        cbv [EncodedBignum] in *.
        rewrite map_unsigned_of_Z.
        erewrite map_word_wrap_bounded by
            auto using byte_unsigned_within_max_bounds.
        change (Z.of_nat (Memory.bytes_per access_size.one)) with 1 in *.
        seprewrite array_truncated_scalar_ptsto_iff1.
        rewrite byte_map_of_Z_unsigned.
        (* end differ *)
        ecancel_assumption. }
    Qed.
  End Proofs.
End __.

  (* TODO: delete if unused
  Fixpoint word_base_interp (t : base.type) : Type :=
    match t with
    | base.type.prod a b => word_base_interp a * word_base_interp b
    | base_listZ => list Semantics.word
    | _ => Semantics.word
    end.
  Definition word_interp := type.interp word_base_interp.
  Fixpoint ptr_base_interp (t : base.type) : Type :=
    match t with
    | base.type.prod a b => ptr_base_interp a * ptr_base_interp b
    | _ => Semantics.word
    end.
  Definition ptr_interp := type.interp ptr_base_interp.

  Fixpoint in_bounds {t}
    : ZRange.type.base.option.interp t
      -> ptr_base_interp t -> word_base_interp t
      -> Semantics.mem -> Prop :=
    match t with
    | base.type.prod a b =>
      fun bounds ptrs values =>
        sep (in_bounds (fst bounds) (fst ptrs) (fst values))
            (in_bounds (snd bounds) (snd ptrs) (snd values))
    | base_listZ =>
      fun bounds ptr value =>
        match bounds with
        | Some bounds =>
          BignumSuchThat ptr value (list_Z_bounded_by bounds)
        | None => emp False
        end
    | base_Z =>
      fun bounds ptr value =>
        sep (emp (ZRange.type.base.option.is_bounded_by
                    bounds (word.unsigned value) = true))
            (scalar ptr value)
    | _ => fun _ _ _ => emp False
    end.
  Fixpoint input_ok {t}
    : foreach_arg ZRange.type.option.interp t
      -> foreach_arg ptr_interp t
      -> foreach_arg word_interp t
      -> Semantics.mem -> Prop :=
    match t with
    | type.base b => fun _ _ _ => emp True
    | type.arrow (type.base s) d =>
      fun bounds ptrs values =>
        sep (in_bounds (fst bounds) (fst ptrs) (fst values))
            (input_ok (snd bounds) (snd ptrs) (snd values))
    | _ => fun _ _ _ => emp False
    end.

  (* What would be really nice:
     In [operation], include
        in_pre : foreach_arg ptr_interp t ->
                 foreach_arg word_interp t ->
                 Semantics.mem -> Prop
        out_pre: foreach_ret ptr_interp t ->
                 foreach_ret word_interp t ->
    and use tactics to infer these

    pros :
         spec becomes very simple and duplicates across operations
    cons:
        makes spec harder to view/modify
  *)

  Fixpoint lengths_match {t}
    : base_list_lengths t
      -> ptr_base_interp t -> word_base_interp t
      -> Semantics.mem -> Prop :=
    match t with
    | base.type.prod a b =>
      fun lengths ptrs values =>
        sep (lengths_match (fst lengths) (fst ptrs) (fst values))
            (lengths_match (snd lengths) (snd ptrs) (snd values))
    | base_listZ =>
      fun n ptr value =>
        BignumSuchThat ptr value (fun l => length l = n)
    | base_Z =>
      fun lengths ptr value =>
        sep (emp (ZRange.type.base.option.is_bounded_by
                    lengths (word.unsigned value) = true))
            (scalar ptr value)
    | _ => fun _ _ _ => emp False
    end.
  Definition output_placeholder_ok {t}
    : foreach_ret list_lengths t
      -> foreach_ret ptr_interp t
      -> foreach_ret word_interp t
      -> Semantics.mem -> Prop :=
*)
