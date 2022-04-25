Require Rupicola.Lib.Tactics.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. (* after strings *)
Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.Bedrock.Field.Common.Names.MakeNames.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Func.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Language.API.
Require Import Crypto.Spec.ModularArithmetic.
Import Language.API.Compilers.
Import ListNotations.
Import Types.Notations.
Import Syntax.Coercions.
Local Open Scope Z_scope.

Section Generic.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Definition make_bedrock_func {t} (name : string)
             insizes outsizes inlengths (res : API.Expr t)
  : func :=
    let innames := make_innames (inname_gen:=default_inname_gen) _ in
    let outnames := make_outnames (outname_gen:=default_outname_gen) _ in
    let body := fst (translate_func
                       res innames inlengths insizes outnames outsizes) in
    (name, body).
End Generic.

Local Hint Unfold fst snd : pairs.
Local Hint Unfold type.final_codomain : types.
Local Hint Unfold Equivalence.equivalent_args
      Equivalence.equivalent_base rep.equiv
      rep.listZ_mem rep.Z type.map_for_each_lhs_of_arrow
      rtype_of_ltype base_rtype_of_ltype rep.rtype_of_ltype
      WeakestPrecondition.dexpr WeakestPrecondition.expr
      WeakestPrecondition.expr_body
  : equivalence.
Local Hint Unfold LoadStoreList.list_lengths_from_args
      LoadStoreList.list_lengths_from_value
  : list_lengths.
Local Hint Unfold LoadStoreList.access_sizes_good_args
      LoadStoreList.access_sizes_good
      LoadStoreList.base_access_sizes_good
      LoadStoreList.within_access_sizes_args
      LoadStoreList.within_base_access_sizes
  : access_sizes.
Local Hint Unfold LoadStoreList.lists_reserved_with_initial_context
      LoadStoreList.lists_reserved
      LoadStoreList.extract_listnames
      Flatten.flatten_listonly_base_ltype
      Flatten.flatten_argnames
      Flatten.flatten_base_ltype
      List.app map.of_list_zip
      map.putmany_of_list_zip
  : lists_reserved.

Local Hint Resolve MakeAccessSizes.bits_per_word_le_width
      MakeAccessSizes.width_ge_8 width_0mod_8
      Util.Forall_map_byte_unsigned
  : translate_func_preconditions.

Section WithParameters.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : Types.ok}
          {prime_field_parameters : PrimeFieldParameters}.
  Context (n n_bytes : nat) (weight : nat -> Z)
          (bounds : Type)
          (loose_bounds tight_bounds byte_bounds : bounds)
          (list_in_bounds : bounds -> list Z -> Prop)
          (relax_bounds :
             forall X,
               list_in_bounds tight_bounds X ->
               list_in_bounds loose_bounds X)
          (eval_transformation : list Z -> list Z).
  Context (inname_gen_varname_gen_disjoint :
             disjoint default_inname_gen varname_gen)
          (outname_gen_varname_gen_disjoint :
             disjoint default_outname_gen varname_gen).

  Local Instance field_parameters : FieldParameters := PrimeField.prime_field_parameters.

  Local Instance field_representation : FieldRepresentation
    := @frep _ BW _ _ prime_field_parameters n n_bytes weight bounds list_in_bounds loose_bounds tight_bounds
             byte_bounds eval_transformation.
  Local Instance field_representation_ok : FieldRepresentation_ok
    := frep_ok n n_bytes weight bounds list_in_bounds loose_bounds tight_bounds byte_bounds
               relax_bounds _.

  Lemma FElem_array_truncated_scalar_iff1 px x :
    Lift1Prop.iff1
      (FElem px x)
      (sep (map:=mem)
           (emp (map:=mem) (length x = n))
           (Array.array
              (Scalars.truncated_scalar access_size.word)
              (word.of_Z
                 (Z.of_nat (BinIntDef.Z.to_nat (bytes_per_word width))))
              px (map word.unsigned x))).
  Proof using ok.
    cbv [FElem Bignum.Bignum field_representation frep].
    rewrite Util.array_truncated_scalar_scalar_iff1.
    Morphisms.f_equiv. Morphisms.f_equiv. Morphisms.f_equiv.
    destruct Bitwidth.width_cases as [W|W]; rewrite W; trivial.
  Qed.

  Lemma FElemBytes_array_truncated_scalar_iff1 pbs bs :
    Lift1Prop.iff1
      (FElemBytes pbs bs)
      (sep (map:=mem)
           (emp (map:=mem)
                (length bs = encoded_felem_size_in_bytes
                 /\ bytes_in_bounds bs))
           (Array.array
              (Scalars.truncated_scalar access_size.one)
              (word.of_Z 1) pbs (map byte.unsigned bs))).
  Proof using ok.
    cbv [FElemBytes].
    rewrite Util.array_truncated_scalar_ptsto_iff1.
    rewrite ByteBounds.byte_map_of_Z_unsigned.
    reflexivity.
  Qed.

  Ltac felem_to_array :=
    repeat
      lazymatch goal with
      | H:context[sep (FElem _ _) _]
        |- _ => seprewrite_in FElem_array_truncated_scalar_iff1 H
      | H : context [sep (FElemBytes _ _) _] |- _ =>
        seprewrite_in FElemBytes_array_truncated_scalar_iff1 H
      end.

  Ltac equivalence_side_conditions_hook := fail.
  Ltac solve_equivalence_side_conditions :=
    lazymatch goal with
    | |- map word.unsigned _ = map word.unsigned _ => reflexivity
    | |- word.unsigned _ = word.unsigned _ => reflexivity
    | |- WeakestPrecondition.get _ _ _ =>
      repeat (apply Util.get_put_diff; [ congruence | ]);
      apply Util.get_put_same; reflexivity
    | |- Forall (fun z => 0 <= z < 2 ^ (?e * 8))
                (map word.unsigned _) =>
          unshelve eapply Util.Forall_word_unsigned_within_access_size;
          destruct Bitwidth.width_cases as [W|W]; rewrite W; trivial
    | |- Forall (fun z => 0 <= z < ?e)
                (map byte.unsigned _) =>
      change e with 256;
      apply Util.Forall_map_byte_unsigned
    | |- sep _ _ _ =>
      change (Z.of_nat (bytes_per access_size.one)) with 1;
      try erewrite Util.map_unsigned_of_Z,MaxBounds.map_word_wrap_bounded
        by eauto using byte_unsigned_within_max_bounds;
      felem_to_array; sepsimpl; (assumption || ecancel_assumption)
    | |- map word.unsigned ?x = map byte.unsigned _ =>
      is_evar x;
      erewrite Util.map_unsigned_of_Z,MaxBounds.map_word_wrap_bounded
        by eauto using byte_unsigned_within_max_bounds;
      reflexivity
    | _ => equivalence_side_conditions_hook
    end.

  Ltac crush_sep :=
    repeat lazymatch goal with
           | |- exists _, _ => eexists
           | |- Lift1Prop.ex1 _ _ => Tactics.lift_eexists
           | |- True => tauto
           | _ => progress sepsimpl; cleanup
           end.

  Ltac compute_names :=
    repeat lazymatch goal with
           | |- context [@make_innames ?w ?B ?W ?M ?L ?E ?X ?G ?R ?p ?gen ?t] =>
             let x := constr:(@make_innames w B W M L E X G R p gen t) in
             let y := (eval compute in x) in
             change x with y
           | |- context [@make_outnames  ?w ?B ?W ?M ?L ?E ?X ?G ?R ?p ?gen ?t] =>
             let x := constr:(@make_outnames w B W M L E X G R p gen t) in
             let y := (eval compute in x) in
             change x with y
           end.

  Ltac use_translate_func_correct b2_args R_ :=
    let arg_ptrs :=
        lazymatch goal with
          |- WeakestPrecondition.call _ _ _ _ ?args _ =>
          args end in
    let out_ptr := (eval compute in (hd (word.of_Z 0) arg_ptrs)) in
    let in_ptrs := (eval compute in (tl arg_ptrs)) in
    eapply (translate_func_correct (parameters_sentinel:=parameters_sentinel))
    with (out_ptrs:=[out_ptr]) (flat_args:=in_ptrs)
         (args:=b2_args) (R:=R_).

  Ltac types_autounfold :=
    repeat first [ progress autounfold with types pairs
                 | progress autounfold with equivalence ].
  Ltac lists_autounfold :=
    repeat first [ progress types_autounfold
                 | progress autounfold with list_lengths
                 | progress autounfold with lists_reserved ].

  Ltac translate_func_precondition_hammer :=
    lazymatch goal with
    | |- valid_func _ => assumption
    | |- API.Wf _ => assumption
    | |- @eq (list word.rep) _ _ => reflexivity
    | |- length [?p] = _ => reflexivity
    | |- forall _, ~ VarnameSet.varname_set_args _ _ =>
      solve [auto using make_innames_varname_gen_disjoint]
    | |- forall _, ~ VarnameSet.varname_set_base (make_outnames _)
                     (varname_gen _) =>
      apply make_outnames_varname_gen_disjoint;
      solve [apply outname_gen_varname_gen_disjoint]
    | |- NoDup (Flatten.flatten_argnames (make_innames _)) =>
      apply flatten_make_innames_NoDup;
      solve [eapply prefix_name_gen_unique]
    | |- NoDup (Flatten.flatten_base_ltype (make_outnames _)) =>
      apply flatten_make_outnames_NoDup;
      solve [eapply prefix_name_gen_unique]
    | |- LoadStoreList.base_access_sizes_good _ =>
       autounfold with types access_sizes; cbn;
       destruct Bitwidth.width_cases as [W|W]; rewrite ?W;
           clear; cbn; intuition Lia.lia
    | |- PropSet.disjoint
           (VarnameSet.varname_set_args (make_innames _))
           (VarnameSet.varname_set_base (make_outnames _)) =>
      apply make_innames_make_outnames_disjoint;
      eauto using outname_gen_inname_gen_disjoint;
      solve [apply prefix_name_gen_unique]
    | |- Equivalence.equivalent_flat_args _ _ _ _ =>
      eapply (equivalent_flat_args_iff1
                (make_innames (inname_gen:=default_inname_gen) _)
                _ _ _
                map.empty);
      [ apply flatten_make_innames_NoDup;
        solve [eapply prefix_name_gen_unique]
      | reflexivity | ];
      compute_names; autounfold with equivalence pairs;
      cbv [Equivalence.equivalent_base];
      autounfold with equivalence pairs;
      rewrite <-?MakeAccessSizes.bytes_per_word_eq;
      sepsimpl; crush_sep; solve [solve_equivalence_side_conditions]
    | |- LoadStoreList.within_access_sizes_args _ _ =>
      autounfold with types access_sizes; cbn; ssplit; trivial;
      solve_equivalence_side_conditions 
    | |- LoadStoreList.within_base_access_sizes _ _ =>
      autounfold with types access_sizes;
      first [ eapply MaxBounds.max_bounds_range_iff
            | eapply ByteBounds.byte_bounds_range_iff ];
      cbn [type.app_curried fst snd];
      solve [eauto using relax_list_Z_bounded_by]
    | |- LoadStoreList.access_sizes_good_args _ =>
      autounfold with access_sizes pairs access_sizes; cbn;
       destruct Bitwidth.width_cases as [W|W]; rewrite ?W;
           clear; cbn; intuition Lia.lia
    | |- _ = LoadStoreList.list_lengths_from_args _ =>
      autounfold with list_lengths pairs list_lengths;
      felem_to_array; sepsimpl; rewrite !map_length;
      repeat match goal with
             | H : length _ = _ |- _ => rewrite H end;
      reflexivity
    | _ => idtac
    end.

  Ltac lists_reserved_simplify pout :=
    compute_names; cbn [type.app_curried fst snd];
    autounfold with types list_lengths pairs;
    lists_autounfold; sepsimpl;
    match goal with
    | H : context [FElem pout ?old_out]
      |- @Lift1Prop.ex1 (list Z) _ _ _ =>
      exists (map word.unsigned old_out)
    | H : context [FElemBytes pout ?old_out]
      |- @Lift1Prop.ex1 (list Z) _ _ _ =>
      exists (map byte.unsigned old_out)
    end;
    crush_sep.

  Ltac postcondition_simplify :=
    lists_autounfold;
    cbn [type.app_curried fst snd];
    cbv [Equivalence.equivalent_listexcl_flat_base
           Equivalence.equivalent_listonly_flat_base
           Equivalence.equivalent_flat_base
        ]; lists_autounfold; cbn [hd];
    repeat intro;
    cbv [Core.postcondition_func_norets
           Core.postcondition_func];
    sepsimpl; [ assumption .. | ];
    repeat match goal with
           | _ => progress subst
           | H : WeakestPrecondition.literal (word.unsigned _) _ |- _ =>
             cbv [WeakestPrecondition.literal dlet.dlet] in H;
             rewrite word.of_Z_unsigned in H
           | H : word.unsigned _ = word.unsigned _ |- _ =>
             apply Properties.word.unsigned_inj in H
           | |- exists _, _ => eexists
           | |- _ /\ _ => eexists
           end.

    Ltac solve_length x Hlength := rewrite map_length;
    match goal with
        | H : (FElem _ x * _)%sep _ |- _ => cbv [FElem Bignum.Bignum] in H; sepsimpl_hyps
        | _ => idtac
    end;
    match goal with
        | H : Datatypes.length x = _ |- _ => rewrite H
        | _ => idtac
    end; rewrite Hlength; auto.

  Section ListBinop.
    Context {res : API.Expr (type_listZ -> type_listZ -> type_listZ)}
            (res_valid :
               valid_func (res (fun _ : API.type => unit)))
            (res_Wf : API.Wf res).
    Context name (bop : BinOp name)
            (res_eq : forall x y : list word,
                bounded_by bin_xbounds x ->
                bounded_by bin_ybounds y ->
                feval (map word.of_Z
                           (API.interp (res _)
                                       (map word.unsigned x)
                                       (map word.unsigned y)))
                = bin_model (feval x) (feval y))
            (res_bounds : forall x y,
                list_in_bounds bin_xbounds x ->
                list_in_bounds bin_ybounds y ->
                list_in_bounds bin_outbounds (API.interp (res _) x y))

            (outbounds_tighter_than_max : forall x, list_in_bounds bin_outbounds x -> list_Z_bounded_by ((@max_bounds width) n) x)
            (xbounds_length : forall x, list_in_bounds bin_xbounds x -> length x = n)
            (ybounds_length : forall x, list_in_bounds bin_ybounds x -> length x = n)
            (outbounds_length : forall x, list_in_bounds bin_outbounds x -> length x = n).

    Local Ltac equivalence_side_conditions_hook ::=
      lazymatch goal with
      | |- context [length (API.interp (res _) ?x ?y)] =>
        specialize (res_bounds x y ltac:(auto) ltac:(auto));
        rewrite (length_list_Z_bounded_by _ _ res_bounds);
        try congruence;
        rewrite !map_length, outbounds_length;
        felem_to_array; sepsimpl; congruence
      | _ => idtac
      end.

    Local Notation t :=
      (type.arrow type_listZ (type.arrow type_listZ type_listZ))
        (only parsing).

    Definition list_binop_insizes
      : type.for_each_lhs_of_arrow access_sizes t :=
      (access_size.word, (access_size.word, tt)).
    Definition list_binop_outsizes
      : base_access_sizes (type.final_codomain t) :=
      access_size.word.
    Definition list_binop_inlengths
      : type.for_each_lhs_of_arrow list_lengths t :=
      (n, (n, tt)).
    Let insizes := list_binop_insizes.
    Let outsizes := list_binop_outsizes.
    Let inlengths := list_binop_inlengths.

    Lemma list_binop_correct f :
      f = make_bedrock_func name insizes outsizes inlengths res ->
      forall functions, (binop_spec _ (f :: functions)).
    Proof.
      subst inlengths insizes outsizes.
      cbv [binop_spec list_binop_insizes list_binop_outsizes list_binop_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup. eapply Proper_call.
      2: {
        use_translate_func_correct
          constr:((map word.unsigned x, (map word.unsigned y, tt))) Rr;
        translate_func_precondition_hammer.
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout; try solve_equivalence_side_conditions; solve_length out outbounds_length.
          } }
      { postcondition_simplify; [ | | ]; cycle -1.
        { refine (proj1 (Proper_sep_iff1 _ _ _ _ _ _ _) _);
            [symmetry; eapply FElem_array_truncated_scalar_iff1 | reflexivity | sepsimpl ].
          2:eassumption.
          erewrite <-map_length.
          match goal with H : map word.unsigned _ = API.interp (res _) _ _ |- _ =>
            rewrite H end.
          erewrite length_list_Z_bounded_by; eauto using res_bounds; apply repeat_length. }
        { (* output correctness *)
          erewrite <-res_eq; auto.
          match goal with H : map word.unsigned _ = API.interp (res _) _ _ |- _ =>
            rewrite <-H end.
          rewrite map_map.
          f_equal; eapply List.nth_error_ext; intros i; rewrite ListUtil.nth_error_map.
          case (nth_error _ i); cbn; trivial; []; intros; eapply f_equal.
          symmetry; eapply word.of_Z_unsigned. }
        { (* output bounds *)
          cbn [bounded_by field_representation frep] in *.
          match goal with H : map word.unsigned _ = API.interp (res _) _ _ |- _ =>
            rewrite H end.
          eauto using res_bounds. } }
    Qed.
  End ListBinop.

  Section ListUnop.
    Context {res : API.Expr (type_listZ -> type_listZ)}
            (res_valid :
               valid_func (res (fun _ : API.type => unit)))
            (res_Wf : API.Wf res).
    Context name (uop : UnOp name)
            (res_eq : forall x : list word,
                bounded_by un_xbounds x ->
                feval (map word.of_Z
                           (API.interp (res _) (map word.unsigned x)))
                = un_model (feval x))
            (res_bounds : forall x,
                list_in_bounds un_xbounds x ->
                list_in_bounds un_outbounds (API.interp (res _) x))
            (outbounds_tighter_than_max : forall x, list_in_bounds un_outbounds x -> list_Z_bounded_by (@max_bounds width n) x)
            (xbounds_length : forall x, list_in_bounds un_xbounds x -> length x = n)
            (outbounds_length : forall x, list_in_bounds un_outbounds x -> length x = n).

    Local Ltac equivalence_side_conditions_hook ::=
      lazymatch goal with
      | |- context [length (API.interp (res _) ?x)] =>
        specialize (res_bounds x ltac:(auto));
        rewrite (length_list_Z_bounded_by _ _ res_bounds);
        try congruence;
        rewrite !map_length, outbounds_length;
        felem_to_array; sepsimpl; congruence
      | _ => idtac
      end.

    Local Notation t :=
      (type.arrow type_listZ type_listZ) (only parsing).

    Definition list_unop_insizes
      : type.for_each_lhs_of_arrow access_sizes t :=
      (access_size.word, tt).
    Definition list_unop_outsizes
      : base_access_sizes (type.final_codomain t) :=
      access_size.word.
    Definition list_unop_inlengths
      : type.for_each_lhs_of_arrow list_lengths t :=
      (n, tt).
    Let insizes := list_unop_insizes.
    Let outsizes := list_unop_outsizes.
    Let inlengths := list_unop_inlengths.

    Lemma list_unop_correct f :
      f = make_bedrock_func name insizes outsizes inlengths res ->
      forall functions, unop_spec _ (f :: functions).
    Proof using inname_gen_varname_gen_disjoint outbounds_length
          outbounds_tighter_than_max outname_gen_varname_gen_disjoint
          ok relax_bounds res_Wf res_bounds res_eq res_valid.
      subst inlengths insizes outsizes.
      cbv [unop_spec list_unop_insizes list_unop_outsizes list_unop_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup. eapply Proper_call.
      2: {
        use_translate_func_correct constr:((map word.unsigned x, tt)) Rr.
        all:translate_func_precondition_hammer.
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout.
          all: try solve_equivalence_side_conditions.
          solve_length out outbounds_length. } }
      { postcondition_simplify; [ | | ].
        { (* output correctness *)
          eapply res_eq; auto. }
        { (* output bounds *)
          cbn [bounded_by field_representation frep] in *.
          erewrite Util.map_unsigned_of_Z, MaxBounds.map_word_wrap_bounded
            by eauto using relax_list_Z_bounded_by.
          eauto. }
        { (* separation-logic postcondition *)
          eapply Proper_sep_iff1;
            [ solve [apply FElem_array_truncated_scalar_iff1]
            | reflexivity | ].
          sepsimpl; [ | ].
          { rewrite !map_length. apply outbounds_length; auto. }
          { erewrite Util.map_unsigned_of_Z, MaxBounds.map_word_wrap_bounded
              by eauto using relax_list_Z_bounded_by.
            rewrite MakeAccessSizes.bytes_per_word_eq.
            clear outbounds_length; subst.
            match goal with
              H : map word.unsigned _ = API.interp (res _) _ |- _ =>
              rewrite <-H end.
            auto. } } }
    Qed.
  End ListUnop.

  Section FromWord.
    Context {res : API.Expr (type_Z -> type_listZ)}
            (res_valid :
               valid_func (res (fun _ : API.type => unit)))
            (res_Wf : API.Wf res).
    Context (res_eq : forall w,
                feval (map word.of_Z
                           (API.interp (res _) w))
                = F.of_Z _ w)
            (res_bounds : forall w,
                list_in_bounds
                  tight_bounds
                  (API.interp (res _) w)).
    Context (tight_bounds_tighter_than_max : forall x,
                list_in_bounds tight_bounds x -> list_Z_bounded_by (@MaxBounds.max_bounds width n) x).

    Local Notation t :=
      (type.arrow type_Z type_listZ) (only parsing).

    Definition from_word_insizes
      : type.for_each_lhs_of_arrow access_sizes t :=
      (tt, tt).
    Definition from_word_outsizes
      : base_access_sizes (type.final_codomain t) :=
      access_size.word.
    Definition from_word_inlengths
      : type.for_each_lhs_of_arrow list_lengths t :=
      (tt, tt).
    Let insizes := from_word_insizes.
    Let outsizes := from_word_outsizes.
    Let inlengths := from_word_inlengths.

    Lemma from_word_correct f :
      f = make_bedrock_func from_word insizes outsizes inlengths res ->
      forall functions,
        spec_of_from_word (f :: functions).
    Proof using inname_gen_varname_gen_disjoint
          outname_gen_varname_gen_disjoint ok relax_bounds res_Wf
          res_bounds res_eq res_valid tight_bounds_tighter_than_max.
      subst inlengths insizes outsizes. cbv [spec_of_from_word].
      cbv [from_word_insizes from_word_outsizes from_word_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup.
      eapply Proper_call.
      2:{
        (* inlined [use_translate_func_correct constr:((word.unsigned x, tt)) R] and edited R0 *)
        let b2_args := constr:((word.unsigned x, tt)) in
        let R_ := R in
        let arg_ptrs :=
          lazymatch goal with
          |- WeakestPrecondition.call _ _ _ _ ?args _ =>
          args end in
          let out_ptr := (eval compute in (hd (word.of_Z 0) arg_ptrs)) in
          let in_ptrs := (eval compute in (tl arg_ptrs)) in
          eapply (translate_func_correct (parameters_sentinel:=parameters_sentinel))
          with (out_ptrs:=[out_ptr]) (flat_args:=in_ptrs)
          (args:=b2_args).
        16:instantiate (1:=R).
        all:try translate_func_precondition_hammer.
        1:reflexivity.
        { cbv [Equivalence.equivalent_flat_args]; eexists 1%nat; split; [eexists|reflexivity].
          cbv [Equivalence.equivalent_flat_base rep.equiv rep.Z]; sepsimpl; [reflexivity|eexists].
          sepsimpl; trivial.
          { cbn. cbv [WeakestPrecondition.literal dlet.dlet]. rewrite word.of_Z_unsigned; trivial. }
          { eassumption. } }
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout.
          all:try solve_equivalence_side_conditions.
          symmetry.
          erewrite length_list_Z_bounded_by; [| eapply tight_bounds_tighter_than_max, res_bounds].
          cbv [max_bounds]. rewrite repeat_length. rewrite map_length.
          cbv [FElem Bignum.Bignum] in *. sepsimpl. auto.
          lazymatch goal with
          | H : _ ?m |- _ ?m => destruct H as [m1 [m2 [Hsplit [ Hmem Hmem2] ] ] ]
          | _ => idtac
          end.
          do 2 eexists; split; [| split]; eauto.
          eapply FElem_array_truncated_scalar_iff1 in Hmem. sepsimpl.
          auto.
        } }
      { postcondition_simplify; [ | | ].
        { (* output correctness *)
          eapply res_eq; auto. }
        { (* output bounds *)
          cbn [bounded_by field_representation frep] in *.
          erewrite Util.map_unsigned_of_Z, MaxBounds.map_word_wrap_bounded
            by eauto using relax_list_Z_bounded_by. cbv [AbstractField.tight_bounds]. simpl.
          eauto. }
        { (* separation-logic postcondition *)
          eapply Proper_sep_iff1;
            [ solve [apply FElem_array_truncated_scalar_iff1]
            | reflexivity | ].
          sepsimpl; [ | ].
          { rewrite !map_length.
            erewrite length_list_Z_bounded_by; [| eapply tight_bounds_tighter_than_max, res_bounds].
            cbv [max_bounds]; rewrite repeat_length; trivial. }
          { erewrite Util.map_unsigned_of_Z, MaxBounds.map_word_wrap_bounded
              by eauto using relax_list_Z_bounded_by.
            rewrite MakeAccessSizes.bytes_per_word_eq.
            (* clear tight_bounds_length; subst. *)
            match goal with
              H : map word.unsigned _ = API.interp (res _) _ |- _ =>
              rewrite <-H end.
            auto. } } }
    Qed.
  End FromWord.

  Section FelemCopy.
    Context {res : API.Expr (type_listZ -> type_listZ)}
            (res_valid :
               valid_func (res (fun _ : API.type => unit)))
            (res_Wf : API.Wf res).
    Context (res_eq : forall x : list word,
                length x = n ->
                (map word.of_Z (API.interp (res _) (map word.unsigned x)))
                = x)
            (res_bounds : forall x,
                list_Z_bounded_by (max_bounds (width:=width) n) x ->
                list_Z_bounded_by (max_bounds (width:=width) n) (API.interp (res _) x)).

    Local Ltac equivalence_side_conditions_hook ::=
      lazymatch goal with
      | |- context [length (API.interp (res _) ?x)] =>
      idtac (*; specialize (res_bounds x ltac:(auto));
        rewrite (length_list_Z_bounded_by _ _ res_bounds);
        try congruence;
        rewrite !map_length, outbounds_length;
                felem_to_array; sepsimpl; congruence*)
      | _ => idtac
      end.

    Local Notation t :=
      (type.arrow type_listZ type_listZ) (only parsing).

    Definition felem_copy_insizes
      : type.for_each_lhs_of_arrow access_sizes t :=
      (access_size.word, tt).
    Definition felem_copy_outsizes
      : base_access_sizes (type.final_codomain t) :=
      access_size.word.
    Definition felem_copy_inlengths
      : type.for_each_lhs_of_arrow list_lengths t :=
      (n, tt).
    Let insizes := felem_copy_insizes.
    Let outsizes := felem_copy_outsizes.
    Let inlengths := felem_copy_inlengths.

    Lemma felem_copy_correct f :
      f = make_bedrock_func felem_copy insizes outsizes inlengths res ->
      forall functions, spec_of_felem_copy (f :: functions).
    Proof.
      subst inlengths insizes outsizes.
      cbv [spec_of_felem_copy felem_copy_insizes felem_copy_outsizes felem_copy_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup. eapply Proper_call.
      2: {
        Set Ltac Backtrace.
        rename R into Rr.
        use_translate_func_correct constr:((map word.unsigned x, tt)) (FElem px x * Rr)%sep.
        all:try translate_func_precondition_hammer.


      autounfold with types access_sizes;
      first [ eapply MaxBounds.max_bounds_range_iff
            | eapply ByteBounds.byte_bounds_range_iff ];
      cbn [type.app_curried fst snd].
apply res_bounds.
rewrite max_bounds_range_iff.
(* note: need to constrain length of x, extract that from H0 *)
admit.
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout.
          all:try solve_equivalence_side_conditions.
          setoid_rewrite max_bounds_range_iff in res_bounds.
          rewrite (fun x pf => proj1 (res_bounds x pf)).
          admit. admit.
      use_sep_assumption.
      cancel; unfold seps.
      admit.
        Admitted.
  End FelemCopy.

  Section FromBytes.
    Context {res : API.Expr (type_listZ -> type_listZ)}
            (res_valid :
               valid_func (res (fun _ : API.type => unit)))
            (res_Wf : API.Wf res).
    Context (tight_bounds_tighter_than_max :
              forall x,
                list_in_bounds tight_bounds x ->
                list_Z_bounded_by (@max_bounds width n) x)
            (tight_bounds_length : forall x, list_in_bounds tight_bounds x -> length x = n)
            (res_eq : forall bs,
                bytes_in_bounds bs ->
                feval (map word.of_Z
                           (API.interp (res _) (map byte.unsigned bs)))
                = feval_bytes bs)
            (res_bounds : forall bs,
                bytes_in_bounds bs ->
                list_in_bounds
                  tight_bounds
                  (API.interp (res _) (map byte.unsigned bs))).

    Lemma FElemBytes_in_bounds p bs R m :
      (FElemBytes p bs ⋆ R)%sep m ->
      bytes_in_bounds bs.
    Proof. cbv [FElemBytes]. intros; sepsimpl. assumption. Qed.

    Local Ltac equivalence_side_conditions_hook ::=
      lazymatch goal with
      | |- context [length (API.interp (res _)
                                       (map byte.unsigned ?x))] =>
        specialize (res_bounds x ltac:(auto));
        rewrite (length_list_Z_bounded_by _ _ res_bounds);
        try congruence;
        rewrite !map_length, tight_bounds_length;
        felem_to_array; sepsimpl; congruence
      | _ => idtac
      end.

    Local Notation t :=
      (type.arrow type_listZ type_listZ) (only parsing).

    Definition from_bytes_insizes
      : type.for_each_lhs_of_arrow access_sizes t :=
      (access_size.one, tt).
    Definition from_bytes_outsizes
      : base_access_sizes (type.final_codomain t) :=
      access_size.word.
    Definition from_bytes_inlengths
      : type.for_each_lhs_of_arrow list_lengths t :=
      (n_bytes, tt).
    Let insizes := from_bytes_insizes.
    Let outsizes := from_bytes_outsizes.
    Let inlengths := from_bytes_inlengths.

    Lemma from_bytes_correct f :
      f = make_bedrock_func from_bytes insizes outsizes inlengths res ->
      forall functions,
        spec_of_from_bytes (f :: functions).
    Proof using inname_gen_varname_gen_disjoint
          outname_gen_varname_gen_disjoint ok relax_bounds res_Wf
          res_bounds res_eq res_valid tight_bounds_length
          tight_bounds_tighter_than_max.
      subst inlengths insizes outsizes. cbv [spec_of_from_bytes].
      cbv [from_bytes_insizes from_bytes_outsizes from_bytes_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup.
      pose proof FElemBytes_in_bounds _ _ _ _ H.
      eapply Proper_call.
      2:{
        use_translate_func_correct constr:((map Byte.byte.unsigned bs, tt)) Rr.
        all: try translate_func_precondition_hammer.
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout.
          all: try solve_equivalence_side_conditions.
          solve_length out tight_bounds_length.
        } }
      { postcondition_simplify; [ | | ].
        { (* output correctness *)
          eapply res_eq; auto. }
        { (* output bounds *)
          cbn [bounded_by field_representation frep] in *.
          erewrite Util.map_unsigned_of_Z, MaxBounds.map_word_wrap_bounded
            by eauto using relax_list_Z_bounded_by.
          eauto. }
        { (* separation-logic postcondition *)
          eapply Proper_sep_iff1;
            [ solve [apply FElem_array_truncated_scalar_iff1]
            | reflexivity | ].
          sepsimpl; [ | ].
          { rewrite !map_length; apply tight_bounds_length; auto. }
          { erewrite Util.map_unsigned_of_Z, MaxBounds.map_word_wrap_bounded
              by eauto using relax_list_Z_bounded_by.
            rewrite MakeAccessSizes.bytes_per_word_eq.
            clear tight_bounds_length; subst.
            match goal with
              H : map word.unsigned _ = API.interp (res _) _ |- _ =>
              rewrite <-H end.
            auto. } } }
    Qed.
  End FromBytes.

  Section ToBytes.
    Context {res : API.Expr (type_listZ -> type_listZ)}
            (res_valid :
               valid_func (res (fun _ : API.type => unit)))
            (res_Wf : API.Wf res).
    Context (byte_bounds_tighter_than_max :
              forall x,
                list_in_bounds byte_bounds x ->
                list_Z_bounded_by (ByteBounds.byte_bounds n_bytes) x)
            (byte_bounds_length :
              forall x,
                list_in_bounds byte_bounds x ->
                length x = encoded_felem_size_in_bytes)
            (res_eq : forall x,
                bounded_by tight_bounds x ->
                feval x
                = feval_bytes (map byte.of_Z (API.interp (res _) (map word.unsigned x))))
            (res_bounds : forall x,
                bounded_by tight_bounds x ->
                list_Z_bounded_by (ByteBounds.byte_bounds n_bytes)
                       (API.interp (res _)
                                   (map word.unsigned x)))
            (res_bounds' : forall x,
              bounded_by tight_bounds x ->
              list_in_bounds byte_bounds (API.interp (res _)
                                (map word.unsigned x))).

    Local Ltac equivalence_side_conditions_hook ::=
      lazymatch goal with
      | |- context [length (Partition.partition _ _ _)] =>
          autorewrite with distr_length;
          cbv [FElemBytes] in *; sepsimpl; solve [auto]
      end.

    Local Notation t :=
      (type.arrow type_listZ type_listZ) (only parsing).

    Definition to_bytes_insizes
      : type.for_each_lhs_of_arrow access_sizes t :=
      (access_size.word, tt).
    Definition to_bytes_outsizes
      : base_access_sizes (type.final_codomain t) :=
      access_size.one.
    Definition to_bytes_inlengths
      : type.for_each_lhs_of_arrow list_lengths t :=
      (n, tt).
    Let insizes := to_bytes_insizes.
    Let outsizes := to_bytes_outsizes.
    Let inlengths := to_bytes_inlengths.

    (* helper lemma about partition and nth_byte *)
    Lemma nth_byte_partition x nbytes :
      map (nth_byte x) (seq 0 nbytes) =
      map byte.of_Z
          (Partition.partition (ModOps.weight 8 1) nbytes x).
    Proof.
      cbv [Partition.partition nth_byte]. rewrite map_map.
      apply map_ext; intros. rewrite Z.shiftr_div_pow2 by Lia.lia.
      apply byte.unsigned_inj. rewrite !byte.unsigned_of_Z.
      cbv [byte.wrap ModOps.weight].
      autorewrite with zsimplify.
      rewrite Nat2Z.inj_succ.
      autorewrite with zsimplify.
      rewrite Z.add_comm, Z.pow_add_r by Lia.lia.
      rewrite !Modulo.Z.mod_pull_div by Lia.lia.
      rewrite Z.mod_mod by auto with zarith.
      reflexivity.
    Qed.

    Lemma FElem_bytes_length p x R m : (AbstractField.FElemBytes p x * R)%sep m -> Datatypes.length x = encoded_felem_size_in_bytes.
    Proof.
        intros; cbv [AbstractField.FElemBytes] in *; sepsimpl; auto.
    Qed.

    Lemma to_bytes_correct f :
      f = make_bedrock_func to_bytes insizes outsizes inlengths res ->
      forall functions,
        spec_of_to_bytes (f :: functions).
    Proof using byte_bounds_length byte_bounds_tighter_than_max
          inname_gen_varname_gen_disjoint
          outname_gen_varname_gen_disjoint ok res_Wf
          res_eq res_valid res_bounds res_bounds'.
      subst inlengths insizes outsizes. cbv [spec_of_to_bytes].
      cbv [to_bytes_insizes to_bytes_outsizes to_bytes_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup. eapply Proper_call.
      2:{
        use_translate_func_correct
          constr:((map word.unsigned x, tt)) Rr.
        all:try translate_func_precondition_hammer.
        all:cbn [type.app_curried fst snd].
        all:try rewrite res_eq by auto.
        (* { eapply ByteBounds.byte_bounds_range_iff.
          auto using ByteBounds.partition_bounded_by. } *)
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout.
          all: try solve_equivalence_side_conditions.
          (*output length*)
          rewrite map_length; erewrite FElem_bytes_length; eauto.
          erewrite length_list_Z_bounded_by; [| eapply res_bounds; auto].
          simpl; cbv [ByteBounds.byte_bounds]; rewrite repeat_length; auto.
          } }
      { postcondition_simplify; [ eapply res_eq; eauto| ].
        (* separation-logic postcondition *)
      {  eapply Proper_sep_iff1;
      [ solve [apply FElemBytes_array_truncated_scalar_iff1]
      | reflexivity | ].
      cbv [Z_to_bytes]; sepsimpl.
      {
        autorewrite with distr_length. erewrite  length_list_Z_bounded_by; [|eapply res_bounds; eauto]. 
          cbv [ByteBounds.byte_bounds]; rewrite repeat_length; eauto.
      }
      {
        cbv [bytes_in_bounds]. simpl. rewrite ByteBounds.byte_map_unsigned_of_Z.
        erewrite ByteBounds.map_byte_wrap_bounded; [| eauto].
        eapply res_bounds'; auto.
      }
      {
        erewrite ByteBounds.byte_map_unsigned_of_Z, ByteBounds.map_byte_wrap_bounded; [ |
        eapply res_bounds; auto].
        match goal with
            H : map word.unsigned _ = API.interp (res _) _ |- _ =>
            rewrite <-H end. auto.
      }
    } }
    Qed.
  End ToBytes.


Section SelectZnZ.

  Local Notation bit_range := {|ZRange.lower := 0; ZRange.upper := 1|}.
  Context {res : API.Expr (type_Z -> type_listZ -> type_listZ -> type_listZ)}
  (res_valid :
     valid_func (res (fun _ : API.type => unit)))
  (res_Wf : API.Wf res).

Context
  (res_eq : forall (x y : list word) (c : word),
      list_Z_bounded_by (@max_bounds width n) (map word.unsigned x) ->
      list_Z_bounded_by (@max_bounds width n) (map word.unsigned y) ->
      ZRange.is_bounded_by_bool (word.unsigned c) bit_range = true ->
                 (API.interp (res _)    
                             (word.unsigned c)
                             (map word.unsigned x)
                             (map word.unsigned y))
      = map word.unsigned (if (word.unsigned c =? 0) then x else y)).

    Local Ltac equivalence_side_conditions_hook ::=
      lazymatch goal with
      | |- context [length (Partition.partition _ _ _)] =>
          autorewrite with distr_length;
          cbv [FElemBytes] in *; sepsimpl; solve [auto]
      end.

      Local Notation t :=
      (type.arrow type_Z (type.arrow type_listZ (type.arrow type_listZ type_listZ)))
        (only parsing).

    Definition list_selectznz_insizes
      : type.for_each_lhs_of_arrow access_sizes t :=
      (tt, (access_size.word, (access_size.word, tt))).
    Definition list_selectznz_outsizes
      : base_access_sizes (type.final_codomain t) :=
      access_size.word.
    Definition list_selectznz_inlengths
      : type.for_each_lhs_of_arrow list_lengths t :=
      (tt, (n, (n, tt))).

      Let insizes := list_selectznz_insizes.
      Let outsizes := list_selectznz_outsizes.
      Let inlengths := list_selectznz_inlengths.

    Lemma bit_range_eq : forall x, ZRange.is_bounded_by_bool x bit_range = true -> x = 0 \/ x = 1.
    Proof.
        intros. apply RulesProofs.unfold_is_bounded_by_bool in H.
        simpl in H. lia.
    Qed.

    Lemma max_bounds_words : forall (x : list word) n, length x = n -> list_Z_bounded_by (@max_bounds width n) (map word.unsigned x).
    Proof.
        intros. generalize dependent x.
        induction n0; intros.
            - destruct x; try discriminate. simpl. cbv. auto.
            - destruct x; try discriminate. simpl.
              eapply Util.list_Z_bounded_by_cons. split.
              2: {
                  simpl in IHn0. eapply IHn0. auto.
              }
              apply Expr.is_bounded_by_bool_width_range.
              eauto.
              pose proof Properties.word.unsigned_range. auto.
    Qed. 

    Lemma FElem_max_bounds : forall px x m R, (FElem px x * R)%sep m -> list_Z_bounded_by (@max_bounds width n) (map word.unsigned x).
    Proof.
      intros. eapply max_bounds_words. cbv [FElem Bignum.Bignum] in H. sepsimpl. eauto.
    Qed. 

    Lemma select_znz_correct f :
      f = make_bedrock_func select_znz insizes outsizes inlengths res ->
      forall functions,
        spec_of_selectznz (f :: functions).
    Proof using inname_gen_varname_gen_disjoint
          outname_gen_varname_gen_disjoint ok res_Wf
          res_eq res_valid.
      subst inlengths insizes outsizes. cbv [spec_of_selectznz].
      cbv [list_selectznz_insizes list_selectznz_outsizes list_selectznz_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup.
      pose proof (FElem_max_bounds _ _ _ _ H0) as Hxbounds.
      pose proof (FElem_max_bounds _ _ _ _ H1) as Hybounds.
      match goal with
      | H : ZRange.is_bounded_by_bool _ _ = _ |- _ => rename H into Hbound
      | _ => idtac
      end.
      eapply Proper_call.
      2:{ use_translate_func_correct
          constr:((word.unsigned pc, (map word.unsigned x, (map word.unsigned y, tt)))) Rout.
        all:try translate_func_precondition_hammer.
        all:cbn [type.app_curried fst snd].
        all:try rewrite res_eq by auto.
        {
            eapply (equivalent_flat_args_iff1
            (make_innames (inname_gen:=default_inname_gen) _)
            _ _ _
            map.empty).
                - apply flatten_make_innames_NoDup; solve [eapply prefix_name_gen_unique].
                - reflexivity.
                - compute_names. autounfold with equivalence pairs.
                cbv [Equivalence.equivalent_base].
                autounfold with equivalence pairs.
                rewrite <- ?MakeAccessSizes.bytes_per_word_eq; sepsimpl.
                    + crush_sep; try solve_equivalence_side_conditions. eauto. (*Which one?*)
                    + crush_sep; try solve_equivalence_side_conditions.
                    + crush_sep; try solve_equivalence_side_conditions.
                    + auto.
        }
        1:  destruct (bit_range_eq _ Hbound) as [Hbit| Hbit]; rewrite Hbit; simpl;
            eapply MaxBounds.max_bounds_range_iff; eauto.
            lists_reserved_simplify pout.
            all: try solve_equivalence_side_conditions.
            destruct (bit_range_eq _ Hbound) as [Hbit| Hbit]; rewrite Hbit; simpl; auto; cbv [FElem Bignum.Bignum] in *; sepsimpl;
            repeat rewrite map_length;
            match goal with
              | H : ?n1 = _ |- ?n1 = _ => rewrite H
              | _ => idtac
            end; eauto.
      }
        postcondition_simplify.
        destruct (bit_range_eq _ Hbound) as [Hbit| Hbit].
            - rewrite Hbit. simpl. eapply Proper_sep_iff1.
                + apply FElem_array_truncated_scalar_iff1.
                + intros; split; intros; eauto.
                + sepsimpl; try ecancel_assumption.
                    * erewrite <- map_length. erewrite length_list_Z_bounded_by; eauto.
                      cbv [max_bounds]. rewrite repeat_length. eauto.
                    * specialize (res_eq x y pc); rewrite Hbit in res_eq; simpl in res_eq.
                      erewrite <- res_eq; eauto; rewrite <- Hbit; simpl in *; eauto.
                      match goal with
                      | H : map word.unsigned _ = _ |- _ => rewrite <- H
                      | _ => idtac
                      end; eauto.
            - rewrite Hbit; simpl; eapply Proper_sep_iff1.
                + apply FElem_array_truncated_scalar_iff1.
                + intros; split; intros; eauto.
                + sepsimpl; try ecancel_assumption.
                    * erewrite <- map_length; erewrite length_list_Z_bounded_by; eauto;
                      cbv [max_bounds]; rewrite repeat_length; eauto.
                    * specialize (res_eq x y pc); rewrite Hbit in res_eq; simpl in res_eq.
                      erewrite <- res_eq; eauto; rewrite <- Hbit; simpl in *; eauto.
                      match goal with
                      | H : map word.unsigned _ = _ |- _ => rewrite <- H
                      | _ => idtac
                      end; eauto.
    Qed.
  End SelectZnZ.
End WithParameters.