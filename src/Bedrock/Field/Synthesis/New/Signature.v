Require Rupicola.Lib.Tactics.
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
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.Bedrock.Field.Common.Names.MakeNames.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Func.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Specs.Field.
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
          {field_parameters : FieldParameters}.
  Context (n n_bytes : nat) (weight : nat -> Z)
          (loose_bounds tight_bounds byte_bounds
           : list (option ZRange.zrange))
          (relax_bounds :
             forall X,
               list_Z_bounded_by tight_bounds X ->
               list_Z_bounded_by loose_bounds X).
  Context (inname_gen_varname_gen_disjoint :
             disjoint default_inname_gen varname_gen)
          (outname_gen_varname_gen_disjoint :
             disjoint default_outname_gen varname_gen).
  Local Instance field_representation : FieldRepresentation
    := @frep _ BW _ _ field_parameters n n_bytes weight loose_bounds tight_bounds
             byte_bounds.
  Local Instance field_representation_ok : FieldRepresentation_ok
    := frep_ok n n_bytes weight loose_bounds tight_bounds byte_bounds
               relax_bounds.

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
                (length bs = encoded_felem_size_in_bytes))
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
      eapply equivalent_flat_args_iff1
        with (argnames:=make_innames (inname_gen:=default_inname_gen) _)
             (locals0:=map.empty);
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
                list_Z_bounded_by bin_xbounds x ->
                list_Z_bounded_by bin_ybounds y ->
                list_Z_bounded_by bin_outbounds (API.interp (res _) x y))

            (outbounds_tighter_than_max : list_Z_tighter_than bin_outbounds ((@max_bounds width) n))
            (xbounds_length : length bin_xbounds = n)
            (ybounds_length : length bin_ybounds = n)
            (outbounds_length : length bin_outbounds = n).

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
          lists_reserved_simplify pout; solve_equivalence_side_conditions. } }
      { postcondition_simplify; [ | | ]; cycle -1.
        { refine (proj1 (Proper_sep_iff1 _ _ _ _ _ _ _) _);
            [symmetry; eapply FElem_array_truncated_scalar_iff1 | reflexivity | sepsimpl ].
          2:eassumption.
          erewrite <-map_length.
          match goal with H : map word.unsigned _ = API.interp (res _) _ _ |- _ =>
            rewrite H end.
          erewrite length_list_Z_bounded_by; eauto using res_bounds. }
        { (* output correctness *)
          erewrite <-res_eq; auto.
          match goal with H : map word.unsigned _ = API.interp (res _) _ _ |- _ =>
            rewrite <-H end.
          rewrite map_map.
          f_equal; eapply List.nth_error_ext; intros i; rewrite ListUtil.nth_error_map.
          case (nth_error x2 i); cbn; trivial; []; intros; eapply f_equal.
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
                list_Z_bounded_by un_xbounds x ->
                list_Z_bounded_by un_outbounds (API.interp (res _) x))
            (outbounds_tighter_than_max : list_Z_tighter_than un_outbounds (@max_bounds width n))
            (xbounds_length : length un_xbounds = n)
            (outbounds_length : length un_outbounds = n).

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
          all:solve_equivalence_side_conditions. } }
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
          { rewrite !map_length.
            solve_equivalence_side_conditions. }
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

  Section FromBytes.
    Context {res : API.Expr (type_listZ -> type_listZ)}
            (res_valid :
               valid_func (res (fun _ : API.type => unit)))
            (res_Wf : API.Wf res).
    Context (tight_bounds_tighter_than_max :
               list_Z_tighter_than tight_bounds (@MaxBounds.max_bounds width n))
            (tight_bounds_length : length tight_bounds = n)
            (res_eq : forall bs,
                bytes_in_bounds bs ->
                feval (map word.of_Z
                           (API.interp (res _) (map byte.unsigned bs)))
                = feval_bytes bs)
            (res_bounds : forall bs,
                bytes_in_bounds bs ->
                list_Z_bounded_by
                  tight_bounds
                  (API.interp (res _) (map byte.unsigned bs))).
    Context (FElemBytes_in_bounds :
      forall p bs R m, (FElemBytes p bs ⋆ R)%sep m -> bytes_in_bounds bs).

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
          tight_bounds_tighter_than_max FElemBytes_in_bounds.
      subst inlengths insizes outsizes. cbv [spec_of_from_bytes].
      cbv [from_bytes_insizes from_bytes_outsizes from_bytes_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup.
      pose proof FElemBytes_in_bounds _ _ _ _ H.
      eapply Proper_call.
      2:{
        use_translate_func_correct constr:((map Byte.byte.unsigned bs, tt)) Rr.
        all:translate_func_precondition_hammer.
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout.
          all:solve_equivalence_side_conditions.
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
          { rewrite !map_length.
            solve_equivalence_side_conditions. }
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
               list_Z_tighter_than
                 byte_bounds (ByteBounds.byte_bounds n_bytes))
            (byte_bounds_length :
               length byte_bounds = encoded_felem_size_in_bytes)
            (res_eq : forall x,
                bounded_by tight_bounds x ->
                feval_bytes
                  (map byte.of_Z
                       (API.interp (res _) (map word.unsigned x)))
                = feval x)
            (res_bounds : forall x,
                bounded_by tight_bounds x ->
                list_Z_bounded_by
                  byte_bounds
                  (API.interp (res _)
                              (map word.unsigned x))).

    Local Ltac equivalence_side_conditions_hook ::=
      lazymatch goal with
      | |- context [length (API.interp (res _) (map word.unsigned ?x))] =>
        specialize (res_bounds x ltac:(auto));
          rewrite (length_list_Z_bounded_by _ _ res_bounds);
          try congruence; rewrite !map_length;
          felem_to_array; sepsimpl; congruence
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

    Lemma to_bytes_correct f :
      f = make_bedrock_func to_bytes insizes outsizes inlengths res ->
      forall functions,
        spec_of_to_bytes (f :: functions).
    Proof using byte_bounds_length byte_bounds_tighter_than_max
          inname_gen_varname_gen_disjoint
          outname_gen_varname_gen_disjoint ok res_Wf res_bounds
          res_eq res_valid.
      subst inlengths insizes outsizes. cbv [spec_of_to_bytes].
      cbv [to_bytes_insizes to_bytes_outsizes to_bytes_inlengths].
      cbv beta; intros; subst f. cbv [make_bedrock_func].
      cleanup. eapply Proper_call.
      2:{
        use_translate_func_correct
          constr:((map word.unsigned x, tt)) Rr.
        all:try translate_func_precondition_hammer.
        { (* lists_reserved_with_initial_context *)
          lists_reserved_simplify pout.
          all:solve_equivalence_side_conditions. } }
      { postcondition_simplify; [ | ].
        { (* output correctness *)
          eapply res_eq; auto. }
        { (* separation-logic postcondition *)
          eapply Proper_sep_iff1;
            [ solve [apply FElemBytes_array_truncated_scalar_iff1]
            | reflexivity | ].
          sepsimpl; [ | ].
          { rewrite !map_length.
            solve_equivalence_side_conditions. }
          { erewrite ByteBounds.byte_map_unsigned_of_Z,
            ByteBounds.map_byte_wrap_bounded
              by eauto using relax_list_Z_bounded_by.
            change (Z.of_nat (bytes_per access_size.one)) with 1 in *.
            match goal with
              H : map word.unsigned _ = API.interp (res _) _ |- _ =>
              rewrite <-H end.
            auto. } } }
    Qed.
  End ToBytes.
End WithParameters.
