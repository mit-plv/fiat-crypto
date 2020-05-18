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

  Record FunctionSignature t :=
    { name : string;
      input_array_sizes : foreach_arg access_sizes t;
      output_array_sizes : foreach_ret access_sizes t;
      input_array_lengths : foreach_arg list_lengths t;
      output_array_lengths : foreach_ret list_lengths t;
    }.
  Arguments name {_}.
  Arguments input_array_sizes {_}.
  Arguments output_array_sizes {_}.
  Arguments input_array_lengths {_}.
  Arguments output_array_lengths {_}.

  Definition make_bedrock_func
             {t} (sig : FunctionSignature t) (res : API.Expr t)
    : bedrock_func :=
    (sig.(name), make_bedrock_func_with_sizes
                   (sig.(input_array_sizes)) (sig.(output_array_sizes))
                   (sig.(input_array_lengths)) res).

  Definition carry_mul
    : FunctionSignature (type_listZ -> type_listZ -> type_listZ) :=
    {| name := carry_mul_name;
       input_array_sizes := access_sizes_repeat_args access_size.word _;
       output_array_sizes := access_sizes_repeat_base access_size.word _;
       input_array_lengths := list_lengths_repeat_args n _;
       output_array_lengths := list_lengths_repeat_base n _ |}.

  Definition add
    : FunctionSignature (type_listZ -> type_listZ -> type_listZ) :=
    {| name := add_name;
       input_array_sizes := access_sizes_repeat_args access_size.word _;
       output_array_sizes := access_sizes_repeat_base access_size.word _;
       input_array_lengths := list_lengths_repeat_args n _;
       output_array_lengths := list_lengths_repeat_base n _ |}.

  Local Definition limbwidth :=
    (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
  Local Definition n_bytes :=
    (Freeze.bytes_n (Qnum limbwidth) (Qden limbwidth) n).

  Definition to_bytes
    : FunctionSignature (type_listZ -> type_listZ) :=
    {| name := to_bytes_name;
       input_array_sizes := access_sizes_repeat_args access_size.word _;
       output_array_sizes := access_sizes_repeat_base access_size.one _;
       input_array_lengths := list_lengths_repeat_args n _;
       output_array_lengths := list_lengths_repeat_base n_bytes _ |}.

  Section Proofs.
    Context {ok : Types.ok}.
    Existing Instance semantics_ok.

    Local Notation M := (s - Associational.eval c)%Z.
    Definition weight :=
      (ModOps.weight
         (Qnum (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))
         (QDen (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))).
    Local Notation eval := (eval weight n).
    Local Notation loose_bounds := (UnsaturatedSolinas.loose_bounds n s c).
    Local Notation tight_bounds := (UnsaturatedSolinas.tight_bounds n s c).

    Context
      (* loose_bounds_ok could be proven in parameterized form, but is a pain
      and is easily computable with parameters plugged in. So for now, leaving
      as a precondition. *)
      (loose_bounds_ok :
         ZRange.type.option.is_tighter_than
           (t:=type_listZ) (Some loose_bounds)
           (Some (max_bounds n)) = true)
      (check_args_ok :
         check_args n s c Semantics.width (ErrorT.Success tt)
         = ErrorT.Success tt).

    Context (inname_gen_varname_gen_ok : disjoint inname_gen varname_gen)
            (outname_gen_varname_gen_ok : disjoint outname_gen varname_gen)
            (outname_gen_inname_gen_ok : disjoint outname_gen inname_gen).
    Context (inname_gen_unique : unique inname_gen)
            (outname_gen_unique : unique outname_gen).

    (* TODO : add length to Bignums and ByteArrays *)
    Definition Bignum : Semantics.word -> list Semantics.word -> Semantics.mem -> Prop :=
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

    Record Op {t : API.type}
          (pipeline_out : Pipeline.ErrorT (API.Expr t)) :=
      { post :
          type.for_each_lhs_of_arrow API.interp_type t ->
          API.interp_type (type.base (type.final_codomain t)) -> Prop;
        correctness :
          forall res,
            pipeline_out = ErrorT.Success res ->
            forall args,
              post args (type.app_curried (API.Interp res) args) }.
    Arguments post {_ _}.
    Arguments correctness {_ _}.

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
    Ltac instantiate_postcondition Hcorrect :=
      let Ht := fresh "Ht" in
      let G := fresh "G" in
      match type of Hcorrect with ?T => set (Ht:=T) end;
      match goal with |- ?g => set (G:=g) end;
      repeat
        (let g := (eval hnf in G) in
         let E := fresh "E" in
         match g with
         | ?f ?e =>
           remember e as E;
           let T := (eval hnf in Ht) in
           let y := lazymatch (eval pattern E in T) with
                      ?f _ => f end in
           let y := (eval cbn iota zeta delta in y) in
           let Ht' := fresh "Ht" in
           set (Ht':=y);
           subst G; set (G:=f);
           subst Ht; rename Ht' into Ht; subst E
         end);
      subst G;
      let T := (eval hnf in Ht) in
      instantiate (1:=T); exact Hcorrect.
    Ltac pose_evar_for_post_with_name name :=
      let T := fresh "T" in
      let postT := fresh "postT" in
      let postT' := fresh "postT" in
      match goal with
        |- @Op ?t _ => pose (T := t) end;
      pose (postT := Prop);
      repeat
        (let t := (eval hnf in T) in
         let bodyt := (eval hnf in postT) in
         match t with
         | type.arrow ?s ?d =>
           let st := (eval cbn in (API.interp_type s)) in
           rename postT into postT';
           pose (postT := st -> postT'); subst postT' T;
           pose (T:=d)
         | ?s =>
           let st := (eval cbn in (API.interp_type s)) in
           rename postT into postT';
           pose (postT := st -> postT'); subst postT' T
         end);
      evar (name : postT); subst postT.
    Ltac prove_Op :=
      repeat match goal with p := _ |- _ => subst p end;
      intros;
      let Hcorrect :=
          lazymatch goal with
            H : _ = ErrorT.Success _ |- _ => H end in
      apply_correctness;
      specialize_to_args Hcorrect;
      fold weight in Hcorrect;
      cbn; instantiate_postcondition Hcorrect.

    Definition carry_mul_op
      : Op (UnsaturatedSolinas.carry_mul n s c Semantics.width).
    Proof.
      pose_evar_for_post_with_name body.
      (* TODO: below uncurrying of post could probably be automated (for other
         ops as well) *)
      apply Build_Op with
          (post:= fun args =>
                    let x := fst args in
                    let y := fst (snd args) in
                    body x y).
      prove_Op.
    Defined.

    Definition add_op
      : Op (UnsaturatedSolinas.add n s c Semantics.width).
    Proof.
      pose_evar_for_post_with_name body.
      apply Build_Op with
          (post:= fun args =>
                    let x := fst args in
                    let y := fst (snd args) in
                    body x y).
      prove_Op.
    Defined.

    Definition to_bytes_op
      : Op (UnsaturatedSolinas.to_bytes n s c Semantics.width).
    Proof.
      pose_evar_for_post_with_name body.
      apply Build_Op
        with (post:= fun args =>
                       let x := fst args in
                       body x).
      prove_Op.
    Defined.

    (* TODO: move *)
    Definition within_input_sizes
               {t} (sig : FunctionSignature t)
               (args : type.for_each_lhs_of_arrow API.interp_type t) : Prop :=
      LoadStoreList.within_access_sizes_args args sig.(input_array_sizes).
    Definition within_output_sizes
               {t} (sig : FunctionSignature t)
               (out : base.interp (type.final_codomain t)) : Prop :=
      LoadStoreList.within_base_access_sizes out sig.(output_array_sizes).
    Definition output_sizes_obeyed
               {t} (sig : FunctionSignature t) (res : API.Expr t) : Prop :=
      forall args,
        within_input_sizes sig args ->
        within_output_sizes sig (type.app_curried (API.Interp res) args).

    (* TODO: definition to construct seplogic/args automatically from type? Put in Op? *)
    Definition spec_of_carry_mul : spec_of carry_mul_name :=
      fun functions =>
        forall wx wy px py pout wold_out t m
               (Ra Rr : Semantics.mem -> Prop),
          sep (sep (BignumSuchThat px wx (fun l => length l = n))
                   (BignumSuchThat py wy (fun l => length l = n)))
              Ra m ->
          sep (BignumSuchThat pout wold_out (fun l => length l = n))
              Rr m ->
          let args := (map word.unsigned wx,
                       (map word.unsigned wy, tt)) in
          within_input_sizes carry_mul args ->
          WeakestPrecondition.call
            functions carry_mul_name t m
            (px :: py :: pout :: nil)
            (fun t' m' rets =>
               t = t' /\
               rets = []%list /\
               exists wout,
                 sep (BignumSuchThat pout wout (post carry_mul_op args))
                     Rr m').

    Definition spec_of_add : spec_of add_name :=
      fun functions =>
        forall wx wy px py pout wold_out t m
               (Ra Rr : Semantics.mem -> Prop),
          sep (sep (BignumSuchThat px wx (fun l => length l = n))
                   (BignumSuchThat py wy (fun l => length l = n)))
              Ra m ->
          sep (BignumSuchThat pout wold_out (fun l => length l = n))
              Rr m ->
          let args := (map word.unsigned wx,
                       (map word.unsigned wy, tt)) in
          within_input_sizes add args ->
          WeakestPrecondition.call
            functions add_name t m
            (px :: py :: pout :: nil)
            (fun t' m' rets =>
               t = t' /\
               rets = []%list /\
               exists wout,
                 sep (BignumSuchThat pout wout (post add_op args))
                     Rr m').

    Definition spec_of_to_bytes : spec_of to_bytes_name :=
      fun functions =>
        forall wx px pout wold_out t m
               (Ra Rr : Semantics.mem -> Prop),
          sep (BignumSuchThat px wx (fun l => length l = n)) Ra m ->
          sep (EncodedBignumSuchThat pout wold_out
                                     (fun l => length l = n_bytes))
              Rr m ->
          let args := (map word.unsigned wx, tt) in
          within_input_sizes to_bytes args ->
          WeakestPrecondition.call
            functions to_bytes_name t m
            (px :: pout :: nil)
            (fun t' m' rets =>
               t = t' /\
               rets = []%list /\
               exists wout,
                 sep (EncodedBignumSuchThat pout wout (post to_bytes_op args))
                     Rr m').

    Definition output_lengths_ok
               {t} (sig : FunctionSignature t) (res : API.Expr t)
      : Prop :=
      forall args : type.for_each_lhs_of_arrow API.interp_type t,
        LoadStoreList.list_lengths_from_value
          (type.app_curried (API.Interp res) args)
        = sig.(output_array_lengths).

    Definition is_correct
               {t : API.type}
               (start : Pipeline.ErrorT (API.Expr t))
               (sig : FunctionSignature t)
               {name : string} (spec : spec_of name) : Prop :=
      (forall res : API.Expr t,
          start = ErrorT.Success res ->
          expr.Wf3 res ->
          valid_func (res (fun _ : API.type => unit)) ->
          output_sizes_obeyed sig res ->
          output_lengths_ok sig res ->
          forall functions,
            spec (make_bedrock_func sig res :: functions)).

    Ltac setup :=
      match goal with
        |- is_correct _ ?def ?spec =>
        cbv [is_correct def spec make_bedrock_func
                        output_sizes_obeyed within_output_sizes
                        within_input_sizes] in *; intros;
        sepsimpl
      end;
      cbn [name input_array_sizes output_array_sizes] in *.

    Lemma carry_mul_correct :
      is_correct
        (UnsaturatedSolinas.carry_mul n s c Semantics.width)
        carry_mul spec_of_carry_mul.
    Proof.
      setup.
      match goal with |- context [post ?op ?args] =>
                      pose proof (correctness op)
                           ltac:(assumption) ltac:(assumption) args
      end.

      (* pick out arguments *)
      match goal with |- context [post ?op ?args] =>
                      set (A:=args) end.

      (* get output length here for convenience *)
      match goal with H : output_lengths_ok _ _ |- _ =>
                      specialize (H A); cbn - [n_bytes] in H end.

      (* TODO: automate flat_args, out_ptrs? *)
      (* use translate_func_correct to get the translation postcondition *)
      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=A) (flat_args := [px; py]) ]; subst A.

      { (* prove that the translation postcondition is sufficient *)
        repeat intro.
        match goal with
          H : context [sep _ _ ?m] |- context [_ ?m] =>
          cbn - [Memory.bytes_per translate_func] in H
        end.
        sepsimpl_hyps; ssplit; [ congruence | congruence | eexists ].
        fold Bignum in *.
        sepsimpl;
          [ erewrite map_unsigned_of_Z, map_word_wrap_bounded
            by (eapply max_bounds_range_iff; eauto);
            match goal with H : _ |- _ => apply H; assumption end | ].
        cbv [Bignum expr.Interp].
        match goal with
        | H : literal (word.unsigned _) (eq _) |- _ =>
          inversion H as [H']; clear H;
            rewrite word.of_Z_unsigned in H'
        end.
        match goal with H : word.unsigned _ = word.unsigned _ |- _ =>
                        apply word.unsigned_inj in H end.
        (* TODO: without the below clear, subst fails, this is dumb *)
        repeat match goal with H : _ = n |- _ => clear H end.
        subst.
        match goal with
          H : map word.unsigned _ = ?l |- context [map word.of_Z ?l] =>
          rewrite <-H, map_of_Z_unsigned
        end.
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
        cbn. congruence. }
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
      { (* output access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* space is reserved for output lists *)
        cbn - [Memory.bytes_per]. sepsimpl.
        cbv [expr.Interp] in *. cbn [Compilers.base_interp] in *.
        exists (map word.unsigned wold_out).
        sepsimpl; [ rewrite map_length in *; congruence | ].
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
        use_sep_assumption.
        rewrite array_truncated_scalar_scalar_iff1.
        cancel. }
    Qed.
    Lemma add_correct :
      is_correct
        (UnsaturatedSolinas.add n s c Semantics.width)
        add spec_of_add.
    Proof.
      setup.
      match goal with |- context [post ?op ?args] =>
                      pose proof (correctness op)
                           ltac:(assumption) ltac:(assumption) args
      end.

      (* pick out arguments *)
      match goal with |- context [post ?op ?args] =>
                      set (A:=args) end.

      (* get output length here for convenience *)
      match goal with H : output_lengths_ok _ _ |- _ =>
                      specialize (H A); cbn - [n_bytes] in H end.

      (* TODO: automate flat_args, out_ptrs? *)
      (* use translate_func_correct to get the translation postcondition *)
      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=A) (flat_args := [px; py]) ]; subst A.

      { (* prove that the translation postcondition is sufficient *)
        repeat intro.
        match goal with
          H : context [sep _ _ ?m] |- context [_ ?m] =>
          cbn - [Memory.bytes_per translate_func] in H
        end.
        sepsimpl_hyps; ssplit; [ congruence | congruence | eexists ].
        fold Bignum in *.
        sepsimpl;
          [ erewrite map_unsigned_of_Z, map_word_wrap_bounded
            by (eapply max_bounds_range_iff; eauto);
            match goal with H : _ |- _ => apply H; assumption end | ].
        cbv [Bignum expr.Interp].
        match goal with
        | H : literal (word.unsigned _) (eq _) |- _ =>
          inversion H as [H']; clear H;
            rewrite word.of_Z_unsigned in H'
        end.
        match goal with H : word.unsigned _ = word.unsigned _ |- _ =>
                        apply word.unsigned_inj in H end.
        (* TODO: without the below clear, subst fails, this is dumb *)
        repeat match goal with H : _ = n |- _ => clear H end.
        subst.
        match goal with
          H : map word.unsigned _ = ?l |- context [map word.of_Z ?l] =>
          rewrite <-H, map_of_Z_unsigned
        end.
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
        cbn. congruence. }
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
      { (* output access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* space is reserved for output lists *)
        cbn - [Memory.bytes_per]. sepsimpl.
        cbv [expr.Interp] in *. cbn [Compilers.base_interp] in *.
        exists (map word.unsigned wold_out).
        sepsimpl; [ rewrite map_length in *; congruence | ].
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
        use_sep_assumption.
        rewrite array_truncated_scalar_scalar_iff1.
        cancel. }
    Qed.

    Lemma to_bytes_correct :
      is_correct
        (UnsaturatedSolinas.to_bytes n s c Semantics.width)
        to_bytes spec_of_to_bytes.
    Proof.
      setup.
      match goal with |- context [post ?op ?args] =>
                      pose proof (correctness op)
                           ltac:(assumption) ltac:(assumption) args
      end.

      (* pick out arguments *)
      match goal with |- context [post ?op ?args] =>
                      set (A:=args) end.

      (* get output length here for convenience *)
      match goal with H : output_lengths_ok _ _ |- _ =>
                      specialize (H A); cbn - [n_bytes] in H end.

      (* TODO: automate flat_args, out_ptrs? *)
      (* use translate_func_correct to get the translation postcondition *)
      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=A) (flat_args := [px]) ]; subst A.

      { (* prove that the translation postcondition is sufficient *)
        repeat intro.
        match goal with
          H : context [sep _ _ ?m] |- context [_ ?m] =>
          cbn - [Memory.bytes_per translate_func] in H
        end.
        sepsimpl_hyps; ssplit; [ congruence | congruence | eexists ].
        (* differs from mul/add *)
        (* mul/add :
           sepsimpl;
             [ erewrite map_unsigned_of_Z, map_word_wrap_bounded
               by (eapply max_bounds_range_iff; eauto);
               match goal with H : _ |- _ => apply H; assumption end | ].
        cbv [Bignum expr.Interp]. *)
        sepsimpl;
          [ erewrite byte_map_unsigned_of_Z, map_byte_wrap_bounded
            by (eapply byte_bounds_range_iff; eauto);
            match goal with H : _ |- _ => apply H; assumption end | ].
        cbv [EncodedBignum expr.Interp].
        (* end differ *)
        match goal with
        | H : literal (word.unsigned _) (eq _) |- _ =>
          inversion H as [H']; clear H;
            rewrite word.of_Z_unsigned in H'
        end.
        match goal with H : word.unsigned _ = word.unsigned _ |- _ =>
                        apply word.unsigned_inj in H end.
        (* TODO: without the below clear, subst fails, this is dumb *)
        repeat match goal with H : _ = n |- _ => clear H end.
        subst.
        (* differs from mul/add:
        match goal with
          H : map word.unsigned _ = ?l |- context [map word.of_Z ?l] =>
          rewrite <-H, map_of_Z_unsigned
        end.
        rewrite word_size_in_bytes_eq.
        use_sep_assumption.
        rewrite array_truncated_scalar_scalar_iff1.
        *)
        subst.
        match goal with
          H : map word.unsigned _ = ?l |- context [?l] =>
          rewrite <-H end.
        change (Z.of_nat (Memory.bytes_per access_size.one)) with 1 in *.
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
        cbn. congruence. }
      { (* arg pointers are correct *)
        cbn - [Memory.bytes_per]; sepsimpl.
        next_argument. exists_list_ptr px.
        (* differs from mul/add:
        next_argument. exists_list_ptr py. *)
        (* end differ *)
        cbv [Bignum] in *.
        repeat seprewrite array_truncated_scalar_scalar_iff1.
        rewrite <-word_size_in_bytes_eq.
        ecancel_assumption. }
      { (* input access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* output access sizes are legal *)
        (* differs from mul/add :
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. *)
        cbn. apply width_ge_8.
        (* end differ *) }
      { (* space is reserved for output lists *)
        cbn - [Memory.bytes_per]. sepsimpl.
        cbv [expr.Interp] in *. cbn [Compilers.base_interp] in *.
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
        use_sep_assumption.
        rewrite array_truncated_scalar_scalar_iff1. *)
        cbv [EncodedBignum] in *.
        rewrite map_unsigned_of_Z.
        erewrite map_word_wrap_bounded by
            auto using byte_unsigned_within_max_bounds.
        change (Z.of_nat (Memory.bytes_per access_size.one)) with 1 in *.
        use_sep_assumption.
        rewrite array_truncated_scalar_ptsto_iff1.
        rewrite byte_map_of_Z_unsigned.
        (* end differ *)
        cancel. }
    Qed.
  End Proofs.
End __.
