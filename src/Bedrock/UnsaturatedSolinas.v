Require Import Coq.ZArith.ZArith.
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

  Definition make_bedrock_func_with_sizes
             {t} insize outsize (res : API.Expr t)
    : list string * list string * cmd.cmd :=
    fst (translate_func res
                        (make_innames (inname_gen:=inname_gen) _)
                        (list_lengths_repeat_args n _)
                        (access_sizes_repeat_args insize _)
                        (make_outnames (outname_gen:=outname_gen) _)
                        (access_sizes_repeat_base outsize _)).

  Definition make_bedrock_func {t} (res : API.Expr t)
    : list string * list string * cmd.cmd :=
    make_bedrock_func_with_sizes
      (t:=t) access_size.word access_size.word res.

  Definition carry_mul
             (res : API.Expr (type.arrow type_listZ
                                         (type.arrow type_listZ
                                                     type_listZ)))
    : bedrock_func :=
    ("carry_mul", make_bedrock_func res).

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

    Definition Bignum : Semantics.word -> list Semantics.word -> Semantics.mem -> Prop :=
      array scalar (word.of_Z word_size_in_bytes).

    Definition BignumSuchThat
               (addr : Semantics.word) (ws : list Semantics.word) (P: list Z -> Prop)
      : Semantics.mem -> Prop :=
      let xs := map word.unsigned ws in
      sep (emp (P xs)) (Bignum addr ws).

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

    Ltac crush_list_ptr_subgoals :=
      repeat match goal with
             | _ => progress cbv [WeakestPrecondition.literal]
             | _ => rewrite word.of_Z_unsigned
             | _ => rewrite map.get_put_diff by congruence
             | _ => rewrite map.get_put_same by auto
             | |- WeakestPrecondition.get _ _ _ => eexists
             | _ => eapply max_bounds_range_iff;
                    solve [auto using relax_to_max_bounds, relax_correct]
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

    (* TODO: figure where to put this and if we want to do this strategy *)
    Definition Solinas_carry_mul_correct x y out :=
      eval out mod M = (Z.mul (eval x) (eval y)) mod M
      /\ list_Z_bounded_by tight_bounds out.

    Lemma carry_mul_correct_iff carry_mul :
      Solinas.carry_mul_correct
        weight n M tight_bounds loose_bounds carry_mul
      <-> (forall x y,
              list_Z_bounded_by loose_bounds x ->
              list_Z_bounded_by loose_bounds y ->
              Solinas_carry_mul_correct x y (carry_mul x y)).
    Proof. reflexivity. Qed.

    (* For out, you can get a Bignum from an array of bytes using
       Bignum_from_bytes. *)
    Definition spec_of_carry_mul name : spec_of name :=
      fun functions =>
        forall wx wy px py pout wold_out t m
               (Ra Rr : Semantics.mem -> Prop),
          sep (sep (BignumSuchThat px wx (list_Z_bounded_by loose_bounds))
                   (BignumSuchThat py wy (list_Z_bounded_by loose_bounds))) Ra m ->
          sep (BignumSuchThat pout wold_out (fun l => length l = n)) Rr m ->
          let post := Solinas_carry_mul_correct (map word.unsigned wx)
                                                (map word.unsigned wy) in
          WeakestPrecondition.call
            functions name t m
            (px :: py :: pout :: nil)
            (fun t' m' rets =>
               t = t' /\
               rets = []%list /\
               exists wout,
                 sep (BignumSuchThat pout wout post) Rr m').

    Lemma carry_mul_correct carry_mul_name:
      forall carry_mul_res :
               API.Expr (type_listZ -> type_listZ -> type_listZ),
        UnsaturatedSolinas.carry_mul n s c Semantics.width
        = ErrorT.Success carry_mul_res ->
        expr.Wf3 carry_mul_res ->
        valid_func (carry_mul_res (fun _ : API.type => unit)) ->
        forall functions,
          spec_of_carry_mul carry_mul_name
            ((carry_mul_name, make_bedrock_func carry_mul_res) :: functions).
    Proof.
      cbv [spec_of_carry_mul make_bedrock_func]; intros.
      cbv [BignumSuchThat] in *. sepsimpl.

      (* get the carry_mul correctness proof *)
      match goal with H : _ = ErrorT.Success _ |- _ =>
                      apply UnsaturatedSolinas.carry_mul_correct in H;
                        [ | assumption ];
                        rewrite carry_mul_correct_iff in H;
                        specialize (H (_ wx) (_ wy)
                                      ltac:(eassumption) ltac:(eassumption))
      end.

      (* assert output length for convenience *)
      match goal with
        H : context [Solinas_carry_mul_correct _ _ ?e] |- _ =>
        assert (length e = n)
          by (apply bounded_by_loose_bounds_length, relax_correct;
              apply H)
      end.

      (* use translate_func_correct to get the translation postcondition *)
      eapply Proper_call;
        [ | eapply translate_func_correct with
                (Ra0:=Ra) (Rr0:=Rr) (out_ptrs:=[pout])
                (args:=(map word.unsigned wx, (map word.unsigned wy, tt)))
                (flat_args := [px; py]) ].

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
        subst. cbv [Bignum expr.Interp].
        match goal with
        | H : literal (word.unsigned _) (eq _) |- _ =>
          inversion H as [H']; clear H;
            rewrite word.of_Z_unsigned in H'
        end.
        match goal with H : word.unsigned _ = word.unsigned _ |- _ =>
                        apply word.unsigned_inj in H end.
        (* TODO: without the below clear, subst fails, this is dumb *)
        match goal with H : _ = n |- _ => clear H end.
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
        cbn. rewrite !bounded_by_loose_bounds_length by auto.
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
          eapply max_bounds_range_iff;
            auto using relax_to_max_bounds. }
      { (* output access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* output access sizes are accurate *)
        cbn - [Memory.bytes_per].
        eapply max_bounds_range_iff;
          apply relax_to_max_bounds, relax_correct.
        match goal with H : _ |- _ => apply H end. }
      { (* space is reserved for output lists *)
        cbn - [Memory.bytes_per]. sepsimpl.
        repeat match goal with
               | _ => progress cbv [expr.Interp] in *
               | _ => rewrite eval_bytes_length by lia
               | _ => rewrite length_tight_bounds in *
               | H : context [array ptsto _ _ ?bs] |- _ =>
                 seprewrite_in Bignum_of_bytes H; [ assumption | ];
                   exists (eval_bytes bs)
               | H : context [Solinas.carry_mul_correct _ _ _ _ _ ?e] |- _ =>
                 specialize (H x y ltac:(eauto) ltac:(eauto));
                   cleanup;
                   pose proof length_list_Z_bounded_by _ (e x y)
                        ltac:(eassumption)
               end.
        cbn [Compilers.base_interp] in *.
        exists (map word.unsigned wold_out).
        sepsimpl; [ rewrite map_length in *; congruence | ].
        exists pout; sepsimpl; [ ].
        match goal with
          H : Solinas_carry_mul_correct _ _ ?e |- _ =>
          assert (list_Z_bounded_by (max_bounds n) e)
            by (apply relax_to_max_bounds, relax_correct; apply H)
        end.
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
  End Proofs.
End __.
