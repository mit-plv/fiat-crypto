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
Require Import Crypto.Bedrock.MakeAccessSizes.
Require Import Crypto.Bedrock.MakeNames.
Require Import Crypto.Bedrock.MakeListLengths.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.VarnameGenerator.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
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

  Definition max_range : ZRange.zrange :=
    {|ZRange.lower:=0; ZRange.upper:=2^Semantics.width-1|}.
  Definition max_bounds : list (option ZRange.zrange) :=
    repeat (Some max_range) n.

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
    Context (inname_gen_unique :
               forall i j : nat, inname_gen i = inname_gen j <-> i = j)
            (outname_gen_unique :
               forall i j : nat, outname_gen i = outname_gen j <-> i = j).

    Definition Bignum :=
      array scalar (word.of_Z word_size_in_bytes).

    Lemma Bignum_of_bytes addr bs :
      length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
      Lift1Prop.iff1
        (array ptsto (word.of_Z 1) addr bs)
        (Bignum addr (map word.of_Z
                          (eval_bytes (width:=Semantics.width) bs))).
    Admitted. (* TODO *)

    Lemma Bignum_to_bytes addr x :
      list_Z_bounded_by max_bounds (map word.unsigned x) ->
      Lift1Prop.iff1
        (Bignum addr x)
        (array ptsto (word.of_Z 1) addr (encode_bytes x)).
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

    Lemma bounded_by_loose_bounds_length x :
      list_Z_bounded_by loose_bounds x -> length x = n.
    Proof.
      intros. pose proof length_list_Z_bounded_by _ _ ltac:(eassumption).
      rewrite length_loose_bounds in *. lia.
    Qed.

    Lemma max_bounds_range_iff x :
      let bytes := (Memory.bytes_per
                      (width:=Semantics.width) access_size.word) in
      list_Z_bounded_by max_bounds x <->
      (length x = n /\
       Forall
        (fun z : Z =>
           0 <= z < 2 ^ (Z.of_nat bytes * 8)) x).
   Proof.
     cbv [max_bounds max_range list_Z_bounded_by].
     rewrite bits_per_word_eq_width by auto using width_0mod_8.
     generalize n as m.
     induction x; destruct m; split;
       cbn [FoldBool.fold_andb_map repeat]; try congruence; intros;
         repeat match goal with
                | _ => progress cleanup
                | _ => progress cbn [length ZRange.lower ZRange.upper] in *
                | |- Forall _ [] => solve [constructor]
                | |- Forall _ (_ :: _) => constructor
                | H: Forall _ (_ :: _) |- _ =>
                  inversion H; clear H; subst
                | |- (_ && _)%bool = true =>
                  apply Bool.andb_true_iff; split
                | H: (_ && _)%bool = true |- _ =>
                  apply Bool.andb_true_iff in H; destruct H
                | H : context [iff] |- _ => eapply H; solve [eauto]
                | H : context [iff] |- _ =>
                  rewrite H; auto; congruence
                | |- _ /\ _ => split
                | |- S _ = S _ => f_equal
                | _ => progress Z.ltb_to_lt
                | _ => congruence
                | _ => lia
                end.
   Qed.

    Lemma map_word_wrap_bounded' r x m :
      ZRange.is_tighter_than_bool r max_range = true ->
      list_Z_bounded_by (repeat (Some r) m) x ->
      map word.wrap x = x.
    Proof.
      intros.
      pose proof length_list_Z_bounded_by _ x ltac:(eassumption).
      cbv [max_bounds max_range list_Z_bounded_by
                      ZRange.is_tighter_than_bool] in *.
      rewrite repeat_length in *.
      generalize dependent m.
      generalize dependent x; induction x; destruct m;
        repeat match goal with
               | _ => progress intros
               | _ => progress cleanup
               | _ => progress
                        cbn [length FoldBool.fold_andb_map
                                    ZRange.upper ZRange.lower
                                    repeat map] in *
               | H : _ && _ = true |- _ =>
                 apply Bool.andb_true_iff in H
               | IH : context [map word.wrap ?x = ?x] |- _ =>
                 rewrite IH with (m:=m) by (try eassumption; lia)
               | _ => progress Z.ltb_to_lt
               | |- word.wrap ?x :: ?y = ?x :: ?y =>
                 cbv [word.wrap]; Z.rewrite_mod_small;
                   reflexivity
               | _ => congruence
               end.
    Qed.

    Lemma map_word_wrap_bounded x :
      list_Z_bounded_by max_bounds x ->
      map word.wrap x = x.
    Proof.
      intros. eapply map_word_wrap_bounded'; [ | eassumption ].
      apply ZRange.is_tighter_than_bool_Reflexive.
    Qed.

    Ltac crush_list_ptr_subgoals :=
      repeat match goal with
             | _ => progress cbv [WeakestPrecondition.literal]
             | _ => rewrite word.of_Z_unsigned
             | _ => rewrite map.get_put_diff by congruence
             | _ => rewrite map.get_put_same by auto
             | |- WeakestPrecondition.get _ _ _ =>
               eexists
             | _ => apply max_bounds_range_iff;
                    solve [auto using relax_to_max_bounds]
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
          let x := map word.unsigned wx in
          let y := map word.unsigned wy in
          (* these bounds go here instead of within Solinas_carry_mul_correct
             because they are needed to prove the length of the output *)
          list_Z_bounded_by loose_bounds x ->
          list_Z_bounded_by loose_bounds y ->
          length wold_out = n ->
          sep (sep (Bignum px wx) (Bignum py wy)) Ra m ->
          sep (Bignum pout wold_out) Rr m ->
          WeakestPrecondition.call
            functions name t m
            (px :: py :: pout :: nil)
            (fun t' m' rets =>
               t = t' /\
               rets = []%list /\
               Lift1Prop.ex1
                 (fun wout =>
                    let out := map word.unsigned wout in
                    sep
                      (sep
                         (emp (Solinas_carry_mul_correct x y out))
                         (Bignum pout wout)) Rr) m').

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
          [ rewrite map_unsigned_of_Z, map_word_wrap_bounded
            by (apply max_bounds_range_iff; eauto);
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
          apply max_bounds_range_iff;
            auto using relax_to_max_bounds. }
      { (* output access sizes are legal *)
        pose proof bits_per_word_le_width.
        cbn - [Memory.bytes_per]; tauto. }
      { (* output access sizes are accurate *)
        cbn - [Memory.bytes_per].
        apply max_bounds_range_iff;
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
        sepsimpl; [ rewrite map_length; congruence | ].
        exists pout; sepsimpl; [ ].
        match goal with
          H : Solinas_carry_mul_correct _ _ ?e |- _ =>
          assert (list_Z_bounded_by max_bounds e)
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
