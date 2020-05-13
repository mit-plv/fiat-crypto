Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String. (* should go before lists *)
Require Import Coq.Lists.List.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Array.
Require Import bedrock2.BasicC32Semantics.
Require Import bedrock2.Scalars.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.Defaults32.
Require Import Crypto.Bedrock.MakeAccessSizes.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Proofs.Func.
Require Import Crypto.Bedrock.Proofs.ValidComputable.Func.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Language.API.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Rewriter.Language.Wf.
Require bedrock2.Map.SeparationLogic. (* if imported, list firstn/skipn get overwritten and it's annoying *)
Local Open Scope Z_scope.

Import Language.Compilers.
Import Language.Wf.Compilers.
Import Associational Positional.

Require Import Crypto.Util.Notations.
Import Types.Notations ListNotations.
Import QArith_base.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import Crypto.Bedrock.Tests.X25519_32.
Import X25519_32.
Local Coercion name_of_func (f : bedrock_func) := fst f.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.


Existing Instance Defaults32.default_parameters.
Existing Instance Defaults32.default_parameters_ok.

Section Proofs.
  Context (n : nat := 10%nat)
          (s : Z := 2^255)
          (c : list (Z * Z) := [(1,19)])
          (machine_wordsize : Z := 32).

  Local Notation M := (s - Associational.eval c)%Z.
  Local Notation eval :=
    (eval (weight (Qnum (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))
                  (QDen (inject_Z (Z.log2_up M) / inject_Z (Z.of_nat n)))) n).
  Local Notation loose_bounds := (UnsaturatedSolinasHeuristics.loose_bounds n s c).
  Local Notation tight_bounds := (UnsaturatedSolinasHeuristics.tight_bounds n s c).

  Definition Bignum
             bounds
             (addr : Semantics.word) (x : Z) :
    Semantics.mem -> Prop :=
    Lift1Prop.ex1
      (fun xs =>
         sep (emp (eval (map word.unsigned xs) = x))
             (sep (emp (length xs = n
                        /\ list_Z_bounded_by
                             bounds (map word.unsigned xs)))
                  (array (truncated_scalar Syntax.access_size.word)
                         (word.of_Z word_size_in_bytes)
                         addr (map word.unsigned xs)))).

  Instance spec_of_mulmod_bedrock : spec_of mulmod_bedrock :=
    fun functions =>
      forall x y px py pout old_out t m
             (Ra Rr : Semantics.mem -> Prop),
        sep (sep (Bignum loose_bounds px x)
                 (Bignum loose_bounds py y)) Ra m ->
        sep (Bignum (repeat None n) pout old_out) Rr m ->
        WeakestPrecondition.call
          (p:=@semantics default_parameters)
          functions mulmod_bedrock t m
          (px :: py :: pout :: nil)
          (fun t' m' rets =>
             t = t' /\
             rets = []%list /\
             sep (Lift1Prop.ex1
                    (fun out =>
                       sep (emp (out mod M = (x * y) mod M)%Z)
                           (Bignum tight_bounds pout out))) Rr m').

  Lemma mulmod_valid_func :
    valid_func (mulmod (fun H3 : API.type => unit)).
  Proof.
    apply valid_func_bool_iff.
    vm_compute; reflexivity.
  Qed.

  Lemma mulmod_Wf : expr.Wf3 mulmod.
  Proof. prove_Wf3 (). Qed.

  Lemma mulmod_length (x y : API.interp_type type_listZ) :
    length (API.interp (mulmod _) x y) = n.
  Proof. vm_compute. reflexivity. Qed.

  Lemma map_word_wrap_bounded x :
    length x = n ->
    list_Z_bounded_by tight_bounds x ->
    map word.wrap x = x.
  Proof.
    cbv [n]. intro.
    repeat (destruct x; cbn [length] in *; try congruence).
    match goal with
      | |- context [list_Z_bounded_by ?b _] =>
        let x := eval vm_compute in b in
            change b with x
    end.
    cbv [list_Z_bounded_by FoldBool.fold_andb_map];
      cbn [ZRange.upper ZRange.lower].
    intros.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ =>
             apply Bool.andb_true_iff in H;
               destruct H
           end.
    Z.ltb_to_lt. cbv [map word.wrap].
    let x := eval vm_compute in (2^Semantics.width) in
        change (2^Semantics.width) with x.
    Z.rewrite_mod_small.
    reflexivity.
  Qed.

  Lemma loose_bounds_within_base_access_sizes xs :
    list_Z_bounded_by loose_bounds xs ->
    LoadStoreList.within_base_access_sizes
      (t:=base_listZ) xs Syntax.access_size.word.
  Proof.
    cbn [LoadStoreList.within_base_access_sizes
           LoadStoreList.within_access_sizes_args].
    intro.
    assert (length xs = n) by
        (erewrite <-length_loose_bounds;
         eauto using length_list_Z_bounded_by).
    generalize dependent xs.
    set (b:=loose_bounds).
    vm_compute in b. subst b. subst n.
    repeat (destruct xs as [| ? xs]; intros; cbn [length] in *;
            try congruence; [ ]).
    cbv [list_Z_bounded_by FoldBool.fold_andb_map] in *.
    cbn [ZRange.lower ZRange.upper] in *.
    repeat match goal with
           | H : (_ && _) = true |- _ =>
             apply Bool.andb_true_iff in H; destruct H
           end.
    Z.ltb_to_lt.
    match goal with
      |- context [0 <= _ < ?w] =>
      let w' := (eval vm_compute in w) in
      change w with w'
    end.
    repeat constructor; lia.
  Qed.

  Lemma mulmod_carry_mul_correct :
    Solinas.carry_mul_correct
      (weight (Qnum (Z.log2_up M / n)) (Qden (Z.log2_up M / n)))
      n M
      tight_bounds
      loose_bounds
      (API.Interp mulmod).
  Proof.
    apply carry_mul_correct with (machine_wordsize0:=machine_wordsize).
    { subst n s c machine_wordsize. vm_compute. reflexivity. }
    { apply mulmod_eq. }
  Qed.

  Lemma mulmod_correct x y :
    length x = n ->
    length y = n ->
    list_Z_bounded_by loose_bounds x ->
    list_Z_bounded_by loose_bounds y ->
    let xy :=
        type.app_curried
          (API.Interp mulmod)
          (x, (y, tt)) in
    list_Z_bounded_by tight_bounds xy /\
    eval xy mod M = (eval x * eval y) mod M.
  Proof.
    cbv zeta.
    intros ? ? Hxbounds Hybounds.
    pose proof mulmod_length x y.
    pose proof mulmod_carry_mul_correct x y Hxbounds Hybounds
      as Hspec.
    cbv [expr.Interp] in Hspec. destruct Hspec.
    cbn [type.app_curried fst snd] in *.
    split; assumption.
  Qed.

  Lemma mulmod_bedrock_correct :
    program_logic_goal_for_function! mulmod_bedrock.
  Proof.
    cbv [program_logic_goal_for spec_of_mulmod_bedrock].
    cbn [name_of_func mulmod_bedrock fst]. intros.
    cbv [mulmod_bedrock].
    intros. cbv [Bignum] in * |-. sepsimpl.

    let xs := match goal with
              | H : eval ?xs = x |- _ => xs end in
    let ys := match goal with
              | H : eval ?ys = y |- _ => ys end in
    assert (length xs = n) by (rewrite map_length; eauto);
    assert (length ys = n) by (rewrite map_length; eauto);
    pose proof mulmod_correct xs ys
         (ltac:(assumption)) (ltac:(assumption))
         (ltac:(assumption)) (ltac:(assumption)) as Hcorrect.
    cbn [type.app_curried fst snd] in Hcorrect.
    cbv [expr.Interp] in Hcorrect.
    destruct Hcorrect as [Hcorrect_bounds Hcorrect_eval].

    eapply Proper_call.
    2:{
      let xs := match goal with
                  Hx : eval ?xs = x |- _ =>
                  xs end in
      let ys := match goal with
                  Hy : eval ?ys = y |- _ =>
                  ys end in
      apply translate_func_correct
        with (args:=(xs, (ys, tt)))
             (flat_args:=[px;py]%list)
             (out_ptrs:=[pout]%list)
             (Ra0:=Ra) (Rr0:=Rr).
      { apply mulmod_valid_func; eauto. }
      { apply mulmod_Wf; eauto. }
      { cbn [LoadStoreList.list_lengths_from_args
               LoadStoreList.list_lengths_from_value
               fst snd].
        rewrite !map_length.
        repeat match goal with H : length _ = n |- _ =>
                               rewrite H end.
        reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { intros.
        cbn [fst snd Types.varname_set_args Types.varname_set_base
                 Types.rep.varname_set Types.rep.listZ_mem
                 Types.rep.Z].
        cbv [PropSet.union PropSet.singleton_set PropSet.elem_of
                           PropSet.empty_set].
        destruct 1 as [? | [? | ?] ]; try tauto;
          match goal with H : _ = varname_gen _ |- _ =>
                          apply varname_gen_startswith in H;
                            vm_compute in H; congruence
          end. }
      { cbn [fst snd Types.equivalent_flat_args Types.rep.listZ_mem
                 Types.equivalent_flat_base Types.rep.equiv
                 Types.rep.Z]. sepsimpl.
        exists 1%nat. cbn [firstn skipn length hd].
        apply SeparationLogic.sep_comm.
        apply SeparationLogic.sep_assoc.
        apply SeparationLogic.sep_comm.
        apply SeparationLogic.sep_ex1_l.
        exists 1%nat. cbn [firstn skipn length hd].
        apply SeparationLogic.sep_assoc.
        sepsimpl; try reflexivity; [ ].
        eexists.
        sepsimpl;
          try match goal with
              | |- dexpr _ _ (Syntax.expr.literal _) _ => reflexivity
              | _ => apply word.unsigned_range
              end;
          eauto using Forall_map_unsigned; [ ].
        eexists; sepsimpl;
          [ reflexivity
          | rewrite bits_per_word_eq_width;
            solve [apply Forall_map_unsigned]
          | ].
        eexists; sepsimpl; [ reflexivity .. | ].
        apply SeparationLogic.sep_comm.
        apply SeparationLogic.sep_assoc.
        apply SeparationLogic.sep_comm.
        sepsimpl; try reflexivity; [ ].
        eexists.
        sepsimpl;
          try match goal with
              | |- dexpr _ _ (Syntax.expr.literal _) _ => reflexivity
              | _ => apply word.unsigned_range
              end;
          eauto using Forall_map_unsigned; [ ].
        eexists; sepsimpl;
          [ reflexivity
          | rewrite bits_per_word_eq_width;
            solve [apply Forall_map_unsigned]
          | ].
        eexists; sepsimpl; [ reflexivity .. | ].
        rewrite @word_size_in_bytes_eq in * by typeclasses eauto.
        change BasicC32Semantics.parameters with semantics in *.
        rewrite !word.of_Z_unsigned.
        SeparationLogic.ecancel_assumption. }
      { cbn. repeat constructor; cbn [In]; try tauto.
        destruct 1; congruence. }
      { cbn. ssplit; reflexivity. }
      { cbn [LoadStoreList.within_access_sizes_args fst snd].
        ssplit; try apply loose_bounds_within_base_access_sizes;
          auto. }
      { intros.
        cbn [fst snd Types.varname_set_base type.final_codomain
                 Types.rep.varname_set Types.rep.listZ_mem
                 Types.rep.Z].
        cbv [PropSet.singleton_set PropSet.elem_of PropSet.empty_set].
        intro;
          match goal with H : _ = varname_gen _ |- _ =>
                          apply varname_gen_startswith in H;
                            vm_compute in H; congruence
          end. }
      { cbn. repeat constructor; cbn [In]; tauto. }
      { cbn. reflexivity. }
      { cbn [type.app_curried fst snd].
        apply loose_bounds_within_base_access_sizes.
        apply relax_correct.
        apply Hcorrect_bounds. }
      { cbn. rewrite union_empty_r.
        apply disjoint_singleton_r_iff.
        cbv [PropSet.singleton_set PropSet.elem_of PropSet.union].
        destruct 1; congruence. }
      { cbn [LoadStoreList.lists_reserved_with_initial_context
               LoadStoreList.list_lengths_from_value
               LoadStoreList.extract_listnames
               LoadStoreList.lists_reserved
               Flatten.flatten_listonly_base_ltype
               Flatten.flatten_base_ltype
               Flatten.flatten_argnames List.app
               map.of_list_zip map.putmany_of_list_zip
               type.app_curried type.final_codomain fst snd].
        sepsimpl.
        (let xs := (match goal with
                      Hx : eval ?xs = old_out |- _ =>
                      xs end) in
         exists xs).
        sepsimpl;
          [ rewrite map_length, mulmod_length by assumption;
            congruence | ].
        cbn [Types.rep.equiv Types.base_rtype_of_ltype
                             Types.rep.Z Types.rep.listZ_mem].
        sepsimpl.
        eexists.
        sepsimpl;
          try match goal with
                | |- dexpr _ _ _ _ =>
                  apply get_put_same, word.of_Z_unsigned
                | _ => apply word.unsigned_range
              end.
        eexists; sepsimpl; [ reflexivity
                           | rewrite bits_per_word_eq_width;
                             solve [apply Forall_map_unsigned] | ].
        eexists; sepsimpl; [ reflexivity
                           | eexists; split; reflexivity | ].
        eauto using Forall_map_unsigned. } }

    repeat intro; cbv beta in *.
    cbn [Types.equivalent_flat_base
           Types.equivalent_listexcl_flat_base
           Types.equivalent_listonly_flat_base
           Types.rep.equiv Types.rep.listZ_mem Types.rep.Z
           type.final_codomain] in *.
    repeat match goal with
           | _ => progress subst
           | _ => progress sepsimpl_hyps
           | H : _ /\ _ |- _ => destruct H
           | |- _ /\ _ => split; [ reflexivity | ]
           end.
    sepsimpl.
    match goal with
    | H : dexpr _ _ (Syntax.expr.literal _) _ |- _ =>
      cbn [dexpr WeakestPrecondition.expr expr_body hd] in H;
        cbv [literal] in H; rewrite word.of_Z_unsigned in H;
          inversion H; clear H; subst
    end.
    eexists; cbv [Bignum]; sepsimpl; [ eassumption | ].
    eexists; sepsimpl.
    { rewrite <-(map_word_wrap_bounded
                   (expr.interp _ (mulmod API.interp_type) _ _))
        by auto.
      rewrite <-map_unsigned_of_Z. reflexivity. }
    { rewrite map_length. assumption. }
    { rewrite map_unsigned_of_Z.
      rewrite map_word_wrap_bounded by auto.
      assumption. }
    { rewrite map_unsigned_of_Z.
      rewrite map_word_wrap_bounded by auto.
      cbn [type.app_curried fst snd] in *.
      rewrite word_size_in_bytes_eq, ?word.of_Z_unsigned.
      match goal with H : word.unsigned _ = word.unsigned _ |- _ =>
                      apply word.unsigned_inj in H end.
      match goal with H : map word.unsigned _ = _ |- _ =>
                      rewrite <-H end.
      subst.
      assumption. }
  Qed.
  (* Print Assumptions mulmod_bedrock_correct. *)
End Proofs.
