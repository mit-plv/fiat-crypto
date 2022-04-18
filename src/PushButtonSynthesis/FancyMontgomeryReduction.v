(** * Push-Button Synthesis of Montgomery Reduction *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.FancyMontgomeryReduction.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Fancy.Compiler.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.FancyMontgomeryReductionReificationCache.
Require Import Crypto.PushButtonSynthesis.InvertHighLow.
Import ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Compilers
  Language.Wf.Compilers
  Stringification.Language.Compilers.
Import Compilers.API.

Import COperationSpecifications.Primitives.

Import COperationSpecifications.MontgomeryReduction.

Import Associational Positional FancyMontgomeryReduction.MontgomeryReduction.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Local Opaque reified_montred_gen. (* needed for making [autorewrite] not take a very long time *)

Section rmontred.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {static : static_opt}
          {internal_static : internal_static_opt}
          {inline : inline_opt}
          {inline_internal : inline_internal_opt}
          (N R N' : Z) (n : nat)
          (machine_wordsize : machine_wordsize_opt).

  Let value_range := r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.
  Let flag_range := r[0 ~> 1]%zrange.
  Let bound := Some value_range.
  Let consts_list := [N; N'].
  Let R' := Z.modinv R N.

  Definition possible_values_of_machine_wordsize
    := [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
  Local Arguments possible_values_of_machine_wordsize / .

  Let possible_values := possible_values_of_machine_wordsize.

  Local Existing Instance default_language_naming_conventions.
  Local Existing Instance default_documentation_options.
  Local Existing Instance default_output_options.
  Local Existing Instance AbstractInterpretation.default_Options.
  Local Instance widen_carry : widen_carry_opt := false.
  Local Instance widen_bytes : widen_bytes_opt := true.
  Local Instance only_signed : only_signed_opt := false.
  Local Instance no_select_size : no_select_size_opt := None.
  Local Instance split_mul_to : split_mul_to_opt := None.
  Local Instance split_multiret_to : split_multiret_to_opt := None.
  Local Instance unfold_value_barrier : unfold_value_barrier_opt := true.
  Local Instance assembly_hints_lines : assembly_hints_lines_opt := [].
  Local Instance ignore_unique_asm_names : ignore_unique_asm_names_opt := false.
  Local Instance low_level_rewriter_method : low_level_rewriter_method_opt := default_low_level_rewriter_method.

  Let fancy_args
    := (Some {| Pipeline.invert_low log2wordsize := invert_low log2wordsize consts_list;
                Pipeline.invert_high log2wordsize := invert_high log2wordsize consts_list;
                Pipeline.value_range := value_range;
                Pipeline.flag_range := flag_range |}).

  Lemma fancy_args_good
    : match fancy_args with
      | Some {| Pipeline.invert_low := il ; Pipeline.invert_high := ih |}
        => (forall s v v' : Z, il s v = Some v' -> v = Z.land v' (2^(s/2)-1))
           /\ (forall s v v' : Z, ih s v = Some v' -> v = Z.shiftr v' (s/2))
      | None => True
      end.
  Proof.
    cbv [fancy_args invert_low invert_high constant_to_scalar constant_to_scalar_single consts_list fold_right];
      split; intros; break_innermost_match_hyps; Z.ltb_to_lt; subst; congruence.
  Qed.
  Local Hint Extern 1 => apply fancy_args_good: typeclass_instances. (* This is a kludge *)

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (requests : list string) (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := fold_right
         (fun '(b, e) k => if b:bool then Error e else k)
         res
         [
            ((negb (1 <? R))%Z, Pipeline.Value_not_ltZ "R ≤ 1" 1 R);
            ((n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" (Z.of_nat n) 0);
            ((R' =? 0)%Z, Pipeline.No_modular_inverse "R⁻¹ mod N" R N);
            (negb ((R * R') mod N =? 1 mod N)%Z, Pipeline.Values_not_provably_equalZ "(R * R') mod N ≠ 1 mod N" ((R * R') mod N) (1 mod N));
            (negb ((N * N') mod R =? (-1) mod R)%Z, Pipeline.Values_not_provably_equalZ "(N * N') mod R ≠ (-1) mod R" ((N * N') mod R) ((-1) mod R));
            (negb (2 ^ machine_wordsize =? R)%Z, Pipeline.Values_not_provably_equalZ "2^machine_wordsize ≠ R" (2^machine_wordsize) R);
            ((negb (0 <? N))%Z, Pipeline.Value_not_ltZ "N ≤ 0" 0 N);
            ((negb (N <? R))%Z, Pipeline.Value_not_ltZ "R ≤ N" R N);
            ((negb (0 <=? N'))%Z, Pipeline.Value_not_leZ "N' < 0" 0 N');
            ((negb (N' <? R))%Z, Pipeline.Value_not_ltZ "R ≤ N'" R N');
            ((negb (2 <=? machine_wordsize))%Z, Pipeline.Value_not_leZ "machine_wordsize < 2" 2 machine_wordsize)].

  Local Arguments Z.mul !_ !_.

  Local Ltac use_curve_good_t :=
    repeat first [ assumption
                 | progress cbv [EquivModulo.Z.equiv_modulo]
                 | progress rewrite ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *
                 | reflexivity
                 | lia
                 | progress cbn in *
                 | progress intros
                 | solve [ auto with zarith ]
                 | rewrite Z.log2_pow2 by use_curve_good_t ].

  Context (requests : list string)
          (curve_good : check_args requests (Success tt) = Success tt).

  Lemma use_curve_good
    : 0 <= N < R
      /\ 0 <= N' < R
      /\ N <> 0
      /\ R > 1
      /\ EquivModulo.Z.equiv_modulo R (N * N') (-1)
      /\ EquivModulo.Z.equiv_modulo N (R * R') 1
      /\ n <> 0%nat
      /\ 2 <= machine_wordsize
      /\ 2 ^ machine_wordsize = R.
  Proof using curve_good.
    prepare_use_curve_good ().
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
  Qed.

  Definition montred
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         fancy_args (* fancy *)
         possible_values
         (reified_montred_gen
            @ GallinaReify.Reify N @ GallinaReify.Reify R @ GallinaReify.Reify N' @ GallinaReify.Reify (machine_wordsize:Z))
         (bound, (bound, tt))
         bound.

  Definition smontred (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "montred" montred
          (fun _ _ _ => @nil string).

  Local Ltac solve_montred_preconditions :=
    repeat first [ lia
           | apply use_curve_good
           | progress (push_Zmod; pull_Zmod)
           | progress autorewrite with zsimplify_fast
           | rewrite Z.div_add' by lia
           | rewrite Z.div_small by lia
           | progress Z.rewrite_mod_small ].

  Local Strategy -100 [montred]. (* needed for making Qed not take forever *)
  Local Strategy -100 [montred' reified_montred_gen]. (* needed for making prove_correctness not take forever *)
  Lemma montred_correct res (Hres : montred = Success res)
    : montred_correct N R R' (API.Interp res).
  Proof using n curve_good.
    cbv [montred_correct]; intros.
    rewrite <- MontgomeryReduction.montred'_correct with (R:=R) (N':=N') (Zlog2R:=machine_wordsize) (n:=n) (lo:=lo) (hi:=hi) by solve_montred_preconditions.
    prove_correctness' ltac:(fun _ => idtac) use_curve_good.
    { cbv [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by bound is_bounded_by_bool value_range upper lower].
      rewrite Bool.andb_true_iff, !Z.leb_le. lia. }
    { cbv [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by bound is_bounded_by_bool value_range upper lower].
      rewrite Bool.andb_true_iff, !Z.leb_le. lia. }
  Qed.

  Lemma Wf_montred res (Hres : montred = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). apply fancy_args_good. Qed.
End rmontred.

Module Export Hints.
  Hint Opaque
       montred
  : wf_op_cache.
  Hint Immediate
       Wf_montred
  : wf_op_cache.
End Hints.
