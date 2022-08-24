(** * Push-Button Synthesis of Saturated Reduction *)
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Rewriter.Language.Wf.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.SolinasReduction.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.SaturatedSolinasReificationCache.
Require Import Crypto.PushButtonSynthesis.SolinasReductionReificationCache.
Require Import Crypto.Assembly.Equivalence.
Import ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Wf.Compilers
  Language.Compilers
  AbstractInterpretation.Compilers
  Stringification.Language.Compilers.
Import Compilers.API.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.Solinas.
Import COperationSpecifications.SolinasReduction.

Import Associational Positional.
Import SolinasReduction.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Local Opaque reified_solmul_gen. (* needed for making [autorewrite] not take a very long time *)
(* needed for making [autorewrite] with [Set Keyed Unification] fast *)
Local Opaque expr.Interp.

Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {language_naming_conventions : language_naming_conventions_opt}
          {documentation_options : documentation_options_opt}
          {output_options : output_options_opt}
          {opts : AbstractInterpretation.Options}
          {package_namev : package_name_opt}
          {class_namev : class_name_opt}
          {static : static_opt}
          {internal_static : internal_static_opt}
          {inline : inline_opt}
          {inline_internal : inline_internal_opt}
          {low_level_rewriter_method : low_level_rewriter_method_opt}
          {only_signed : only_signed_opt}
          {no_select : no_select_opt}
          {use_mul_for_cmovznz : use_mul_for_cmovznz_opt}
          {emit_primitives : emit_primitives_opt}
          {should_split_mul : should_split_mul_opt}
          {should_split_multiret : should_split_multiret_opt}
          {unfold_value_barrier : unfold_value_barrier_opt}
          {assembly_hints_lines : assembly_hints_lines_opt}
          {ignore_unique_asm_names : ignore_unique_asm_names_opt}
          {widen_carry : widen_carry_opt}
          (widen_bytes : widen_bytes_opt := true) (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)
          {assembly_conventions : assembly_conventions_opt}
          {error_on_unused_assembly_functions : error_on_unused_assembly_functions_opt}
          (s : Z)
          (c : list (Z * Z)).
  Context (machine_wordsize := 64).

  Local Existing Instance widen_bytes.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize].

  Definition n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Definition m := s - Associational.eval c.
  Definition weight := UniformWeight.uweight machine_wordsize.
  Definition up_bound := 2 ^ (machine_wordsize / 4).
  Definition base : Z := 2 ^ machine_wordsize.
  
  Let possible_values := possible_values_of_machine_wordsize.
  Definition bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
  Definition boundsn : list (ZRange.type.option.interp base.type.Z)
    := repeat bound n.

  Local Instance no_select_size : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
  Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Local Instance split_multiret_to : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (requests : list string) (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := check_args_of_list
         (List.map
            (fun v => (true, v))
            [((0 <? s)%Z, Pipeline.Value_not_ltZ "0 < s" 0 s)
             ; ((0 <? Associational.eval c)%Z, Pipeline.Value_not_ltZ "0 < Associational.eval c" 0 (Associational.eval c))
             ; ((0 <? s - Associational.eval c)%Z, Pipeline.Value_not_ltZ "s - Associational.eval c ≤ 0" 0 (s - Associational.eval c))
             ; (negb (s =? 0)%Z, Pipeline.Values_not_provably_distinctZ "s ≠ 0" s 0)
             ; (negb (n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n ≠ 0" n 0)
             ; (0 <? machine_wordsize, Pipeline.Value_not_ltZ "0 < machine_wordsize" 0 machine_wordsize)
             ; ((1 <? n)%nat, Pipeline.Value_not_ltZ "1 < n" 1 n)
             ; (fst (Rows.adjust_s weight (S (S n)) s) =? weight n, Pipeline.Values_not_provably_equalZ "fst (Rows.adjust_s weight (S (S n)) s) = weight n" (fst (Rows.adjust_s weight (S (S n)) s)) (weight n))
             ; (snd (Rows.adjust_s weight (S (S n)) s), Pipeline.Invalid_argument "tmp")
             ; (weight n / s * Associational.eval c <? up_bound, Pipeline.Value_not_ltZ "weight n / s * Associational.eval c < up_bound" (weight n / s * Associational.eval c) up_bound)
         ])
         res.

  Local Ltac use_curve_good_t :=
    repeat first [ use_requests_to_prove_curve_good_t_step
                 | assumption
                 | lia
                 | progress autorewrite with distr_length
                 | progress distr_length ].

  Context (requests : list string)
          (curve_good : check_args requests (Success tt) = Success tt).
  
  Lemma use_curve_good
    : (n > 1)%nat /\
        s > 0 /\
        Associational.eval c > 0 /\
        s - Associational.eval c <> 0 /\
        base <> 0 /\
        Rows.adjust_s weight (S (S n)) s = (weight n, true) /\
        weight n / s * Associational.eval c < up_bound.
  Proof using curve_good.
    prepare_use_curve_good ().
    { use_curve_good_t. }
    { use_curve_good_t. }
    { unfold base.
      use_curve_good_t. }
    { lazymatch goal with
      | |- ?x = _ => rewrite surjective_pairing with (p:=x)
      end.
      repeat match goal with
             | H : ?x = _ |- (?x, _) = _ => rewrite H
             | H : ?x = _ |- (_, ?x) = _ => rewrite H
             end.
      auto. }
  Qed.

  Local Notation evalf := (eval weight n).
  Local Notation notations_for_docstring
    := (CorrectnessStringification.dyn_context.cons
          evalf "evalf"
          (CorrectnessStringification.dyn_context.cons
             weight "weight"
             CorrectnessStringification.dyn_context.nil))%string.
  Local Notation "'docstring_with_summary_from_lemma!' summary correctness"
    := (docstring_with_summary_from_lemma_with_ctx!
          notations_for_docstring
          summary
          correctness)
         (only parsing, at level 10, summary at next level, correctness at next level).

  Definition mulmod
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_solmul_gen
            @ GallinaReify.Reify base
            @ GallinaReify.Reify s
            @ GallinaReify.Reify c
            @ GallinaReify.Reify n )
         (Some boundsn, (Some boundsn, tt))
         (Some boundsn).

  Definition smulmod (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "mulmod" mulmod
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " multiplies two field elements."]%string)
             (mulmod_correct weight n m boundsn)).

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       (fun pf => @SolinasReduction.SolinasReduction.mulmod_correct (@wprops _ _ pf)) using solve [ auto with zarith | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  Hint Unfold mulmod : push_eval.

  Local Ltac prove_correctness _ := Primitives.prove_correctness use_curve_good.

  Lemma mulmod_correct res
        (Hres : mulmod = Success res)
    : mulmod_correct weight n m boundsn (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_mulmod res (Hres : mulmod = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("mulmod", wrap_s smulmod)].

    Definition valid_names : string := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions).

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (synthesis_output_kind * string * Pipeline.ErrorT (list string))
      := Primitives.Synthesize
           machine_wordsize valid_names known_functions (fun _ => nil) all_typedefs!
           check_args
           ((ToString.comment_file_header_block
               (comment_header
                  ++ ["";
                     "Computed values:";
                     ""]%string)))
           function_name_prefix requests.
  End for_stringification.
End __.

Module Export Hints.
#[global]
  Hint Opaque
       mulmod
  : wf_op_cache.
#[global]
  Hint Immediate
       Wf_mulmod
  : wf_op_cache.
End Hints.
