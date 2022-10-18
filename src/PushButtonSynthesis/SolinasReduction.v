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

Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)
(* needed for making [autorewrite] with [Set Keyed Unification] fast *)
Local Opaque expr.Interp.

Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {pipeline_opts : PipelineOptions}
          {pipeline_to_string_opts : PipelineToStringOptions}
          {synthesis_opts : SynthesisOptions}
          (s : Z)
          (c : list (Z * Z)).
  Context (machine_wordsize : machine_wordsize_opt).

  Local Instance override_pipeline_opts : PipelineOptions
    := {| widen_bytes := true (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)
       |}.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize].

  Definition n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Definition m := s - Associational.eval c.
  Definition weight := UniformWeight.uweight machine_wordsize.
  Definition up_bound := 2 ^ (machine_wordsize / 4).
  Definition base : Z := 2 ^ machine_wordsize.

  Local Notation possible_values := possible_values_of_machine_wordsize.
  Local Notation boundsn := (saturated_bounds n machine_wordsize).

  Local Existing Instance default_translate_to_fancy.
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
             ; ((0 <? s - Associational.eval c)%Z, Pipeline.Value_not_ltZ "0 < s - Associational.eval c" 0 (s - Associational.eval c))
             ; (negb (s =? 0)%Z, Pipeline.Values_not_provably_distinctZ "s ≠ 0" s 0)
             ; (negb (n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n ≠ 0" n 0)
             ; (0 <? machine_wordsize, Pipeline.Value_not_ltZ "0 < machine_wordsize" 0 machine_wordsize)
             ; (machine_wordsize =? 64, Pipeline.Values_not_provably_equalZ "machine_wordsize = 64" machine_wordsize 64)
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
        machine_wordsize = 64 /\
        base <> 0 /\
        Rows.adjust_s weight (S (S n)) s = (weight n, true) /\
        weight n / s * Associational.eval c < up_bound.
  Proof using curve_good.
    prepare_use_curve_good ().
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { unfold base.
      apply Z.pow_nonzero; use_curve_good_t. }
    { lazymatch goal with
      | |- ?x = _ => rewrite surjective_pairing with (p:=x)
      end.
      congruence. }
  Qed.

  Local Notation evalf := (eval weight n).
  Local Notation weightf := weight.
  Local Notation notations_for_docstring
    := (CorrectnessStringification.dyn_context.cons
          evalf "evalf"
          (CorrectnessStringification.dyn_context.cons
             weightf "weightf"
             CorrectnessStringification.dyn_context.nil))%string.
  Local Notation "'docstring_with_summary_from_lemma!' summary correctness"
    := (docstring_with_summary_from_lemma_with_ctx!
          notations_for_docstring
          summary
          correctness)
         (only parsing, at level 10, summary at next level, correctness at next level).

  Definition mul
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         possible_values
         (reified_mul_gen
            @ GallinaReify.Reify base
            @ GallinaReify.Reify s
            @ GallinaReify.Reify c
            @ GallinaReify.Reify n)
         (Some boundsn, (Some boundsn, tt))
         (Some boundsn).

  Definition smul (prefix : string)
    : string * (Pipeline.M (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "mul" mul
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " multiplies two field elements."]%string)
             (mul_correct weight n m boundsn)).

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       (fun pf => @SolinasReduction.SolinasReduction.mulmod_correct (@wprops _ _ pf)) using solve [ auto with zarith | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  Hint Unfold mul : push_eval.

  Local Ltac prove_correctness _ := Primitives.prove_correctness use_curve_good.

  Lemma mul_correct res
        (Hres : mul = Success res)
    : mul_correct weight n m boundsn (Interp res).
  Proof using curve_good.
    prove_correctness ().
    cbv [evalf weightf weight up_bound] in *.
    match goal with
    | H : machine_wordsize = _ |- _ => rewrite H in *
    end.
    apply (fun pf => @SolinasReduction.SolinasReduction.mulmod_correct (@wprops _ _ pf)); auto; lia.
  Qed.

  Lemma Wf_mul res (Hres : mul = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("mul", wrap_s smul)].

    Definition valid_names : string := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions).

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (synthesis_output_kind * string * Pipeline.M (list string))
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
       mul
  : wf_op_cache.
#[global]
  Hint Immediate
       Wf_mul
  : wf_op_cache.
End Hints.
