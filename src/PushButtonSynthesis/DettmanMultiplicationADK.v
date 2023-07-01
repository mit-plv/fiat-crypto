(** * Push-Button Synthesis of Dettman Multiplication *)
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
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.DettmanMultiplicationADKReificationCache.
Require Import Crypto.Arithmetic.DettmanMultiplication.

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
Import COperationSpecifications.DettmanMultiplication.

Import Associational Positional.

Import dettman_multiplication_with_adk_mod_ops.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)
(* needed for making [autorewrite] not take a very long time *)
Local Opaque reified_mul_gen.
(* needed for making [autorewrite] with [Set Keyed Unification] fast *)
Local Opaque expr.Interp.

Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {pipeline_opts : PipelineOptions}
          {pipeline_to_string_opts : PipelineToStringOptions}
          {synthesis_opts : SynthesisOptions}
          (machine_wordsize : machine_wordsize_opt)
          (s : Z)
          (c_ : list (Z*Z))
          (n : nat) (* number of limbs *)
          (limbwidth : nat)
          (last_reduction : nat)
          (inbounds_multiplier : option Q).

  Local Instance override_pipeline_opts : PipelineOptions
    := {| widen_bytes := true (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)
       |}.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize; 2 * machine_wordsize].
  
  Local Notation c := (Associational.eval c_).
  Definition m := s - c.

  Local Notation possible_values := possible_values_of_machine_wordsize.
  Definition last_limb_width : nat := (Z.to_nat (Z.log2 s)) - (n - 1) * limbwidth.

  Definition input_magnitude := Option.value inbounds_multiplier 1.
  Definition output_magnitude_first_limbs : Q := input_magnitude / 2 + 1 / 2.
  Definition output_magnitude_last_limb : Q := input_magnitude / 2 + 1 / 4.
  (* Where these bounds came from:
     https://github.com/bitcoin-core/secp256k1/blob/0eb3000417fcf996e3805d0eb00f0f32b8849315/src/field_5x52_impl.h#L545
     These bounds are correct, and reasonably tight, for the following parameters:
           s = 2^256
           c = 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
           n = 5
           last_limb_width = 48
           last_reduction = 2.

           s = 2^256
           c = 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
           n = 10
           last_limb_width = 22
           last_reduction = 6.
     Given parameters dissimilar to those above, these bounds are no better than a guess.
     I suppose they provide a reasonable default, though. *)

  Definition weightf := weight limbwidth.
  Definition input_bounds : list (ZRange.type.option.interp base.type.Z)
    := fold_left (fun l i => Some r[0 ~> Qceiling (2 * input_magnitude * ((weightf (i + 1) / weightf i) - 1))]%zrange :: l) (seq 0 (n - 1)) [] ++
                 [Some r[0 ~> Qceiling (2 * input_magnitude * (2^last_limb_width - 1))]%zrange].
  Definition output_bounds : list (ZRange.type.option.interp base.type.Z)
    := fold_left (fun l i => Some r[0 ~> Qceiling (2 * output_magnitude_first_limbs * ((weightf (i + 1) / weightf i) - 1))]%zrange :: l) (seq 0 (n - 1)) [] ++
         [Some r[0 ~> Qceiling (2 * output_magnitude_last_limb * (2^last_limb_width - 1))]%zrange].
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
            [(negb (s - c =? 0), Pipeline.Values_not_provably_distinctZ "s - c <> 0" (s - c) 0)
             ; (4 <=? n, Pipeline.Value_not_leZ "4 <= n" 4 n)
             ; (negb (0 =? limbwidth), Pipeline.Values_not_provably_distinctZ "0 <> limbwidth" 0 limbwidth)
             ; (2 ^ (Z.log2 s) =? s, Pipeline.Values_not_provably_equalZ "2 ^ (Z.log2 s) = s" (2 ^ Z.log2 s) s)
             ; ((n - 1) * limbwidth <=? Z.log2 s, Pipeline.Value_not_leZ "(n - 1) * limbwidth <= Z.log2 s" ((n - 1) * limbwidth) (Z.log2 s))
             ; (Z.log2 s <=? n * limbwidth, Pipeline.Value_not_leZ "Z.log2 s <= n * limbwidth" (Z.log2 s) (n * limbwidth))
             ; (limbwidth <=? machine_wordsize, Pipeline.Value_not_leZ "limbwidth <= machine_word_size" limbwidth machine_wordsize)
            ])
            res.

  Context (requests : list string)
    (curve_good : check_args requests (Success tt) = Success tt).

  Lemma use_curve_good
    : s - c <> 0
      /\ (4 <= n)
      /\ 0 <> limbwidth
      /\ 2 ^ (Z.log2 s) = s
      /\ (n - 1) * limbwidth <= Z.log2 s
      /\ Z.log2 s <= n * limbwidth
      /\ limbwidth <= machine_wordsize.
  Proof using curve_good. prepare_use_curve_good (). Qed.

  Local Notation evalf := (eval weightf n).
  Local Notation notations_for_docstring
    := (CorrectnessStringification.dyn_context.cons
          weightf "weight"
          (CorrectnessStringification.dyn_context.cons
             evalf "eval"
             CorrectnessStringification.dyn_context.nil))%string.
  Local Notation "'docstring_with_summary_from_lemma!' summary correctness"
    := (docstring_with_summary_from_lemma_with_ctx!
          notations_for_docstring
          summary
          correctness)
         (only parsing, at level 10, summary at next level, correctness at next level).

  Check reified_mul_gen. Print adk_mulmod.

  Definition mul
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         possible_values
         (reified_mul_gen
            @ GallinaReify.Reify s @ GallinaReify.Reify c
            @ GallinaReify.Reify (Z.to_nat machine_wordsize) @ GallinaReify.Reify n
            @ GallinaReify.Reify limbwidth @ GallinaReify.Reify last_reduction)
         (Some input_bounds, (Some input_bounds, tt))
         (Some output_bounds).


  Definition smul (prefix : string)
    : string * (Pipeline.M (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "mul" mul
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " multiplies two field elements."]%string)
             (mul_correct weightf n m input_bounds output_bounds)).

  (** Work around COQBUG(https://github.com/coq/coq/issues/9286) *)
  Local Opaque DettmanMultiplication.adk_mulmod.

  Local Ltac prove_correctness _ := Primitives.prove_correctness use_curve_good.

  Lemma mul_correct res
        (Hres : mul = Success res)
    : mul_correct (weightf) n m input_bounds output_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

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
                     ""; ""]%string)))
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
