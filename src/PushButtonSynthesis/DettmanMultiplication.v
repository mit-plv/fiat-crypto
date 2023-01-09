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
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.DettmanMultiplicationReificationCache.
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
          (machine_wordsize : machine_wordsize_opt)
          (s_ : Z)
          (c_ : list (Z*Z))
          (n : nat) (* number of limbs *)
          (limbwidth : nat)
          (inbounds_multiplier : option Q).

  Local Instance override_pipeline_opts : PipelineOptions
    := {| widen_bytes := true (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)
       |}.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize; 2 * machine_wordsize].
  Definition e : nat := Z.abs_nat (Z.log2_up s_).
  Local Notation s := (2 ^ e).
  Local Notation c := (Associational.eval c_).
  Definition m := s - c.

  Local Notation possible_values := possible_values_of_machine_wordsize.

  Definition input_magnitude := Option.value inbounds_multiplier 1.
  Definition output_magnitude_first_limbs : Q := input_magnitude / 2 + 1 / 2.
  Definition output_magnitude_last_limb : Q := input_magnitude / 2 + 1 / 4. (* Where these bounds came from: https://github.com/bitcoin-core/secp256k1/blob/0eb3000417fcf996e3805d0eb00f0f32b8849315/src/field_5x52_impl.h#L545 *)
  Definition last_limb_width : nat := Z.to_nat (Qceiling (Z.log2_up s) - ((n - 1) * limbwidth)).
  Definition input_bounds : list (ZRange.type.option.interp base.type.Z)
    := (repeat (Some r[0 ~> Qceiling (2 * input_magnitude * (2^limbwidth - 1))]%zrange) (n - 1)) ++ [Some r[0 ~> Qceiling (2 * input_magnitude * (2^last_limb_width - 1))]%zrange].
  Definition output_bounds : list (ZRange.type.option.interp base.type.Z)
    := (repeat (Some r[0 ~> Qceiling (2 * output_magnitude_first_limbs * (2^limbwidth - 1))]%zrange) (n - 1)) ++ [Some r[0 ~> Qceiling (2 * output_magnitude_last_limb * (2^last_limb_width - 1))]%zrange].

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
            [(negb (s - c =? 0)%Z, Pipeline.Value_not_ltZ "s - c <> 0" (s - c) 0)
             ; (negb (s =? 0)%Z, Pipeline.Values_not_provably_distinctZ "s ≠ 0" s 0)
             ; ((3 <=? n)%nat, Pipeline.Value_not_leZ "n < 3" 3 n)
             ; ((e <=? limbwidth * n)%nat, Pipeline.Value_not_leZ "e <= limb_size * limbs" e (limbwidth * n))
             ; ((limbwidth * (n - 1) <=? e)%nat, Pipeline.Value_not_leZ "limb_size * (limbs - 1) <= e" (limbwidth * (n - 1)) e)
             ; ((s_ =? s)%Z, Pipeline.Values_not_provably_equalZ "s not a power of 2" s_ s)
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
    : 2 ^ e - c <> 0
      /\ 3 <= n
      /\ e <= limbwidth * n
      /\ limbwidth * (n - 1) <= e
      /\ 2 ^ e = s.
  Proof using curve_good.
    prepare_use_curve_good ().
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
  Qed.

  Local Notation weightf := (fun n : nat => (2 ^ limbwidth) ^ n).
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

  Definition mul
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         possible_values
         (reified_mul_gen
            @ GallinaReify.Reify e @ GallinaReify.Reify c_ @ GallinaReify.Reify (n: nat) @ GallinaReify.Reify (limbwidth : nat))
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

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       DettmanMultiplication.eval_mulmod
       using solve [ auto with zarith | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  Hint Unfold DettmanMultiplication.mulmod : push_eval.

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
