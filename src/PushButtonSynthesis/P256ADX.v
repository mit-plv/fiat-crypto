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
Require Import Crypto.Arithmetic.WeightStream.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.P256ADXReificationCache.
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

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Local Opaque reified_p256_mul. (* needed for making [autorewrite] not take a very long time *)
Local Opaque reified_p256_sqr. (* needed for making [autorewrite] not take a very long time *)
(* needed for making [autorewrite] with [Set Keyed Unification] fast *)
Local Opaque expr.Interp.

Section __.
  Import P256ADX.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {pipeline_opts : PipelineOptions}
          {pipeline_to_string_opts : PipelineToStringOptions}
          {synthesis_opts : SynthesisOptions}
          (machine_wordsize : machine_wordsize_opt).

  Local Instance override_pipeline_opts : PipelineOptions
    := {| widen_bytes := true (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)
       |}.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize].

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
            [
               (machine_wordsize =? 64, Pipeline.Values_not_provably_equalZ "machine_wordsize = 64" machine_wordsize 64)
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
    : machine_wordsize = 64.
  Proof using curve_good.
    prepare_use_curve_good ().
  Qed.

  Definition t_p256_mul := (
    type.base (base.type.list (base.type.type_base Compilers.Z)) ->
    type.base (base.type.list (base.type.type_base Compilers.Z)) ->
    type.base (base.type.list (base.type.type_base Compilers.Z))
  )%etype.

  Definition p256_mul (prefix : string)
    : string * (Pipeline.M (Pipeline.ExtendedSynthesisResult t_p256_mul)).
    refine  ("", Pipeline.BoundsPipelineToExtendedResult "" "p256_mul" false false possible_values machine_wordsize reified_p256_mul (fun _ _ => []) (Some boundsn, (Some boundsn, tt)) (Some boundsn) (None,(None,tt)) None).
  Defined.

  Definition t_p256_sqr := (
    type.base (base.type.list (base.type.type_base Compilers.Z)) ->
    type.base (base.type.list (base.type.type_base Compilers.Z))
  )%etype.

  Definition p256_sqr (prefix : string)
    : string * (Pipeline.M (Pipeline.ExtendedSynthesisResult t_p256_sqr)).
    refine  ("", Pipeline.BoundsPipelineToExtendedResult "" "p256_sqr" false false possible_values machine_wordsize reified_p256_sqr (fun _ _ => []) (Some boundsn, tt) (Some boundsn) (None,tt) None).
  Defined.

  Definition known_functions
    := [("p256_mul", wrap_s p256_mul); ("p256_sqr", wrap_s p256_sqr)].

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
End __.
