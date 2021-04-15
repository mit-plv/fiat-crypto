(** * Push-Button Synthesis of Saturated Solinas *)
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
Require Import Crypto.PushButtonSynthesis.SaturatedSolinasReificationCache.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Wf.Compilers
  Language.Compilers
  AbstractInterpretation.Compilers
  Stringification.Language.Compilers.
Import Compilers.API.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.Solinas.
Import COperationSpecifications.SaturatedSolinas.

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
          {language_naming_conventions : language_naming_conventions_opt}
          {package_namev : package_name_opt}
          {class_namev : class_name_opt}
          {static : static_opt}
          {internal_static : internal_static_opt}
          {low_level_rewriter_method : low_level_rewriter_method_opt}
          {only_signed : only_signed_opt}
          {no_select : no_select_opt}
          {use_mul_for_cmovznz : use_mul_for_cmovznz_opt}
          {emit_primitives : emit_primitives_opt}
          {should_split_mul : should_split_mul_opt}
          {should_split_multiret : should_split_multiret_opt}
          {unfold_value_barrier : unfold_value_barrier_opt}
          {assembly_hints_lines : assembly_hints_lines_opt}
          {widen_carry : widen_carry_opt}
          (widen_bytes : widen_bytes_opt := true) (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : Z).

  Local Existing Instance widen_bytes.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize].

  Definition n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Definition m := s - Associational.eval c.
  (* Number of reductions is calculated as follows :
         Let i be the highest limb index of c. Then, each reduction
         decreases the number of extra limbs by (n-i-1). (The -1 comes
         from possibly having an extra high partial product at the end
         of a reduction.) So, to go from the n extra limbs we have
         post-multiplication down to 0, we need ceil (n / (n - i - 1))
         reductions.  In some cases. however, [n - i <= 1], and in
         this case, we do [n] reductions (is this enough?). *)
  Definition nreductions : nat :=
    let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
    if Z.of_nat n - i <=? 1
    then n
    else Z.to_nat (Qceiling (Z.of_nat n / (Z.of_nat n - i - 1))).
  Let possible_values := possible_values_of_machine_wordsize.
  Definition bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
  Definition boundsn : list (ZRange.type.option.interp base.type.Z)
    := repeat bound n.

  Local Instance no_select_size : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
  Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Local Instance split_multiret_to : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := fold_right
         (fun '(b, e) k => if b:bool then Error e else k)
         res
         [((negb (0 <? s - Associational.eval c))%Z, Pipeline.Value_not_ltZ "s - Associational.eval c ≤ 0" 0 (s - Associational.eval c));
            ((s =? 0)%Z, Pipeline.Values_not_provably_distinctZ "s ≠ 0" s 0);
            ((n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n ≠ 0" n 0);
            ((negb (0 <? machine_wordsize)), Pipeline.Value_not_ltZ "0 < machine_wordsize" 0 machine_wordsize)].

  Local Ltac prepare_use_curve_good _ :=
    let curve_good := lazymatch goal with | curve_good : check_args _ = Success _ |- _ => curve_good end in
    clear -curve_good;
    cbv [check_args] in curve_good |- *;
    cbn [fold_right] in curve_good |- *;
    repeat first [ match goal with
                   | [ H : context[match ?b with true => _ | false => _ end ] |- _ ] => destruct b eqn:?
                   end
                 | discriminate
                 | progress Reflect.reflect_hyps
                 | assumption
                 | apply conj
                 | progress destruct_head'_and ].

  Local Ltac use_curve_good_t :=
    repeat first [ assumption
                 | progress rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *
                 | reflexivity
                 | lia
                 | rewrite expr.interp_reify_list, ?map_map
                 | rewrite map_ext with (g:=id), map_id
                 | progress distr_length
                 | progress cbv [Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *
                 | progress cbv [Qle] in *
                 | progress cbn -[reify_list] in *
                 | progress intros
                 | solve [ auto ] ].

  Context (curve_good : check_args (Success tt) = Success tt).

  Lemma use_curve_good
    : 0 < s - Associational.eval c
      /\ s - Associational.eval c <> 0
      /\ s <> 0
      /\ 0 < machine_wordsize
      /\ n <> 0%nat.
  Proof using curve_good.
    prepare_use_curve_good ().
    { use_curve_good_t. }
  Qed.

  Local Notation weightf := (weight machine_wordsize 1).
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
         None (* fancy *)
         possible_values
         (reified_mul_gen
            @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify nreductions)
         (Some boundsn, (Some boundsn, tt))
         (Some boundsn, None (* Should be: Some r[0~>0]%zrange, but bounds analysis is not good enough *) ).

  Definition smul (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          machine_wordsize prefix "mul" mul
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " multiplies two field elements."]%string)
             (mul_correct weightf n m boundsn)).

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       (fun pf => @Rows.eval_mulmod (weight machine_wordsize 1) (@wprops _ _ pf))
       using solve [ auto with zarith | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  Hint Unfold mulmod : push_eval.

  Local Ltac prove_correctness _ := Primitives.prove_correctness use_curve_good.

  Lemma mul_correct res
        (Hres : mul = Success res)
    : mul_correct (weight machine_wordsize 1) n m boundsn (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("mul", smul)].

    Definition valid_names : string := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions).

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (synthesis_output_kind * string * Pipeline.ErrorT (list string))
      := Primitives.Synthesize
           machine_wordsize valid_names known_functions (fun _ => nil)
           check_args
           ((ToString.comment_file_header_block
               (comment_header
                  ++ ["";
                     "Computed values:";
                     "# reductions = " ++ show false nreductions]%string)))
           function_name_prefix requests.
  End for_stringification.
End __.