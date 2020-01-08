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
Require Import Crypto.Util.Strings.Equality.
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
          {static : static_opt}
          {use_mul_for_cmovznz : use_mul_for_cmovznz_opt}
          {emit_primitives : emit_primitives_opt}
          {should_split_mul : should_split_mul_opt}
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

  Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Let m := s - Associational.eval c.
  (* Number of reductions is calculated as follows :
         Let i be the highest limb index of c. Then, each reduction
         decreases the number of extra limbs by (n-i). So, to go from
         the n extra limbs we have post-multiplication down to 0, we
         need ceil (n / (n - i)) reductions. *)
  Let nreductions : nat :=
    let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
    Z.to_nat (Qceiling (Z.of_nat n / (Z.of_nat n - i))).
  Let possible_values := possible_values_of_machine_wordsize.
  Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
  Let boundsn : list (ZRange.type.option.interp base.type.Z)
    := repeat bound n.

  Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.

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
    clear -curve_good.
    cbv [check_args fold_right] in curve_good.
    break_innermost_match_hyps; try discriminate.
    rewrite negb_false_iff in *.
    Z.ltb_to_lt.
    rewrite NPeano.Nat.eqb_neq in *.
    intros.
    rewrite ?map_length, ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *.
    specialize_by lia.
    repeat match goal with H := _ |- _ => subst H end.
    repeat match goal with
           | [ H : list_beq _ _ _ _ = true |- _ ] => apply internal_list_dec_bl in H; [ | intros; Z.ltb_to_lt; omega.. ]
           end.
    repeat apply conj.
    { destruct (s - Associational.eval c) eqn:?; cbn; lia. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
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
          prefix "mul" mul
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
      : list (string * Pipeline.ErrorT (list string))
      := Primitives.Synthesize
           machine_wordsize valid_names known_functions (fun _ => nil)
           check_args
           (ToString.comment_block comment_header ++ [""]) function_name_prefix requests.
  End for_stringification.
End __.
