(** * Push-Button Synthesis of Unsaturated Solinas *)
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
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
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
Require Import Crypto.Arithmetic.BaseConversion.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.BaseConversionReificationCache.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Wf.Compilers
  Language.Compilers
  AbstractInterpretation.Compilers
  Stringification.Language.Compilers.
Import Compilers.API.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.BaseConversion.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

(* needed for making [autorewrite] not take a very long time *)
Local Opaque
      reified_convert_bases_gen
      expr.Interp.

Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {static : static_opt}
          {use_mul_for_cmovznz : use_mul_for_cmovznz_opt}
          {emit_primitives : emit_primitives_opt}
          {should_split_mul : should_split_mul_opt}
          {widen_carry : widen_carry_opt}
          {widen_bytes : widen_bytes_opt}
          (src_n : nat)
          (src_limbwidth : Q)
          (dst_limbwidth : Q)
          (machine_wordsize : Z)
          (max_opt : option Z)
          (inbounds_multiplier : option Q).

  Local Notation src_weight := (weight (Qnum src_limbwidth) (Qden src_limbwidth)).
  Local Notation dst_weight := (weight (Qnum dst_limbwidth) (Qden dst_limbwidth)).

  Local Notation force_power_of_two v
    := (2^Z.log2_up v) (only parsing).

  Let max : Z
    := force_power_of_two
         (Option.value
            max_opt
            (src_weight src_n)).

  Let dst_n : nat
    := Z.to_nat (Qceiling (Z.log2_up max / dst_limbwidth)).

  Let in_upperbounds : list Z
    := List.map
         (fun v : Z => Qceiling (Option.value inbounds_multiplier 1 * v))
         (encode_no_reduce src_weight src_n (max - 1)).
  Let out_upperbounds : list Z
    := (encode_no_reduce dst_weight dst_n (max - 1)).

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize_with_bytes
    := prefix_with_carry_bytes [machine_wordsize; 2 * machine_wordsize]%Z.

  Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.
  Definition in_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun u => Some r[0~>u]%zrange) in_upperbounds.
  Definition out_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun u => Some r[0~>u]%zrange) out_upperbounds.

  Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values_of_machine_wordsize_with_bytes.

  Lemma length_in_upperbounds : List.length in_upperbounds = src_n.
  Proof using Type. cbv [in_upperbounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_in_upperbounds : distr_length.
  Lemma length_out_upperbounds : List.length out_upperbounds = dst_n.
  Proof using Type. cbv [out_upperbounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_out_upperbounds : distr_length.
  Lemma length_in_bounds : List.length in_bounds = src_n.
  Proof using Type. cbv [in_bounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_in_bounds : distr_length.
  Lemma length_out_bounds : List.length out_bounds = dst_n.
  Proof using Type. cbv [out_bounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_out_bounds : distr_length.

  Lemma max_None_le_weight : (1 <= src_limbwidth)%Q -> src_n <> 0%nat -> max_opt = None -> 1 < max <= src_weight src_n.
  Proof using Type.
    clear.
    cbv [max Option.value weight Qle]; cbn [Qnum Qden]; autorewrite with zsimplify_const;
      intros; subst.
    rewrite !Z.log2_up_pow2 by (Z.div_mod_to_quot_rem; nia).
    rewrite <- Z.pow_gt_1 by lia.
    split; [ | lia ]; Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma max_Some_le_weight (v := Option.value max_opt 0) : max_opt = Some v -> (1 <= src_limbwidth)%Q -> 1 < v <= src_weight src_n -> 1 < max <= src_weight src_n.
  Proof using Type.
    clear.
    clearbody v.
    intro; cbv [max Option.value weight Qle]; cbn [Qnum Qden]; subst max_opt.
    intros; rewrite <- Z.pow_gt_1 by lia; destruct_head'_and.
    split; auto using Z.log2_up_pos with lia; [].
    Z.peel_le.
    etransitivity; [ apply Z.log2_up_le_mono; eassumption | ].
    rewrite Z.log2_up_pow2; [ reflexivity | ].
    Z.div_mod_to_quot_rem;
      repeat match goal with
             | [ H : context[- ?v] |- _ ]
               => is_var v; assert (v <= 0) by nia; Z.replace_with_neg v
             | [ |- context[- ?v] ]
               => is_var v; assert (v <= 0) by nia; Z.replace_with_neg v
             end;
      nia.
  Qed.

  Lemma dst_weight_n_ge_max : (1 <= dst_limbwidth)%Q -> max <= dst_weight dst_n.
  Proof using Type.
    clear.
    assert (0 <= Z.log2_up max) by auto with zarith.
    cbv [dst_n weight].
    cbv [inject_Z Qceiling Qfloor Qdiv Qmult Qopp Qinv Qle Pos.mul Qnum Qden];
      break_innermost_match; autorewrite with zsimplify_const;
        try lia.
    intros; eapply Z.le_trans; [ apply Z.log2_up_le_full | Z.peel_le ].
    rewrite !Z2Nat.id;
      Z.div_mod_to_quot_rem;
      repeat match goal with
             | [ H : context[- ?v] |- _ ]
               => is_var v; assert (v <= 0) by nia; Z.replace_with_neg v
             | [ |- context[- ?v] ]
               => is_var v; assert (v <= 0) by nia; Z.replace_with_neg v
             end;
      nia.
  Qed.

  Lemma dst_n_nz : 1 < max -> (1 <= dst_limbwidth)%Q -> dst_n <> 0%nat.
  Proof using Type.
    clear.
    intro; assert (0 < Z.log2_up max) by auto using Z.log2_up_pos.
    subst dst_n.
    cbv [inject_Z Qceiling Qfloor Qdiv Qmult Qopp Qinv Qle Pos.mul Qnum Qden];
      break_innermost_match; autorewrite with zsimplify_const;
        try lia.
    rewrite <- Z2Nat.inj_0.
    intros; Z.div_mod_to_quot_rem.
    repeat match goal with
           | [ H : context[- ?v] |- _ ]
             => is_var v; assert (v < 0) by nia; Z.replace_with_neg v
           | [ |- context[- ?v] ]
             => is_var v; assert (v < 0) by nia; Z.replace_with_neg v
           end.
    rewrite Z2Nat.inj_iff by nia; nia.
  Qed.

  Local Notation dummy_not_zero_nat := (1%nat) (only parsing).
  Local Notation dummy_gt_1_Z := (2%Z) (only parsing).
  Local Notation dummy_le_weight_Z := (-1%Z) (only parsing).

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := fold_right
         (fun '(b, e) k => if b:bool then Error e else k)
         res
         [(negb (Qle_bool 1 src_limbwidth)%Q, Pipeline.Value_not_leQ "src_limbwidth < 1" 1%Q src_limbwidth);
            (negb (Qle_bool 1 dst_limbwidth)%Q, Pipeline.Value_not_leQ "dst_limbwidth < 1" 1%Q dst_limbwidth);
            ((src_n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "src_n = 0" src_n 0%nat);
            (let max := Option.value max_opt dummy_gt_1_Z in
             (negb (1 <? max)%Z,
              Pipeline.Value_not_ltZ "max ≤ 1" 1 max));
            (let max := Option.value max_opt dummy_le_weight_Z in
             (negb (max <=? src_weight src_n)%Z,
              Pipeline.Value_not_leZ "src_weight src_n < max" max (src_weight src_n)));
            (let eval_in_upperbounds := eval src_weight src_n in_upperbounds in
             let dst_weight_n := dst_weight dst_n in
             (negb (eval_in_upperbounds <? dst_weight_n)%Z,
              Pipeline.Value_not_ltZ "dst_weight dst_n ≤ src_eval in_upperbounds" eval_in_upperbounds dst_weight_n));
            ((negb (0 <? machine_wordsize)), Pipeline.Value_not_ltZ "machine_wordsize ≤ 0" 0 machine_wordsize)].

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
                 | progress break_innermost_match
                 | progress specialize_by_assumption
                 | progress specialize_by (exact eq_refl)
                 | solve [ auto ]
                 | progress break_innermost_match_hyps ].

  Context (curve_good : check_args (Success tt) = Success tt).

  Lemma use_curve_good
    : 0 < machine_wordsize
      /\ src_n <> 0%nat
      /\ dst_n <> 0%nat
      /\ List.length in_bounds = src_n
      /\ List.length out_bounds = dst_n
      /\ List.length in_upperbounds = src_n
      /\ List.length out_upperbounds = dst_n
      /\ 0 < Qden src_limbwidth <= Qnum src_limbwidth
      /\ 0 < Qden dst_limbwidth <= Qnum dst_limbwidth
      /\ 1 < max <= src_weight src_n
      /\ 1 < max <= dst_weight dst_n
      /\ eval src_weight src_n in_upperbounds < dst_weight dst_n.
  Proof using curve_good.
    clear -curve_good.
    pose proof max_None_le_weight.
    pose proof dst_weight_n_ge_max.
    pose proof dst_n_nz.
    pose proof max_Some_le_weight.
    cbv [check_args fold_right] in curve_good |- *.
    autorewrite with distr_length.
    break_innermost_match_hyps; try discriminate.
    rewrite negb_false_iff in *.
    Z.ltb_to_lt.
    rewrite Qle_bool_iff in *.
    rewrite NPeano.Nat.eqb_neq in *.
    cbv [Option.value] in *.
    cbv [Qnum Qden limbwidth Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *.
    specialize_by_assumption.
    repeat apply conj.
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
  Qed.

  Local Notation src_weightf := (weight (Qnum src_limbwidth) (QDen src_limbwidth)).
  Local Notation src_evalf := (eval src_weightf src_n).
  Local Notation dst_weightf := (weight (Qnum dst_limbwidth) (QDen dst_limbwidth)).
  Local Notation dst_evalf := (eval dst_weightf dst_n).
  Local Notation notations_for_docstring
    := (CorrectnessStringification.dyn_context.cons
          src_weightf "src_weight"
          (CorrectnessStringification.dyn_context.cons
             src_evalf "src_eval"
             (CorrectnessStringification.dyn_context.cons
                dst_weightf "dst_weight"
                (CorrectnessStringification.dyn_context.cons
                   dst_evalf "dst_eval"
                   CorrectnessStringification.dyn_context.nil))))%string.
  Local Notation "'docstring_with_summary_from_lemma!' summary correctness"
    := (docstring_with_summary_from_lemma_with_ctx!
          notations_for_docstring
          summary
          correctness)
         (only parsing, at level 10, summary at next level, correctness at next level).

  Definition convert_bases
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_convert_bases_gen
            @ GallinaReify.Reify (Qnum src_limbwidth) @ GallinaReify.Reify (Z.pos (Qden src_limbwidth))
            @ GallinaReify.Reify (Qnum dst_limbwidth) @ GallinaReify.Reify (Z.pos (Qden dst_limbwidth))
            @ GallinaReify.Reify src_n
            @ GallinaReify.Reify dst_n)
         (Some in_bounds, tt)
         (Some out_bounds).

  Definition sconvert_bases (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "convert_bases" convert_bases
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " converts a field element from base " ++ Decimal.show_Q false src_limbwidth ++ " to base " ++ Decimal.show_Q false dst_limbwidth ++ " in little-endian order."]%string)
             (convert_bases_correct src_weight dst_weight src_n dst_n in_bounds)).

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       eval_convert_basesmod
       using solve [ auto | congruence | solve_extra_bounds_side_conditions ] : push_eval.

  Local Ltac prove_correctness _ :=
    Primitives.prove_correctness use_curve_good;
    try solve [ auto | congruence | solve_extra_bounds_side_conditions ].

  Lemma convert_bases_correct res
        (Hres : convert_bases = Success res)
    : convert_bases_correct src_weight dst_weight src_n dst_n in_bounds (Interp res).
  Proof using curve_good.
    prove_correctness (); [].
    erewrite convert_basesmod_partitions; [ reflexivity | .. ].
    all: repeat apply conj; (congruence || auto).
    all: cbv [in_bounds] in *.
    all: lazymatch goal with
         | [ H1 : list_Z_bounded_by (List.map (fun y => Some (@?f y)) ?b) ?x
             |- context[eval ?wt ?n ?x] ]
           => unshelve epose proof (eval_list_Z_bounded_by wt n (List.map (fun x => Some (f x)) b) (List.map f b) x H1 _ _ (fun A B => Z.lt_le_incl _ _ (weight_positive _ _))); clear H1
         end.
    all: congruence || auto.
    all: repeat first [ reflexivity
                      | apply wprops
                      | progress rewrite ?map_map in *
                      | progress rewrite ?map_id in *
                      | progress cbn [upper lower] in *
                      | lia
                      | match goal with
                        | [ H : context[List.map (fun _ => 0) _] |- _ ] => erewrite <- zeros_ext_map, ?eval_zeros in H by reflexivity
                        end
                      | progress autorewrite with distr_length push_eval in *
                      | destruct_head'_and; eapply Z.le_lt_trans; eassumption ].
  Qed.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("convert_bases", sconvert_bases)].

    Definition valid_names : string
      := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions).

    Definition extra_special_synthesis (function_name_prefix : string) (name : string)
      : list (option (string * Pipeline.ErrorT (list string * ToString.ident_infos)))
      := [].

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (string * Pipeline.ErrorT (list string))
      := Primitives.Synthesize
           machine_wordsize valid_names known_functions (extra_special_synthesis function_name_prefix)
           check_args
           ((ToString.comment_block comment_header)
              ++ [""]
              ++ (ToString.comment_block
                    ["Computed values:";
                       "dst_n = " ++ show false dst_n;
                       "max = " ++ PowersOfTwo.show_Z false max]%string)
              ++ [""])
           function_name_prefix requests.
  End for_stringification.
End __.
