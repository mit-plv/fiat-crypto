(** * Push-Button Synthesis of Unsaturated Solinas *)
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.derive.Derive.
Require Crypto.TAPSort.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.ZRange.
Require Crypto.Util.Option.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Prod.
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
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinasReificationCache.
Require Import Crypto.Assembly.Equivalence.
Import Option.Notations.
Import ListNotations.
Local Open Scope string_scope. Local Open Scope bool_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Wf.Compilers
  Language.Compilers
  AbstractInterpretation.Compilers
  Stringification.Language.Compilers
  Rewriter.All.Compilers.RewriteRules.
Import Compilers.API.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.Solinas.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

(* needed for making [autorewrite] not take a very long time *)
Local Opaque
      reified_carry_square_gen
      reified_carry_scmul_gen
      reified_carry_gen
      reified_encode_gen
      reified_add_gen
      reified_sub_gen
      reified_opp_gen
      reified_id_gen
      reified_zero_gen
      reified_one_gen
      reified_prime_gen
      reified_eval_gen
      reified_bytes_eval_gen
      reified_to_bytes_gen
      reified_from_bytes_gen
      expr.Interp.

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
          {widen_bytes : widen_bytes_opt}
          {tight_upperbound_fraction : tight_upperbound_fraction_opt}
          {assembly_conventions : assembly_conventions_opt}
          {error_on_unused_assembly_functions : error_on_unused_assembly_functions_opt}
          (n : nat)
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : machine_wordsize_opt).

  Local Notation limbwidth := (limbwidth n s c).
  Definition idxs : list nat := carry_chains n s c.
  Definition n_bytes := bytes_n s.
  Local Notation prime_upperbound_list := (prime_upperbound_list n s c) (only parsing).
  Definition prime_bytes_upperbound_list : list Z
    := Partition.partition (weight 8 1) n_bytes (s-1).
  Local Notation tight_upperbounds := (tight_upperbounds n s c) (only parsing).
  Local Notation loose_upperbounds := (loose_upperbounds n s c) (only parsing).
  Local Notation tight_bounds := (tight_bounds n s c) (only parsing).
  Local Notation loose_bounds := (loose_bounds n s c) (only parsing).
  Global Instance tight_bounds_typedef : typedef (t:=base.type.list base.type.Z) (Some tight_bounds)
    := { name := "tight_field_element"
         ; description name := (text_before_type_name ++ name ++ " is a field element with tight bounds.")%string }.
  Global Instance loose_bounds_typedef : typedef (t:=base.type.list base.type.Z) (Some loose_bounds)
    := { name := "loose_field_element"
         ; description name := (text_before_type_name ++ name ++ " is a field element with loose bounds.")%string }.
  Definition prime_bound : ZRange.type.interp base.type.Z
    := r[0~>(s - Associational.eval c - 1)]%zrange.
  Definition prime_bounds : list (ZRange.type.option.interp (base.type.Z))
    := List.map (fun v => Some r[0 ~> v]%zrange) prime_upperbound_list.
  Definition prime_bytes_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun v => Some r[0 ~> v]%zrange) prime_bytes_upperbound_list.
  Local Notation word_bound := (word_bound machine_wordsize).
  Local Notation saturated_bounds := (saturated_bounds n machine_wordsize).
  Local Notation balance := (balance n s c).

  Definition m : Z := s - Associational.eval c.
  (* m_enc needs to be such that, if x is bounded by tight bounds:

     -2*fw[i] <= x[i] - m_enc[i] <= fw[i]

     ...so as to obey the bounds for the sub-with-borrow in
     freeze. fw[i] here is shorthand for (weight (S i) / weight i). To
     obey the upper bound, we need to redistribute m_enc such that:

     tight_upperbounds[i] - fw[i] <= m_enc[i]

     Additionally, we cannot have the minimum be uniformly 0, or else
     we'll encode 0; if this happens, we bump the highest limb to be
     at least 1 *)
  Definition m_enc_min : list Z :=
    let wt := weight (Qnum limbwidth) (Qden limbwidth) in
    let fw := List.map (fun i => wt (S i) / wt i) (seq 0 n) in
    let m_enc_min := map2 Z.sub tight_upperbounds fw in
    if List.forallb (Z.eqb 0) m_enc_min
    then set_nth (n-1) 1 m_enc_min
    else m_enc_min.

  Definition m_enc : list Z :=
    let M := encode (weight (Qnum limbwidth) (Qden limbwidth)) n s c m in
    distribute_balance n s c m_enc_min M.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

  Definition possible_values_of_machine_wordsize_with_bytes
    := prefix_with_carry_bytes [machine_wordsize; 2 * machine_wordsize]%Z.

  Let possible_values := possible_values_of_machine_wordsize.
  Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.

  Local Instance no_select_size : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
  Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Local Instance split_multiret_to : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

  Lemma length_prime_bytes_upperbound_list : List.length prime_bytes_upperbound_list = n_bytes.
  Proof using Type. cbv [prime_bytes_upperbound_list]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_prime_bytes_upperbound_list : distr_length.
  Lemma length_saturated_bounds : List.length saturated_bounds = n.
  Proof using Type. cbv [saturated_bounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_saturated_bounds : distr_length.
  Lemma length_m_enc : List.length m_enc = n.
  Proof using Type. cbv [m_enc]; repeat distr_length. Qed.
  Hint Rewrite length_m_enc : distr_length.

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (requests : list string) (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := check_args_of_list
         ((List.map
             (fun v => (true, v))
             (* first, all the ones that should always hold *)
             [((Qle_bool 1 limbwidth)%Q, Pipeline.Value_not_leQ "limbwidth < 1" 1%Q limbwidth)
              ; (n <=? Z.log2_up (s - Associational.eval c), Pipeline.Value_not_leZ "Z.log2_up (s - Associational.eval c) < n" n (Z.log2_up (s - Associational.eval c)))
              ; (Associational.eval c <? s, Pipeline.Value_not_ltZ "s ≤ Associational.eval c" (Associational.eval c) s)
              ; (0 <? s, Pipeline.Value_not_ltZ "s ≤ 0" 0 s)
              ; (negb (n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" n 0%nat)
              ; (0 <? machine_wordsize, Pipeline.Value_not_ltZ "machine_wordsize ≤ 0" 0 machine_wordsize)
              ; (let v1 := s - Associational.eval c in
                 let v2 := weight (Qnum limbwidth) (QDen limbwidth) n in
                 (v1 <=? v2, Pipeline.Value_not_leZ "weight n < s - Associational.eval c" v1 v2))

                  (** For bedrock2 *)
              ; (let v1 := List.fold_right Z.max 0 prime_bytes_upperbound_list in
                 let v2 := 2^machine_wordsize-1 in
                 (v1 <=? v2,
                  Pipeline.Value_not_leZ "max(prime_bytes_upperbounds) > 2^machine_wordsize-1" v1 v2))
              ; (let v1 := List.fold_right Z.max 0 tight_upperbounds in
                 let v2 := 2^machine_wordsize-1 in
                 (v1 <=? v2,
                  Pipeline.Value_not_leZ "max(tight_upperbounds) > 2^machine_wordsize-1" v1 v2))
              ; (let v1 := List.fold_right Z.max 0 loose_upperbounds in
                 let v2 := 2^machine_wordsize-1 in
                 (v1 <=? v2,
                  Pipeline.Value_not_leZ "max(loose_upperbounds) > 2^machine_wordsize-1" v1 v2))
          ])
            (* the littany of to_bytes ones *)
            ++ (List.map
                  (fun v => (request_present requests "to_bytes", v))
                  [(0 <? Associational.eval c, Pipeline.Value_not_ltZ "Associational.eval c ≤ 0 (needed for to_bytes)" 0 (Associational.eval c))
                   ; (let v1 := s in
                      let v2 := weight (Qnum limbwidth) (QDen limbwidth) n in
                      (v1 =? v2, Pipeline.Values_not_provably_equalZ "s ≠ weight n (needed for to_bytes)" v1 v2))
                   ; (let v1 := (List.map (Z.land (Z.ones machine_wordsize)) m_enc) in
                      let v2 := m_enc in
                      (list_beq _ Z.eqb v1 v2, Pipeline.Values_not_provably_equal_listZ "map mask m_enc ≠ m_enc (needed for to_bytes)" v1 v2))
                   ; (let v1 := eval (weight (Qnum limbwidth) (QDen limbwidth)) n m_enc in
                      let v2 := s - Associational.eval c in
                      (v1 =? v2, Pipeline.Values_not_provably_equalZ "eval m_enc ≠ s - Associational.eval c (needed for to_bytes)" v1 v2))
                   ; (let v1 := eval (weight (Qnum limbwidth) (QDen limbwidth)) n tight_upperbounds in
                      let v2 := 2 * eval (weight (Qnum limbwidth) (QDen limbwidth)) n m_enc in
                      (v1 <? v2, Pipeline.Value_not_ltZ "2 * eval m_enc ≤ eval tight_upperbounds (needed for to_bytes)" v1 v2))
               ])
            ++ [(request_present requests "from_bytes",
                 (1 <? s, Pipeline.Value_not_ltZ "s ≤ 1 (need for from_bytes)" 1 s))
         ])
         res.

  Local Ltac use_curve_good_t :=
    repeat first [ use_requests_to_prove_curve_good_t_step
                 | assumption
                 | lia
                 | progress autorewrite with distr_length
                 | progress distr_length
                 | progress autorewrite with zsimplify_fast in * ].

  Context (requests : list string)
          (curve_good : check_args requests (Success tt) = Success tt).

  Lemma use_curve_good
    : let eval := eval (weight (Qnum limbwidth) (QDen limbwidth)) n in
      0 < Qden limbwidth <= Qnum limbwidth
      /\ n <= Z.log2_up (s - Associational.eval c)
      /\ 0 < s - Associational.eval c
      /\ 0 < s - Associational.eval c <= weight (Qnum limbwidth) (QDen limbwidth) n
      /\ s - Associational.eval c <> 0
      /\ s <> 0
      /\ 0 < machine_wordsize
      /\ n <> 0%nat
      /\ List.fold_right Z.max 0 prime_bytes_upperbound_list <= 2^machine_wordsize-1
      /\ List.fold_right Z.max 0 tight_upperbounds <= 2^machine_wordsize-1
      /\ List.fold_right Z.max 0 loose_upperbounds <= 2^machine_wordsize-1
      /\ (request_present requests "from_bytes" = true -> 1 < s)
      /\ (request_present requests "to_bytes" = true -> 1 < s)
      /\ (request_present requests "to_bytes" = true -> 0 < Associational.eval c < s)
      /\ (request_present requests "to_bytes" = true -> s = weight (Qnum limbwidth) (QDen limbwidth) n)
      /\ (request_present requests "to_bytes" = true -> List.map (Z.land (Z.ones machine_wordsize)) m_enc = m_enc)
      /\ (request_present requests "to_bytes" = true -> eval m_enc = s - Associational.eval c)
      /\ (request_present requests "to_bytes" = true -> eval tight_upperbounds < 2 * eval m_enc)
      /\ List.length tight_bounds = n
      /\ List.length loose_bounds = n
      /\ List.length prime_bytes_upperbound_list = n_bytes
      /\ List.length saturated_bounds = n
      /\ Datatypes.length m_enc = n.
  Proof using curve_good.
    prepare_use_curve_good ().
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
    { use_curve_good_t. }
    { use_curve_good_t. }
  Qed.

  Local Notation weightf := (weight (Qnum limbwidth) (QDen limbwidth)).
  Local Notation evalf := (eval weightf n).
  Local Notation notations_for_docstring
    := (CorrectnessStringification.dyn_context.cons
          m "m"
          (CorrectnessStringification.dyn_context.cons
             weightf "weight"
             (CorrectnessStringification.dyn_context.cons
                evalf "eval"
                CorrectnessStringification.dyn_context.nil)))%string.
  Local Notation "'docstring_with_summary_from_lemma!' summary correctness"
    := (docstring_with_summary_from_lemma_with_ctx!
          notations_for_docstring
          summary
          correctness)
         (only parsing, at level 10, summary at next level, correctness at next level).

  Definition carry_mul
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_carry_mul_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)
         (Some loose_bounds, (Some loose_bounds, tt))
         (Some tight_bounds).

  Definition scarry_mul (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "carry_mul" carry_mul
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " multiplies two field elements and reduces the result."]%string)
             (carry_mul_correct weightf n m tight_bounds loose_bounds)).

  Definition carry_square
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_carry_square_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)
         (Some loose_bounds, tt)
         (Some tight_bounds).

  Definition scarry_square (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "carry_square" carry_square
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " squares a field element and reduces the result."]%string)
             (carry_square_correct weightf n m tight_bounds loose_bounds)).

  Definition carry_scmul_const (x : Z)
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_carry_scmul_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs @ GallinaReify.Reify x)
         (Some loose_bounds, tt)
         (Some tight_bounds).

  Definition scarry_scmul_const (prefix : string) (x : Z)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix ("carry_scmul_" ++ Decimal.Z.to_string x)%string (carry_scmul_const x)
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " multiplies a field element by " ++ Decimal.Z.to_string x ++ " and reduces the result."]%string)
             (carry_scmul_const_correct weightf n m tight_bounds loose_bounds x)).

  Definition carry
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_carry_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)
         (Some loose_bounds, tt)
         (Some tight_bounds).

  Definition scarry (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "carry" carry
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " reduces a field element."]%string)
             (carry_correct weightf n m tight_bounds loose_bounds)).

  Definition add
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_add_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n)
         (Some tight_bounds, (Some tight_bounds, tt))
         (Some loose_bounds).

  Definition sadd (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "add" add
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " adds two field elements."]%string)
             (add_correct weightf n m tight_bounds loose_bounds)).

  Definition sub
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_sub_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n @ GallinaReify.Reify balance)
         (Some tight_bounds, (Some tight_bounds, tt))
         (Some loose_bounds).

  Definition ssub (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "sub" sub
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " subtracts two field elements."]%string)
             (sub_correct weightf n m tight_bounds loose_bounds)).

  Definition opp
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_opp_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n @ GallinaReify.Reify balance)
         (Some tight_bounds, tt)
         (Some loose_bounds).

  Definition sopp (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "opp" opp
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " negates a field element."]%string)
             (opp_correct weightf n m tight_bounds loose_bounds)).

  Definition carry_add
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_carry_add_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs)
         (Some tight_bounds, (Some tight_bounds, tt))
         (Some tight_bounds).

  Definition scarry_add (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "carry_add" carry_add
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " adds two field elements."]%string)
             (carry_add_correct weightf n m tight_bounds)).

  Definition carry_sub
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_carry_sub_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs @ GallinaReify.Reify balance)
         (Some tight_bounds, (Some tight_bounds, tt))
         (Some tight_bounds).

  Definition scarry_sub (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "carry_sub" carry_sub
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " subtracts two field elements."]%string)
             (carry_sub_correct weightf n m tight_bounds)).

  Definition carry_opp
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_carry_opp_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify idxs @ GallinaReify.Reify balance)
         (Some tight_bounds, tt)
         (Some tight_bounds).

  Definition scarry_opp (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "carry_opp" carry_opp
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " negates a field element."]%string)
             (carry_opp_correct weightf n m tight_bounds)).

  Definition relax
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         reified_id_gen
         (Some tight_bounds, tt)
         (Some loose_bounds).

  Definition srelax (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "relax" relax
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is the identity function converting from tight field elements to loose field elements."]%string)
             (relax_correct tight_bounds loose_bounds)).

  Definition to_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_to_bytes_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify n @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify m_enc)
         (Some tight_bounds, tt)
         (Some prime_bytes_bounds).

  Definition sto_bytes (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "to_bytes" to_bytes
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " serializes a field element to bytes in little-endian order."]%string)
             (to_bytes_correct weightf n n_bytes m tight_bounds)).

  Definition from_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_from_bytes_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify n)
         (Some prime_bytes_bounds, tt)
         (Some tight_bounds).

  Definition sfrom_bytes (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "from_bytes" from_bytes
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " deserializes a field element from bytes in little-endian order."]%string)
             (from_bytes_correct weightf n n_bytes m s tight_bounds)).

  Definition encode
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_encode_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n)
         (Some prime_bound, tt)
         (Some tight_bounds).

  Definition sencode (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "encode" encode
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " encodes an integer as a field element."]%string)
             (encode_correct weightf n m tight_bounds)).

  Definition encode_word
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_encode_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n)
         (Some word_bound, tt)
         (Some tight_bounds).

  Definition sencode_word (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "encode_word" encode_word
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " encodes an integer as a field element."]%string)
             (encode_word_correct machine_wordsize weightf n m tight_bounds)).

  Definition zero
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_zero_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n)
         tt
         (Some tight_bounds).

  Definition szero (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "zero" zero
          (docstring_with_summary_from_lemma!
             (fun fname => [text_before_function_name ++ fname ++ " returns the field element zero."]%string)
             (zero_correct weightf n m tight_bounds)).

  Definition one
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_one_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n)
         tt
         (Some tight_bounds).

  Definition sone (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "one" one
          (docstring_with_summary_from_lemma!
             (fun fname => [text_before_function_name ++ fname ++ " returns the field element one."]%string)
             (one_correct weightf n m tight_bounds)).

  Definition reval (* r for reified *)
    := Pipeline.RepeatRewriteAddAssocLeftAndFlattenThunkedRects
         n
         (Pipeline.PreBoundsPipeline
            true (* subst01 *)
            false (* let_bind_return *)
            None (* fancy *)
            (reified_eval_gen
               @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n)
            (Some loose_bounds, tt)).

  Definition seval (arg_name : string) (* s for string *)
    := show (invert_expr.smart_App_curried (reval _) (arg_name, tt)).

  Definition rbytes_eval (* r for reified *)
    := Pipeline.RepeatRewriteAddAssocLeftAndFlattenThunkedRects
         n_bytes
         (Pipeline.PreBoundsPipeline
            true (* subst01 *)
            false (* let_bind_return *)
            None (* fancy *)
            (reified_bytes_eval_gen
               @ GallinaReify.Reify s)
            (Some prime_bytes_bounds, tt)).

  Definition sbytes_eval (arg_name : string) (* s for string *)
    := show (invert_expr.smart_App_curried (rbytes_eval _) (arg_name, tt)).

  Definition selectznz : Pipeline.ErrorT _ := Primitives.selectznz n machine_wordsize.
  Definition sselectznz (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Primitives.sselectznz n machine_wordsize prefix.

  Definition copy : Pipeline.ErrorT _ := Primitives.copy n machine_wordsize.
  Definition scopy (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Primitives.scopy n machine_wordsize prefix.

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       eval_carry_mulmod
       eval_carry_squaremod
       eval_carry_scmulmod
       eval_addmod
       eval_submod
       eval_oppmod
       eval_carry_addmod
       eval_carry_submod
       eval_carry_oppmod
       eval_carrymod
       freeze_to_bytesmod_partitions
       eval_to_bytesmod
       eval_from_bytesmod
       eval_encodemod
       using solve [ auto using eval_balance, length_balance | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  Hint Unfold zeromod onemod : push_eval.

  Local Ltac prove_correctness _ :=
    Primitives.prove_correctness use_curve_good;
    try solve [ auto | congruence | solve_extra_bounds_side_conditions ].

  (** Work around COQBUG(https://github.com/coq/coq/issues/9286) *)
  Local Opaque
        carry_mulmod
        carry_squaremod
        carry_scmulmod
        carrymod
        addmod
        submod
        oppmod
        carry_addmod
        carry_submod
        carry_oppmod
        from_bytesmod
        to_bytesmod
        (* Set Printing Width 100000. Print Rewrite HintDb push_eval. | sed s'/^.*->//g' | grep -o ' eval \(([^)]\+)\|[^ ]*\) \(([^)]\+)\|[^ ]*\) [^ )]*' | grep -o '[A-Za-z0-9_\.][A-Za-z0-9_\.]\+$' | sort | uniq *)
        addmod
        BaseConversion.convert_bases
        BaseConversion.convert_basesmod
        carrymod
        carry_mulmod
        carry_scmulmod
        carry_squaremod
        encodemod
        extend_to_length
        Freeze.from_bytes
        Freeze.to_bytes
        freeze_to_bytesmod
        from_bytesmod
        oppmod
        Partition.partition
        select
        submod
        to_bytesmod
        zeros
        zselect
  .

  Lemma carry_mul_correct res
        (Hres : carry_mul = Success res)
    : carry_mul_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_carry_mul res (Hres : carry_mul = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma carry_square_correct res
        (Hres : carry_square = Success res)
    : carry_square_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_carry_square res (Hres : carry_square = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma carry_scmul_const_correct a res
        (Hres : carry_scmul_const a = Success res)
    : carry_scmul_const_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds a (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_carry_scmul_const a res (Hres : carry_scmul_const a = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma carry_correct res
        (Hres : carry = Success res)
    : carry_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_carry res (Hres : carry = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma add_correct res
        (Hres : add = Success res)
    : add_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_add res (Hres : add = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma sub_correct res
        (Hres : sub = Success res)
    : sub_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_sub res (Hres : sub = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma opp_correct res
        (Hres : opp = Success res)
    : opp_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_opp res (Hres : opp = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma carry_add_correct res
        (Hres : carry_add = Success res)
    : carry_add_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_carry_add res (Hres : carry_add = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma carry_sub_correct res
        (Hres : carry_sub = Success res)
    : carry_sub_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_carry_sub res (Hres : carry_sub = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma carry_opp_correct res
        (Hres : carry_opp = Success res)
    : carry_opp_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_carry_opp res (Hres : carry_opp = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma relax_correct res
        (Hres : relax = Success res)
    : relax_correct tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_relax res (Hres : relax = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma from_bytes_correct res
        (Hres : from_bytes = Success res)
        (Hrequests : request_present requests "from_bytes" = true)
    : from_bytes_correct (weight (Qnum limbwidth) (QDen limbwidth)) n n_bytes m s tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_from_bytes res (Hres : from_bytes = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma relax_valid
    : forall x, list_Z_bounded_by tight_bounds x -> list_Z_bounded_by loose_bounds x.
  Proof using Type. apply relax_list_Z_bounded_by, tight_bounds_tighter. Qed.

  Lemma to_bytes_correct res
        (Hres : to_bytes = Success res)
        (Hrequests : request_present requests "to_bytes" = true)
    : to_bytes_correct (weight (Qnum limbwidth) (QDen limbwidth)) n n_bytes m tight_bounds (Interp res).
  Proof using curve_good.
    prove_correctness (); [].
    erewrite freeze_to_bytesmod_partitions; [ reflexivity | .. ].
    all: repeat apply conj; autorewrite with distr_length; (congruence || auto).
    all: cbv [tight_bounds] in *.
    all: lazymatch goal with
         | [ H1 : list_Z_bounded_by (List.map (fun y => Some (@?f y)) ?b) ?x, H2 : eval ?wt ?n ?b < _
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
                      | progress cbv [tight_upperbounds] in * ].
  Qed.

  Lemma Wf_to_bytes res (Hres : to_bytes = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [encode]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma encode_correct res
        (Hres : encode = Success res)
    : encode_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_encode res (Hres : encode = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [zero]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma zero_correct res
        (Hres : zero = Success res)
    : zero_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_zero res (Hres : zero = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [one]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma one_correct res
        (Hres : one = Success res)
    : one_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma Wf_one res (Hres : one = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma copy_correct res
        (Hres : copy = Success res)
    : copy_correct saturated_bounds (Interp res).
  Proof using curve_good. Primitives.prove_correctness use_curve_good. Qed.

  Lemma Wf_copy res (Hres : copy = Success res) : Wf res.
  Proof using Type. revert Hres; cbv [copy]; apply Wf_copy. Qed.

  Section ring.
    Context carry_mul_res (Hcarry_mul : carry_mul = Success carry_mul_res)
            add_res       (Hadd       : add       = Success add_res)
            sub_res       (Hsub       : sub       = Success sub_res)
            opp_res       (Hopp       : opp       = Success opp_res)
            carry_res     (Hcarry     : carry     = Success carry_res)
            encode_res    (Hencode    : encode    = Success encode_res)
            zero_res      (Hzero      : zero      = Success zero_res)
            one_res       (Hone       : one       = Success one_res).

    Definition GoodT : Prop
      := GoodT
           (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds
           (Interp carry_mul_res)
           (Interp add_res)
           (Interp sub_res)
           (Interp opp_res)
           (Interp carry_res)
           (Interp encode_res)
           (Interp zero_res)
           (Interp one_res).

    Theorem Good : GoodT.
    Proof using curve_good Hcarry_mul Hadd Hsub Hopp Hcarry Hencode Hzero Hone.
      pose proof use_curve_good; cbv zeta in *; destruct_head'_and.
      eapply Good.
      all: repeat first [ assumption
                        | apply carry_mul_correct
                        | apply add_correct
                        | apply sub_correct
                        | apply opp_correct
                        | apply carry_correct
                        | apply encode_correct
                        | apply zero_correct
                        | apply one_correct
                        | apply relax_valid ].
    Qed.
  End ring.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("carry_mul", wrap_s scarry_mul);
            ("carry_square", wrap_s scarry_square);
            ("carry", wrap_s scarry);
            ("add", wrap_s sadd);
            ("sub", wrap_s ssub);
            ("opp", wrap_s sopp);
            ("carry_add", wrap_s scarry_add);
            ("carry_sub", wrap_s scarry_sub);
            ("carry_opp", wrap_s scarry_opp);
            ("relax", wrap_s srelax);
            ("selectznz", wrap_s sselectznz);
            ("to_bytes", wrap_s sto_bytes);
            ("from_bytes", wrap_s sfrom_bytes)].

    Definition valid_names : string
      := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions) ++ ", or 'carry_scmul' followed by a decimal literal".

    Definition extra_special_synthesis (function_name_prefix : string) (name : string)
      : list (option { t : _ & string * Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult t) }%type)
      := [if prefix "carry_scmul" name
          then let sc := substring (String.length "carry_scmul") (String.length name) name in
               (scZ <- Decimal.Z.of_string sc;
               if (sc =? Decimal.Z.to_string scZ)%string
               then Some (wrap_s (fun _ => scarry_scmul_const function_name_prefix scZ) tt)
               else None)%option
          else None].

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (synthesis_output_kind * string * Pipeline.ErrorT (list string))
      := Primitives.Synthesize
           machine_wordsize valid_names known_functions (extra_special_synthesis function_name_prefix) all_typedefs!
           check_args
           (ToString.comment_file_header_block
              (comment_header
                 ++ [""
                     ; "Computed values:"]
                 ++ (List.map
                       (fun s => "  " ++ s)%string
                       ((ToString.prefix_and_indent "carry_chain = " [show idxs])
                          ++ (ToString.prefix_and_indent "eval z = " [seval "z"])
                          ++ (ToString.prefix_and_indent "bytes_eval z = " [sbytes_eval "z"])
                          ++ (ToString.prefix_and_indent "balance = " [let show_lvl_Z := Hex.show_lvl_Z in show balance])))))
           function_name_prefix requests.
  End for_stringification.
End __.

Module Export Hints.
  Hint Opaque
       carry_mul
       carry_square
       carry_scmul_const
       carry
       add
       sub
       opp
       carry_add
       carry_sub
       carry_opp
       relax
       from_bytes
       to_bytes
       encode
       zero
       one
       copy
  : wf_op_cache.
  Hint Immediate
       Wf_carry_mul
       Wf_carry_square
       Wf_carry_scmul_const
       Wf_carry
       Wf_add
       Wf_sub
       Wf_opp
       Wf_carry_add
       Wf_carry_sub
       Wf_carry_opp
       Wf_relax
       Wf_from_bytes
       Wf_to_bytes
       Wf_encode
       Wf_zero
       Wf_one
       Wf_copy
  : wf_op_cache.
End Hints.
