(** * Push-Button Synthesis of Word-By-Word Montgomery *)
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.Program.Tactics. (* For WBW Montgomery proofs *)
Require Import Coq.derive.Derive.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.ModInv. (* Only needed for WBW Montgomery *)
Require Import Crypto.Util.ZUtil.Modulo. (* Only needed for WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Le. (* Only needed for WBW Montgomery proofs *)
Require Import Crypto.Util.Prod. (* For WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo. (* For WBW montgomery proofs *)
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall. (* For WBW montgomery proofs *)
Require Import Crypto.Util.ZUtil.Div. (* For WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem. (* For WBW Montgomery proofs *)
Require Import Crypto.Util.ZUtil.Ones. (* For WBW montgomery proofs *)
Require Import Crypto.Util.ZUtil.Shift. (* For WBW montgomery proofs *)
Require Import Crypto.Util.ZUtil.ModExp.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.BYInv.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.WordByWordMontgomeryReificationCache.
Require Import Crypto.PushButtonSynthesis.BYInversionReificationCache.
Require Import Crypto.Assembly.Equivalence.
Import ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Wf.Compilers
  Language.WfExtra.Compilers
  Language.Compilers
  AbstractInterpretation.Compilers
  Stringification.Language.Compilers.
Import Compilers.API.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.Solinas.
Import COperationSpecifications.WordByWordMontgomery.

Import Associational Positional.
Import Arithmetic.WordByWordMontgomery.WordByWordMontgomery.

Import WordByWordMontgomeryReificationCache.WordByWordMontgomery.
Import BYInversionReificationCache.WordByWordMontgomeryInversion.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

(* needed for making [autorewrite] not take a very long time *)
Local Opaque
      reified_mul_gen
      reified_add_gen
      reified_sub_gen
      reified_opp_gen
      reified_to_bytes_gen
      reified_from_bytes_gen
      reified_nonzero_gen
      reified_square_gen
      reified_encode_gen
      reified_from_montgomery_gen
      reified_to_montgomery_gen
      reified_zero_gen
      reified_one_gen
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
          {assembly_conventions : assembly_conventions_opt}
          {error_on_unused_assembly_functions : error_on_unused_assembly_functions_opt}
          (m : Z)
          (machine_wordsize : machine_wordsize_opt).

  Definition s := 2^Z.log2_up m.
  Definition c := s - m.
  Definition n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Definition sat_limbs := (n + 1)%nat.   (* to represent m in twos complement we might need another bit *)
  Definition r := 2^machine_wordsize.
  Definition r' := Z.modinv r m.
  Definition m' := Z.modinv (-m) r.
  Definition n_bytes := bytes_n s.

  Definition divstep_precompmod :=
    let bits := (Z.log2 m) + 1 in
    let i := if bits <? 46 then (49 * bits + 80) / 17 else (49 * bits + 57) / 17 in
    let k := (m + 1) / 2 in
    (Z.modexp k i m).

  Definition prime_upperbound_list : list Z
    := Partition.partition (uweight machine_wordsize) n (s-1).
  Definition prime_bytes_upperbound_list : list Z
    := Partition.partition (weight 8 1) n_bytes (s-1).
  Definition upperbounds : list Z := prime_upperbound_list.
  Definition prime_bound : ZRange.type.interp (base.type.Z)
    := r[0~>m-1]%zrange.
  Definition prime_word_bound : ZRange.type.interp (base.type.Z) (* a word that's guaranteed to be smaller than the prime *)
    := r[0 ~> Z.min m (2^machine_wordsize) - 1]%zrange.
  Definition prime_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun v => Some r[0 ~> v]%zrange) prime_upperbound_list.
  Definition prime_bytes_bounds : list (ZRange.type.option.interp (base.type.Z))
    := List.map (fun v => Some r[0 ~> v]%zrange) prime_bytes_upperbound_list.
  Local Notation word_bound := (word_bound machine_wordsize).
  Local Notation saturated_bounds := (saturated_bounds n machine_wordsize).
  Local Notation larger_saturated_bounds := (Primitives.saturated_bounds sat_limbs machine_wordsize).


  Definition divstep_input :=
    (Some r[0~>2^machine_wordsize-1],
     (Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) sat_limbs),
      (Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) sat_limbs),
       (Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) n),
        (Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) n),tt)))))%zrange.

  Definition divstep_output :=
    (Some r[0~>2^machine_wordsize-1],
     Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) sat_limbs),
     Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) sat_limbs),
     Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) n),
     Some (repeat (Some r[0 ~> 2^machine_wordsize-1]) n))%zrange.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

  Definition possible_values_of_machine_wordsize_with_bytes
    := prefix_with_carry_bytes [machine_wordsize; 2 * machine_wordsize]%Z.

  Let possible_values := possible_values_of_machine_wordsize.
  Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.
  Definition bounds : list (ZRange.type.option.interp base.type.Z)
    := saturated_bounds (*List.map (fun u => Some r[0~>u]%zrange) upperbounds*).
  Definition larger_bounds : list (ZRange.type.option.interp base.type.Z)
    := larger_saturated_bounds (*List.map (fun u => Some r[0~>u]%zrange) upperbounds*).
  Definition montgomery_domain_bounds := saturated_bounds.
  Definition non_montgomery_domain_bounds := saturated_bounds.
  Typeclasses Opaque montgomery_domain_bounds.
  Typeclasses Opaque non_montgomery_domain_bounds.
  Global Instance montgomery_domain_bounds_typedef : typedef (t:=base.type.list base.type.Z) (Some montgomery_domain_bounds)
    := { name := "montgomery_domain_field_element"
         ; description name := (text_before_type_name ++ name ++ " is a field element in the Montgomery domain.")%string }.
  Global Instance non_montgomery_domain_bounds_typedef : typedef (t:=base.type.list base.type.Z) (Some non_montgomery_domain_bounds)
    := { name := "non_montgomery_domain_field_element"
         ; description name := (text_before_type_name ++ name ++ " is a field element NOT in the Montgomery domain.")%string }.


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
            [((1 <? machine_wordsize)%Z, Pipeline.Value_not_ltZ "machine_wordsize <= 1" 1 machine_wordsize)
             ; ((0 <? c)%Z, Pipeline.Value_not_ltZ "c ≤ 0" 0 c)
             ; ((1 <? m)%Z, Pipeline.Value_not_ltZ "m ≤ 1" 1 m)
             ; (negb (n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" n 0%nat)
             ; (negb (r' =? 0)%Z, Pipeline.No_modular_inverse "r⁻¹ mod m" r m)
             ; (((r * r') mod m =? 1)%Z, Pipeline.Values_not_provably_equalZ "(r * r') mod m ≠ 1" ((r * r') mod m) 1)
             ; (((m * m') mod r =? (-1) mod r)%Z, Pipeline.Values_not_provably_equalZ "(m * m') mod r ≠ (-1) mod r" ((m * m') mod r) ((-1) mod r))
             ; (s <=? r^n, Pipeline.Value_not_leZ "r^n ≤ s" s (r^n))
             ; (s <=? uweight machine_wordsize n, Pipeline.Value_not_leZ "weight n < s (needed for from_bytes)" s (uweight machine_wordsize n))
             ; (s <=? uweight 8 n_bytes, Pipeline.Value_not_leZ "bytes_weight n_bytes < s (needed for from_bytes)" s (uweight 8 n_bytes))
         ])
         res.

  Local Arguments Z.mul !_ !_.

  Local Ltac use_curve_good_t :=
    repeat first [ use_requests_to_prove_curve_good_t_step
                 | assumption
                 | lia
                 | progress autorewrite with distr_length
                 | progress distr_length
                 | solve [ auto with zarith ]
                 | rewrite Z.log2_pow2 by use_curve_good_t ].

  Context (requests : list string)
          (curve_good : check_args requests (Success tt) = Success tt).

  Lemma use_curve_good
    : Z.pos (Z.to_pos m) = m
      /\ m = s - c
      /\ Z.pos (Z.to_pos m) <> 0
      /\ s - c <> 0
      /\ 0 < s
      /\ s <> 0
      /\ 0 < machine_wordsize
      /\ n <> 0%nat
      /\ List.length bounds = n
      /\ 0 < 1 <= machine_wordsize
      /\ 0 < c < s
      /\ (r * r') mod m = 1
      /\ (m * m') mod r = (-1) mod r
      /\ 0 < machine_wordsize
      /\ 1 < m
      /\ m < r^n
      /\ s = 2^Z.log2 s
      /\ s <= uweight machine_wordsize n
      /\ s <= uweight 8 n_bytes.
  Proof using curve_good.
    prepare_use_curve_good (); cbv [s c] in *.
    { destruct m eqn:?; cbn; lia. }
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

  Local Notation valid := (valid machine_wordsize n m).
  Local Notation bytes_valid := (WordByWordMontgomery.valid 8 n_bytes m).

  Local Notation from_montgomery_res := (from_montgomerymod machine_wordsize n m m').

  Local Notation notations_for_docstring prefix
    := ((CorrectnessStringification.dyn_context.cons
           m "m"
           (CorrectnessStringification.dyn_context.cons
              r' ("((2^" ++ Decimal.Z.to_string machine_wordsize ++ ")⁻¹ mod m)")
              (CorrectnessStringification.dyn_context.cons
                 from_montgomery_res "from_montgomery"
                 (CorrectnessStringification.dyn_context.cons
                    (@eval machine_wordsize n) "eval"
                    (CorrectnessStringification.dyn_context.cons
                       (@eval 8 n_bytes) "bytes_eval"
                            (CorrectnessStringification.dyn_context.cons
                               (Z.log2 m) "⌊log2 m⌋"
                               (CorrectnessStringification.dyn_context.cons
                                  (@eval_twos_complement machine_wordsize n) "twos_complement_eval"
                                  CorrectnessStringification.dyn_context.nil)))))))%string)
         (only parsing).
  Local Notation "'docstring_with_summary_from_lemma!' prefix summary correctness"
    := (docstring_with_summary_from_lemma_with_ctx!
          (notations_for_docstring prefix)
          summary
          correctness)
         (only parsing, at level 10, prefix at next level, summary at next level, correctness at next level).

  Definition mul
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_mul_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some montgomery_domain_bounds, (Some montgomery_domain_bounds, tt))
         (Some montgomery_domain_bounds).

  Definition smul (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "mul" mul
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " multiplies two field elements in the Montgomery domain."]%string)
             (mul_correct machine_wordsize n m valid from_montgomery_res)).

  Definition square
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_square_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some montgomery_domain_bounds, tt)
         (Some montgomery_domain_bounds).

  Definition ssquare (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "square" square
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " squares a field element in the Montgomery domain."]%string)
             (square_correct machine_wordsize n m valid from_montgomery_res)).

  Definition add
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_add_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (Some montgomery_domain_bounds, (Some montgomery_domain_bounds, tt))
         (Some montgomery_domain_bounds).

  Definition sadd (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "add" add
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " adds two field elements in the Montgomery domain."]%string)
             (add_correct machine_wordsize n m valid from_montgomery_res)).

  Definition sub
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_sub_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (Some montgomery_domain_bounds, (Some montgomery_domain_bounds, tt))
         (Some montgomery_domain_bounds).

  Definition ssub (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "sub" sub
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " subtracts two field elements in the Montgomery domain."]%string)
             (sub_correct machine_wordsize n m valid from_montgomery_res)).

  Definition opp
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_opp_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (Some montgomery_domain_bounds, tt)
         (Some montgomery_domain_bounds).

  Definition sopp (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "opp" opp
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " negates a field element in the Montgomery domain."]%string)
             (opp_correct machine_wordsize n m valid from_montgomery_res)).

  Definition from_montgomery
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_from_montgomery_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some montgomery_domain_bounds, tt)
         (Some non_montgomery_domain_bounds).

  Definition sfrom_montgomery (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "from_montgomery" from_montgomery
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " translates a field element out of the Montgomery domain."]%string)
             (from_montgomery_correct machine_wordsize n m r' valid)).

  Definition to_montgomery
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_to_montgomery_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some non_montgomery_domain_bounds, tt)
         (Some montgomery_domain_bounds).

  Definition sto_montgomery (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "to_montgomery" to_montgomery
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " translates a field element into the Montgomery domain."]%string)
             (to_montgomery_correct machine_wordsize n m valid from_montgomery_res)).

  Definition nonzero
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         reified_nonzero_gen
         (Some bounds, tt)
         (Some r[0~>r-1]%zrange).

  Definition snonzero (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "nonzero" nonzero
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " outputs a single non-zero word if the input is non-zero and zero otherwise."]%string)
             (nonzero_correct machine_wordsize n m valid from_montgomery_res)).

  Definition to_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_to_bytes_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (Some prime_bounds, tt)
         (Some prime_bytes_bounds).

  Definition sto_bytes (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "to_bytes" to_bytes
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " serializes a field element NOT in the Montgomery domain to bytes in little-endian order."]%string)
             (to_bytes_correct machine_wordsize n n_bytes m valid)).

  Definition from_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_from_bytes_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify 1 @ GallinaReify.Reify s @ GallinaReify.Reify n)
         (Some prime_bytes_bounds, tt)
         (Some prime_bounds).

  Definition sfrom_bytes (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "from_bytes" from_bytes
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " deserializes a field element NOT in the Montgomery domain from bytes in little-endian order."]%string)
             (from_bytes_correct machine_wordsize n n_bytes m valid bytes_valid)).

  Definition encode
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_encode_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some prime_bound, tt)
         (Some montgomery_domain_bounds).

  Definition sencode (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "encode" encode
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " encodes an integer as a field element in the Montgomery domain."]%string)
             (encode_correct machine_wordsize n m valid from_montgomery_res)).


  Definition encode_word
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_encode_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         (Some prime_word_bound, tt)
         (Some saturated_bounds).

  Definition sencode_word (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "encode_word" encode_word
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " encodes an integer as a field element in the Montgomery domain."]%string)
             (encode_word_correct machine_wordsize n m valid from_montgomery_res)).

  Definition zero
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_zero_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         tt
         (Some montgomery_domain_bounds).

  Definition szero (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "zero" zero
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname => [text_before_function_name ++ fname ++ " returns the field element zero in the Montgomery domain."]%string)
             (zero_correct machine_wordsize n m valid from_montgomery_res)).

  Definition one
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_one_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
         tt
         (Some montgomery_domain_bounds).

  Definition sone (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "set_one" one (* to avoid conflict with boringSSL *)
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname => [text_before_function_name ++ fname ++ " returns the field element one in the Montgomery domain."]%string)
             (one_correct machine_wordsize n m valid from_montgomery_res)).

  Definition reval (* r for reified *)
    := Pipeline.RepeatRewriteAddAssocLeftAndFlattenThunkedRects
         n
         (Pipeline.PreBoundsPipeline
            true (* subst01 *)
            false (* let_bind_return *)
            None (* fancy *)
            (reified_eval_gen
               @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n)
            (Some montgomery_domain_bounds, tt)).

  Definition seval (arg_name : string) (* s for string *)
    := Show.show (invert_expr.smart_App_curried (reval _) (arg_name, tt)).

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
    := Show.show (invert_expr.smart_App_curried (rbytes_eval _) (arg_name, tt)).

  Definition reval_twos_complement (* r for reified *)
    := Pipeline.RepeatRewriteAddAssocLeftAndFlattenThunkedRects
         n
         (Pipeline.PreBoundsPipeline
            true (* subst01 *)
            false (* let_bind_return *)
            None (* fancy *)
            (reified_eval_twos_complement_gen
               @ GallinaReify.Reify (machine_wordsize:Z)
               @ GallinaReify.Reify n)
            (Some bounds, tt)).

  Definition seval_twos_complement (arg_name : string) (* s for string *)
    := Show.show (invert_expr.smart_App_curried (reval_twos_complement _) (arg_name, tt)).

  Definition selectznz : Pipeline.ErrorT _ := Primitives.selectznz n machine_wordsize.
  Definition sselectznz (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Primitives.sselectznz n machine_wordsize prefix.

  Definition copy : Pipeline.ErrorT _ := Primitives.copy n machine_wordsize.
  Definition scopy (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Primitives.scopy n machine_wordsize prefix.

  Definition msat
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_msat_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify sat_limbs @ GallinaReify.Reify m)
         tt
         (Some larger_bounds).

 Definition smsat (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "msat" msat
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname => [text_before_function_name ++ fname ++ " returns the saturated representation of the prime modulus."]%string)
             (msat_correct machine_wordsize n m valid)).

  Definition divstep_precomp
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_encode_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m' @ GallinaReify.Reify divstep_precompmod)
         tt
         (Some bounds).

  Definition sdivstep_precomp (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "divstep_precomp" divstep_precomp
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname => [text_before_function_name ++ fname ++ " returns the precomputed value for Bernstein-Yang-inversion (in montgomery form)."]%string)
             (divstep_precomp_correct machine_wordsize n m valid from_montgomery_res)).

  Definition divstep
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_divstep_gen
            @ GallinaReify.Reify (machine_wordsize:Z) @ GallinaReify.Reify sat_limbs @ GallinaReify.Reify n @ GallinaReify.Reify m)
         (divstep_input)
         (divstep_output).

  Definition sdivstep (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "divstep" divstep
          (docstring_with_summary_from_lemma!
             prefix
             (fun fname : string => [text_before_function_name ++ fname ++ " computes a divstep."]%string)
             (divstep_correct machine_wordsize n m valid from_montgomery_res)).

  Lemma bounded_by_of_valid x
        (H : valid x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some bounds) x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    clear -H use_curve_good curve_good.
    destruct H as [H _]; destruct_head'_and.
    cbv [small] in H.
    cbv [ZRange.type.base.option.is_bounded_by bounds saturated_bounds word_bound].
    replace n with (List.length x) by now rewrite H, Partition.length_partition.
    rewrite <- map_const, fold_andb_map_map1, fold_andb_map_iff.
    cbv [ZRange.type.base.is_bounded_by is_bounded_by_bool lower upper type_base].
    split; [ reflexivity | ].
    intros *; rewrite combine_same, in_map_iff, Bool.andb_true_iff, !Z.leb_le.
    intros; destruct_head'_ex; destruct_head'_and; subst *; cbn [fst snd].
    match goal with
    | [ H : In ?v x |- _ ] => revert v H
    end.
    rewrite H.
    generalize (eval (n:=n) machine_wordsize x).
    cbn [base.interp base.base_interp].
    generalize n.
    intro n'.
    induction n' as [|n' IHn'].
    { cbv [Partition.partition seq List.map In]; tauto. }
    { intros *; rewrite Partition.partition_step, in_app_iff; cbn [List.In].
      intros; destruct_head'_or; subst *; eauto; try tauto; [].
      rewrite uweight_S by lia.
      assert (0 < uweight machine_wordsize n') by now apply uwprops.
      assert (0 < 2 ^ machine_wordsize) by auto with zarith.
      assert (0 < 2 ^ machine_wordsize * uweight machine_wordsize n') by nia.
      rewrite <- Z.mod_pull_div by lia.
      rewrite Z.le_sub_1_iff.
      auto with zarith. }
  Qed.

  (* XXX FIXME *)
  Lemma bounded_by_prime_bounds_of_valid_gen lgr n' x
        (Hlgr : 0 < lgr)
        (Hs : s = 2^Z.log2 s)
        (Hs' : s <= uweight lgr n')
        (H : WordByWordMontgomery.valid lgr n' m x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some (List.map (fun v => Some r[0~>v]%zrange) (Partition.partition (uweight lgr) n' (s-1)))) x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    clear -H use_curve_good curve_good Hlgr Hs Hs'.
    destruct H as [H ?]; destruct_head'_and.
    cbv [small] in H.
    cbv [ZRange.type.base.option.is_bounded_by].
    replace n' with (List.length x) by now rewrite H, Partition.length_partition.
    rewrite fold_andb_map_map1, fold_andb_map_iff.
    split; [ now autorewrite with distr_length | ].
    cbv [ZRange.type.base.is_bounded_by is_bounded_by_bool lower upper].
    rewrite H; autorewrite with distr_length.
    intros [v1 v0]; cbn [fst snd].
    rename x into x'.
    generalize dependent (eval (n:=n') lgr x').
    replace m with (s - c) in * by easy.
    intro x; intros ??? H; subst x'.
    eapply In_nth_error in H; destruct H as [i H].
    rewrite nth_error_combine in H.
    break_match_hyps; try discriminate; []; Option.inversion_option; Prod.inversion_prod; subst.
    cbv [Partition.partition] in *.
    apply nth_error_map_ex in Heqo; apply nth_error_map_ex in Heqo0; destruct Heqo as (?&?&?), Heqo0 as (?&?&?).
    rewrite nth_error_seq in *.
    break_match_hyps; try discriminate; Option.inversion_option; Prod.inversion_prod; subst.
    rewrite ?Nat.add_0_l.
    assert (0 <= x < s) by lia.
    replace s with (2^Z.log2 s) by easy.
    assert (1 < s) by lia.
    assert (0 < Z.log2 s) by now apply Z.log2_pos.
    assert (1 < 2^Z.log2 s) by auto with zarith.
    generalize dependent (Z.log2 s); intro lgs; intros.

    edestruct (uwprops lgr); try lia.
    assert (forall i : nat, 0 <= uweight lgr i) by (intro z; specialize (weight_positive z); lia).
    apply Bool.andb_true_intro; split; apply OrdersEx.Z_as_OT.leb_le;
      [apply Z.div_nonneg | apply Z.div_le_mono_nonneg]; trivial.
    apply Z.mod_pos_bound; trivial.

    cbv [uweight].
    cbv [weight].
    rewrite Z.div_1_r.
    rewrite Z.opp_involutive.
    rewrite <-2Z.land_ones by nia.
    rewrite Z.sub_1_r, <-Z.ones_equiv.
    rewrite Z.land_ones_ones.
    destruct ((lgs <? 0) || (lgr * Z.of_nat (S i) <? 0)) eqn:?.
    { rewrite Z.land_ones, Z.ones_equiv, <-Z.sub_1_r by nia.
      pose proof Z.le_max_r lgs (lgr*Z.of_nat (S i)).
      etransitivity.
      2:rewrite <- Z.sub_le_mono_r.
      2:eapply Z.pow_le_mono_r; try lia; eassumption.
      eapply Z.le_sub_1_iff, Z.mod_pos_bound, Z.pow_pos_nonneg; nia. }
    rewrite (Z.ones_equiv (Z.min _ _)), <-Z.sub_1_r.
    enough (Z.land x (Z.ones (lgr * Z.of_nat (S i))) < 2 ^ Z.min lgs (lgr * Z.of_nat (S i))) by lia.
    eapply Testbit.Z.testbit_false_bound. nia.
    intros j ?; assert (Z.min lgs (lgr * Z.of_nat (S i)) <= j) by lia.
    rewrite Hs in *. revert H; intros.
    rewrite <-(Z.mod_small x (2^lgs)) by lia.
    rewrite OrdersEx.Z_as_OT.land_spec.
    destruct (Zmin_irreducible lgs (lgr * Z.of_nat (S i))) as [HH|HH]; rewrite HH in *; clear HH.
    { rewrite Z.mod_pow2_bits_high; trivial; lia. }
    { rewrite OrdersEx.Z_as_DT.ones_spec_high, Bool.andb_false_r; trivial; nia. }
  Qed.

  Lemma length_of_valid lgr n' x
        (H : WordByWordMontgomery.valid lgr n' m x)
    : List.length x = n'.
  Proof using Type.
    destruct H as [H _]; rewrite H.
    now autorewrite with distr_length.
  Qed.

  Lemma bounded_by_prime_bounds_of_valid x
        (H : valid x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some prime_bounds) x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    destruct_head'_and.
    now apply bounded_by_prime_bounds_of_valid_gen.
  Qed.

  Lemma bounded_by_prime_bytes_bounds_of_bytes_valid x
        (H : bytes_valid x)
    : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some prime_bytes_bounds) x = true.
  Proof using curve_good.
    pose proof use_curve_good as use_curve_good.
    destruct_head'_and.
    now apply bounded_by_prime_bounds_of_valid_gen.
  Qed.

  Lemma weight_bounded_of_bytes_valid x
        (H : bytes_valid x)
    : 0 <= eval 8 (n:=n_bytes) x < weight machine_wordsize 1 n.
  Proof using curve_good.
    cbv [bytes_valid] in H.
    destruct H as [_ H].
    pose proof use_curve_good.
    cbv [uweight] in *; destruct_head'_and; lia.
  Qed.

  Local Ltac solve_extra_bounds_side_conditions :=
    solve [ cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia
          | cbv [valid small eval uweight n_bytes] in *; destruct_head'_and; auto
          | now apply weight_bounded_of_bytes_valid
          | eapply length_of_valid; eassumption ].

  Hint Rewrite
       (@eval_mulmod machine_wordsize n m r' m')
       (@eval_squaremod machine_wordsize n m r' m')
       (@eval_addmod machine_wordsize n m r' m')
       (@eval_submod machine_wordsize n m r' m')
       (@eval_oppmod machine_wordsize n m r' m')
       (@eval_from_montgomerymod machine_wordsize n m r' m')
       (@eval_to_montgomerymod machine_wordsize n m r' m')
       (@eval_encodemod machine_wordsize n m r' m')
       eval_to_bytesmod
       eval_from_bytesmod
       using solve [ eauto using length_of_valid | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  (* needed for making [autorewrite] fast enough *)
  Local Opaque
        WordByWordMontgomery.WordByWordMontgomery.onemod
        WordByWordMontgomery.WordByWordMontgomery.from_montgomerymod
        WordByWordMontgomery.WordByWordMontgomery.to_montgomerymod
        WordByWordMontgomery.WordByWordMontgomery.mulmod
        WordByWordMontgomery.WordByWordMontgomery.squaremod
        WordByWordMontgomery.WordByWordMontgomery.encodemod
        WordByWordMontgomery.WordByWordMontgomery.addmod
        WordByWordMontgomery.WordByWordMontgomery.submod
        WordByWordMontgomery.WordByWordMontgomery.oppmod
        WordByWordMontgomery.WordByWordMontgomery.to_bytesmod.
  Hint Unfold eval zeromod onemod : push_eval.

  Local Ltac prove_correctness op_correct :=
    let dont_clear H := first [ constr_eq H curve_good ] in
    let Hres := match goal with H : _ = Success _ |- _ => H end in
    let H := fresh in
    pose proof use_curve_good as H;
    (* I want to just use [clear -H Hres], but then I can't use any lemmas in the section because of COQBUG(https://github.com/coq/coq/issues/8153) *)
    repeat match goal with
           | [ H' : _ |- _ ]
             => tryif first [ has_body H' | constr_eq H' H | constr_eq H' Hres | dont_clear H' ]
             then fail
             else clear H'
           end;
    cbv zeta in *;
    destruct_head'_and;
    let f := match type of Hres with ?f = _ => head f end in
    try cbv [f] in *;
    hnf;
    PipelineTactics.do_unfolding;
    try (let m := match goal with m := _ - Associational.eval _ |- _ => m end in
         cbv [m] in * );
    intros;
    lazymatch goal with
    | [ |- _ <-> _ ] => idtac
    | [ |- _ = _ ] => idtac
    | _ => split; [ | try split ];
           cbv [small]
    end;
    PipelineTactics.use_compilers_correctness Hres;
    repeat first [ reflexivity
                 | now apply bounded_by_of_valid
                 | now apply bounded_by_prime_bounds_of_valid
                 | now apply bounded_by_prime_bytes_bounds_of_bytes_valid
                 | now apply weight_bounded_of_bytes_valid
                 | solve [ eapply op_correct; try eassumption; solve_extra_bounds_side_conditions ]
                 | progress autorewrite with interp_gen_cache interp_extra
                 | progress autorewrite with push_eval
                 | progress autounfold with push_eval
                 | progress autorewrite with distr_length in *
                 | solve [ cbv [valid small eval uweight n_bytes] in *; destruct_head'_and; auto ] ].

  (** TODO: DESIGN DECISION:

        The correctness lemmas for most of the montgomery things are
        parameterized over a `from_montgomery`.  When filling this in
        for, e.g., mul-correctness, should I use `from_montgomery`
        from arithmetic, or should I use `Interp
        reified_from_montgomery` (the post-pipeline version), and take
        in success of the pipeline on `from_montgomery` as well? *)

  Lemma mul_correct res
        (Hres : mul = Success res)
    : mul_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness mulmod_correct. Qed.

  Lemma Wf_mul res (Hres : mul = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma square_correct res
        (Hres : square = Success res)
    : square_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness squaremod_correct. Qed.

  Lemma Wf_square res (Hres : square = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma add_correct res
        (Hres : add = Success res)
    : add_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness addmod_correct. Qed.

  Lemma Wf_add res (Hres : add = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma sub_correct res
        (Hres : sub = Success res)
    : sub_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness submod_correct. Qed.

  Lemma Wf_sub res (Hres : sub = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma opp_correct res
        (Hres : opp = Success res)
    : opp_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness oppmod_correct. Qed.

  Lemma Wf_opp res (Hres : opp = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma from_montgomery_correct res
        (Hres : from_montgomery = Success res)
    : from_montgomery_correct machine_wordsize n m r' valid (Interp res).
  Proof using curve_good. prove_correctness from_montgomerymod_correct. Qed.

  Lemma Wf_from_montgomery res (Hres : from_montgomery = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma to_montgomery_correct res
        (Hres : to_montgomery = Success res)
    : to_montgomery_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness to_montgomerymod_correct. Qed.

  Lemma Wf_to_montgomery res (Hres : to_montgomery = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma nonzero_correct res
        (Hres : nonzero = Success res)
    : nonzero_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness nonzeromod_correct. Qed.

  Lemma Wf_nonzero res (Hres : nonzero = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma to_bytes_correct res
        (Hres : to_bytes = Success res)
    : to_bytes_correct machine_wordsize n n_bytes m valid (Interp res).
  Proof using curve_good. prove_correctness to_bytesmod_correct. Qed.

  Lemma Wf_to_bytes res (Hres : to_bytes = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma from_bytes_correct res
        (Hres : from_bytes = Success res)
    : from_bytes_correct machine_wordsize n n_bytes m valid bytes_valid (Interp res).
  Proof using curve_good. prove_correctness eval_from_bytesmod_and_partitions. Qed.

  Lemma Wf_from_bytes res (Hres : from_bytes = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [encode]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma encode_correct res
        (Hres : encode = Success res)
    : encode_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness encodemod_correct. Qed.

  Lemma Wf_encode res (Hres : encode = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [encode_word]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma encode_word_correct res
        (Hres : encode_word = Success res)
    : encode_word_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness encodemod_correct. Qed.

  Lemma Wf_encode_word res (Hres : encode_word = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [zero]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma zero_correct res
        (Hres : zero = Success res)
    : zero_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness encodemod_correct. Qed.

  Lemma Wf_zero res (Hres : zero = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [one]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma one_correct res
        (Hres : one = Success res)
    : one_correct machine_wordsize n m valid from_montgomery_res (Interp res).
  Proof using curve_good. prove_correctness encodemod_correct. Qed.

  Lemma Wf_one res (Hres : one = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Local Opaque Pipeline.BoundsPipeline. (* need this or else [eapply Pipeline.BoundsPipeline_correct in Hres] takes forever *)

  Lemma selectznz_correct res
        (Hres : selectznz = Success res)
    : selectznz_correct saturated_bounds (Interp res).
  Proof using curve_good. Primitives.prove_correctness use_curve_good. Qed.

  Lemma Wf_selectznz res (Hres : selectznz = Success res) : Wf res.
  Proof using Type. revert Hres; cbv [selectznz]; apply Wf_selectznz. Qed.

  Lemma copy_correct res
        (Hres : copy = Success res)
    : copy_correct saturated_bounds (Interp res).
  Proof using curve_good. Primitives.prove_correctness use_curve_good. Qed.

  Lemma Wf_copy res (Hres : copy = Success res) : Wf res.
  Proof using Type. revert Hres; cbv [copy]; apply Wf_copy. Qed.

  Section ring.
    Context from_montgomery_res (Hfrom_montgomery : from_montgomery = Success from_montgomery_res)
            mul_res    (Hmul    : mul    = Success mul_res)
            add_res    (Hadd    : add    = Success add_res)
            sub_res    (Hsub    : sub    = Success sub_res)
            opp_res    (Hopp    : opp    = Success opp_res)
            encode_res (Hencode : encode = Success encode_res)
            zero_res   (Hzero   : zero   = Success zero_res)
            one_res    (Hone    : one    = Success one_res).

    Definition GoodT : Prop
      := GoodT
           machine_wordsize n m valid
           (Interp from_montgomery_res)
           (Interp mul_res)
           (Interp add_res)
           (Interp sub_res)
           (Interp opp_res)
           (Interp encode_res)
           (Interp zero_res)
           (Interp one_res).

    Theorem Good : GoodT.
    Proof using curve_good Hfrom_montgomery Hmul Hadd Hsub Hopp Hencode Hzero Hone.
      pose proof use_curve_good; cbv zeta in *; destruct_head'_and.
      eapply Good.
      all: repeat first [ assumption
                        | apply from_montgomery_correct
                        | lia ].
      all: hnf; intros.
      all: push_Zmod; erewrite !(fun v Hv => proj1 (from_montgomery_correct _ Hfrom_montgomery v Hv)), <- !eval_from_montgomerymod; try eassumption; pull_Zmod.
      all: repeat first [ assumption
                        | lazymatch goal with
                          | [ |- context[mul_res] ] => apply mul_correct
                          | [ |- context[add_res] ] => apply add_correct
                          | [ |- context[sub_res] ] => apply sub_correct
                          | [ |- context[opp_res] ] => apply opp_correct
                          | [ |- context[encode_res] ] => apply encode_correct
                          | [ |- context[zero_res] ] => apply zero_correct
                          | [ |- context[one_res] ] => apply one_correct
                          end ].
    Qed.
  End ring.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("mul", wrap_s smul);
            ("square", wrap_s ssquare);
            ("add", wrap_s sadd);
            ("sub", wrap_s ssub);
            ("opp", wrap_s sopp);
            ("from_montgomery", wrap_s sfrom_montgomery);
            ("to_montgomery", wrap_s sto_montgomery);
            ("nonzero", wrap_s snonzero);
            ("selectznz", wrap_s sselectznz);
            ("to_bytes", wrap_s sto_bytes);
            ("from_bytes", wrap_s sfrom_bytes);
            ("one", wrap_s sone);
            ("msat", wrap_s smsat);
            ("divstep_precomp", wrap_s sdivstep_precomp);
            ("divstep", wrap_s sdivstep)].

    Definition valid_names : string := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions).

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (synthesis_output_kind * string * Pipeline.ErrorT (list string))
      := Primitives.Synthesize
           machine_wordsize valid_names known_functions (fun _ => nil) all_typedefs!
           check_args
           (ToString.comment_file_header_block
              (comment_header
                 ++ [""
                     ; "Computed values:"]
                 ++ (List.map
                       (fun s => "  " ++ s)%string
                       ((ToString.prefix_and_indent "eval z = " [seval "z"])
                          ++ (ToString.prefix_and_indent "bytes_eval z = " [sbytes_eval "z"])
                          ++ (ToString.prefix_and_indent "twos_complement_eval z = " [seval_twos_complement "z"])))))
           function_name_prefix requests.
  End for_stringification.
End __.

Module Export Hints.
#[global]
  Hint Opaque
       mul
       square
       add
       sub
       opp
       from_montgomery
       to_montgomery
       nonzero
       to_bytes
       from_bytes
       encode
       encode_word
       zero
       one
       selectznz
       copy
  : wf_op_cache.
#[global]
  Hint Immediate
       Wf_mul
       Wf_square
       Wf_add
       Wf_sub
       Wf_opp
       Wf_from_montgomery
       Wf_to_montgomery
       Wf_nonzero
       Wf_to_bytes
       Wf_from_bytes
       Wf_encode
       Wf_encode_word
       Wf_zero
       Wf_one
       Wf_selectznz
       Wf_copy
  : wf_op_cache.
End Hints.
