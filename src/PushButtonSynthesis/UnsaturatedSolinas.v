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
Require Import Crypto.Util.Strings.Equality.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Strings.Show.
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
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinasReificationCache.
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
      reified_zero_gen
      reified_one_gen
      reified_prime_gen
      reified_to_bytes_gen
      reified_from_bytes_gen
      expr.Interp.

Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {static : static_opt}
          {emit_primitives : emit_primitives_opt}
          {should_split_mul : should_split_mul_opt}
          {widen_carry : widen_carry_opt}
          {widen_bytes : widen_bytes_opt}
          (n : nat)
          (s : Z)
          (c : list (Z * Z))
          (machine_wordsize : Z).

  Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
  Let idxs : list nat := carry_chains n s c.
  Let coef := 2.
  Let n_bytes := bytes_n (Qnum limbwidth) (Qden limbwidth) n.
  Let prime_upperbound_list : list Z
    := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
  Let prime_bytes_upperbound_list : list Z
    := encode_no_reduce (weight 8 1) n_bytes (s-1).
  Let tight_upperbounds : list Z
    := List.map
         (fun v : Z => Qceiling (tight_upperbound_fraction * v))
         prime_upperbound_list.
  Definition prime_bound : ZRange.type.option.interp (base.type.Z)
    := Some r[0~>(s - Associational.eval c - 1)]%zrange.
  Definition prime_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
    := Some (List.map (fun v => Some r[0 ~> v]%zrange) prime_upperbound_list).
  Definition prime_bytes_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
    := Some (List.map (fun v => Some r[0 ~> v]%zrange) prime_bytes_upperbound_list).
  Local Notation saturated_bounds_list := (saturated_bounds_list n machine_wordsize).
  Local Notation saturated_bounds := (saturated_bounds n machine_wordsize).

  Let m : Z := s - Associational.eval c.
  Definition m_enc : list Z
    := encode (weight (Qnum limbwidth) (Qden limbwidth)) n s c m.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := [0; machine_wordsize; 2 * machine_wordsize]%Z.

  Definition possible_values_of_machine_wordsize_with_bytes
    := prefix_with_carry_bytes [machine_wordsize; 2 * machine_wordsize]%Z.

  Let possible_values := possible_values_of_machine_wordsize.
  Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.
  Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
  Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun u => Some r[0 ~> loose_upperbound_extra_multiplicand*u]%zrange) tight_upperbounds.

  Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.

  Lemma length_prime_upperbound_list : List.length prime_upperbound_list = n.
  Proof using Type. cbv [prime_upperbound_list]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_prime_upperbound_list : distr_length.
  Lemma length_tight_upperbounds : List.length tight_upperbounds = n.
  Proof using Type. cbv [tight_upperbounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_tight_upperbounds : distr_length.
  Lemma length_tight_bounds : List.length tight_bounds = n.
  Proof using Type. cbv [tight_bounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_tight_bounds : distr_length.
  Lemma length_loose_bounds : List.length loose_bounds = n.
  Proof using Type. cbv [loose_bounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_loose_bounds : distr_length.
  Lemma length_prime_bytes_upperbound_list : List.length prime_bytes_upperbound_list = bytes_n (Qnum limbwidth) (Qden limbwidth) n.
  Proof using Type. cbv [prime_bytes_upperbound_list]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_prime_bytes_upperbound_list : distr_length.
  Lemma length_saturated_bounds_list : List.length saturated_bounds_list = n.
  Proof using Type. cbv [saturated_bounds_list]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_saturated_bounds_list : distr_length.

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := fold_right
         (fun '(b, e) k => if b:bool then Error e else k)
         res
         [(negb (Qle_bool 1 limbwidth)%Q, Pipeline.Value_not_leQ "limbwidth < 1" 1%Q limbwidth);
            ((negb (0 <? Associational.eval c))%Z, Pipeline.Value_not_ltZ "Associational.eval c ≤ 0" 0 (Associational.eval c));
            ((negb (Associational.eval c <? s))%Z, Pipeline.Value_not_ltZ "s ≤ Associational.eval c" (Associational.eval c) s);
            ((s =? 0)%Z, Pipeline.Values_not_provably_distinctZ "s = 0" s 0);
            ((n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" n 0%nat);
            ((negb (0 <? machine_wordsize)), Pipeline.Value_not_ltZ "machine_wordsize ≤ 0" 0 machine_wordsize);
            (let v1 := s in
             let v2 := weight (Qnum limbwidth) (QDen limbwidth) n in
             (negb (v1 =? v2), Pipeline.Values_not_provably_equalZ "s ≠ weight n (needed for to_bytes)" v1 v2));
            (let v1 := (map (Z.land (Z.ones machine_wordsize)) m_enc) in
             let v2 := m_enc in
             (negb (list_beq _ Z.eqb v1 v2), Pipeline.Values_not_provably_equal_listZ "map mask m_enc ≠ m_enc (needed for to_bytes)" v1 v2));
            (let v1 := eval (weight (Qnum limbwidth) (QDen limbwidth)) n m_enc in
             let v2 := s - Associational.eval c in
             (negb (v1 =? v2)%Z, Pipeline.Values_not_provably_equalZ "eval m_enc ≠ s - Associational.eval c (needed for to_bytes)" v1 v2));
            (let v1 := eval (weight (Qnum limbwidth) (QDen limbwidth)) n tight_upperbounds in
             let v2 := 2 * eval (weight (Qnum limbwidth) (QDen limbwidth)) n m_enc in
             (negb (v1 <? v2)%Z, Pipeline.Value_not_ltZ "2 * eval m_enc ≤ eval tight_upperbounds (needed for to_bytes)" v1 v2))].

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
    : let eval := eval (weight (Qnum limbwidth) (QDen limbwidth)) n in
      s - Associational.eval c <> 0
      /\ s <> 0
      /\ 0 < machine_wordsize
      /\ n <> 0%nat
      /\ List.length tight_bounds = n
      /\ List.length loose_bounds = n
      /\ List.length prime_bytes_upperbound_list = n_bytes
      /\ List.length saturated_bounds_list = n
      /\ 0 < Qden limbwidth <= Qnum limbwidth
      /\ s = weight (Qnum limbwidth) (QDen limbwidth) n
      /\ map (Z.land (Z.ones machine_wordsize)) m_enc = m_enc
      /\ eval m_enc = s - Associational.eval c
      /\ Datatypes.length m_enc = n
      /\ 0 < Associational.eval c < s
      /\ eval tight_upperbounds < 2 * eval m_enc
      /\ 0 < m.
  Proof using curve_good.
    clear -curve_good.
    cbv [check_args fold_right] in curve_good.
    cbv [tight_bounds loose_bounds prime_bound m_enc] in *.
    break_innermost_match_hyps; try discriminate.
    rewrite negb_false_iff in *.
    Z.ltb_to_lt.
    rewrite Qle_bool_iff in *.
    rewrite NPeano.Nat.eqb_neq in *.
    intros.
    cbv [Qnum Qden limbwidth Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *.
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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "carry_mul" carry_mul
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " multiplies two field elements and reduces the result."]%string)
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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "carry_square" carry_square
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " squares a field element and reduces the result."]%string)
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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix ("carry_scmul_" ++ decimal_string_of_Z x) (carry_scmul_const x)
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " multiplies a field element by " ++ decimal_string_of_Z x ++ " and reduces the result."]%string)
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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "carry" carry
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " reduces a field element."]%string)
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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "add" add
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " adds two field elements."]%string)
             (add_correct weightf n m tight_bounds loose_bounds)).

  Definition sub
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_sub_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify coef)
         (Some tight_bounds, (Some tight_bounds, tt))
         (Some loose_bounds).

  Definition ssub (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "sub" sub
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " subtracts two field elements."]%string)
             (sub_correct weightf n m tight_bounds loose_bounds)).

  Definition opp
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_opp_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n @ GallinaReify.Reify coef)
         (Some tight_bounds, tt)
         (Some loose_bounds).

  Definition sopp (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "opp" opp
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " negates a field element."]%string)
             (opp_correct weightf n m tight_bounds loose_bounds)).

  Definition to_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_to_bytes_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify m_enc)
         (Some tight_bounds, tt)
         prime_bytes_bounds.

  Definition sto_bytes (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "to_bytes" to_bytes
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " serializes a field element to bytes in little-endian order."]%string)
             (to_bytes_correct weightf n n_bytes m tight_bounds)).

  Definition from_bytes
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_from_bytes_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify n)
         (prime_bytes_bounds, tt)
         (Some tight_bounds).

  Definition sfrom_bytes (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "from_bytes" from_bytes
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " deserializes a field element from bytes in little-endian order."]%string)
             (from_bytes_correct weightf n n_bytes m s tight_bounds)).

  Definition encode
    := Pipeline.BoundsPipeline
         true (* subst01 *)
         None (* fancy *)
         possible_values
         (reified_encode_gen
            @ GallinaReify.Reify (Qnum limbwidth) @ GallinaReify.Reify (Z.pos (Qden limbwidth)) @ GallinaReify.Reify s @ GallinaReify.Reify c @ GallinaReify.Reify n)
         (prime_bound, tt)
         (Some tight_bounds).

  Definition sencode (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "encode" encode
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " encodes an integer as a field element."]%string)
             (encode_correct weightf n m tight_bounds)).

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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "zero" zero
          (docstring_with_summary_from_lemma!
             (fun fname => ["The function " ++ fname ++ " returns the field element zero."]%string)
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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "one" one
          (docstring_with_summary_from_lemma!
             (fun fname => ["The function " ++ fname ++ " returns the field element one."]%string)
             (one_correct weightf n m tight_bounds)).

  Definition selectznz : Pipeline.ErrorT _ := Primitives.selectznz n machine_wordsize.
  Definition sselectznz (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Primitives.sselectznz n machine_wordsize prefix.

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       eval_carry_mulmod
       eval_carry_squaremod
       eval_carry_scmulmod
       eval_addmod
       eval_submod
       eval_oppmod
       eval_carrymod
       freeze_to_bytesmod_partitions
       eval_to_bytesmod
       eval_from_bytesmod
       eval_encodemod
       using solve [ auto | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  Hint Unfold zeromod onemod : push_eval.

  Local Ltac prove_correctness _ :=
    Primitives.prove_correctness use_curve_good;
    try solve [ auto | congruence | solve_extra_bounds_side_conditions ].

  Lemma carry_mul_correct res
        (Hres : carry_mul = Success res)
    : carry_mul_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma carry_square_correct res
        (Hres : carry_square = Success res)
    : carry_square_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma carry_scmul_const_correct a res
        (Hres : carry_scmul_const a = Success res)
    : carry_scmul_const_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds a (Interp res).
  Proof using curve_good.
    prove_correctness ().
    erewrite eval_carry_scmulmod by (auto || congruence); reflexivity.
  Qed.

  Lemma carry_correct res
        (Hres : carry = Success res)
    : carry_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma add_correct res
        (Hres : add = Success res)
    : add_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma sub_correct res
        (Hres : sub = Success res)
    : sub_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma opp_correct res
        (Hres : opp = Success res)
    : opp_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma from_bytes_correct res
        (Hres : from_bytes = Success res)
    : from_bytes_correct (weight (Qnum limbwidth) (QDen limbwidth)) n n_bytes m s tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Lemma relax_correct
    : forall x, list_Z_bounded_by tight_bounds x -> list_Z_bounded_by loose_bounds x.
  Proof using Type.
    cbv [tight_bounds loose_bounds list_Z_bounded_by].
    intro.
    rewrite !fold_andb_map_map1, !fold_andb_map_iff; cbn [upper lower].
    setoid_rewrite Bool.andb_true_iff.
    intro H.
    repeat first [ lazymatch type of H with
                   | and _ _ => let H' := fresh in destruct H as [H' H]; split; [ assumption | ]
                   end
                 | let x := fresh in intro x; specialize (H x) ].
    cbv [loose_upperbound_extra_multiplicand].
    Z.ltb_to_lt; lia.
  Qed.

  Lemma to_bytes_correct res
        (Hres : to_bytes = Success res)
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

  Strategy -1000 [encode]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma encode_correct res
        (Hres : encode = Success res)
    : encode_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Strategy -1000 [zero]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma zero_correct res
        (Hres : zero = Success res)
    : zero_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

  Strategy -1000 [one]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma one_correct res
        (Hres : one = Success res)
    : one_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds (Interp res).
  Proof using curve_good. prove_correctness (). Qed.

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
                        | apply relax_correct ].
    Qed.
  End ring.

  Section for_stringification.
    Local Open Scope string_scope.
    Local Open Scope list_scope.

    Definition known_functions
      := [("carry_mul", scarry_mul);
            ("carry_square", scarry_square);
            ("carry", scarry);
            ("add", sadd);
            ("sub", ssub);
            ("opp", sopp);
            ("selectznz", sselectznz);
            ("to_bytes", sto_bytes);
            ("from_bytes", sfrom_bytes)].

    Definition valid_names : string
      := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions) ++ ", or 'carry_scmul' followed by a decimal literal".

    Definition extra_special_synthesis (function_name_prefix : string) (name : string)
      : list (option (string * Pipeline.ErrorT (list string * ToString.ident_infos)))
      := [if prefix "carry_scmul" name
          then let sc := substring (String.length "carry_scmul") (String.length name) name in
               let scZ := Z_of_decimal_string sc in
               if string_beq sc (decimal_string_of_Z scZ)
               then Some (scarry_scmul_const function_name_prefix scZ)
               else None
          else None].

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
                       "carry_chain = " ++ show false idxs]%string)
              ++ [""])
           function_name_prefix requests.
  End for_stringification.
End __.
