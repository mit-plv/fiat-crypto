(** * Push-Button Synthesis of Saturated Solinas *)
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
Require Import Crypto.Util.Strings.Equality.
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
Require Import Crypto.Util.LetIn. (* For Barrett *)
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds. (* For Barrett *)
Require Import Crypto.Arithmetic.BarrettReduction.Generalized. (* For Barrett *)
Require Import Crypto.Util.Tactics.UniquePose. (* For Barrett *)
Require Import Crypto.Util.ZUtil.Rshi. (* For Barrett *)
Require Import Crypto.Algebra.Ring. (* For Barrett *)
Require Import Crypto.Util.ZUtil.AddModulo. (* For Barrett *)
Require Import Crypto.Util.ZUtil.Zselect. (* For Barrett *)
Require Import Crypto.Util.ZUtil.CC. (* For Barrett *)
Require Import Crypto.Util.ZUtil.EquivModulo. (* For MontgomeryReduction *)
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition. (* For MontgomeryReduction *)
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs. (* For MontgomeryReduction *)
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.AbstractInterpretation.
Require Import Crypto.Experiments.NewPipeline.CStringification.
Require Import Crypto.Experiments.NewPipeline.Arithmetic.
Require Import Crypto.Experiments.NewPipeline.BoundsPipeline.
Require Import Crypto.Experiments.NewPipeline.COperationSpecifications.
Require Import Crypto.Experiments.NewPipeline.PushButtonSynthesis.ReificationCache.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  LanguageWf.Compilers
  Language.Compilers
  AbstractInterpretation.Compilers
  CStringification.Compilers.
Import Compilers.defaults.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.Solinas.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export Primitives.
  (**
<<
#!/usr/bin/env python

indent = '  '

print((indent + '(' + r'''**
<<
%s
>>
*''' + ')\n') % open(__file__, 'r').read())

for (op, opmod) in (('id', '(@id (list Z))'), ('selectznz', 'Positional.select'), ('mulx', 'mulx'), ('addcarryx', 'addcarryx'), ('subborrowx', 'subborrowx'), ('cmovznz', 'cmovznz')):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %s)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %s (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, op, op, opmod, op, opmod, op, op, op, op)).replace('\n', '\n%s' % indent) + '\n')

>>
*)

  Derive reified_id_gen
         SuchThat (is_reification_of reified_id_gen (@id (list Z)))
         As reified_id_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification (@id (list Z)) (proj1 reified_id_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_id_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_id_gen_correct) : interp_gen_cache.
  Local Opaque reified_id_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_selectznz_gen
         SuchThat (is_reification_of reified_selectznz_gen Positional.select)
         As reified_selectznz_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification Positional.select (proj1 reified_selectznz_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_selectznz_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_selectznz_gen_correct) : interp_gen_cache.
  Local Opaque reified_selectznz_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_mulx_gen
         SuchThat (is_reification_of reified_mulx_gen mulx)
         As reified_mulx_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification mulx (proj1 reified_mulx_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_mulx_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_mulx_gen_correct) : interp_gen_cache.
  Local Opaque reified_mulx_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_addcarryx_gen
         SuchThat (is_reification_of reified_addcarryx_gen addcarryx)
         As reified_addcarryx_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification addcarryx (proj1 reified_addcarryx_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_addcarryx_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_addcarryx_gen_correct) : interp_gen_cache.
  Local Opaque reified_addcarryx_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_subborrowx_gen
         SuchThat (is_reification_of reified_subborrowx_gen subborrowx)
         As reified_subborrowx_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification subborrowx (proj1 reified_subborrowx_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_subborrowx_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_subborrowx_gen_correct) : interp_gen_cache.
  Local Opaque reified_subborrowx_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_cmovznz_gen
         SuchThat (is_reification_of reified_cmovznz_gen cmovznz)
         As reified_cmovznz_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification cmovznz (proj1 reified_cmovznz_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_cmovznz_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_cmovznz_gen_correct) : interp_gen_cache.
  Local Opaque reified_cmovznz_gen. (* needed for making [autorewrite] not take a very long time *)

  (* needed for making [autorewrite] with [Set Keyed Unification] fast *)
  Local Opaque expr.Interp.

  Local Notation arg_bounds_of_pipeline result
    := ((fun a b c d e arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c d e arg_bounds out_bounds = result') => arg_bounds) _ _ _ _ _ _ _ result eq_refl)
         (only parsing).
  Local Notation out_bounds_of_pipeline result
    := ((fun a b c d e arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c d e arg_bounds out_bounds = result') => out_bounds) _ _ _ _ _ _ _ result eq_refl)
         (only parsing).

  Notation FromPipelineToString prefix name result
    := (((prefix ++ name)%string,
         match result with
         | Success E'
           => let E := ToString.C.ToFunctionLines
                         true true (* static *) prefix (prefix ++ name)%string [] E' None
                         (arg_bounds_of_pipeline result)
                         (out_bounds_of_pipeline result) in
              match E with
              | inl E => Success E
              | inr err => Error (Pipeline.Stringification_failed E' err)
              end
         | Error err => Error err
         end)).

  Ltac prove_correctness use_curve_good :=
    let Hres := match goal with H : _ = Success _ |- _ => H end in
    let H := fresh in
    pose proof use_curve_good as H;
    (* I want to just use [clear -H Hres], but then I can't use any lemmas in the section because of COQBUG(https://github.com/coq/coq/issues/8153) *)
    repeat match goal with
           | [ H' : _ |- _ ]
             => tryif first [ has_body H' | constr_eq H' H | constr_eq H' Hres ]
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
    try split; PipelineTactics.use_compilers_correctness Hres;
    [ pose_proof_length_list_Z_bounded_by;
      repeat first [ reflexivity
                   | progress autorewrite with interp interp_gen_cache push_eval
                   | progress autounfold with push_eval
                   | progress autorewrite with distr_length in * ]
    | .. ].

  Section __.
    Context (n : nat)
            (machine_wordsize : Z).

    Definition saturated_bounds_list : list (option zrange)
      := List.repeat (Some r[0 ~> 2^machine_wordsize-1]%zrange) n.
    Definition saturated_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
      := Some saturated_bounds_list.

    Definition possible_values_of_machine_wordsize
      := [machine_wordsize; 2 * machine_wordsize]%Z.

    Definition possible_values_of_machine_wordsize_with_bytes
      := [1; 8; machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.
    Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.

    Lemma length_saturated_bounds_list : List.length saturated_bounds_list = n.
    Proof using Type. cbv [saturated_bounds_list]; now autorewrite with distr_length. Qed.
    Hint Rewrite length_saturated_bounds_list : distr_length.

    Definition selectznz
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values_with_bytes
           reified_selectznz_gen
           (Some r[0~>1], (saturated_bounds, (saturated_bounds, tt)))%zrange
           saturated_bounds.

    Definition sselectznz (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "selectznz" selectznz.

    Definition mulx (s : Z)
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values_with_bytes
           (reified_mulx_gen
              @ GallinaReify.Reify s)
           (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt))%zrange
           (Some r[0~>2^s-1], Some r[0~>2^s-1])%zrange.

    Definition smulx (prefix : string) (s : Z)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix ("mulx_u" ++ decimal_string_of_Z s) (mulx s).

    Definition addcarryx (s : Z)
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values_with_bytes
           (reified_addcarryx_gen
              @ GallinaReify.Reify s)
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1], Some r[0~>1])%zrange.

    Definition saddcarryx (prefix : string) (s : Z)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix ("addcarryx_u" ++ decimal_string_of_Z s) (addcarryx s).

    Definition subborrowx (s : Z)
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values_with_bytes
           (reified_subborrowx_gen
              @ GallinaReify.Reify s)
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1], Some r[0~>1])%zrange.

    Definition ssubborrowx (prefix : string) (s : Z)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix ("subborrowx_u" ++ decimal_string_of_Z s) (subborrowx s).

    Definition cmovznz (s : Z)
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values_with_bytes
           (reified_cmovznz_gen
              @ GallinaReify.Reify s)
           (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
           (Some r[0~>2^s-1])%zrange.

    Definition scmovznz (prefix : string) (s : Z)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix ("cmovznz_u" ++ decimal_string_of_Z s) (cmovznz s).

    Local Ltac solve_extra_bounds_side_conditions :=
      cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

    Hint Rewrite
          eval_select
          Arithmetic.mulx_correct
          Arithmetic.addcarryx_correct
          Arithmetic.subborrowx_correct
          Arithmetic.cmovznz_correct
          Z.zselect_correct
          using solve [ auto | congruence | solve_extra_bounds_side_conditions ] : push_eval.

    Strategy -1000 [mulx]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
    Lemma mulx_correct s' res
          (Hres : mulx s' = Success res)
      : mulx_correct s' (Interp res).
    Proof using Type. prove_correctness I. Qed.

    Strategy -1000 [addcarryx]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
    Lemma addcarryx_correct s' res
          (Hres : addcarryx s' = Success res)
      : addcarryx_correct s' (Interp res).
    Proof using Type. prove_correctness I. Qed.

    Strategy -1000 [subborrowx]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
    Lemma subborrowx_correct s' res
          (Hres : subborrowx s' = Success res)
      : subborrowx_correct s' (Interp res).
    Proof using Type. prove_correctness I. Qed.

    Strategy -1000 [cmovznz]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
    Lemma cmovznz_correct s' res
          (Hres : cmovznz s' = Success res)
      : cmovznz_correct s' (Interp res).
    Proof using Type. prove_correctness I. Qed.

    Lemma selectznz_correct limbwidth res
          (Hres : selectznz = Success res)
      : selectznz_correct (weight (Qnum limbwidth) (QDen limbwidth)) n saturated_bounds_list (Interp res).
    Proof using Type. prove_correctness I. Qed.

    Section for_stringification.
      Context (valid_names : string)
              (known_functions : list (string
                                       * (string
                                          -> string *
                                             Pipeline.ErrorT (list string * ToString.C.ident_infos))))
              (extra_special_synthesis : string ->
                                         list
                                           (option
                                              (string *
                                               Pipeline.ErrorT
                                                 (list string * ToString.C.ident_infos)))).

      Definition aggregate_infos {A B C} (ls : list (A * ErrorT B (C * ToString.C.ident_infos))) : ToString.C.ident_infos
        := fold_right
             ToString.C.ident_info_union
             ToString.C.ident_info_empty
             (List.map
                (fun '(_, res) => match res with
                                  | Success (_, infos) => infos
                                  | Error _ => ToString.C.ident_info_empty
                                  end)
                ls).

      Definition extra_synthesis (function_name_prefix : string) (infos : ToString.C.ident_infos)
        : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t
        := let ls_addcarryx := List.flat_map
                                 (fun lg_split:positive => [saddcarryx function_name_prefix lg_split; ssubborrowx function_name_prefix lg_split])
                                 (PositiveSet.elements (ToString.C.addcarryx_lg_splits infos)) in
           let ls_mulx := List.map
                            (fun lg_split:positive => smulx function_name_prefix lg_split)
                            (PositiveSet.elements (ToString.C.mulx_lg_splits infos)) in
           let ls_cmov := List.map
                            (fun bitwidth:positive => scmovznz function_name_prefix bitwidth)
                            (PositiveSet.elements (ToString.C.cmovznz_bitwidths infos)) in
           let ls := ls_addcarryx ++ ls_mulx ++ ls_cmov in
           let infos := aggregate_infos ls in
           (List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls,
            ToString.C.bitwidths_used infos).


      Definition synthesize_of_name (function_name_prefix : string) (name : string)
        : string * ErrorT Pipeline.ErrorMessage (list string * ToString.C.ident_infos)
        := fold_right
             (fun v default
              => match v with
                 | Some res => res
                 | None => default
                 end)
             ((name,
               Error
                 (Pipeline.Invalid_argument
                    ("Unrecognized request to synthesize """ ++ name ++ """; valid names are " ++ valid_names ++ "."))))
             ((map
                 (fun '(expected_name, resf) => if string_beq name expected_name then Some (resf function_name_prefix) else None)
                 known_functions)
                ++ extra_special_synthesis name).

      (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
      Definition Synthesize (function_name_prefix : string) (requests : list string)
        : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t (* types used *)
        := let ls := match requests with
                     | nil => List.map (fun '(_, sr) => sr function_name_prefix) known_functions
                     | requests => List.map (synthesize_of_name function_name_prefix) requests
                     end in
           let infos := aggregate_infos ls in
           let '(extra_ls, extra_bit_widths) := extra_synthesis function_name_prefix infos in
           (extra_ls ++ List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls,
            PositiveSet.union extra_bit_widths (ToString.C.bitwidths_used infos)).
    End for_stringification.
  End __.
End Primitives.

Module UnsaturatedSolinas.
  Definition zeromod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 0.
  Definition onemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n 1.
  Definition primemod limbwidth_num limbwidth_den s c n := encodemod limbwidth_num limbwidth_den s c n (s - Associational.eval c).

  (**
<<
#!/usr/bin/env python

indent = '  '

print((indent + '(' + r'''**
<<
%s
>>
*''' + ')\n') % open(__file__, 'r').read())

for i in ('carry_mul', 'carry_square', 'carry_scmul', 'carry', 'encode', 'add', 'sub', 'opp', 'zero', 'one', 'prime'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')

for (op, opmod) in (('to_bytes', 'freeze_to_bytesmod'), ('from_bytes', 'from_bytesmod')):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %s)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %s (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, op, op, opmod, op, opmod, op, op, op, op)).replace('\n', '\n%s' % indent) + '\n')

>>
*)

  Derive reified_carry_mul_gen
         SuchThat (is_reification_of reified_carry_mul_gen carry_mulmod)
         As reified_carry_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carry_mulmod (proj1 reified_carry_mul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_mul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_square_gen
         SuchThat (is_reification_of reified_carry_square_gen carry_squaremod)
         As reified_carry_square_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carry_squaremod (proj1 reified_carry_square_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_square_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_square_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_square_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_scmul_gen
         SuchThat (is_reification_of reified_carry_scmul_gen carry_scmulmod)
         As reified_carry_scmul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carry_scmulmod (proj1 reified_carry_scmul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_scmul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_scmul_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_scmul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_carry_gen
         SuchThat (is_reification_of reified_carry_gen carrymod)
         As reified_carry_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification carrymod (proj1 reified_carry_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_carry_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_carry_gen_correct) : interp_gen_cache.
  Local Opaque reified_carry_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_encode_gen
         SuchThat (is_reification_of reified_encode_gen encodemod)
         As reified_encode_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification encodemod (proj1 reified_encode_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_encode_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_encode_gen_correct) : interp_gen_cache.
  Local Opaque reified_encode_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_add_gen
         SuchThat (is_reification_of reified_add_gen addmod)
         As reified_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification addmod (proj1 reified_add_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_add_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_add_gen_correct) : interp_gen_cache.
  Local Opaque reified_add_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_sub_gen
         SuchThat (is_reification_of reified_sub_gen submod)
         As reified_sub_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification submod (proj1 reified_sub_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_sub_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_sub_gen_correct) : interp_gen_cache.
  Local Opaque reified_sub_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_opp_gen
         SuchThat (is_reification_of reified_opp_gen oppmod)
         As reified_opp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification oppmod (proj1 reified_opp_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_opp_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_opp_gen_correct) : interp_gen_cache.
  Local Opaque reified_opp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_zero_gen
         SuchThat (is_reification_of reified_zero_gen zeromod)
         As reified_zero_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification zeromod (proj1 reified_zero_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_zero_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_zero_gen_correct) : interp_gen_cache.
  Local Opaque reified_zero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_one_gen
         SuchThat (is_reification_of reified_one_gen onemod)
         As reified_one_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification onemod (proj1 reified_one_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_one_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_one_gen_correct) : interp_gen_cache.
  Local Opaque reified_one_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_prime_gen
         SuchThat (is_reification_of reified_prime_gen primemod)
         As reified_prime_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification primemod (proj1 reified_prime_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_prime_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_prime_gen_correct) : interp_gen_cache.
  Local Opaque reified_prime_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_to_bytes_gen
         SuchThat (is_reification_of reified_to_bytes_gen freeze_to_bytesmod)
         As reified_to_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification freeze_to_bytesmod (proj1 reified_to_bytes_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_to_bytes_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_to_bytes_gen_correct) : interp_gen_cache.
  Local Opaque reified_to_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_bytes_gen
         SuchThat (is_reification_of reified_from_bytes_gen from_bytesmod)
         As reified_from_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification from_bytesmod (proj1 reified_from_bytes_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_from_bytes_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_from_bytes_gen_correct) : interp_gen_cache.
  Local Opaque reified_from_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  (* needed for making [autorewrite] with [Set Keyed Unification] fast *)
  Local Opaque expr.Interp.

  Section __.
    Context (n : nat)
            (s : Z)
            (c : list (Z * Z))
            (machine_wordsize : Z).

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.
    Let coef := 2.
    Let n_bytes := bytes_n (Qnum limbwidth) (Qden limbwidth) n.
    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let prime_bytes_upperbound_list : list Z
      := encode_no_reduce (weight 8 1) n_bytes (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
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

    Definition possible_values_of_machine_wordsize
      := [machine_wordsize; 2 * machine_wordsize]%Z.

    Definition possible_values_of_machine_wordsize_with_bytes
      := [1; 8; machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.
    Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.
    Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "carry_mul" carry_mul.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "carry_square" carry_square.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix ("carry_scmul_" ++ decimal_string_of_Z x) (carry_scmul_const x).

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "carry" carry.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "add" add.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "sub" sub.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "opp" opp.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "to_bytes" to_bytes.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "from_bytes" from_bytes.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "encode" encode.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "zero" zero.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "one" one.

    Definition selectznz : Pipeline.ErrorT _ := Primitives.selectznz n machine_wordsize.
    Definition sselectznz (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
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
      repeat first [ let H' := fresh in destruct H as [H' H]; split; [ assumption | ]
                   | let x := fresh in intro x; specialize (H x) ].
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
           | [ H1 : list_Z_bounded_by (List.map (fun x => Some (@?f x)) ?b) ?x, H2 : eval ?wt ?n ?b < _
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
        : list (option (string * Pipeline.ErrorT (list string * ToString.C.ident_infos)))
        := [if prefix "carry_scmul" name
            then let sc := substring (String.length "carry_scmul") (String.length name) name in
                 let scZ := Z_of_decimal_string sc in
                 if string_beq sc (decimal_string_of_Z scZ)
                 then Some (scarry_scmul_const function_name_prefix scZ)
                 else None
            else None].

      (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
      Definition Synthesize (function_name_prefix : string) (requests : list string)
        : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t (* types used *)
        := Primitives.Synthesize
             machine_wordsize valid_names known_functions (extra_special_synthesis function_name_prefix)
             function_name_prefix requests.
    End for_stringification.
  End __.
End UnsaturatedSolinas.

Module SaturatedSolinas.
  Import COperationSpecifications.SaturatedSolinas.

  Definition mulmod
             (s : Z)
             (c : list (Z * Z))
             (log2base : Z)
             (n nreductions : nat)
    := @Rows.mulmod (weight log2base 1) (2^log2base) s c n nreductions.

  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  (* needed for making [autorewrite] with [Set Keyed Unification] fast *)
  Local Opaque expr.Interp.

  Section __.
    Context (s : Z)
            (c : list (Z * Z))
            (machine_wordsize : Z).

    Definition possible_values_of_machine_wordsize
      := [1; machine_wordsize]%Z.

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
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "mul" mul.

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
      Definition Synthesize (function_name_prefix : string) (requests : list string)
        : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t (* types used *)
        := Primitives.Synthesize
             machine_wordsize valid_names known_functions (fun _ => nil)
             function_name_prefix requests.
    End for_stringification.
  End __.
End SaturatedSolinas.

Module WordByWordMontgomery.
  Import Arithmetic.WordByWordMontgomery.
  Import COperationSpecifications.WordByWordMontgomery.

  Definition zeromod bitwidth n m m' := encodemod bitwidth n m m' 0.
  Definition onemod bitwidth n m m' := encodemod bitwidth n m m' 1.

  (* we would do something faster, but it generally breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
  Local Ltac precache_reify_faster _ :=
    split;
    [ let marker := fresh "marker" in
      pose I as marker;
      intros;
      let LHS := lazymatch goal with |- ?LHS = _ => LHS end in
      let reified_op_gen := lazymatch LHS with context[expr.Interp _ ?reified_op_gen] => reified_op_gen end in
      subst reified_op_gen;
      etransitivity;
      [
      | let opmod := match goal with |- _ = ?RHS => head RHS end in
        cbv [opmod]; solve [ eauto with reify_cache_gen nocore ] ];
      repeat lazymatch goal with
             | [ H : _ |- _ ] => tryif constr_eq H marker then fail else revert H
             end;
      clear marker
    | ].
  Local Ltac cache_reify_faster_2arg _ :=
    precache_reify_faster ();
    [ lazymatch goal with
      | [ |- forall bw n m m' v, ?interp ?ev bw n m m' v = ?interp' ?reified_mul_gen bw n m m' (@?A bw n m m' v) (@?B bw n m m' v) ]
        => let rv := constr:(fun F bw n m m' v => (F bw n m m' (A bw n m m' v) (B bw n m m' v)):list Z) in
           intros;
           instantiate (1:=ltac:(let r := Reify rv in
                                 refine (r @ reified_mul_gen)%Expr))
      end;
      reflexivity
    | prove_Wf () ].
  Local Ltac cache_reify_faster_1arg _ :=
    precache_reify_faster ();
    [ lazymatch goal with
      | [ |- forall bw n m m', ?interp ?ev bw n m m' = ?interp' ?reified_op_gen bw n m m' (@?A bw n m m') ]
        => let rv := constr:(fun F bw n m m' => (F bw n m m' (A bw n m m')):list Z) in
           intros;
           instantiate (1:=ltac:(let r := Reify rv in
                                 refine (r @ reified_op_gen)%Expr))
      end;
      reflexivity
    | prove_Wf () ].

  (**
<<
#!/usr/bin/env python

indent = '  '

print((indent + '(' + r'''**
<<
%s
>>
*''' + ')\n') % open(__file__, 'r').read())

for i in ('mul', 'add', 'sub', 'opp', 'to_bytes', 'from_bytes', 'nonzero'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')

for i in ('square', 'encode', 'from_montgomery'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof.
  Time cache_reify ().
  (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
  (* Time cache_reify_faster_2arg (). *)
Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')


for i in ('zero', 'one'):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %smod)
       As reified_%s_gen_correct.
Proof.
  (* Time cache_reify (). *)
  (* we do something faster *)
  Time cache_reify_faster_1arg ().
Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification %smod (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, i, i, i, i, i, i, i, i, i)).replace('\n', '\n%s' % indent) + '\n')

>>
*)

  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod (proj1 reified_mul_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_mul_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_mul_gen_correct) : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_add_gen
         SuchThat (is_reification_of reified_add_gen addmod)
         As reified_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification addmod (proj1 reified_add_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_add_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_add_gen_correct) : interp_gen_cache.
  Local Opaque reified_add_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_sub_gen
         SuchThat (is_reification_of reified_sub_gen submod)
         As reified_sub_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification submod (proj1 reified_sub_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_sub_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_sub_gen_correct) : interp_gen_cache.
  Local Opaque reified_sub_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_opp_gen
         SuchThat (is_reification_of reified_opp_gen oppmod)
         As reified_opp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification oppmod (proj1 reified_opp_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_opp_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_opp_gen_correct) : interp_gen_cache.
  Local Opaque reified_opp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_to_bytes_gen
         SuchThat (is_reification_of reified_to_bytes_gen to_bytesmod)
         As reified_to_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification to_bytesmod (proj1 reified_to_bytes_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_to_bytes_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_to_bytes_gen_correct) : interp_gen_cache.
  Local Opaque reified_to_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_bytes_gen
         SuchThat (is_reification_of reified_from_bytes_gen from_bytesmod)
         As reified_from_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification from_bytesmod (proj1 reified_from_bytes_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_from_bytes_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_from_bytes_gen_correct) : interp_gen_cache.
  Local Opaque reified_from_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_nonzero_gen
         SuchThat (is_reification_of reified_nonzero_gen nonzeromod)
         As reified_nonzero_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification nonzeromod (proj1 reified_nonzero_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_nonzero_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_nonzero_gen_correct) : interp_gen_cache.
  Local Opaque reified_nonzero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_square_gen
         SuchThat (is_reification_of reified_square_gen squaremod)
         As reified_square_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification squaremod (proj1 reified_square_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_square_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_square_gen_correct) : interp_gen_cache.
  Local Opaque reified_square_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_encode_gen
         SuchThat (is_reification_of reified_encode_gen encodemod)
         As reified_encode_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification encodemod (proj1 reified_encode_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_encode_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_encode_gen_correct) : interp_gen_cache.
  Local Opaque reified_encode_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_montgomery_gen
         SuchThat (is_reification_of reified_from_montgomery_gen from_montgomerymod)
         As reified_from_montgomery_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification from_montgomerymod (proj1 reified_from_montgomery_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_from_montgomery_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_from_montgomery_gen_correct) : interp_gen_cache.
  Local Opaque reified_from_montgomery_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_zero_gen
         SuchThat (is_reification_of reified_zero_gen zeromod)
         As reified_zero_gen_correct.
  Proof.
    (* Time cache_reify (). *)
    (* we do something faster *)
    Time cache_reify_faster_1arg ().
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification zeromod (proj1 reified_zero_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_zero_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_zero_gen_correct) : interp_gen_cache.
  Local Opaque reified_zero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_one_gen
         SuchThat (is_reification_of reified_one_gen onemod)
         As reified_one_gen_correct.
  Proof.
    (* Time cache_reify (). *)
    (* we do something faster *)
    Time cache_reify_faster_1arg ().
  Time Qed.
  Hint Extern 1 (_ = _) => apply_cached_reification onemod (proj1 reified_one_gen_correct) : reify_cache_gen.
  Hint Immediate (proj2 reified_one_gen_correct) : wf_gen_cache.
  Hint Rewrite (proj1 reified_one_gen_correct) : interp_gen_cache.
  Local Opaque reified_one_gen. (* needed for making [autorewrite] not take a very long time *)

  (* needed for making [autorewrite] with [Set Keyed Unification] fast *)
  Local Opaque expr.Interp.

  Section __.
    Context (s : Z)
            (c : list (Z * Z))
            (machine_wordsize : Z).

    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m := s - Associational.eval c.
    Let r := 2^machine_wordsize.
    Let r' := match Z.modinv r m with
              | Some r' => r'
              | None => 0
              end.
    Let m' := match Z.modinv (-m) r with
              | Some m' => m'
              | None => 0
              end.
    Let n_bytes := bytes_n machine_wordsize 1 n.
    Let prime_upperbound_list : list Z
      := Partition.partition (UniformWeight.uweight machine_wordsize) n (s-1).
    Let prime_bytes_upperbound_list : list Z
      := Partition.partition (weight 8 1) n_bytes (s-1).
    Let upperbounds : list Z := prime_upperbound_list.
    Definition prime_bound : ZRange.type.option.interp (base.type.Z)
      := Some r[0~>(s - Associational.eval c - 1)]%zrange.
    Definition prime_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
      := Some (List.map (fun v => Some r[0 ~> v]%zrange) prime_upperbound_list).
    Definition prime_bytes_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
      := Some (List.map (fun v => Some r[0 ~> v]%zrange) prime_bytes_upperbound_list).
    Local Notation saturated_bounds_list := (saturated_bounds_list n machine_wordsize).
    Local Notation saturated_bounds := (saturated_bounds n machine_wordsize).

    Definition m_enc : list Z
      := encode (UniformWeight.uweight machine_wordsize) n s c (s-Associational.eval c).

    Definition possible_values_of_machine_wordsize
      := [1; machine_wordsize; 2 * machine_wordsize]%Z.

    Definition possible_values_of_machine_wordsize_with_bytes
      := [1; 8; machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.
    Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.
    Definition bounds : list (ZRange.type.option.interp base.type.Z)
      := Option.invert_Some saturated_bounds (*List.map (fun u => Some r[0~>u]%zrange) upperbounds*).

    (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := fold_right
           (fun '(b, e) k => if b:bool then Error e else k)
           res
           [(negb (1 <? machine_wordsize)%Z, Pipeline.Value_not_ltZ "machine_wordsize <= 1" 1 machine_wordsize);
              ((negb (0 <? Associational.eval c))%Z, Pipeline.Value_not_ltZ "Associational.eval c ≤ 0" 0 (Associational.eval c));
              ((negb (Associational.eval c <? s))%Z, Pipeline.Value_not_ltZ "s ≤ Associational.eval c" (Associational.eval c) s);
              ((s =? 0)%Z, Pipeline.Values_not_provably_distinctZ "s = 0" s 0);
              ((n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" n 0%nat);
              ((r' =? 0)%Z, Pipeline.No_modular_inverse "r⁻¹ mod m" r m);
              (negb ((r * r') mod m =? 1)%Z, Pipeline.Values_not_provably_equalZ "(r * r') mod m ≠ 1" ((r * r') mod m) 1);
              (negb ((m * m') mod r =? (-1) mod r)%Z, Pipeline.Values_not_provably_equalZ "(m * m') mod r ≠ (-1) mod r" ((m * m') mod r) ((-1) mod r));
              (negb (s <=? r^n), Pipeline.Value_not_leZ "r^n ≤ s" s (r^n));
              (negb (1 <? s - Associational.eval c), Pipeline.Value_not_ltZ "s - Associational.eval c ≤ 1" 1 (s - Associational.eval c));
              (negb (s =? 2^Z.log2 s), Pipeline.Values_not_provably_equalZ "s ≠ 2^log2(s) (needed for from_bytes)" s (2^Z.log2 s));
              (negb (s <=? UniformWeight.uweight machine_wordsize n), Pipeline.Value_not_leZ "weight n < s (needed for from_bytes)" s (UniformWeight.uweight machine_wordsize n));
              (negb (UniformWeight.uweight machine_wordsize n =? UniformWeight.uweight 8 n_bytes), Pipeline.Values_not_provably_equalZ "weight n ≠ bytes_weight n_bytes (needed for from_bytes)" (UniformWeight.uweight machine_wordsize n) (UniformWeight.uweight 8 n_bytes))].

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
      : Z.pos (Z.to_pos m) = s - Associational.eval c
        /\ Z.pos (Z.to_pos m) <> 0
        /\ s - Associational.eval c <> 0
        /\ s <> 0
        /\ 0 < machine_wordsize
        /\ n <> 0%nat
        /\ List.length bounds = n
        /\ 0 < 1 <= machine_wordsize
        /\ 0 < Associational.eval c < s
        /\ (r * r') mod m = 1
        /\ (m * m') mod r = (-1) mod r
        /\ 0 < machine_wordsize
        /\ 1 < m
        /\ m < r^n
        /\ s = 2^Z.log2 s
        /\ s <= UniformWeight.uweight machine_wordsize n
        /\ s <= UniformWeight.uweight 8 n_bytes
        /\ UniformWeight.uweight machine_wordsize n = UniformWeight.uweight 8 n_bytes.
    Proof.
      clear -curve_good.
      cbv [check_args fold_right] in curve_good.
      cbv [bounds prime_bound m_enc prime_bounds saturated_bounds] in *.
      break_innermost_match_hyps; try discriminate.
      rewrite negb_false_iff in *.
      Z.ltb_to_lt.
      rewrite NPeano.Nat.eqb_neq in *.
      intros.
      cbv [Qnum Qden Qceiling Qfloor Qopp Qdiv Qplus inject_Z Qmult Qinv] in *.
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
      { use_curve_good_t. }
      { use_curve_good_t. }
    Qed.


    Definition mul
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_mul_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
           (Some bounds, (Some bounds, tt))
           (Some bounds).

    Definition smul (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "mul" mul.

    Definition square
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_square_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
           (Some bounds, tt)
           (Some bounds).

    Definition ssquare (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "square" square.

    Definition add
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_add_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m)
           (Some bounds, (Some bounds, tt))
           (Some bounds).

    Definition sadd (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "add" add.

    Definition sub
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_sub_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m)
           (Some bounds, (Some bounds, tt))
           (Some bounds).

    Definition ssub (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "sub" sub.

    Definition opp
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_opp_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m)
           (Some bounds, tt)
           (Some bounds).

    Definition sopp (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "opp" opp.

    Definition from_montgomery
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_from_montgomery_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
           (Some bounds, tt)
           (Some bounds).

    Definition sfrom_montgomery (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "from_montgomery" from_montgomery.

    Definition nonzero
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           reified_nonzero_gen
           (Some bounds, tt)
           (Some r[0~>r-1]%zrange).

    Definition snonzero (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "nonzero" nonzero.

    Definition to_bytes
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values_with_bytes
           (reified_to_bytes_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n)
           (prime_bounds, tt)
           prime_bytes_bounds.

    Definition sto_bytes (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "to_bytes" to_bytes.

    Definition from_bytes
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           None (* fancy *)
           possible_values_with_bytes
           (reified_from_bytes_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify 1 @ GallinaReify.Reify n)
           (prime_bytes_bounds, tt)
           prime_bounds.

    Definition sfrom_bytes (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "from_bytes" from_bytes.

    Definition encode
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_encode_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
           (prime_bound, tt)
           (Some bounds).

    Definition sencode (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "encode" encode.

    Definition zero
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_zero_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
           tt
           (Some bounds).

    Definition szero (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "zero" zero.

    Definition one
      := Pipeline.BoundsPipeline
           true (* subst01 *)
           None (* fancy *)
           possible_values
           (reified_one_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify n @ GallinaReify.Reify m @ GallinaReify.Reify m')
           tt
           (Some bounds).

    Definition sone (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "one" one.

    Definition selectznz : Pipeline.ErrorT _ := Primitives.selectznz n machine_wordsize.
    Definition sselectznz (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Primitives.sselectznz n machine_wordsize prefix.

    Local Notation valid := (Arithmetic.WordByWordMontgomery.valid machine_wordsize n m).
    Local Notation bytes_valid := (Arithmetic.WordByWordMontgomery.valid 8 n_bytes m).

    Lemma bounded_by_of_valid x
          (H : valid x)
      : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some bounds) x = true.
    Proof using curve_good.
      pose proof use_curve_good as use_curve_good.
      clear -H use_curve_good curve_good.
      destruct H as [H _]; destruct_head'_and.
      cbv [small] in H.
      cbv [ZRange.type.base.option.is_bounded_by bounds saturated_bounds saturated_bounds_list Option.invert_Some].
      replace n with (List.length x) by now rewrite H, Partition.length_partition.
      rewrite <- map_const, fold_andb_map_map1, fold_andb_map_iff.
      cbv [ZRange.type.base.is_bounded_by is_bounded_by_bool lower upper].
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
      { cbv [Partition.partition seq map In]; tauto. }
      { intros *; rewrite Partition.partition_step, in_app_iff; cbn [List.In].
        intros; destruct_head'_or; subst *; eauto; try tauto; [].
        rewrite UniformWeight.uweight_S by lia.
        assert (0 < UniformWeight.uweight machine_wordsize n') by now apply UniformWeight.uwprops.
        assert (0 < 2 ^ machine_wordsize) by auto with zarith.
        assert (0 < 2 ^ machine_wordsize * UniformWeight.uweight machine_wordsize n') by nia.
        rewrite <- Z.mod_pull_div by lia.
        rewrite Z.le_sub_1_iff.
        auto with zarith. }
    Qed.

    (* XXX FIXME *)
    Lemma bounded_by_prime_bounds_of_valid_gen lgr n' x
          (Hlgr : 0 < lgr)
          (Hs : s = 2^Z.log2 s)
          (Hs' : s <= UniformWeight.uweight lgr n')
          (H : WordByWordMontgomery.valid lgr n' m x)
      : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) (Some (List.map (fun v => Some r[0~>v]%zrange) (Partition.partition (UniformWeight.uweight lgr) n' (s-1)))) x = true.
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
      rewrite !Partition.recursive_partition_equiv by now apply UniformWeight.uwprops.
      rename x into x'.
      generalize dependent (eval (n:=n') lgr x').
      cbv [m].
      intro x; intros ???; subst x'.
      assert (H' : 0 <= x < s) by lia.
      revert H'; generalize x; clear dependent x.
      replace s with (2^Z.log2 s) by easy.
      clear Hs.
      assert (1 < s) by lia.
      assert (0 < Z.log2 s) by now apply Z.log2_pos.
      assert (H' : 1 < 2^Z.log2 s) by auto with zarith; revert H'.
      generalize (Z.log2 s); intro lgs.
      revert lgs.
      induction n' as [|n' IHn']; [ cbn; tauto | ].
      cbn [Partition.recursive_partition List.combine List.In] in *.
      rewrite UniformWeight.uweight_1, weight_0, Z.div_1_r by ((now apply UniformWeight.uwprops) || lia).
      intros lgs ?.
      assert (0 < 2^lgr) by auto with zarith.
      assert (1 < 2^lgr) by auto with zarith.
      intros; destruct_head'_or; [ rewrite Bool.andb_true_iff, !Z.leb_le | ];
        inversion_prod; subst *.
      { push_Zmod; pull_Zmod; autorewrite with zsimplify_const.
        (*rewrite Z_mod_nz_opp_full by (Z.rewrite_mod_small; lia).
        Z.rewrite_mod_small.
        rewrite Z.le_sub_1_iff; auto with zarith. }
      { rewrite <- Z.add_opp_r, !Z.div_add_l', !Z_div_nz_opp_full, !Z.div_1_l, !Z.sub_0_l, !Z.add_opp_r in * by (Z.rewrite_mod_small; lia).
        rewrite !UniformWeight.uweight_recursive_partition_change_start with (i:=1%nat) (j:=0%nat) in * by lia.
        eapply IHn'; [ | eassumption ].
        Z.generalize_div_eucl x (2^lgr); intros; subst *.
        nia. }*)
    Admitted.

    Lemma length_of_valid lgr n' x
          (H : WordByWordMontgomery.valid lgr n' m x)
      : List.length x = n'.
    Proof using Type.
      destruct H as [H _]; rewrite H.
      now autorewrite with distr_length.
    Qed.

    Lemma bounded_by_prime_bounds_of_valid x
          (H : valid x)
      : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) prime_bounds x = true.
    Proof using curve_good.
      pose proof use_curve_good as use_curve_good.
      destruct_head'_and.
      now apply bounded_by_prime_bounds_of_valid_gen.
    Qed.

    Lemma bounded_by_prime_bytes_bounds_of_bytes_valid x
          (H : bytes_valid x)
      : ZRange.type.base.option.is_bounded_by (t:=base.type.list base.type.Z) prime_bytes_bounds x = true.
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
      cbv [m UniformWeight.uweight] in *; destruct_head'_and; lia.
    Qed.

    Local Ltac solve_extra_bounds_side_conditions :=
      solve [ cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; cbv [m] in *; lia
            | cbv [valid small eval UniformWeight.uweight n_bytes] in *; destruct_head'_and; auto
            | now apply weight_bounded_of_bytes_valid
            | eapply length_of_valid; eassumption ].

    Hint Rewrite
          (@eval_mulmod machine_wordsize n m r' m')
          (@eval_squaremod machine_wordsize n m r' m')
          (@eval_addmod machine_wordsize n m r' m')
          (@eval_submod machine_wordsize n m r' m')
          (@eval_oppmod machine_wordsize n m r' m')
          (@eval_from_montgomerymod machine_wordsize n m r' m')
          (@eval_encodemod machine_wordsize n m r' m')
          eval_to_bytesmod
          eval_from_bytesmod
          using solve [ eauto using length_of_valid | congruence | solve_extra_bounds_side_conditions ] : push_eval.
    (* needed for making [autorewrite] fast enough *)
    Local Opaque
          Arithmetic.WordByWordMontgomery.onemod
          Arithmetic.WordByWordMontgomery.from_montgomerymod
          Arithmetic.WordByWordMontgomery.mulmod
          Arithmetic.WordByWordMontgomery.squaremod
          Arithmetic.WordByWordMontgomery.encodemod
          Arithmetic.WordByWordMontgomery.addmod
          Arithmetic.WordByWordMontgomery.submod
          Arithmetic.WordByWordMontgomery.oppmod
          Arithmetic.WordByWordMontgomery.to_bytesmod.
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
                   | progress autorewrite with interp interp_gen_cache push_eval
                   | progress autounfold with push_eval
                   | progress autorewrite with distr_length in *
                   | solve [ cbv [valid small eval UniformWeight.uweight n_bytes] in *; destruct_head'_and; auto ] ].

    (** TODO: DESIGN DECISION:

        The correctness lemmas for most of the montgomery things are
        parameterized over a `from_montgomery`.  When filling this in
        for, e.g., mul-correctness, should I use `from_montgomery`
        from arithmetic, or should I use `Interp
        reified_from_montgomery` (the post-pipeline version), and take
        in success of the pipeline on `from_montgomery` as well? *)

    Local Notation from_montgomery_res := (from_montgomerymod machine_wordsize n m m').

    Lemma mul_correct res
          (Hres : mul = Success res)
      : mul_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness mulmod_correct. Qed.

    Lemma square_correct res
          (Hres : square = Success res)
      : square_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness squaremod_correct. Qed.

    Lemma add_correct res
          (Hres : add = Success res)
      : add_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness addmod_correct. Qed.

    Lemma sub_correct res
          (Hres : sub = Success res)
      : sub_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness submod_correct. Qed.

    Lemma opp_correct res
          (Hres : opp = Success res)
      : opp_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness oppmod_correct. Qed.

    Lemma from_montgomery_correct res
          (Hres : from_montgomery = Success res)
      : from_montgomery_correct machine_wordsize n m r' valid (Interp res).
    Proof using curve_good. prove_correctness from_montgomerymod_correct. Qed.

    Lemma nonzero_correct res
          (Hres : nonzero = Success res)
      : nonzero_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness nonzeromod_correct. Qed.

    Lemma to_bytes_correct res
          (Hres : to_bytes = Success res)
      : to_bytes_correct machine_wordsize n n_bytes m valid (Interp res).
    Proof using curve_good. prove_correctness to_bytesmod_correct. Qed.

    Lemma from_bytes_correct res
          (Hres : from_bytes = Success res)
      : from_bytes_correct machine_wordsize n n_bytes m valid bytes_valid (Interp res).
    Proof using curve_good. prove_correctness eval_from_bytesmod_and_partitions. Qed.

    Strategy -1000 [encode]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
    Lemma encode_correct res
          (Hres : encode = Success res)
      : encode_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness encodemod_correct. Qed.

    Strategy -1000 [zero]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
    Lemma zero_correct res
          (Hres : zero = Success res)
      : zero_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness encodemod_correct. Qed.

    Strategy -1000 [one]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
    Lemma one_correct res
          (Hres : one = Success res)
      : one_correct machine_wordsize n m valid from_montgomery_res (Interp res).
    Proof using curve_good. prove_correctness encodemod_correct. Qed.

    Local Opaque Pipeline.BoundsPipeline. (* need this or else [eapply Pipeline.BoundsPipeline_correct in Hres] takes forever *)
    Lemma selectznz_correct res
          (Hres : selectznz = Success res)
      : selectznz_correct machine_wordsize n saturated_bounds_list (Interp res).
    Proof using curve_good. Primitives.prove_correctness use_curve_good. Qed.

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
        := [("mul", smul);
              ("square", ssquare);
              ("add", sadd);
              ("sub", ssub);
              ("opp", sopp);
              ("from_montgomery", sfrom_montgomery);
              ("nonzero", snonzero);
              ("selectznz", sselectznz);
              ("to_bytes", sto_bytes);
              ("from_bytes", sfrom_bytes)].

      Definition valid_names : string := Eval compute in String.concat ", " (List.map (@fst _ _) known_functions).

      (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
      Definition Synthesize (function_name_prefix : string) (requests : list string)
        : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t (* types used *)
        := Primitives.Synthesize
             machine_wordsize valid_names known_functions (fun _ => nil)
             function_name_prefix requests.
    End for_stringification.
  End __.
End WordByWordMontgomery.

Module Import InvertHighLow.
  Section with_wordmax.
    Context (log2wordmax : Z) (consts : list Z).
    Let wordmax := 2 ^ log2wordmax.
    Let half_bits := log2wordmax / 2.
    Let wordmax_half_bits := 2 ^ half_bits.

    Inductive kind_of_constant := upper_half (c : BinInt.Z) | lower_half (c : BinInt.Z).

    Definition constant_to_scalar_single (const x : BinInt.Z) : option kind_of_constant :=
      if x =? (BinInt.Z.shiftr const half_bits)
      then Some (upper_half const)
      else if x =? (BinInt.Z.land const (wordmax_half_bits - 1))
           then Some (lower_half const)
           else None.

    Definition constant_to_scalar (x : BinInt.Z)
      : option kind_of_constant :=
      fold_right (fun c res => match res with
                            | Some s => Some s
                            | None => constant_to_scalar_single c x
                            end) None consts.

    Definition invert_low (v : BinInt.Z) : option BinInt.Z
      := match constant_to_scalar v with
         | Some (lower_half v) => Some v
         | _ => None
         end.

    Definition invert_high (v : BinInt.Z) : option BinInt.Z
      := match constant_to_scalar v with
         | Some (upper_half v) => Some v
         | _ => None
         end.
  End with_wordmax.
End InvertHighLow.

(** TODO: Port Barrett and Montgomery to the new glue style, and remove these tactics.  These tactics are only needed for the old-glue-style derivations. *)
Require Import Crypto.Util.Equality. (* fg_equal_rel *)
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.GetGoal.
Ltac peel_interp_app _ :=
  lazymatch goal with
  | [ |- ?R' (?InterpE ?arg) (?f ?arg) ]
    => apply fg_equal_rel; [ | reflexivity ];
       try peel_interp_app ()
  | [ |- ?R' (Interp ?ev) (?f ?x) ]
    => let sv := type of x in
       let fx := constr:(f x) in
       let dv := type of fx in
       let rs := reify_type sv in
       let rd := reify_type dv in
       etransitivity;
       [ apply @expr.Interp_APP_rel_reflexive with (s:=rs) (d:=rd) (R:=R');
         typeclasses eauto
       | apply fg_equal_rel;
         [ try peel_interp_app ()
         | try lazymatch goal with
               | [ |- ?R (Interp ?ev) (Interp _) ]
                 => reflexivity
               | [ |- ?R (Interp ?ev) ?c ]
                 => let rc := constr:(GallinaReify.Reify c) in
                    unify ev rc; vm_compute; reflexivity
               end ] ]
  end.
Ltac pre_cache_reify _ :=
  let H' := fresh in
  lazymatch goal with
  | [ |- ?P /\ Wf ?e ]
    => let P' := fresh in
       evar (P' : Prop);
       assert (H' : P' /\ Wf e); subst P'
  end;
  [
      | split; [ destruct H' as [H' _] | destruct H' as [_ H']; exact H' ];
        cbv [type.app_curried];
        let arg := fresh "arg" in
        let arg2 := fresh in
        intros arg arg2;
        cbn [type.and_for_each_lhs_of_arrow type.eqv];
        let H := fresh in
        intro H;
        repeat match type of H with
               | and _ _ => let H' := fresh in
                            destruct H as [H' H];
                            rewrite <- H'
               end;
        clear dependent arg2; clear H;
        intros _;
        peel_interp_app ();
        [ lazymatch goal with
          | [ |- ?R (Interp ?ev) _ ]
            => (tryif is_evar ev
                 then let ev' := fresh "ev" in set (ev' := ev)
                 else idtac)
          end;
          cbv [pointwise_relation];
          repeat lazymatch goal with
                 | [ H : _ |- _ ] => first [ constr_eq H H'; fail 1
                                           | revert H ]
                 end;
          eexact H'
        | .. ] ];
  [ intros; clear | .. ].
Ltac do_inline_cache_reify do_if_not_cached :=
  pre_cache_reify ();
  [ try solve [
          cbv beta zeta;
          repeat match goal with H := ?e |- _ => is_evar e; subst H end;
          try solve [ split; [ solve [ eauto with nocore reify_gen_cache ] | solve [ eauto with wf_gen_cache; prove_Wf () ] ] ];
          do_if_not_cached ()
        ];
    cache_reify ()
  | .. ].

(* TODO: MOVE ME *)
Ltac vm_compute_lhs_reflexivity :=
  lazymatch goal with
  | [ |- ?LHS = ?RHS ]
    => let x := (eval vm_compute in LHS) in
       (* we cannot use the unify tactic, which just gives "not
          unifiable" as the error message, because we want to see the
          terms that were not unifable.  See also
          COQBUG(https://github.com/coq/coq/issues/7291) *)
       let _unify := constr:(ltac:(reflexivity) : RHS = x) in
       vm_cast_no_check (eq_refl x)
  end.

Ltac solve_rop' rop_correct do_if_not_cached machine_wordsizev :=
  eapply rop_correct with (machine_wordsize:=machine_wordsizev);
  [ do_inline_cache_reify do_if_not_cached
  | subst_evars; vm_compute_lhs_reflexivity (* lazy; reflexivity *) ].
Ltac solve_rop_nocache rop_correct :=
  solve_rop' rop_correct ltac:(fun _ => idtac).
Ltac solve_rop rop_correct :=
  solve_rop'
    rop_correct
    ltac:(fun _ => let G := get_goal in fail 2 "Could not find a solution in reify_gen_cache for" G).

Module BarrettReduction.
  (* TODO : generalize to multi-word and operate on (list Z) instead of T; maybe stop taking ops as context variables *)
  Section Generic.
    Context {T} (rep : T -> Z -> Prop)
            (k : Z) (k_pos : 0 < k)
            (low : T -> Z)
            (low_correct : forall a x, rep a x -> low a = x mod 2 ^ k)
            (shiftr : T -> Z -> T)
            (shiftr_correct : forall a x n,
                rep a x ->
                0 <= n <= k ->
                rep (shiftr a n) (x / 2 ^ n))
            (mul_high : T -> T -> Z -> T)
            (mul_high_correct : forall a b x y x0y1,
                rep a x ->
                rep b y ->
                2 ^ k <= x < 2^(k+1) ->
                0 <= y < 2^(k+1) ->
                x0y1 = x mod 2 ^ k * (y / 2 ^ k) ->
                rep (mul_high a b x0y1) (x * y / 2 ^ k))
            (mul : Z -> Z -> T)
            (mul_correct : forall x y,
                0 <= x < 2^k ->
                0 <= y < 2^k ->
                rep (mul x y) (x * y))
            (sub : T -> T -> T)
            (sub_correct : forall a b x y,
                rep a x ->
                rep b y ->
                0 <= x - y < 2^k * 2^k ->
                rep (sub a b) (x - y))
            (cond_sub1 : T -> Z -> Z)
            (cond_sub1_correct : forall a x y,
                rep a x ->
                0 <= x < 2 * y ->
                0 <= y < 2 ^ k ->
                cond_sub1 a y = if (x <? 2 ^ k) then x else x - y)
            (cond_sub2 : Z -> Z -> Z)
            (cond_sub2_correct : forall x y, cond_sub2 x y = if (x <? y) then x else x - y).
    Context (xt mut : T) (M muSelect: Z).

    Let mu := 2 ^ (2 * k) / M.
    Context x (mu_rep : rep mut mu) (x_rep : rep xt x).
    Context (M_nz : 0 < M)
            (x_range : 0 <= x < M * 2 ^ k)
            (M_range : 2 ^ (k - 1) < M < 2 ^ k)
            (M_good : 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - mu)
            (muSelect_correct: muSelect = mu mod 2 ^ k * (x / 2 ^ (k - 1) / 2 ^ k)).

    Definition qt :=
      dlet_nd muSelect := muSelect in (* makes sure muSelect is not inlined in the output *)
      dlet_nd q1 := shiftr xt (k - 1) in
      dlet_nd twoq := mul_high mut q1 muSelect in
      shiftr twoq 1.
    Definition reduce  :=
      dlet_nd qt := qt in
      dlet_nd r2 := mul (low qt) M in
      dlet_nd r := sub xt r2 in
      let q3 := cond_sub1 r M in
      cond_sub2 q3 M.

    Lemma looser_bound : M * 2 ^ k < 2 ^ (2*k).
    Proof. clear -M_range M_nz x_range k_pos; rewrite <-Z.add_diag, Z.pow_add_r; nia. Qed.

    Lemma pow_2k_eq : 2 ^ (2*k) = 2 ^ (k - 1) * 2 ^ (k + 1).
    Proof. clear -k_pos; rewrite <-Z.pow_add_r by omega. f_equal; ring. Qed.

    Lemma mu_bounds : 2 ^ k <= mu < 2^(k+1).
    Proof.
      pose proof looser_bound.
      subst mu. split.
      { apply Z.div_le_lower_bound; omega. }
      { apply Z.div_lt_upper_bound; try omega.
        rewrite pow_2k_eq; apply Z.mul_lt_mono_pos_r; auto with zarith. }
    Qed.

    Lemma shiftr_x_bounds : 0 <= x / 2 ^ (k - 1) < 2^(k+1).
    Proof.
      pose proof looser_bound.
      split; [ solve [Z.zero_bounds] | ].
      apply Z.div_lt_upper_bound; auto with zarith.
      rewrite <-pow_2k_eq. omega.
    Qed.
    Hint Resolve shiftr_x_bounds.

    Ltac solve_rep := eauto using shiftr_correct, mul_high_correct, mul_correct, sub_correct with omega.

    Let q := mu * (x / 2 ^ (k - 1)) / 2 ^ (k + 1).

    Lemma q_correct : rep qt q .
    Proof.
      pose proof mu_bounds. cbv [qt]; subst q.
      rewrite Z.pow_add_r, <-Z.div_div by Z.zero_bounds.
      solve_rep.
    Qed.
    Hint Resolve q_correct.

    Lemma x_mod_small : x mod 2 ^ (k - 1) <= M.
    Proof. transitivity (2 ^ (k - 1)); auto with zarith. Qed.
    Hint Resolve x_mod_small.

    Lemma q_bounds : 0 <= q < 2 ^ k.
    Proof.
      pose proof looser_bound. pose proof x_mod_small. pose proof mu_bounds.
      split; subst q; [ solve [Z.zero_bounds] | ].
      edestruct q_nice_strong with (n:=M) as [? Hqnice];
        try rewrite Hqnice; auto; try omega; [ ].
      apply Z.le_lt_trans with (m:= x / M).
      { break_match; omega. }
      { apply Z.div_lt_upper_bound; omega. }
    Qed.

    Lemma two_conditional_subtracts :
      forall a x,
      rep a x ->
      0 <= x < 2 * M ->
      cond_sub2 (cond_sub1 a M) M = cond_sub2 (cond_sub2 x M) M.
    Proof.
      intros.
      erewrite !cond_sub2_correct, !cond_sub1_correct by (eassumption || omega).
      break_match; Z.ltb_to_lt; try lia; discriminate.
    Qed.

    Lemma r_bounds : 0 <= x - q * M < 2 * M.
    Proof.
      pose proof looser_bound. pose proof q_bounds. pose proof x_mod_small.
      subst q mu; split.
      { Z.zero_bounds. apply qn_small; omega. }
      { apply r_small_strong; rewrite ?Z.pow_1_r; auto; omega. }
    Qed.

    Lemma reduce_correct : reduce = x mod M.
    Proof.
      pose proof looser_bound. pose proof r_bounds. pose proof q_bounds.
      assert (2 * M < 2^k * 2^k) by nia.
      rewrite barrett_reduction_small with (k:=k) (m:=mu) (offset:=1) (b:=2) by (auto; omega).
      cbv [reduce Let_In].
      erewrite low_correct by eauto. Z.rewrite_mod_small.
      erewrite two_conditional_subtracts by solve_rep.
      rewrite !cond_sub2_correct.
      subst q; reflexivity.
    Qed.
  End Generic.

  Section BarrettReduction.
    Context (k : Z) (k_bound : 2 <= k).
    Context (M muLow : Z).
    Context (M_pos : 0 < M)
            (muLow_eq : muLow + 2^k = 2^(2*k) / M)
            (muLow_bounds : 0 <= muLow < 2^k)
            (M_bound1 : 2 ^ (k - 1) < M < 2^k)
            (M_bound2: 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - (muLow + 2^k)).

    Context (n:nat) (Hn_nz: n <> 0%nat) (n_le_k : Z.of_nat n <= k).
    Context (nout : nat) (Hnout : nout = 2%nat).
    Let w := weight k 1.
    Local Lemma k_range : 0 < 1 <= k. Proof. omega. Qed.
    Let props : @weight_properties w := wprops k 1 k_range.

    Hint Rewrite Positional.eval_nil Positional.eval_snoc : push_eval.

    Definition low (t : list Z) : Z := nth_default 0 t 0.
    Definition high (t : list Z) : Z := nth_default 0 t 1.
    Definition represents (t : list Z) (x : Z) :=
      t = [x mod 2^k; x / 2^k] /\ 0 <= x < 2^k * 2^k.

    Lemma represents_eq t x :
      represents t x -> t = [x mod 2^k; x / 2^k].
    Proof. cbv [represents]; tauto. Qed.

    Lemma represents_length t x : represents t x -> length t = 2%nat.
    Proof. cbv [represents]; intuition. subst t; reflexivity. Qed.

    Lemma represents_low t x :
      represents t x -> low t = x mod 2^k.
    Proof. cbv [represents]; intros; rewrite (represents_eq t x) by auto; reflexivity. Qed.

    Lemma represents_high t x :
      represents t x -> high t = x / 2^k.
    Proof. cbv [represents]; intros; rewrite (represents_eq t x) by auto; reflexivity. Qed.

    Lemma represents_low_range t x :
      represents t x -> 0 <= x mod 2^k < 2^k.
    Proof. auto with zarith. Qed.

    Lemma represents_high_range t x :
      represents t x -> 0 <= x / 2^k < 2^k.
    Proof.
      destruct 1 as [? [? ?] ]; intros.
      auto using Z.div_lt_upper_bound with zarith.
    Qed.
    Hint Resolve represents_length represents_low_range represents_high_range.

    Lemma represents_range t x :
      represents t x -> 0 <= x < 2^k*2^k.
    Proof. cbv [represents]; tauto. Qed.

    Lemma represents_id x :
      0 <= x < 2^k * 2^k ->
      represents [x mod 2^k; x / 2^k] x.
    Proof.
      intros; cbv [represents]; autorewrite with cancel_pair.
      Z.rewrite_mod_small; tauto.
    Qed.

    Local Ltac push_rep :=
      repeat match goal with
             | H : represents ?t ?x |- _ => unique pose proof (represents_low_range _ _ H)
             | H : represents ?t ?x |- _ => unique pose proof (represents_high_range _ _ H)
             | H : represents ?t ?x |- _ => rewrite (represents_low t x) in * by assumption
             | H : represents ?t ?x |- _ => rewrite (represents_high t x) in * by assumption
             end.

    Definition shiftr (t : list Z) (n : Z) : list Z :=
      [Z.rshi (2^k) (high t) (low t) n; Z.rshi (2^k) 0 (high t) n].

    Lemma shiftr_represents a i x :
      represents a x ->
      0 <= i <= k ->
      represents (shiftr a i) (x / 2 ^ i).
    Proof.
      cbv [shiftr]; intros; push_rep.
      match goal with H : _ |- _ => pose proof (represents_range _ _ H) end.
      assert (0 < 2 ^ i) by auto with zarith.
      assert (x < 2 ^ i * 2 ^ k * 2 ^ k) by nia.
      assert (0 <= x / 2 ^ k / 2 ^ i < 2 ^ k) by
          (split; Z.zero_bounds; auto using Z.div_lt_upper_bound with zarith).
      repeat match goal with
             | _ => rewrite Z.rshi_correct by auto with zarith
             | _ => rewrite <-Z.div_mod''' by auto with zarith
             | _ => progress autorewrite with zsimplify_fast
             | _ => progress Z.rewrite_mod_small
             | |- context [represents [(?a / ?c) mod ?b; ?a / ?b / ?c] ] =>
               rewrite (Z.div_div_comm a b c) by auto with zarith
             | _ => solve [auto using represents_id, Z.div_lt_upper_bound with zarith lia]
             end.
    Qed.

    Context (Hw : forall i, w i = (2 ^ k) ^ Z.of_nat i).
    Ltac change_weight := rewrite !Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r.

    Definition wideadd t1 t2 := fst (Rows.add w 2 t1 t2).
    (* TODO: use this definition once issue #352 is resolved *)
    (* Definition widesub t1 t2 := fst (Rows.sub w 2 t1 t2). *)
    Definition widesub (t1 t2 : list Z) :=
      let t1_0 := hd 0 t1 in
      let t1_1 := hd 0 (tl t1) in
      let t2_0 := hd 0 t2 in
      let t2_1 := hd 0 (tl t2) in
      dlet_nd x0 := Z.sub_get_borrow_full (2^k) t1_0 t2_0 in
      dlet_nd x1 := Z.sub_with_get_borrow_full (2^k) (snd x0) t1_1 t2_1 in
      [fst x0; fst x1].
    Definition widemul := BaseConversion.widemul_inlined k n nout.

    Lemma partition_represents x :
      0 <= x < 2^k*2^k ->
      represents (Partition.partition w 2 x) x.
    Proof.
      intros; cbn. change_weight.
      Z.rewrite_mod_small.
      autorewrite with zsimplify_fast.
      auto using represents_id.
    Qed.

    Lemma eval_represents t x :
      represents t x -> eval w 2 t = x.
    Proof.
      intros; rewrite (represents_eq t x) by assumption.
      cbn. change_weight; push_rep.
      autorewrite with zsimplify. reflexivity.
    Qed.

    Ltac wide_op partitions_pf :=
      repeat match goal with
             | _ => rewrite partitions_pf by eauto
             | _ => rewrite partitions_pf by auto with zarith
             | _ => erewrite eval_represents by eauto
             | _ => solve [auto using partition_represents, represents_id]
             end.

    Lemma wideadd_represents t1 t2 x y :
      represents t1 x ->
      represents t2 y ->
      0 <= x + y < 2^k*2^k ->
      represents (wideadd t1 t2) (x + y).
    Proof. intros; cbv [wideadd]. wide_op Rows.add_partitions. Qed.

    Lemma widesub_represents t1 t2 x y :
      represents t1 x ->
      represents t2 y ->
      0 <= x - y < 2^k*2^k ->
      represents (widesub t1 t2) (x - y).
    Proof.
      intros; cbv [widesub Let_In].
      rewrite (represents_eq t1 x) by assumption.
      rewrite (represents_eq t2 y) by assumption.
      cbn [hd tl].
      autorewrite with to_div_mod.
      pull_Zmod.
      match goal with |- represents [?m; ?d] ?x =>
                      replace d with (x / 2 ^ k); [solve [auto using represents_id] |] end.
      rewrite <-(Z.mod_small ((x - y) / 2^k) (2^k)) by (split; try apply Z.div_lt_upper_bound; Z.zero_bounds).
      f_equal.
      transitivity ((x mod 2^k - y mod 2^k + 2^k * (x / 2 ^ k) - 2^k * (y / 2^k)) / 2^k). {
        rewrite (Z.div_mod x (2^k)) at 1 by auto using Z.pow_nonzero with omega.
        rewrite (Z.div_mod y (2^k)) at 1 by auto using Z.pow_nonzero with omega.
        f_equal. ring. }
      autorewrite with zsimplify.
      ring.
    Qed.
    (* Works with Rows.sub-based widesub definition
    Proof. intros; cbv [widesub]. wide_op Rows.sub_partitions. Qed.
    *)

    (* TODO: MOVE Equivlalent Keys decl to Arithmetic? *)
    Declare Equivalent Keys BaseConversion.widemul BaseConversion.widemul_inlined.
    Lemma widemul_represents x y :
      0 <= x < 2^k ->
      0 <= y < 2^k ->
      represents (widemul x y) (x * y).
    Proof.
      intros; cbv [widemul].
      assert (0 <= x * y < 2^k*2^k) by auto with zarith.
      wide_op BaseConversion.widemul_correct.
    Qed.

    Definition mul_high (a b : list Z) a0b1 : list Z :=
      dlet_nd a0b0 := widemul (low a) (low b) in
      dlet_nd ab := wideadd [high a0b0; high b] [low b; 0] in
      wideadd ab [a0b1; 0].

    Lemma mul_high_idea d a b a0 a1 b0 b1 :
      d <> 0 ->
      a = d * a1 + a0 ->
      b = d * b1 + b0 ->
      (a * b) / d = a0 * b0 / d + d * a1 * b1 + a1 * b0 + a0 * b1.
    Proof.
      intros. subst a b. autorewrite with push_Zmul.
      ring_simplify_subterms. rewrite Z.pow_2_r.
      rewrite Z.div_add_exact by (push_Zmod; autorewrite with zsimplify; omega).
      repeat match goal with
             | |- context [d * ?a * ?b * ?c] =>
               replace (d * a * b * c) with (a * b * c * d) by ring
             | |- context [d * ?a * ?b] =>
               replace (d * a * b) with (a * b * d) by ring
             end.
      rewrite !Z.div_add by omega.
      autorewrite with zsimplify.
      rewrite (Z.mul_comm a0 b0).
      ring_simplify. ring.
    Qed.

    Lemma represents_trans t x y:
      represents t y -> y = x ->
      represents t x.
    Proof. congruence. Qed.

    Lemma represents_add x y :
      0 <= x < 2 ^ k ->
      0 <= y < 2 ^ k ->
      represents [x;y] (x + 2^k*y).
    Proof.
      intros; cbv [represents]; autorewrite with zsimplify.
      repeat split; (reflexivity || nia).
    Qed.

    Lemma represents_small x :
      0 <= x < 2^k ->
      represents [x; 0] x.
    Proof.
      intros.
      eapply represents_trans.
      { eauto using represents_add with zarith. }
      { ring. }
    Qed.

    Lemma mul_high_represents a b x y a0b1 :
      represents a x ->
      represents b y ->
      2^k <= x < 2^(k+1) ->
      0 <= y < 2^(k+1) ->
      a0b1 = x mod 2^k * (y / 2^k) ->
      represents (mul_high a b a0b1) ((x * y) / 2^k).
    Proof.
      cbv [mul_high Let_In]; rewrite Z.pow_add_r, Z.pow_1_r by omega; intros.
      assert (4 <= 2 ^ k) by (transitivity (Z.pow 2 2); auto with zarith).
      assert (0 <= x * y / 2^k < 2^k*2^k) by (Z.div_mod_to_quot_rem_in_goal; nia).

      rewrite mul_high_idea with (a:=x) (b:=y) (a0 := low a) (a1 := high a) (b0 := low b) (b1 := high b) in *
        by (push_rep; Z.div_mod_to_quot_rem_in_goal; lia).

      push_rep. subst a0b1.
      assert (y / 2 ^ k < 2) by (apply Z.div_lt_upper_bound; omega).
      replace (x / 2 ^ k) with 1 in * by (rewrite Z.div_between_1; lia).
      autorewrite with zsimplify_fast in *.

      eapply represents_trans.
      { repeat (apply wideadd_represents;
                [ | apply represents_small; Z.div_mod_to_quot_rem_in_goal; nia| ]).
        erewrite represents_high; [ | apply widemul_represents; solve [ auto with zarith ] ].
        { apply represents_add; try reflexivity; solve [auto with zarith]. }
        { match goal with H : 0 <= ?x + ?y < ?z |- 0 <= ?x < ?z =>
                          split; [ solve [Z.zero_bounds] | ];
                            eapply Z.le_lt_trans with (m:= x + y); nia
          end. }
        { omega. } }
      { ring. }
    Qed.

    Definition cond_sub1 (a : list Z) y : Z :=
      dlet_nd maybe_y := Z.zselect (Z.cc_l (high a)) 0 y in
      dlet_nd diff := Z.sub_get_borrow_full (2^k) (low a) maybe_y in
      fst diff.

    Lemma cc_l_only_bit : forall x s, 0 <= x < 2 * s -> Z.cc_l (x / s) = 0 <-> x < s.
    Proof.
      cbv [Z.cc_l]; intros.
      rewrite Z.div_between_0_if by omega.
      break_match; Z.ltb_to_lt; Z.rewrite_mod_small; omega.
    Qed.

    Lemma cond_sub1_correct a x y :
      represents a x ->
      0 <= x < 2 * y ->
      0 <= y < 2 ^ k ->
      cond_sub1 a y = if (x <? 2 ^ k) then x else x - y.
    Proof.
      intros; cbv [cond_sub1 Let_In]. rewrite Z.zselect_correct. push_rep.
      break_match; Z.ltb_to_lt; rewrite cc_l_only_bit in *; try omega;
        autorewrite with zsimplify_fast to_div_mod pull_Zmod; auto with zarith.
    Qed.

    Definition cond_sub2 x y := Z.add_modulo x 0 y.
    Lemma cond_sub2_correct x y :
      cond_sub2 x y = if (x <? y) then x else x - y.
    Proof.
      cbv [cond_sub2]. rewrite Z.add_modulo_correct.
      autorewrite with zsimplify_fast. break_match; Z.ltb_to_lt; omega.
    Qed.

    Section Defn.
      Context (xLow xHigh : Z) (xLow_bounds : 0 <= xLow < 2^k) (xHigh_bounds : 0 <= xHigh < M).
      Let xt := [xLow; xHigh].
      Let x := xLow + 2^k * xHigh.

      Lemma x_rep : represents xt x.
      Proof. cbv [represents]; subst xt x; autorewrite with cancel_pair zsimplify; repeat split; nia. Qed.

      Lemma x_bounds : 0 <= x < M * 2 ^ k.
      Proof. subst x; nia. Qed.

      Definition muSelect := Z.zselect (Z.cc_m (2 ^ k) xHigh) 0 muLow.

      Local Hint Resolve Z.div_nonneg Z.div_lt_upper_bound.
      Local Hint Resolve shiftr_represents mul_high_represents widemul_represents widesub_represents
            cond_sub1_correct cond_sub2_correct represents_low represents_add.

      Lemma muSelect_correct :
        muSelect = (2 ^ (2 * k) / M) mod 2 ^ k * ((x / 2 ^ (k - 1)) / 2 ^ k).
      Proof.
        (* assertions to help arith tactics *)
        pose proof x_bounds.
        assert (2^k * M < 2 ^ (2*k)) by (rewrite <-Z.add_diag, Z.pow_add_r; nia).
        assert (0 <= x / (2 ^ k * (2 ^ k / 2)) < 2) by (Z.div_mod_to_quot_rem_in_goal; auto with nia).
        assert (0 < 2 ^ k / 2) by Z.zero_bounds.
        assert (2 ^ (k - 1) <> 0) by auto with zarith.
        assert (2 < 2 ^ k) by (eapply Z.le_lt_trans with (m:=2 ^ 1); auto with zarith).

        cbv [muSelect]. rewrite <-muLow_eq.
        rewrite Z.zselect_correct, Z.cc_m_eq by auto with zarith.
        replace xHigh with (x / 2^k) by (subst x; autorewrite with zsimplify; lia).
        autorewrite with pull_Zdiv push_Zpow.
        rewrite (Z.mul_comm (2 ^ k / 2)).
        break_match; [ ring | ].
        match goal with H : 0 <= ?x < 2, H' : ?x <> 0 |- _ => replace x with 1 by omega end.
        autorewrite with zsimplify; reflexivity.
      Qed.

      Lemma mu_rep : represents [muLow; 1] (2 ^ (2 * k) / M).
      Proof. rewrite <-muLow_eq. eapply represents_trans; auto with zarith. Qed.

      Derive barrett_reduce
             SuchThat (barrett_reduce = x mod M)
             As barrett_reduce_correct.
      Proof.
        erewrite <-reduce_correct with (rep:=represents) (muSelect:=muSelect) (k0:=k) (mut:=[muLow;1]) (xt0:=xt)
          by (auto using x_bounds, muSelect_correct, x_rep, mu_rep; omega).
        subst barrett_reduce. reflexivity.
      Qed.
    End Defn.
  End BarrettReduction.

  (* all the list operations from for_reification.ident *)
  Strategy 100 [length seq repeat combine map flat_map partition app rev fold_right update_nth nth_default ].
  Strategy -10 [barrett_reduce reduce].

  Derive reified_barrett_red_gen
         SuchThat (is_reification_of reified_barrett_red_gen barrett_reduce)
         As reified_barrett_red_gen_correct.
  Proof. Time cache_reify (). Time Qed.

  Module Export ReifyHints.
    Hint Extern 1 (_ = _) => apply_cached_reification barrett_reduce (proj1 reified_barrett_red_gen_correct) : reify_cache_gen.
    Hint Immediate (proj2 reified_barrett_red_gen_correct) : wf_gen_cache.
    Hint Rewrite (proj1 reified_barrett_red_gen_correct) : interp_gen_cache.
  End ReifyHints.
  Local Opaque reified_barrett_red_gen. (* needed for making [autorewrite] not take a very long time *)

  Section rbarrett_red.
    Context (M : Z)
            (machine_wordsize : Z).

    Let value_range := r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.
    Let flag_range := r[0 ~> 1]%zrange.
    Let bound := Some value_range.
    Let mu := (2 ^ (2 * machine_wordsize)) / M.
    Let muLow := mu mod (2 ^ machine_wordsize).
    Let consts_list := [M; muLow].

    Definition possible_values_of_machine_wordsize
      := [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
    Let possible_values := possible_values_of_machine_wordsize.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := fold_right
           (fun '(b, e) k => if b:bool then Error e else k)
           res
           [((mu / (2 ^ machine_wordsize) =? 0), Pipeline.Values_not_provably_distinctZ "mu / 2 ^ k ≠ 0" (mu / 2 ^ machine_wordsize) 0);
              ((machine_wordsize <? 2), Pipeline.Value_not_leZ "~ (2 <=k)" 2 machine_wordsize);
              (negb (Z.log2 M + 1 =? machine_wordsize), Pipeline.Values_not_provably_equalZ "log2(M)+1 != k" (Z.log2 M + 1) machine_wordsize);
              ((2 ^ (machine_wordsize + 1) - mu <? 2 * (2 ^ (2 * machine_wordsize) mod M)),
               Pipeline.Value_not_leZ "~ (2 * (2 ^ (2*k) mod M) <= 2^(k + 1) - mu)"
                                      (2 * (2 ^ (2*machine_wordsize) mod M))
                                      (2^(machine_wordsize + 1) - mu))].

    Let fancy_args
      := (Some {| Pipeline.invert_low log2wordsize := invert_low log2wordsize consts_list;
                  Pipeline.invert_high log2wordsize := invert_high log2wordsize consts_list;
                  Pipeline.value_range := value_range;
                  Pipeline.flag_range := flag_range |}).

    Lemma fancy_args_good
      : match fancy_args with
        | Some {| Pipeline.invert_low := il ; Pipeline.invert_high := ih |}
          => (forall s v v' : Z, il s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            /\ (forall s v v' : Z, ih s v = Some v' -> v = Z.shiftr v' (s/2))
        | None => True
        end.
    Proof.
      cbv [fancy_args invert_low invert_high constant_to_scalar constant_to_scalar_single consts_list fold_right];
        split; intros; break_innermost_match_hyps; Z.ltb_to_lt; subst; congruence.
    Qed.

    Definition barrett_red
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           fancy_args (* fancy *)
           possible_values
           (reified_barrett_red_gen
              @ GallinaReify.Reify machine_wordsize @ GallinaReify.Reify M @ GallinaReify.Reify muLow @ GallinaReify.Reify 2%nat @ GallinaReify.Reify 2%nat)
           (bound, (bound, tt))
           bound.

    Definition sbarrett_red (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "barrett_red" barrett_red.

    (* TODO: Replace the following lemmas with a new-glue-style correctness lemma, like
<<
Lemma barrett_red_correct res
          (Hres : barrett_red = Success res)
      : barrett_red_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
    Proof using curve_good. prove_correctness (). Qed.
>> *)

    Notation BoundsPipeline_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               false (* subst01 *)
               fancy_args
               fancy_args_good
               possible_values
               _
               rop
               in_bounds
               out_bounds
               _
               op
               Hrop rv)
           (only parsing).

    Definition rbarrett_red_correct
      := BoundsPipeline_correct
           (bound, (bound, tt))
           bound
           (barrett_reduce machine_wordsize M muLow 2 2).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rbarrett_red_correctT rv : Prop
      := type_of_strip_3arrow (@rbarrett_red_correct rv).
  End rbarrett_red.
End BarrettReduction.

(* TODO: After moving to new-glue-style, remove these tactics *)
Ltac solve_rbarrett_red := solve_rop BarrettReduction.rbarrett_red_correct.
Ltac solve_rbarrett_red_nocache := solve_rop_nocache BarrettReduction.rbarrett_red_correct.

Module MontgomeryReduction.
  Section MontRed'.
    Context (N R N' R' : Z).
    Context (HN_range : 0 <= N < R) (HN'_range : 0 <= N' < R) (HN_nz : N <> 0) (R_gt_1 : R > 1)
            (N'_good : Z.equiv_modulo R (N*N') (-1)) (R'_good: Z.equiv_modulo N (R*R') 1).

    Context (Zlog2R : Z) .
    Let w : nat -> Z := weight Zlog2R 1.
    Context (n:nat) (Hn_nz: n <> 0%nat) (n_good : Zlog2R mod Z.of_nat n = 0).
    Context (R_big_enough : n <= Zlog2R)
            (R_two_pow : 2^Zlog2R = R).
    Let w_mul : nat -> Z := weight (Zlog2R / n) 1.
    Context (nout : nat) (Hnout : nout = 2%nat).

    Definition montred' (lo_hi : (Z * Z)) :=
      dlet_nd y := nth_default 0 (BaseConversion.widemul_inlined Zlog2R n nout (fst lo_hi) N') 0  in
      dlet_nd t1_t2 := (BaseConversion.widemul_inlined_reverse Zlog2R n nout N y) in
      dlet_nd sum_carry := Rows.add (weight Zlog2R 1) 2 [fst lo_hi; snd lo_hi] t1_t2 in
      dlet_nd y' := Z.zselect (snd sum_carry) 0 N in
      dlet_nd lo''_carry := Z.sub_get_borrow_full R (nth_default 0 (fst sum_carry) 1) y' in
      Z.add_modulo (fst lo''_carry) 0 N.

    Local Lemma Hw : forall i, w i = R ^ Z.of_nat i.
    Proof.
      clear -R_big_enough R_two_pow; cbv [w weight]; intro.
      autorewrite with zsimplify.
      rewrite Z.pow_mul_r, R_two_pow by omega; reflexivity.
    Qed.

    Declare Equivalent Keys weight w.
    Local Ltac change_weight := rewrite !Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r, ?Z.pow_1_l in *.
    Local Ltac solve_range :=
      repeat match goal with
             | _ => progress change_weight
             | |- context [?a mod ?b] => unique pose proof (Z.mod_pos_bound a b ltac:(omega))
             | |- 0 <= _ => progress Z.zero_bounds
             | |- 0 <= _ * _ < _ * _ =>
               split; [ solve [Z.zero_bounds] | apply Z.mul_lt_mono_nonneg; omega ]
             | _ => solve [auto]
             | _ => omega
             end.

    Local Lemma eval2 x y : eval w 2 [x;y] = x + R * y.
    Proof. cbn. change_weight. ring. Qed.

    Hint Rewrite BaseConversion.widemul_inlined_reverse_correct BaseConversion.widemul_inlined_correct
         using (autorewrite with widemul push_nth_default; solve [solve_range]) : widemul.

    Lemma montred'_eq lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R):
      montred' lo_hi = reduce_via_partial N R N' T.
    Proof.
      rewrite <-reduce_via_partial_alt_eq by nia.
      cbv [montred' partial_reduce_alt reduce_via_partial_alt prereduce Let_In].
      rewrite Hlo, Hhi.
      assert (0 <= (T mod R) * N' < w 2) by  (solve_range).

      autorewrite with widemul.
      rewrite Rows.add_partitions, Rows.add_div by (distr_length; apply wprops; omega).
      rewrite R_two_pow.
      cbv [Partition.partition seq]. rewrite !eval2.
      autorewrite with push_nth_default push_map.
      autorewrite with to_div_mod. rewrite ?Z.zselect_correct, ?Z.add_modulo_correct.
      change_weight.

      (* pull out value before last modular reduction *)
      match goal with |- (if (?n <=? ?x)%Z then ?x - ?n else ?x) = (if (?n <=? ?y) then ?y - ?n else ?y)%Z =>
                      let P := fresh "H" in assert (x = y) as P; [|rewrite P; reflexivity] end.

      autorewrite with zsimplify.
      rewrite (Z.mul_comm (((T mod R) * N') mod R) N) in *.
      break_match; try reflexivity; Z.ltb_to_lt; rewrite Z.div_small_iff in * by omega;
        repeat match goal with
               | _ => progress autorewrite with zsimplify_fast
               | |- context [?x mod (R * R)] =>
                 unique pose proof (Z.mod_pos_bound x (R * R));
                   try rewrite (Z.mod_small x (R * R)) in * by Z.rewrite_mod_small_solver
               | _ => omega
               | _ => progress Z.rewrite_mod_small
               end.
    Qed.

    Lemma montred'_correct lo_hi T (HT_range: 0 <= T < R * N)
          (Hlo: fst lo_hi = T mod R) (Hhi: snd lo_hi = T / R): montred' lo_hi = (T * R') mod N.
    Proof.
      erewrite montred'_eq by eauto.
      apply Z.equiv_modulo_mod_small; auto using reduce_via_partial_correct.
      replace 0 with (Z.min 0 (R-N)) by (apply Z.min_l; omega).
      apply reduce_via_partial_in_range; omega.
    Qed.
  End MontRed'.

  Derive reified_montred_gen
         SuchThat (is_reification_of reified_montred_gen montred')
         As reified_montred_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Module Export ReifyHints.
    Hint Extern 1 (_ = _) => apply_cached_reification montred' (proj1 reified_montred_gen_correct) : reify_cache_gen.
    Hint Immediate (proj2 reified_montred_gen_correct) : wf_gen_cache.
    Hint Rewrite (proj1 reified_montred_gen_correct) : interp_gen_cache.
  End ReifyHints.
  Local Opaque reified_montred_gen. (* needed for making [autorewrite] not take a very long time *)

  Section rmontred.
    Context (N R N' : Z)
            (machine_wordsize : Z).

    Let value_range := r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.
    Let flag_range := r[0 ~> 1]%zrange.
    Let bound := Some value_range.
    Let consts_list := [N; N'].

    Definition possible_values_of_machine_wordsize
      := [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
    Local Arguments possible_values_of_machine_wordsize / .

    Let possible_values := possible_values_of_machine_wordsize.

    Definition check_args {T} (res : Pipeline.ErrorT T)
      : Pipeline.ErrorT T
      := res. (* TODO: this should actually check stuff that corresponds with preconditions of montred'_correct *)

    Let fancy_args
      := (Some {| Pipeline.invert_low log2wordsize := invert_low log2wordsize consts_list;
                  Pipeline.invert_high log2wordsize := invert_high log2wordsize consts_list;
                  Pipeline.value_range := value_range;
                  Pipeline.flag_range := flag_range |}).

    Lemma fancy_args_good
      : match fancy_args with
        | Some {| Pipeline.invert_low := il ; Pipeline.invert_high := ih |}
          => (forall s v v' : Z, il s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            /\ (forall s v v' : Z, ih s v = Some v' -> v = Z.shiftr v' (s/2))
        | None => True
        end.
    Proof.
      cbv [fancy_args invert_low invert_high constant_to_scalar constant_to_scalar_single consts_list fold_right];
        split; intros; break_innermost_match_hyps; Z.ltb_to_lt; subst; congruence.
    Qed.

    Print montred'.
    Definition montred
      := Pipeline.BoundsPipeline
           false (* subst01 *)
           fancy_args (* fancy *)
           possible_values
           (reified_montred_gen
              @ GallinaReify.Reify N @ GallinaReify.Reify R @ GallinaReify.Reify N' @ GallinaReify.Reify (Z.log2 R) @ GallinaReify.Reify 2%nat @ GallinaReify.Reify 2%nat)
           ((bound, bound), tt)
           bound.

    Definition smontred (prefix : string)
      : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
      := Eval cbv beta in FromPipelineToString prefix "montred" montred.

    (* TODO: Replace the following lemmas with a new-glue-style correctness lemma, like
<<
Lemma montred_correct res
          (Hres : montred = Success res)
      : montred_correct (weight (Qnum limbwidth) (QDen limbwidth)) n m tight_bounds loose_bounds (Interp res).
    Proof using curve_good. prove_correctness (). Qed.
>> *)

    Notation BoundsPipeline_correct in_bounds out_bounds op
      := (fun rv (rop : Expr (reify_type_of op)) Hrop
          => @Pipeline.BoundsPipeline_correct_trans
               false (* subst01 *)
               fancy_args
               fancy_args_good
               possible_values
               _
               rop
               in_bounds
               out_bounds
               _
               op
               Hrop rv)
           (only parsing).

    Definition rmontred_correct
      := BoundsPipeline_correct
           ((bound, bound), tt)
           bound
           (montred' N R N' (Z.log2 R) 2 2).

    Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
    Definition rmontred_correctT rv : Prop
      := type_of_strip_3arrow (@rmontred_correct rv).
  End rmontred.
End MontgomeryReduction.

(* TODO: After moving to new-glue-style, remove these tactics *)
Ltac solve_rmontred := solve_rop MontgomeryReduction.rmontred_correct.
Ltac solve_rmontred_nocache := solve_rop_nocache MontgomeryReduction.rmontred_correct.


Time Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (to_associational (weight 51 1) 5) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Time Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (scmul (weight 51 1) 5) in
              exact r)
               (None, (Some (repeat (@None _) 5), tt))
               ZRange.type.base.option.None).

Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f => carry_mulmod 51 1 (2^255) [(1,19)] 5 (seq 0 5 ++ [0; 1])%list%nat f f) in
              exact r)
               (Some (repeat (@None _) 5), tt)
               ZRange.type.base.option.None).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_mulx_u64" []
        true None [64; 128]
        ltac:(let r := Reify (Arithmetic.mulx 64) in
              exact r)
               (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt))%zrange
               (Some r[0~>2^64-1], Some r[0~>2^64-1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_addcarryx_u64" []
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.addcarryx 64) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_addcarryx_u51" []
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.addcarryx 51) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_subborrowx_u64" []
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.subborrowx 64) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1], Some r[0~>1])%zrange).
Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_subborrowx_u51" []
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.subborrowx 51) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^51-1], (Some r[0~>2^51-1], tt)))%zrange
               (Some r[0~>2^51-1], Some r[0~>1])%zrange).

Compute
  (Pipeline.BoundsPipelineToString
     true "fiat_" "fiat_cmovznz64" []
        true None [1; 64; 128]
        ltac:(let r := Reify (Arithmetic.cmovznz 64) in
              exact r)
               (Some r[0~>1], (Some r[0~>2^64-1], (Some r[0~>2^64-1], tt)))%zrange
               (Some r[0~>2^64-1])%zrange).
