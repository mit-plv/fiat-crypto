(** * Push-Button Synthesis of Primitives *)
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.Equality.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.LanguageWf.
Require Import Crypto.Language.
Require Import Crypto.CStringification.
Require Import Crypto.Arithmetic.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  LanguageWf.Compilers
  Language.Compilers
  CStringification.Compilers.
Import Compilers.defaults.

Import COperationSpecifications.Primitives.
Import COperationSpecifications.Solinas. (* for selectznz *)

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

(**
<<
#!/usr/bin/env python

indent = ''

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

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := [0; machine_wordsize; 2 * machine_wordsize]%Z.

  Definition possible_values_of_machine_wordsize_with_bytes
    := [0; 1; 8; machine_wordsize; 2 * machine_wordsize]%Z.

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
