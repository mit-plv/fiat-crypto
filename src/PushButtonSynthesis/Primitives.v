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
Require Import Crypto.Util.OptionList.
Require Import Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.FueledLUB.
Require Import Crypto.Util.Tactics.HasBody.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.ConstrFail.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.Language.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.Util.ErrorT.List.
Require Import Crypto.Util.ListUtil.GroupAllBy.
Require Import Crypto.Util.Strings.Show.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Crypto.Assembly.Parse.
Require Import Crypto.Assembly.Equivalence.
Import ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Wf.Compilers
  Language.WfExtra.Compilers
  Language.Compilers
  API.Compilers
  Stringification.Language.Compilers
  Stringification.Language.Compilers.ToString.
Import Compilers.API.

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

for (op, opmod) in (('id', '(@id (list Z))'), ('selectznz', 'Positional.select'), ('mulx', 'mulx'), ('addcarryx', 'addcarryx'), ('subborrowx', 'subborrowx'), ('value_barrier', 'Z.value_barrier'), ('cmovznz', 'cmovznz'), ('cmovznz_by_mul', 'cmovz_nz_by_mul')):
    print((r'''%sDerive reified_%s_gen
       SuchThat (is_reification_of reified_%s_gen %s)
       As reified_%s_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification %s (proj1 reified_%s_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_%s_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_%s_gen_correct) : interp_gen_cache.
Local Opaque reified_%s_gen. (* needed for making [autorewrite] not take a very long time *)''' % (indent, op, op, opmod, op, opmod, op, op, op, op)).replace('\n', '\n%s' % indent) + '\n')

>>
*)

Derive reified_id_gen
       SuchThat (is_reification_of reified_id_gen (@id (list Z)))
       As reified_id_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification (@id (list Z)) (proj1 reified_id_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_id_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_id_gen_correct) : interp_gen_cache.
Local Opaque reified_id_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_selectznz_gen
       SuchThat (is_reification_of reified_selectznz_gen Positional.select)
       As reified_selectznz_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification Positional.select (proj1 reified_selectznz_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_selectznz_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_selectznz_gen_correct) : interp_gen_cache.
Local Opaque reified_selectznz_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_mulx_gen
       SuchThat (is_reification_of reified_mulx_gen mulx)
       As reified_mulx_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification mulx (proj1 reified_mulx_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_mulx_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_mulx_gen_correct) : interp_gen_cache.
Local Opaque reified_mulx_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_addcarryx_gen
       SuchThat (is_reification_of reified_addcarryx_gen addcarryx)
       As reified_addcarryx_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification addcarryx (proj1 reified_addcarryx_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_addcarryx_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_addcarryx_gen_correct) : interp_gen_cache.
Local Opaque reified_addcarryx_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_subborrowx_gen
       SuchThat (is_reification_of reified_subborrowx_gen subborrowx)
       As reified_subborrowx_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification subborrowx (proj1 reified_subborrowx_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_subborrowx_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_subborrowx_gen_correct) : interp_gen_cache.
Local Opaque reified_subborrowx_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_value_barrier_gen
       SuchThat (is_reification_of reified_value_barrier_gen Z.value_barrier)
       As reified_value_barrier_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification Z.value_barrier (proj1 reified_value_barrier_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_value_barrier_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_value_barrier_gen_correct) : interp_gen_cache.
Local Opaque reified_value_barrier_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_cmovznz_gen
       SuchThat (is_reification_of reified_cmovznz_gen cmovznz)
       As reified_cmovznz_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification cmovznz (proj1 reified_cmovznz_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_cmovznz_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_cmovznz_gen_correct) : interp_gen_cache.
Local Opaque reified_cmovznz_gen. (* needed for making [autorewrite] not take a very long time *)

Derive reified_cmovznz_by_mul_gen
       SuchThat (is_reification_of reified_cmovznz_by_mul_gen cmovznz_by_mul)
       As reified_cmovznz_by_mul_gen_correct.
Proof. Time cache_reify (). Time Qed.
Global Hint Extern 1 (_ = _) => apply_cached_reification cmovznz_by_mul (proj1 reified_cmovznz_by_mul_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_cmovznz_by_mul_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_cmovznz_by_mul_gen_correct) : interp_gen_cache.
Local Opaque reified_cmovznz_by_mul_gen. (* needed for making [autorewrite] not take a very long time *)

(* needed for making [autorewrite] with [Set Keyed Unification] fast *)
Local Opaque expr.Interp.

Notation "'FromPipelineToString!' machine_wordsize prefix name result"
  := (Pipeline.FromPipelineToString machine_wordsize prefix name result)
       (only parsing, at level 10, machine_wordsize at next level, prefix at next level, name at next level, result at next level).
Notation "'FromPipelineToInternalString!' machine_wordsize prefix name result"
  := (Pipeline.FromPipelineToInternalString machine_wordsize prefix name result)
       (only parsing, at level 10, machine_wordsize at next level, prefix at next level, name at next level, result at next level).

(** Some utilities for defining [check_args] *)
Definition request_present (requests : list string) (request : string) : bool
  := List.existsb (String.eqb request) requests.
(** [None] means that the condition should hold regardless of what requests were made *)
Definition any_request_present (requests : list string) (search_for : option (list string)) : bool
  := match search_for with
     | None => true
     | Some search_for => List.existsb (request_present requests) search_for
     end.
(** Turns a list of [(precondition : bool, (check : bool, error))]
    into a [check_args] function.  The [precondition] is something
    like "this function was requested" or "this option was passed". *)
Definition check_args_of_list (check_args_descr : list (bool * (bool * Pipeline.ErrorMessage)))
           {T} (res : Pipeline.ErrorT T)
  : Pipeline.ErrorT T
  := fold_right
       (fun '(precondition, (b, e)) k => if implb precondition b then k else Error e)
       res
       check_args_descr.
Ltac prepare_use_curve_good _ :=
  let curve_good := lazymatch goal with | curve_good : ?check_args (Success tt) = Success tt |- _ => curve_good end in
  let requests := lazymatch type of curve_good with ?check_args ?requests _ = Success _ => requests end in
  revert dependent requests; clear; intros;
  lazymatch type of curve_good with
  | ?check = Success ?v => let check' := (eval hnf in check) in change (check' = Success v) in curve_good
  end;
  cbv [machine_wordsize_opt] in *;
  cbv [check_args_of_list] in *;
  cbn [List.fold_right List.map List.app] in *;
  cbv [any_request_present] in *;
  cbn [List.existsb] in *;
  repeat first [ progress cbv beta iota in *
               | progress cbn [andb orb implb] in *
               | discriminate
               | match goal with
                 | [ H : context[match ?b with true => _ | false => _ end ] |- _ ] => destruct b eqn:?
                 | [ H : context[orb _ false] |- _ ] => rewrite Bool.orb_false_r in H
                 | [ H : context[orb false _] |- _ ] => rewrite Bool.orb_false_l in H
                 end
               | progress Reflect.reflect_hyps
               | assumption
               | progress destruct_head'_and
               | apply conj ].
Ltac use_requests_to_prove_curve_good_t_step :=
  first [ progress intros
        | progress Reflect.reflect_hyps
        | exfalso; assumption
        | progress specialize_by auto 50 using or_introl, or_intror with nocore ].
Ltac prove_correctness' should_not_clear use_curve_good :=
  let should_not_clear_requests H := lazymatch type of H with context[request_present] => idtac end in
  let Hres := match goal with H : _ = Success _ |- _ => H end in
  let H := fresh in
  pose proof use_curve_good as H;
  (* I want to just use [clear -H Hres], but then I can't use any lemmas in the section because of COQBUG(https://github.com/coq/coq/issues/8153) *)
  repeat match goal with
         | [ H' : _ |- _ ]
           => tryif first [ has_body H' | constr_eq H' H | constr_eq H' Hres | should_not_clear_requests H' | should_not_clear H' ]
           then fail
           else clear H'
         end;
  cbv zeta in *;
  repeat first [ progress destruct_head'_and
               | progress specialize_by_assumption ];
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
                 | progress autorewrite with interp_extra interp_gen_cache
                 | progress autorewrite with push_eval
                 | erewrite select_eq
                 | progress autounfold with push_eval
                 | progress autorewrite with distr_length in *
                 | typeclasses eauto
                 | solve [ eauto with zarith ] ]
  | .. ].

Ltac prove_correctness use_curve_good := prove_correctness' ltac:(fun _ => fail) use_curve_good.
Ltac prove_pipeline_wf _ := PipelineTactics.prove_pipeline_wf ().

Module CorrectnessStringification.
  Module dyn_context.
    Inductive list :=
    | nil
    | cons {T1 T2} (k : T1) (v : T2) (ctx : list).
  End dyn_context.

  Ltac strip_bounds_info correctness :=
    let rec is_known_non_bounds_equality_type T :=
        lazymatch T with
        | Z => true
        | list Z => true
        | prod ?A ?B
          => let a := is_known_non_bounds_equality_type A in
             let b := is_known_non_bounds_equality_type B in
             (eval cbv in (andb a b))
        | _ => false
        end in
    lazymatch correctness with
    | (fun x : ?T => ?f)
      => let fx := fresh in
         constr:(fun x : T => match f return _ with
                              | fx => ltac:(let fx := (eval cbv [fx] in fx) in
                                            let v := strip_bounds_info fx in
                                            exact v)
                              end)
    | ((lower ?r <=? ?v) && (?v <=? upper ?r))%bool%Z = true -> ?T
      => strip_bounds_info T
    | list_Z_bounded_by _ _ -> ?T
      => strip_bounds_info T
    | (_ = List.map (fun z => (_ mod _) / _) (List.seq _ _)) /\ (?a <= ?b < ?c) -> ?T
      => let T := strip_bounds_info T in
         constr:(a <= b < c -> T)
    | ?T /\ list_Z_bounded_by _ _
      => T
    | ?T /\ (match _ with pair _ _ => _ end = true)
      => T
    | ?T /\ ((lower ?r <=? ?v) && (?v <=? upper ?r))%bool%Z = true
      => T
    | iff _ _
      => correctness
    | ?x = ?y /\ (_ = List.map (fun z => (_ mod _) / _) (List.seq _ _)) /\ (?a <= ?b < ?c)
      => constr:(x = y /\ a <= b < c)
    | (_ = List.map (fun z => (_ mod _) / _) (List.seq _ _)) /\ (?a <= ?b < ?c)
      => constr:(a <= b < c)
    | ?A /\ ?B
      => let A := strip_bounds_info A in
         let B := strip_bounds_info B in
         constr:(A /\ B)
    | _ = _ :> ?T
      => lazymatch is_known_non_bounds_equality_type T with
         | true => correctness
         | false
           => constr_fail_with ltac:(fun _ => idtac "Unrecognized bounds component:" correctness "; unrecognized equality type" T;
                                              fail 1 "Unrecognized bounds component:" correctness "; unrecognized equality type" T)
         end
    | forall x : ?T, ?f
      => let fx := fresh in
         constr:(forall x : T, match f return _ with
                               | fx => ltac:(let fx := (eval cbv [fx] in fx) in
                                             let v := strip_bounds_info fx in
                                             exact v)
                               end)
    | let x : ?T := ?v in ?f
      => let fx := fresh in
         constr:(let x : T := v in
                 match f return _ with
                 | fx => ltac:(let fx := (eval cbv [fx] in fx) in
                               let v := strip_bounds_info fx in
                               exact v)
                 end)
    | match ?v with pair a b => ?f end
      => let fx := fresh in
         constr:(match v return _ with
                 | pair a b
                   => match f return _ with
                      | fx => ltac:(let fx := (eval cbv [fx] in fx) in
                                    let v := strip_bounds_info fx in
                                    exact v)
                      end
                 end)
    | _
      => constr_fail_with ltac:(fun _ => idtac "Unrecognized bounds component:" correctness;
                                         fail 1 "Unrecognized bounds component:" correctness)
    end.
  Ltac with_assoc_list ctx correctness arg_var_names out_var_names cont :=
    lazymatch correctness with
    | (fun x : ?T => ?f)
      => let fx := fresh in
         let x' := fresh in
         constr:(fun x : T
                 => match x, f return _ with
                    | x', fx
                      => ltac:(let fx' := (eval cbv delta [fx] in fx) in
                               let x := (eval cbv delta [x'] in x') in
                               clear fx x';
                               let ret := with_assoc_list
                                            (dyn_context.cons x out_var_names ctx)
                                            fx'
                                            arg_var_names
                                            ()
                                            cont in
                              exact ret)
                    end)
    | _
      => let T := type of arg_var_names in
         lazymatch (eval hnf in T) with
         | prod _ _
           => lazymatch correctness with
              | (forall x : ?T, ?f)
                => let fx := fresh in
                   let x' := fresh in
                   constr:(fun x : T
                           => match x, f return _ with
                              | x', fx
                                => ltac:(let fx' := (eval cbv delta [fx] in fx) in
                                         let x := (eval cbv delta [x'] in x') in
                                         clear fx x';
                                         let ret := with_assoc_list
                                                      (dyn_context.cons x (fst arg_var_names) ctx)
                                                      fx'
                                                      (snd arg_var_names)
                                                      out_var_names
                                                      cont in
                                         exact ret)
                              end)
              | ?T
                => cont ctx T
              end
         | _ => cont ctx correctness
         end
    end.
  Ltac to_level lvl :=
    lazymatch type of lvl with
    | Z => constr:(Level.level lvl)
    | _ => lvl
    end.

  Ltac maybe_parenthesize str natural cur_lvl :=
    let natural := to_level natural in
    let cur_lvl := to_level cur_lvl in
    let should_paren := (eval cbv in (Level.ltb cur_lvl natural)) in
    lazymatch should_paren with
    | true => constr:(("(" ++ str ++ ")")%string)
    | false => str
    end.

  Ltac find_head_in_ctx' ctx x cont :=
    let h := head x in
    lazymatch ctx with
    | context[dyn_context.cons h ?name _] => cont name
    | context[dyn_context.cons x ?name _] => cont name
    | _ => lazymatch x with
           | fst ?x
             => find_head_in_ctx' ctx x ltac:(fun x => cont (fst x))
           | snd ?x
             => find_head_in_ctx' ctx x ltac:(fun x => cont (snd x))
           | _ => constr:(@None string)
           end
    end.
  Ltac find_head_in_ctx ctx x :=
    find_head_in_ctx' ctx x ltac:(fun x => constr:(Some x)).

  Ltac find_in_ctx' ctx x cont :=
    lazymatch ctx with
    | context[dyn_context.cons x ?name _] => cont name
    | _ => lazymatch x with
           | fst ?x
             => find_in_ctx' ctx x ltac:(fun x => cont (fst x))
           | snd ?x
             => find_in_ctx' ctx x ltac:(fun x => cont (snd x))
           | _ => constr:(@None string)
           end
    end.
  Ltac find_in_ctx ctx x :=
    find_in_ctx' ctx x ltac:(fun x => constr:(Some x)).

  Ltac test_is_var_or_const v :=
    constr:(ltac:(tryif first [ is_var v | is_const v ] then exact true else exact false)).
  Local Open Scope string_scope.

  Ltac fresh_from' ctx check_list start_val :=
    lazymatch check_list with
    | cons ?n ?check_list
      => lazymatch ctx with
         | context[dyn_context.cons _ n]
           => fresh_from' ctx check_list start_val
         | _ => n
         end
    | _
      => let n := (eval cbv in ("x" ++ Decimal.Z.to_string start_val)) in
         lazymatch ctx with
         | context[dyn_context.cons _ n]
           => fresh_from' ctx check_list (Z.succ start_val)
         | _ => n
         end
    end.

  Ltac fresh_from ctx := fresh_from' ctx ["x"; "y"; "z"] 0%Z.

  Ltac stringify_function_binders ctx correctness stringify_body :=
    lazymatch correctness with
    | (fun x : ?T => ?f)
      => let fx := fresh in
         let x' := fresh in
         let xn := fresh_from ctx in
         lazymatch
           constr:(
             fun x : T
             => match x, f return string with
                | x', fx
                  => ltac:(
                       let fx' := (eval cbv delta [fx] in fx) in
                       let x := (eval cbv delta [x'] in x') in
                       clear fx x';
                       let res := stringify_function_binders
                                    (dyn_context.cons x xn ctx)
                                    fx'
                                    stringify_body in
                       exact (" " ++ xn ++ res))
                end) with
         | fun _ => ?f => f
         | ?F => constr_fail_with ltac:(fun _ => idtac "Failed to eliminate functional dependencies in" F;
                                                 fail 1 "Failed to eliminate functional dependencies in" F)
         end
    | ?v => let res := stringify_body ctx v in
            constr:(", " ++ res)
    end.

  Ltac is_literal x :=
    lazymatch x with
    | O => true
    | S ?x => is_literal x
    | _ => false
    end.
  Ltac eta_match v :=
    let recr_if_not_same v' :=
        lazymatch v' with
        | v => v'
        | _ => eta_match v'
        end in
    lazymatch v with
    | match ?x with pair a b => ?f end
      => recr_if_not_same (match fst x, snd x with a, b => f end)
    | fst (?x, ?y) => eta_match x
    | snd (?x, ?y) => eta_match y
    | match ?x with true => (?ta, ?tb) | false => (?fa, ?fb) end
      => eta_match (if x then ta else fa, if x then tb else fb)
    | @fst ?A ?B ?x
      => let x := eta_match x in
         recr_if_not_same (@fst A B x)
    | @snd ?A ?B ?x
      => let x := eta_match x in
         recr_if_not_same (@snd A B x)
    | _ => v
    end.

  Ltac stringify_rec0 ctx correctness lvl :=
    let lvl := to_level lvl in
    let term_lvl := constr:(term_lvl) in
    let rel_lvl := constr:(rel_lvl) in
    let next_rel_lvl := constr:(Level.next rel_lvl) in
    let app_lvl := constr:(app_lvl) in
    let next_app_lvl := constr:(Level.next app_lvl) in
    let correctness := eta_match correctness in
    let recurse v lvl := stringify_rec0 ctx v lvl in
    let name_of_var := find_head_in_ctx ctx correctness in
    let stringify_if testv t f :=
        let stest := recurse testv term_lvl in
        let st := recurse t term_lvl in
        let sf := recurse f term_lvl in
        maybe_parenthesize (("if " ++ stest ++ " then " ++ st ++ " else " ++ sf)%string) term_lvl lvl in
    let show_Z _ := constr:(Decimal.show_lvl_Z correctness lvl) in
    let show_nat _ := constr:(Decimal.show_lvl_nat correctness lvl) in
    let show_list_Z_Z _ := constr:(@show_lvl_list _ (@show_lvl_prod _ _ Decimal.show_lvl_Z Decimal.show_lvl_Z) correctness lvl) in
    let stringify_prefix f natural arg_lvl :=
        lazymatch correctness with
        | ?F ?x
          => let sx := recurse x arg_lvl in
             maybe_parenthesize (f ++ sx)%string natural lvl
        end in
    let stringify_postfix f natural arg_lvl :=
        lazymatch correctness with
        | ?F ?x
          => let sx := recurse x arg_lvl in
             maybe_parenthesize (sx ++ f)%string natural lvl
        end in
    let stringify_infix' lvl space f natural l_lvl r_lvl :=
        lazymatch correctness with
        | ?F ?x ?y
          => let sx := recurse x l_lvl in
             let sy := recurse y r_lvl in
             maybe_parenthesize (sx ++ space ++ f ++ space ++ sy)%string natural lvl
        end in
    let stringify_infix := stringify_infix' lvl " " in
    let stringify_infix_without_space := stringify_infix' lvl "" in
    let stringify_infix2 f1 f2 natural l_lvl c_lvl r_lvl :=
        lazymatch correctness with
        | and (?F1 ?x ?y) (?F2 ?y ?z)
          => let sx := recurse x l_lvl in
             let sy := recurse y c_lvl in
             let sz := recurse z r_lvl in
             maybe_parenthesize (sx ++ " " ++ f1 ++ " " ++ sy ++ " " ++ f2 ++ " " ++ sz)%string natural lvl
        end in
    let name_of_fun :=
        lazymatch correctness with
        | ?f ?x => find_in_ctx ctx f
        | _ => constr:(@None string)
        end in
    lazymatch constr:((name_of_var, name_of_fun)) with
    | (Some ?name, _)
      => maybe_parenthesize name (Level.level 1) lvl
    | (None, Some ?name)
      => lazymatch correctness with
         | ?f ?x
           => let sx := recurse x (Level.next app_lvl) in
              maybe_parenthesize ((name ++ " " ++ sx)%string) constr:(app_lvl) lvl
         end
    | (None, None)
      => lazymatch correctness with
         | ?x = ?y :> ?T
           => lazymatch (eval cbv in T) with
              | Z => let sx := recurse x next_rel_lvl in
                     let sy := recurse y next_rel_lvl in
                     maybe_parenthesize ((sx ++ " = " ++ sy)%string) rel_lvl lvl
              | list Z
                => let sx := recurse x next_rel_lvl in
                   let sy := recurse y next_rel_lvl in
                   maybe_parenthesize ((sx ++ " = " ++ sy)%string) rel_lvl lvl
              | prod ?A ?B
                => let v := (eval cbn [fst snd] in (fst x = fst y /\ snd x = snd y)) in
                   recurse v lvl
              | ?T' => constr_fail_with ltac:(fun _ => idtac "Error: Unrecognized type for equality:" T';
                                                       fail 1 "Error: Unrecognized type for equality:" T')
              end
         | eval (weight 8 1) _ ?v
           => let sv := recurse v 9 in
              maybe_parenthesize (("bytes_eval " ++ sv)%string) app_lvl lvl
         | Associational.eval ?c
           => let sc := recurse c 9 in
              maybe_parenthesize (("Associational.eval " ++ sc)%string) app_lvl lvl
         | uweight ?machine_wordsize ?v
           => recurse (2^(machine_wordsize * Z.of_nat v)) lvl
         | weight 8 1 ?i
           => recurse (2^(8 * Z.of_nat i)) lvl
         | List.map ?x ?y
           => let sx := recurse x next_app_lvl in
              let sy := recurse y next_app_lvl in
              maybe_parenthesize (("map " ++ sx ++ " " ++ sy)%string) app_lvl lvl
         | match ?testv with true => ?t | false => ?f end
           => stringify_if testv t f
         | match ?testv with or_introl _ => ?t | or_intror _ => ?f end
           => stringify_if testv t f
         | match ?testv with left _ => ?t | right _ => ?f end
           => stringify_if testv t f
         | Crypto.Util.Decidable.dec ?p
           => recurse p lvl
         | Z.odd ?x
           => let sx := recurse x next_app_lvl in
              maybe_parenthesize ((sx ++ " is odd")%string) app_lvl lvl
         | Z0 => show_Z ()
         | Zpos _ => show_Z ()
         | Zneg _ => show_Z ()
         | O => show_nat ()
         | S ?x
           => let is_lit := is_literal x in
              lazymatch is_lit with
              | true => show_nat ()
              | false => recurse (x + 1)%nat lvl
              end
         | Z.of_nat ?x => recurse x lvl
         | ?x <= ?y <  ?z => stringify_infix2 "≤" "<" rel_lvl next_rel_lvl next_rel_lvl next_rel_lvl
         | ?x <= ?y <= ?z => stringify_infix2 "≤" "≤" rel_lvl next_rel_lvl next_rel_lvl next_rel_lvl
         | ?x <  ?y <= ?z => stringify_infix2 "<" "≤" rel_lvl next_rel_lvl next_rel_lvl next_rel_lvl
         | ?x <  ?y <  ?z => stringify_infix2 "<" "<" rel_lvl next_rel_lvl next_rel_lvl next_rel_lvl
         | iff _ _ => stringify_infix "↔" 95 94 94
         | and _ _  => stringify_infix "∧" 80 80 80
         | andb _ _ => stringify_infix "∧" 80 80 80
         | Z.modulo _ _ => stringify_infix "mod" 41 39 39
         | Z.mul _ _ => stringify_infix "*" 40 40 39
         | Z.pow _ _ => stringify_infix_without_space "^" 30 29 30
         | Z.add _ _ => stringify_infix "+" 50 50 49
         | Z.sub _ _ => stringify_infix "-" 50 50 49
         | Z.opp _ => stringify_prefix "-" 35 35
         | Z.le _ _ => stringify_infix "≤" rel_lvl next_rel_lvl next_rel_lvl
         | Z.lt _ _ => stringify_infix "<" rel_lvl next_rel_lvl next_rel_lvl
         | Z.leb _ _ => stringify_infix "≤" rel_lvl next_rel_lvl next_rel_lvl
         | Z.ltb _ _ => stringify_infix "<" rel_lvl next_rel_lvl next_rel_lvl
         | Nat.mul _ _ => stringify_infix "*" 40 40 39
         | Nat.pow _ _ => stringify_infix "^" 30 29 30
         | Nat.add _ _ => stringify_infix "+" 50 50 49
         | Nat.sub _ _ => stringify_infix "-ℕ" 50 50 49
         | Z.div _ _
           => let res := stringify_infix' next_rel_lvl " " "/" 40 40 39 in
              maybe_parenthesize ("⌊" ++ res ++ "⌋") next_app_lvl lvl
         | List.seq ?x ?y
           => let sx := recurse x next_app_lvl in
              let sy := recurse (pred y) next_app_lvl in
              constr:("[" ++ sx ++ ".." ++ sy ++ "]")
         | pred ?n
           => let iv := test_is_var_or_const n in
              let il := is_literal n in
              lazymatch (eval cbv in (orb il iv)) with
              | true => show_nat ()
              | false
                => recurse (n - 1)%nat lvl
              end
         | fun x : ?T => ?f
           => let slam := stringify_function_binders ctx correctness ltac:(fun ctx body => stringify_rec0 ctx body term_lvl) in
              maybe_parenthesize ("λ" ++ slam) term_lvl lvl
         | ?v
           => let iv := test_is_var_or_const v in
              lazymatch iv with
              | true
                => let T := type of v in
                   lazymatch (eval hnf in T) with
                   | Z => show_Z ()
                   | nat => show_nat ()
                   | list (Z * Z) => show_list_Z_Z ()
                   | _
                     => constr_fail_with ltac:(fun _ => idtac "Error: Unrecognized var:" v " in " ctx;
                                                        fail 1 "Error: Unrecognized var:" v " in " ctx)
                   end
              | false
                => constr_fail_with ltac:(fun _ => idtac "Error: Unrecognized term:" v " in " ctx;
                                                   fail 1 "Error: Unrecognized term:" v " in " ctx)
              end
         end
    end.

  Ltac stringify_preconditions ctx so_far_rev correctness :=
    let correctness := eta_match correctness in
    let recurse so_far_rev v := stringify_preconditions ctx so_far_rev v in
    lazymatch correctness with
    | ?A -> ?B
      => let sA := stringify_rec0 ctx A constr:(term_lvl) in
         recurse (sA :: so_far_rev) B
    | ?T
      => let so_far := (eval cbv [List.rev] in (List.rev so_far_rev)) in
         constr:((so_far, T))
    end.

  Ltac stringify_postconditions ctx correctness :=
    let correctness := eta_match correctness in
    let recurse v := stringify_postconditions ctx v in
    let default _ := let v := stringify_rec0 ctx correctness constr:(term_lvl) in
                     constr:(v::nil) in
    lazymatch correctness with
    | _ <= _ <  _ => default ()
    | _ <= _ <= _ => default ()
    | _ <  _ <= _ => default ()
    | _ <  _ <  _ => default ()
    | and ?A ?B
      => let sA := recurse A in
         let sB := recurse B in
         (eval cbv [List.app] in (List.app sA sB))
    | ?x = ?y :> prod ?A ?B
      => let v := (eval cbn [fst snd] in (fst x = fst y /\ snd x = snd y)) in
         recurse v
    | _
      => default ()
    end.

  Ltac stringify_rec ctx correctness :=
    let pre_rest := stringify_preconditions ctx (@nil string) correctness in
    lazymatch pre_rest with
    | (?preconditions, ?correctness)
      => let postconditions := stringify_postconditions ctx correctness in
         let preconditions_list_string
             := lazymatch preconditions with
                | nil => constr:(@nil string)
                | _ => constr:((["Preconditions:"]
                                  ++ List.map (fun s => "  " ++ s)%string preconditions)%list%string)
                end in
         let postconditions_list_string
             := constr:((["Postconditions:"]
                           ++ List.map (fun s => "  " ++ s)%string postconditions)%list%string) in
         (eval cbv [List.map List.app] in
             ([""] ++ preconditions_list_string ++ postconditions_list_string ++ [""])%list%string)
    end.

  Ltac strip_lambdas v :=
    lazymatch v with
    | fun _ => ?f => strip_lambdas f
    | ?v => v
    end.

  Ltac stringify ctx correctness fname arg_var_data out_var_data :=
    let G := match goal with |- ?G => G end in
    let correctness := (eval hnf in correctness) in
    let correctness := (eval cbv [Partition.partition WordByWordMontgomery.valid WordByWordMontgomery.small] in correctness) in
    let correctness := strip_bounds_info correctness in
    let arg_var_names := constr:(type.map_for_each_lhs_of_arrow (@ToString.OfPHOAS.names_of_var_data) arg_var_data) in
    let out_var_names := constr:(ToString.OfPHOAS.names_of_base_var_data out_var_data) in
    let res := with_assoc_list
                 ctx
                 correctness
                 arg_var_names
                 out_var_names
                 ltac:(
                 fun ctx T
                 => let v := stringify_rec ctx T in refine v
               ) in
    let res := strip_lambdas res in
    res.

  Notation docstring_with_summary_from_lemma_with_ctx ctx summary correctness
    := (fun fname arg_var_data out_var_data
        => match ctx, summary%list, correctness return _ with
           | ctx', summary', correctness'
             => ltac:(let ctx := (eval cbv delta [ctx'] in ctx') in
                      let summary := (eval cbv delta [summary'] in summary') in
                      let correctness := (eval cbv delta [correctness'] in correctness') in
                      clear ctx' summary' correctness';
                        let res := stringify ctx correctness fname arg_var_data out_var_data in
                        refine (List.app (summary fname) res))
           end) (only parsing).
  Notation docstring_with_summary_from_lemma summary correctness
    := (match dyn_context.nil with
        | ctx' => docstring_with_summary_from_lemma_with_ctx ctx' summary correctness
        end)
         (only parsing).
End CorrectnessStringification.
Notation "'docstring_with_summary_from_lemma_with_ctx!' ctx summary correctness"
  := (CorrectnessStringification.docstring_with_summary_from_lemma_with_ctx ctx summary correctness) (only parsing, at level 10, ctx at next level, summary at next level, correctness at next level).
Notation "'docstring_with_summary_from_lemma!' summary correctness"
  := (CorrectnessStringification.docstring_with_summary_from_lemma summary correctness) (only parsing, at level 10, summary at next level, correctness at next level).
(** Used to sigma up the output of stringified pipelines *)
Notation wrap_s v := (fun s => existT (fun t => prod string (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult t))) _ (v s)) (only parsing).
Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {language_naming_conventions : language_naming_conventions_opt}
          {documentation_options : documentation_options_opt}
          {output_options : output_options_opt}
          {absint_opts : AbstractInterpretation.Options}
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
          {widen_carry : widen_carry_opt}
          {widen_bytes : widen_bytes_opt}
          {assembly_conventions : assembly_conventions_opt}
          {error_on_unused_assembly_functions : error_on_unused_assembly_functions_opt}
          {ignore_unique_asm_names : ignore_unique_asm_names_opt}
          (n : nat)
          (machine_wordsize : machine_wordsize_opt).
  Definition word_bound : ZRange.type.interp base.type.Z
    := r[0 ~> 2^machine_wordsize-1]%zrange.
  Definition saturated_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.repeat (Some word_bound) n.
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
  (** We override this instance with a version that does not avoid
      uint1, so that the primitive operations, which in fact do use
      (>>) to get carries, don't have issues *)
  Local Instance absint_opts_with_no_shiftr_avoid_uint1 : AbstractInterpretation.Options
    := {| AbstractInterpretation.shiftr_avoid_uint1 := false |}.
  Local Notation adc_sbb_return_carry_range s
    := ((if List.existsb (Z.eqb s) relax_adc_sbb_return_carry_to_bitwidth then r[0~>2^s%Z-1] else r[0~>1])%zrange).
  Lemma length_saturated_bounds : List.length saturated_bounds = n.
  Proof using Type. cbv [saturated_bounds]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_saturated_bounds : distr_length.
  Local Notation dummy_weight := (weight 0 0).
  Local Notation evalf := (eval dummy_weight n).
  Local Notation notations_for_docstring
    := (CorrectnessStringification.dyn_context.cons
          evalf "eval"
          CorrectnessStringification.dyn_context.nil)%string.
  Local Notation "'docstring_with_summary_from_lemma!' summary correctness"
    := (docstring_with_summary_from_lemma_with_ctx!
          notations_for_docstring
          summary
          correctness)
         (only parsing, at level 10, summary at next level, correctness at next level).
  Definition selectznz
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         reified_selectznz_gen
         (Some r[0~>1], (Some saturated_bounds, (Some saturated_bounds, tt)))%zrange
         (Some saturated_bounds).
  Definition sselectznz (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "selectznz" selectznz
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is a multi-limb conditional select."]%string)
             (selectznz_correct saturated_bounds)).
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
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToInternalString!
          machine_wordsize prefix ("mulx_u" ++ Decimal.Z.to_string s)%string (mulx s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is a multiplication, returning the full double-width result."]%string)
             (mulx_correct s)).
  Definition addcarryx (s : Z)
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_addcarryx_gen
            @ GallinaReify.Reify s)
         (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
         (Some r[0~>2^s-1], Some (adc_sbb_return_carry_range s))%zrange.
  Definition saddcarryx (prefix : string) (s : Z)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToInternalString!
          machine_wordsize prefix ("addcarryx_u" ++ Decimal.Z.to_string s)%string (addcarryx s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is an addition with carry."]%string)
             (addcarryx_correct relax_adc_sbb_return_carry_to_bitwidth s)).

  Definition subborrowx (s : Z)
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_subborrowx_gen
            @ GallinaReify.Reify s)
         (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
         (Some r[0~>2^s-1], Some (adc_sbb_return_carry_range s))%zrange.
  Definition ssubborrowx (prefix : string) (s : Z)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToInternalString!
          machine_wordsize prefix ("subborrowx_u" ++ Decimal.Z.to_string s)%string (subborrowx s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is a subtraction with borrow."]%string)
             (subborrowx_correct relax_adc_sbb_return_carry_to_bitwidth s)).

  Definition value_barrier (s : int.type)
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         reified_value_barrier_gen
         (Some (int.to_zrange s), tt)
         (Some (int.to_zrange s)).
  Definition svalue_barrier (prefix : string) (s : int.type)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToInternalString!
          machine_wordsize prefix ("value_barrier_" ++ (if int.is_unsigned s then "u" else "") ++ Decimal.Z.to_string (int.bitwidth_of s))%string (value_barrier s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is a single-word conditional move."]%string)
             (value_barrier_correct (int.is_signed s) (int.bitwidth_of s))).

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
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToInternalString!
          machine_wordsize prefix ("cmovznz_u" ++ Decimal.Z.to_string s)%string (cmovznz s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is a single-word conditional move."]%string)
             (cmovznz_correct false s)).
  Definition cmovznz_by_mul (s : Z)
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values_with_bytes
         (reified_cmovznz_by_mul_gen
            @ GallinaReify.Reify s)
         (Some r[0~>1], (Some r[0~>2^s-1], (Some r[0~>2^s-1], tt)))%zrange
         (Some r[0~>2^s-1])%zrange.
  Definition scmovznz_by_mul (prefix : string) (s : Z)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToInternalString!
          machine_wordsize prefix ("cmovznz_u" ++ Decimal.Z.to_string s)%string (cmovznz_by_mul s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is a single-word conditional move."]%string)
             (cmovznz_correct false s)).

  Definition copy
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         None (* fancy *)
         possible_values
         reified_id_gen
         (Some saturated_bounds, tt)%zrange
         (Some saturated_bounds).
  Definition scopy (prefix : string)
    : string * (Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult _))
    := Eval cbv beta in
        FromPipelineToString!
          machine_wordsize prefix "copy" copy
          (docstring_with_summary_from_lemma!
             (fun fname : string => [text_before_function_name ++ fname ++ " is a multi-limb identity function."]%string)
             (copy_correct saturated_bounds)).

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd machine_wordsize_opt] in *; Bool.split_andb; Z.ltb_to_lt; lia.
  Hint Rewrite
       eval_select
       select_eq
       Arithmetic.Primitives.mulx_correct
       Arithmetic.Primitives.addcarryx_correct
       Arithmetic.Primitives.subborrowx_correct
       Arithmetic.Primitives.cmovznz_correct
       Arithmetic.Primitives.cmovznz_by_mul_correct
       Z.zselect_correct
       using solve [ auto | congruence | solve_extra_bounds_side_conditions ] : push_eval.
  Strategy -1000 [mulx]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma mulx_correct s' res
        (Hres : mulx s' = Success res)
    : mulx_correct s' (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_mulx s' res (Hres : mulx s' = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.
  Strategy -1000 [addcarryx]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma addcarryx_correct s' res
        (Hres : addcarryx s' = Success res)
    : addcarryx_correct relax_adc_sbb_return_carry_to_bitwidth s' (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_addcarryx s' res (Hres : addcarryx s' = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [subborrowx]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma subborrowx_correct s' res
        (Hres : subborrowx s' = Success res)
    : subborrowx_correct relax_adc_sbb_return_carry_to_bitwidth s' (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_subborrowx s' res (Hres : subborrowx s' = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [value_barrier]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma value_barrier_correct s' res
        (Hres : value_barrier s' = Success res)
    : value_barrier_correct (int.is_signed s') (int.bitwidth_of s') (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_value_barrier s' res (Hres : value_barrier s' = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [cmovznz]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma cmovznz_correct s' res
        (Hres : cmovznz s' = Success res)
    : cmovznz_correct false s' (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_cmovznz s' res (Hres : cmovznz s' = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Strategy -1000 [cmovznz_by_mul]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma cmovznz_by_mul_correct s' res
        (Hres : cmovznz_by_mul s' = Success res)
    : COperationSpecifications.Primitives.cmovznz_correct false s' (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_cmovznz_by_mul s' res (Hres : cmovznz_by_mul s' = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma selectznz_correct res
        (Hres : selectznz = Success res)
    : selectznz_correct saturated_bounds (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_selectznz res (Hres : selectznz = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Lemma copy_correct res
        (Hres : copy = Success res)
    : copy_correct saturated_bounds (Interp res).
  Proof using Type. prove_correctness I. Qed.

  Lemma Wf_copy res (Hres : copy = Success res) : Wf res.
  Proof using Type. prove_pipeline_wf (). Qed.

  Section for_stringification.
    Context (valid_names : string)
            (known_functions : list (string
                                     * (string
                                        -> { t : _
                                                 & string * Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult t) }%type)))
            (extra_special_synthesis : string ->
                                       list
                                         (option
                                            { t : _
                                                  & string * Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult t) }%type)).

    Definition aggregate_infos (ls : list (string * Pipeline.ErrorT { t : _ & Pipeline.ExtendedSynthesisResult t })) : ToString.ident_infos
      := fold_right
           ToString.ident_info_union
           ToString.ident_info_empty
           (List.map
              (fun '(_, res) => match res with
                                | Success (existT _ v) => v.(Pipeline.ident_infos)
                                | Error _ => ToString.ident_info_empty
                                end)
              ls).

    Definition push_sig_type (v : { t : _ & string * Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult t) }%type)
      : string * Pipeline.ErrorT { t : _ & Pipeline.ExtendedSynthesisResult t }
      := let '(existT t (n, v)) := v in
         (n, (v <- v; Success (existT _ t v))%error).

    Definition extra_synthesis (function_name_prefix : string) (infos : ToString.ident_infos)
      : list { t : _ & string * Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult t) }%type * ToString.ident_infos
      := let infos := ToString.strip_special_infos machine_wordsize infos in
         let mk := existT (fun t => string * Pipeline.ErrorT (Pipeline.ExtendedSynthesisResult t))%type in
         let ls_addcarryx := List.flat_map
                               (fun lg_split:positive
                                => [mk _ (saddcarryx function_name_prefix lg_split)
                                    ; mk _ (ssubborrowx function_name_prefix lg_split)])
                               (PositiveSet.elements (ToString.addcarryx_lg_splits infos)) in
         let ls_mulx := List.map
                          (fun lg_split:positive => mk _ (smulx function_name_prefix lg_split))
                          (PositiveSet.elements (ToString.mulx_lg_splits infos)) in
         let ls_value_barrier
             := List.map
                  (fun bw => mk _ (svalue_barrier function_name_prefix bw))
                  (IntSet.elements (value_barrier_bitwidths infos)) in
         let ls_cmov := List.map
                          (fun ty:int.type
                           => mk _ ((if use_mul_for_cmovznz then scmovznz_by_mul else scmovznz) function_name_prefix (int.bitwidth_of ty)))
                          (IntSet.elements (cmovznz_bitwidths infos)) in
         let ls := ls_addcarryx ++ ls_mulx ++ ls_value_barrier ++ ls_cmov in
         let infos := aggregate_infos (List.map push_sig_type ls) in
         (ls, infos).

    (** Since some of the extra functions (such as [cmovznz]) are the
        only users of other extra functions (such as [value_barrier]),
        we iterate extra synthesis until we reach a fixedpoint on the
        info used *)
    Definition union_extra_infos_of_extra_synthesis (infos : ToString.ident_infos)
      : ToString.ident_infos
      := let '(fs, _) := extra_synthesis "" infos in
         let fuel := (1 + List.length fs)%nat in
         snd
           (fueled_lub
              ident_infos_equal ident_info_union fuel
              (fun infos => snd (extra_synthesis "" infos))
              infos).

    Definition synthesize_of_name (function_name_prefix : string) (name : string)
      : string * Pipeline.ErrorT { t : _ & Pipeline.ExtendedSynthesisResult t }%type
      := fold_right
           (fun v default
            => match v with
               | Some (existT t (n, res))
                 => (n, (res <- res; Success (existT _ t res))%error)
               | None => default
               end)
           (name,
            Error
              (Pipeline.Invalid_argument
                 ("Unrecognized request to synthesize """ ++ name ++ """; valid names are " ++ valid_names ++ ".")))
           ((List.map
               (fun '(expected_name, resf)
                => if (name =? expected_name)%string
                   then Some (resf function_name_prefix)
                   else None)
               known_functions)
              ++ extra_special_synthesis name).

    Fixpoint parse_asm_files_lines (ls : list (string (* fname *) * list string))
      : Pipeline.ErrorT (list (string (* fname *) * (Assembly.Syntax.Lines (* prefix *) * list (string (* function name *) * Assembly.Syntax.Lines))))
      := match ls with
         | [] => Success []
         | (fname, lines) :: ls
           => match Assembly.Parse.parse_validated lines with
              | Error err => Error (Pipeline.Assembly_parsing_error fname err)
              | Success v
                => (vs <- parse_asm_files_lines ls;
                    Success ((fname, Assembly.Parse.split_code_to_functions v) :: vs))
              end
         end%error.

    Definition parse_asm_hints
      : Pipeline.ErrorT (list (string (* fname *) * (Assembly.Syntax.Lines (* prefix *) * list (string (* function name *) * Assembly.Syntax.Lines))))
      := parse_asm_files_lines assembly_hints_lines.

    Definition split_to_assembly_functions {A B} (assembly_data : list (string (* file name *) * list (string * A))) (normal_data : list (string * B))
      : list (string * (list (string (* file name *) * A) * B)) * list (string * B) * list (string (* file name *) * list (string (* function name *) * A)) * list (string (* file name of files with no globals *))
      := let assembly_files_without_globals := List.filter (fun '(_, ls) => (List.length ls =? 0)%nat) assembly_data in
         let assembly_files_without_globals := List.map (fun '(fname, _) => fname) assembly_files_without_globals in
         let assembly_data := List.filter (fun '(_, ls) => negb (List.length ls =? 0)%nat) assembly_data in
         if (ignore_unique_asm_names && (forallb (fun '(_, data) => length data =? 1) assembly_data) && (length normal_data =? 1))%nat%bool
         then match normal_data with
              | [(n, b)]
                => ([(n, (List.flat_map (fun '(fname, asm_ls) => List.map (fun '(_, a) => (fname, a)) asm_ls) assembly_data, b))], [], [], assembly_files_without_globals)
              | _ => ([], normal_data, assembly_data, assembly_files_without_globals)
              end
         else
         (* move the function name first, flatten the functions associated to each file *)
         let assembly_data : list (string (* function name *) * (string (* file name *) * A)) := List.flat_map (fun '(fname, asm_ls) => List.map (fun '(func_name, a) => (func_name, (fname, a))) asm_ls) assembly_data in
         (* now group the asesmbly functions by their function name *)
         let assembly_data := List.groupAllBy (fun '(n1, _) '(n2, _) => (n1 =? n2)%string) assembly_data in
         (* now pull out the function name to top level *)
         let assembly_data : list (string (* function name *) * list (string (* file name *) * A))
           := Option.List.map
                (fun ls
                 => match ls with
                    | [] => None
                    | (n, _) :: _ => Some (n, List.map snd ls)
                    end)
                assembly_data in
         (* combine normal data with corresponding assembly data *)
         let ls := List.map (fun '(n1, normal_data)
                             => ((n1, normal_data), List.find (fun '(n2, _) => n1 =? n2)%string assembly_data))
                            normal_data in
         (* split out the normal data that has assembly data from the normal data that doesn't *)
         let '(lsAB, lsB) := List.partition (fun '(_, o) => match o with Some _ => true | None => false end) ls in
         (* get the assembly functions that have no corresponding normal function *)
         let lsA := List.filter (fun '(n1, _) => negb (List.existsb (fun '(n2, _) => (n1 =? n2)%string) normal_data)) assembly_data in
         (* flatten out assembly functions and move the file names first *)
         let lsA := List.flat_map (fun '(function_name, ls) => List.map (fun '(file_name, v) => (file_name, (function_name, v))) ls) lsA in
         (* group by files for assembly data *)
         let lsA := List.groupAllBy (fun '(n1, _) '(n2, _) => (n1 =? n2)%string) lsA in
         let lsA
           := Option.List.map
                (fun ls
                 => match ls with
                    | [] => None
                    | (n, _) :: _ => Some (n, List.map snd ls)
                    end)
                lsA in
         (Option.List.map
            (fun '((n, normal_data), assembly_data)
             => match assembly_data with
                | Some (_n (* should be equal to n *), assembly_data) => Some (n, (assembly_data, normal_data))
                | None => (* should not happen *) None
                end)
            lsAB,
           List.map (@fst _ _) lsB,
           lsA,
           assembly_files_without_globals).

    (** Note: If you change the name or type signature of this
          function, you will need to update the code in CLI.v *)
    Definition Synthesize
               (all_typedefs : list ToString.typedef_info)
               (check_args : list string -> Pipeline.ErrorT (list string) -> Pipeline.ErrorT (list string))
               (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (synthesis_output_kind * string * Pipeline.ErrorT (list string))
      := let requests := match requests with
                         | nil => List.map (@fst _ _) known_functions
                         | _ => requests
                         end in
         let ls := List.map (synthesize_of_name function_name_prefix) requests in
         let '(asm_ls, ls)
             := match parse_asm_hints with
                | Success [] => ([], ls)
                | Success asm_hints
                  => (* TODO: Currently we just pass the prefix/header through unchanged; maybe we should instead generate a better header? *)
                     let asm_ls_prefix
                       := List.map (fun '(fname, (prefix, _)) => (assembly_output, "header-prefix for " ++ fname, Success (Show.show_lines prefix)))%string asm_hints in
                     let function_asms := List.map (fun '(fname, (_prefix, function_asms)) => (fname, function_asms)) asm_hints in
                     let valid_function_names := List.map fst ls in
                     let '(asm_ls, ls, unused_asm_ls, asm_missing_globals) := split_to_assembly_functions function_asms ls in
                     let asm_ls_check
                       := if negb (List.length asm_missing_globals =? 0)%nat
                          then [(assembly_output, "check", Error (Pipeline.Assembly_without_any_global_labels asm_missing_globals))]
                          else [] in
                     let asm_ls_check
                       := asm_ls_check
                            ++ if (error_on_unused_assembly_functions && (0 <? List.length unused_asm_ls))%nat
                               then [(assembly_output, "check", Error (Pipeline.Unused_global_assembly_labels
                                                                         (List.map (fun '(file_name, labels) => (file_name, List.map (@fst _ _) labels)) unused_asm_ls)
                                                                         valid_function_names))]
                               else [] in
                     let asm_ls
                         := List.map
                              (fun '(name, (asm_fname_and_lines, synthesis_res))
                               => (name,
                                   (synthesis_res <- synthesis_res;
                                   let 'existT _ synthesis_res := synthesis_res in
                                   match Assembly.Equivalence.generate_assembly_of_hinted_expr
                                           asm_fname_and_lines
                                           (synthesis_res.(Pipeline.expr))
                                           (synthesis_res.(Pipeline.arg_bounds))
                                           (synthesis_res.(Pipeline.out_bounds))
                                   with
                                   | Success lines => Success (List.flat_map (fun '(_fname, lines) => Show.show_lines lines) lines)
                                   | Error (Some (fname, asm_lines), err)
                                     => Error
                                          (Pipeline.Equivalence_checking_failure
                                             (synthesis_res.(Pipeline.expr))
                                             fname
                                             asm_lines
                                             (synthesis_res.(Pipeline.arg_bounds))
                                             err)
                                   | Error (None, err)
                                     => Error
                                          (Pipeline.Equivalence_checking_failure_pre_asm
                                             (synthesis_res.(Pipeline.expr))
                                             (synthesis_res.(Pipeline.arg_bounds))
                                             err)
                                   end)%error))
                              asm_ls in
                     let asm_ls := List.map (fun '(name, lines) => (assembly_output, name, lines)) asm_ls in
                     (match asm_ls with
                      | [] => asm_ls_check
                      | _ => asm_ls_check ++ asm_ls_prefix ++ asm_ls
                      end,
                      ls)
                | Error err => ([(assembly_output, "parsing", Error err)], ls)
                end in
         let infos := aggregate_infos ls in
         let infos := union_extra_infos_of_extra_synthesis infos in
         let '(extra_ls, extra_infos) := extra_synthesis function_name_prefix infos in
         let extra_bit_widths := ToString.bitwidths_used extra_infos in
         let res := (if emit_primitives then List.map push_sig_type extra_ls else nil) ++ ls in
         let res := List.map (fun '(name, res) => (normal_output, name, (res <- res; Success (projT2 res).(Pipeline.lines))%error)) res in
         let infos := ToString.ident_info_union
                        infos
                        (ToString.ident_info_of_bitwidths_used extra_bit_widths) in
         let header :=
             (comment_header
                ++ ToString.header machine_wordsize (orb internal_static static) static function_name_prefix infos all_typedefs) in
         let footer :=
             ToString.footer machine_wordsize (orb internal_static static) static function_name_prefix infos in
         [(normal_output,
           "check_args" ++ String.NewLine ++ String.concat String.NewLine header,
           check_args requests (ErrorT.Success header))%string]
           ++ asm_ls
           ++ res
           ++ match footer with
              | nil => nil
              | _ => [(normal_output, "footer", ErrorT.Success footer)]
              end.
  End for_stringification.
End __.

Notation "'all_typedefs!'" :=
  (match ((fun r => Option.value (relax_zrange_gen only_signed (possible_values_of_machine_wordsize_with_bytes machine_wordsize) r) r)
          : relax_zrange_opt)
         return _ with
   | relax_zrange
     => Pipeline.all_typedefs
   end) (only parsing).

Module Export Hints.
  Hint Opaque
       mulx
       addcarryx
       subborrowx
       value_barrier
       cmovznz
       cmovznz_by_mul
       selectznz
       copy
  : wf_op_cache.
  Hint Immediate
       Wf_mulx
       Wf_addcarryx
       Wf_subborrowx
       Wf_value_barrier
       Wf_cmovznz
       Wf_cmovznz_by_mul
       Wf_selectznz
       Wf_copy
  : wf_op_cache.
End Hints.
