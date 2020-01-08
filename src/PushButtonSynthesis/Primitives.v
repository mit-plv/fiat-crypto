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
Import ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Wf.Compilers
  Language.WfExtra.Compilers
  Language.Compilers
  API.Compilers
  Stringification.Language.Compilers.
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

for (op, opmod) in (('id', '(@id (list Z))'), ('selectznz', 'Positional.select'), ('mulx', 'mulx'), ('addcarryx', 'addcarryx'), ('subborrowx', 'subborrowx'), ('cmovznz', 'cmovznz'), ('cmovznz_by_mul', 'cmovz_nz_by_mul')):
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

Derive reified_cmovznz_by_mul_gen
       SuchThat (is_reification_of reified_cmovznz_by_mul_gen cmovznz_by_mul)
       As reified_cmovznz_by_mul_gen_correct.
Proof. Time cache_reify (). Time Qed.
Hint Extern 1 (_ = _) => apply_cached_reification cmovznz_by_mul (proj1 reified_cmovznz_by_mul_gen_correct) : reify_cache_gen.
Hint Immediate (proj2 reified_cmovznz_by_mul_gen_correct) : wf_gen_cache.
Hint Rewrite (proj1 reified_cmovznz_by_mul_gen_correct) : interp_gen_cache.
Local Opaque reified_cmovznz_by_mul_gen. (* needed for making [autorewrite] not take a very long time *)

(* needed for making [autorewrite] with [Set Keyed Unification] fast *)
Local Opaque expr.Interp.

Local Notation arg_bounds_of_pipeline result
  := ((fun a b c d e arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c d e arg_bounds out_bounds = result') => arg_bounds) _ _ _ _ _ _ _ result eq_refl)
       (only parsing).
Local Notation out_bounds_of_pipeline result
  := ((fun a b c d e arg_bounds out_bounds result' (H : @Pipeline.BoundsPipeline a b c d e arg_bounds out_bounds = result') => out_bounds) _ _ _ _ _ _ _ result eq_refl)
       (only parsing).

Notation FromPipelineToString prefix name result
  := (Pipeline.FromPipelineToString prefix name result).

Ltac prove_correctness' should_not_clear use_curve_good :=
  let Hres := match goal with H : _ = Success _ |- _ => H end in
  let H := fresh in
  pose proof use_curve_good as H;
  (* I want to just use [clear -H Hres], but then I can't use any lemmas in the section because of COQBUG(https://github.com/coq/coq/issues/8153) *)
  repeat match goal with
         | [ H' : _ |- _ ]
           => tryif first [ has_body H' | constr_eq H' H | constr_eq H' Hres | should_not_clear H' ]
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
                 | progress autorewrite with interp_extra interp_gen_cache
                 | progress autorewrite with push_eval
                 | progress autounfold with push_eval
                 | progress autorewrite with distr_length in *
                 | typeclasses eauto ]
  | .. ].

Ltac prove_correctness use_curve_good := prove_correctness' ltac:(fun _ => fail) use_curve_good.

Module CorrectnessStringification.
  Module dyn_context.
    Inductive list :=
    | nil
    | cons {T1 T2} (k : T1) (v : T2) (ctx : list).
  End dyn_context.

  Ltac strip_bounds_info correctness :=
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
    | _ = _ :> list Z
      => correctness
    | forall x : ?T, ?f
      => let fx := fresh in
         constr:(forall x : T, match f return _ with
                               | fx => ltac:(let fx := (eval cbv [fx] in fx) in
                                             let v := strip_bounds_info fx in
                                             exact v)
                               end)
    | ?T
      => constr_fail_with ltac:(fun _ => idtac "Unrecognized bounds component:" T;
                                         fail 1 "Unrecognized bounds component:" T)
    end.

  Ltac with_assoc_list ctx correctness arg_var_names out_var_names cont :=
    lazymatch correctness with
    | (fun x : ?T => ?f)
      => let fx := fresh in
         constr:(fun x : T
                 => match f return _ with
                    | fx
                      => ltac:(let fx' := (eval cbv delta [fx] in fx) in
                               clear fx;
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
                   constr:(fun x : T
                           => match f return _ with
                              | fx
                                => ltac:(let fx' := (eval cbv delta [fx] in fx) in
                                         clear fx;
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

  Ltac maybe_parenthesize str natural cur_lvl :=
    let should_paren := (eval cbv in (Z.ltb cur_lvl natural)) in
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

  Ltac test_is_var v :=
    constr:(ltac:(tryif is_var v then exact true else exact false)).

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
      => let n := (eval cbv in ("x" ++ decimal_string_of_Z start_val)) in
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
         let xn := fresh_from ctx in
         lazymatch
           constr:(
             fun x : T
             => match f return string with
                | fx
                  => ltac:(
                       let fx' := (eval cbv delta [fx] in fx) in
                       clear fx;
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

  Ltac stringify_rec0 ctx correctness lvl :=
    let recurse v lvl := stringify_rec0 ctx v lvl in
    let name_of_var := find_head_in_ctx ctx correctness in
    let stringify_if testv t f :=
        let stest := recurse testv 200 in
        let st := recurse t 200 in
        let sf := recurse f 200 in
        maybe_parenthesize (("if " ++ stest ++ " then " ++ st ++ " else " ++ sf)%string) 200 lvl in
    let show_Z _ :=
        maybe_parenthesize (Show.Decimal.show_Z false correctness) 1 lvl in
    let show_nat _ :=
        maybe_parenthesize (Show.Decimal.show_nat false correctness) 1 lvl in
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
      => maybe_parenthesize name 1 lvl
    | (None, Some ?name)
      => lazymatch correctness with
         | ?f ?x
           => let sx := recurse x 9 in
              maybe_parenthesize ((name ++ " " ++ sx)%string) 10 lvl
         end
    | (None, None)
      => lazymatch correctness with
         | ?x = ?y :> ?T
           => lazymatch (eval cbv in T) with
              | Z => let sx := recurse x 69 in
                     let sy := recurse y 69 in
                     maybe_parenthesize ((sx ++ " = " ++ sy)%string) 70 lvl
              | list Z
                => let sx := recurse x 69 in
                   let sy := recurse y 69 in
                   maybe_parenthesize ((sx ++ " = " ++ sy)%string) 70 lvl
              | prod ?A ?B
                => let v := (eval cbn [fst snd] in (fst x = fst y /\ snd x = snd y)) in
                   recurse v lvl
              | ?T' => constr_fail_with ltac:(fun _ => idtac "Error: Unrecognized type for equality:" T';
                                                       fail 1 "Error: Unrecognized type for equality:" T')
              end
         | eval (weight 8 1) _ ?v
           => let sv := recurse v 9 in
              maybe_parenthesize (("bytes_eval " ++ sv)%string) 10 lvl
         | uweight ?machine_wordsize ?v
           => recurse (2^(machine_wordsize * Z.of_nat v)) lvl
         | weight 8 1 ?i
           => recurse (2^(8 * Z.of_nat i)) lvl
         | List.map ?x ?y
           => let sx := recurse x 9 in
              let sy := recurse y 9 in
              maybe_parenthesize (("map " ++ sx ++ " " ++ sy)%string) 10 lvl
         | match ?testv with true => ?t | false => ?f end
           => stringify_if testv t f
         | match ?testv with or_introl _ => ?t | or_intror _ => ?f end
           => stringify_if testv t f
         | match ?testv with left _ => ?t | right _ => ?f end
           => stringify_if testv t f
         | Crypto.Util.Decidable.dec ?p
           => recurse p lvl
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
         | ?x <= ?y <  ?z => stringify_infix2 "≤" "<" 70 69 69 69
         | ?x <= ?y <= ?z => stringify_infix2 "≤" "≤" 70 69 69 69
         | ?x <  ?y <= ?z => stringify_infix2 "<" "≤" 70 69 69 69
         | ?x <  ?y <  ?z => stringify_infix2 "<" "<" 70 69 69 69
         | iff _ _ => stringify_infix "↔" 95 94 94
         | and _ _ => stringify_infix "∧" 80 80 80
         | Z.modulo _ _ => stringify_infix "mod" 41 39 39
         | Z.mul _ _ => stringify_infix "*" 40 40 39
         | Z.pow _ _ => stringify_infix_without_space "^" 30 29 30
         | Z.add _ _ => stringify_infix "+" 50 50 49
         | Z.sub _ _ => stringify_infix "-" 50 50 49
         | Z.opp _ => stringify_prefix "-" 35 35
         | Z.le _ _ => stringify_infix "≤" 70 69 69
         | Z.lt _ _ => stringify_infix "<" 70 69 69
         | Nat.mul _ _ => stringify_infix "*" 40 40 39
         | Nat.pow _ _ => stringify_infix "^" 30 29 30
         | Nat.add _ _ => stringify_infix "+" 50 50 49
         | Nat.sub _ _ => stringify_infix "-ℕ" 50 50 49
         | Z.div _ _
           => let res := stringify_infix' 69 " " "/" 40 40 39 in
              maybe_parenthesize ("⌊" ++ res ++ "⌋") 9 lvl
         | List.seq ?x ?y
           => let sx := recurse x 9 in
              let sy := recurse (pred y) 9 in
              constr:("[" ++ sx ++ ".." ++ sy ++ "]")
         | pred ?n
           => let iv := test_is_var n in
              let il := is_literal n in
              lazymatch (eval cbv in (orb il iv)) with
              | true => show_nat ()
              | false
                => recurse (n - 1)%nat lvl
              end
         | fun x : ?T => ?f
           => let slam := stringify_function_binders ctx correctness ltac:(fun ctx body => stringify_rec0 ctx body 200) in
              maybe_parenthesize ("λ" ++ slam) 200 lvl
         | ?v
           => let iv := test_is_var v in
              lazymatch iv with
              | true
                => let T := type of v in
                   lazymatch (eval hnf in T) with
                   | Z => show_Z ()
                   | nat => show_nat ()
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
    let recurse so_far_rev v := stringify_preconditions ctx so_far_rev v in
    lazymatch correctness with
    | ?A -> ?B
      => let sA := stringify_rec0 ctx A 200 in
         recurse (sA :: so_far_rev) B
    | ?T
      => let so_far := (eval cbv [List.rev] in (List.rev so_far_rev)) in
         constr:((so_far, T))
    end.

  Ltac stringify_postconditions ctx correctness :=
    let recurse v := stringify_postconditions ctx v in
    let default _ := let v := stringify_rec0 ctx correctness 200 in
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
             (preconditions_list_string ++ postconditions_list_string ++ [""])%list%string)
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

Section __.
  Context {output_language_api : ToString.OutputLanguageAPI}
          {static : static_opt}
          {use_mul_for_cmovznz : use_mul_for_cmovznz_opt}
          {emit_primitives : emit_primitives_opt}
          {should_split_mul : should_split_mul_opt}
          {widen_carry : widen_carry_opt}
          {widen_bytes : widen_bytes_opt}
          (n : nat)
          (machine_wordsize : Z).

  Definition saturated_bounds_list : list (option zrange)
    := List.repeat (Some r[0 ~> 2^machine_wordsize-1]%zrange) n.
  Definition saturated_bounds : ZRange.type.option.interp (base.type.list (base.type.Z))
    := Some saturated_bounds_list.

  (* We include [0], so that even after bounds relaxation, we can
       notice where the constant 0s are, and remove them. *)
  Definition possible_values_of_machine_wordsize
    := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

  Definition possible_values_of_machine_wordsize_with_bytes
    := prefix_with_carry_bytes [machine_wordsize; 2 * machine_wordsize]%Z.

  Let possible_values := possible_values_of_machine_wordsize.
  Let possible_values_with_bytes := possible_values_of_machine_wordsize_with_bytes.

  Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.

  Lemma length_saturated_bounds_list : List.length saturated_bounds_list = n.
  Proof using Type. cbv [saturated_bounds_list]; now autorewrite with distr_length. Qed.
  Hint Rewrite length_saturated_bounds_list : distr_length.

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
         (Some r[0~>1], (saturated_bounds, (saturated_bounds, tt)))%zrange
         saturated_bounds.

  Definition sselectznz (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "selectznz" selectznz
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " is a multi-limb conditional select."]%string)
             (selectznz_correct dummy_weight n saturated_bounds_list)).

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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix ("mulx_u" ++ decimal_string_of_Z s) (mulx s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " is a multiplication, returning the full double-width result."]%string)
             (mulx_correct s)).

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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix ("addcarryx_u" ++ decimal_string_of_Z s) (addcarryx s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " is an addition with carry."]%string)
             (addcarryx_correct s)).

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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix ("subborrowx_u" ++ decimal_string_of_Z s) (subborrowx s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " is a subtraction with borrow."]%string)
             (subborrowx_correct s)).


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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix ("cmovznz_u" ++ decimal_string_of_Z s) (cmovznz s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " is a single-word conditional move."]%string)
             (cmovznz_correct s)).

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
    : string * (Pipeline.ErrorT (list string * ToString.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix ("cmovznz_u" ++ decimal_string_of_Z s) (cmovznz_by_mul s)
          (docstring_with_summary_from_lemma!
             (fun fname : string => ["The function " ++ fname ++ " is a single-word conditional move."]%string)
             (cmovznz_correct s)).

  Local Ltac solve_extra_bounds_side_conditions :=
    cbn [lower upper fst snd] in *; Bool.split_andb; Z.ltb_to_lt; lia.

  Hint Rewrite
       eval_select
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

  Strategy -1000 [cmovznz_by_mul]. (* if we don't tell the kernel to unfold this early, then [Qed] seems to run off into the weeds *)
  Lemma cmovznz_by_mul_correct s' res
        (Hres : cmovznz_by_mul s' = Success res)
    : COperationSpecifications.Primitives.cmovznz_correct s' (Interp res).
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
                                           Pipeline.ErrorT (list string * ToString.ident_infos))))
            (extra_special_synthesis : string ->
                                       list
                                         (option
                                            (string *
                                             Pipeline.ErrorT
                                               (list string * ToString.ident_infos)))).

    Definition aggregate_infos {A B C} (ls : list (A * ErrorT B (C * ToString.ident_infos))) : ToString.ident_infos
      := fold_right
           ToString.ident_info_union
           ToString.ident_info_empty
           (List.map
              (fun '(_, res) => match res with
                                | Success (_, infos) => infos
                                | Error _ => ToString.ident_info_empty
                                end)
              ls).

    Definition extra_synthesis (function_name_prefix : string) (infos : ToString.ident_infos)
      : list (string * Pipeline.ErrorT (list string)) * PositiveSet.t
      := let ls_addcarryx := List.flat_map
                               (fun lg_split:positive => [saddcarryx function_name_prefix lg_split; ssubborrowx function_name_prefix lg_split])
                               (PositiveSet.elements (ToString.addcarryx_lg_splits infos)) in
         let ls_mulx := List.map
                          (fun lg_split:positive => smulx function_name_prefix lg_split)
                          (PositiveSet.elements (ToString.mulx_lg_splits infos)) in
         let ls_cmov := List.map
                          (fun bitwidth:positive
                           => (if use_mul_for_cmovznz then scmovznz_by_mul else scmovznz) function_name_prefix bitwidth)
                          (PositiveSet.elements (ToString.cmovznz_bitwidths infos)) in
         let ls := ls_addcarryx ++ ls_mulx ++ ls_cmov in
         let infos := aggregate_infos ls in
         (List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls,
          ToString.bitwidths_used infos).


    Definition synthesize_of_name (function_name_prefix : string) (name : string)
      : string * ErrorT Pipeline.ErrorMessage (list string * ToString.ident_infos)
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
    Definition Synthesize (check_args : Pipeline.ErrorT (list string) -> Pipeline.ErrorT (list string))
               (comment_header : list string) (function_name_prefix : string) (requests : list string)
      : list (string * Pipeline.ErrorT (list string))
      := let ls := match requests with
                   | nil => List.map (fun '(_, sr) => sr function_name_prefix) known_functions
                   | requests => List.map (synthesize_of_name function_name_prefix) requests
                   end in
         let infos := aggregate_infos ls in
         let '(extra_ls, extra_bit_widths) := extra_synthesis function_name_prefix infos in
         let res := (if emit_primitives then extra_ls else nil) ++ List.map (fun '(name, res) => (name, (res <- res; Success (fst res))%error)) ls in
         let types_used := PositiveSet.union extra_bit_widths (ToString.bitwidths_used infos) in
         let header :=
             (comment_header
                ++ ToString.typedef_header static function_name_prefix types_used
                ++ [""]) in
         [("check_args" ++ String.NewLine ++ String.concat String.NewLine header,
           check_args (ErrorT.Success header))%string]
           ++ res.
  End for_stringification.
End __.
