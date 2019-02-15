(** * Push-Button Synthesis of Barrett Reduction *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Language.
Require Import Crypto.CStringification.
Require Import Crypto.Arithmetic.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.PushButtonSynthesis.BarrettReductionReificationCache.
Require Import Crypto.PushButtonSynthesis.InvertHighLow.
Require Import Crypto.PushButtonSynthesis.LegacySynthesisTactics.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Compilers
  CStringification.Compilers.
Import Compilers.defaults.

Import COperationSpecifications.Primitives.

Import Associational Positional Arithmetic.BarrettReduction.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

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
    := Eval cbv beta in
        FromPipelineToString
          prefix "barrett_red" barrett_red
          (fun _ _ _ => @nil string).

  Local Strategy -100 [barrett_red]. (* Probably needed to make Qed not take forever *)
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

(* TODO: After moving to new-glue-style, remove these tactics *)
Ltac solve_rbarrett_red := solve_rop rbarrett_red_correct.
Ltac solve_rbarrett_red_nocache := solve_rop_nocache rbarrett_red_correct.
