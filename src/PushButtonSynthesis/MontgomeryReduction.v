(** * Push-Button Synthesis of Montgomery Reduction *)
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
Require Import Crypto.PushButtonSynthesis.MontgomeryReductionReificationCache.
Require Import Crypto.PushButtonSynthesis.InvertHighLow.
Require Import Crypto.PushButtonSynthesis.LegacySynthesisTactics.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope. Local Open Scope bool_scope.

Import
  Language.Compilers
  CStringification.Compilers.
Import Compilers.defaults.

Import COperationSpecifications.Primitives.

Import Associational Positional Arithmetic.MontgomeryReduction.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

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

  Definition montred
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         fancy_args (* fancy *)
         possible_values
         (reified_montred_gen
            @ GallinaReify.Reify N @ GallinaReify.Reify R @ GallinaReify.Reify N' @ GallinaReify.Reify (Z.log2 R) @ GallinaReify.Reify 2%nat @ GallinaReify.Reify 2%nat)
         (bound, (bound, tt))
         bound.

  Definition smontred (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "montred" montred
          (fun _ _ _ => @nil string).

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
         (bound, (bound, tt))
         bound
         (montred' N R N' (Z.log2 R) 2 2).

  Notation type_of_strip_3arrow := ((fun (d : Prop) (_ : forall A B C, d) => d) _).
  Definition rmontred_correctT rv : Prop
    := type_of_strip_3arrow (@rmontred_correct rv).
End rmontred.

(* TODO: After moving to new-glue-style, remove these tactics *)
Ltac solve_rmontred := solve_rop rmontred_correct.
Ltac solve_rmontred_nocache := solve_rop_nocache rmontred_correct.
