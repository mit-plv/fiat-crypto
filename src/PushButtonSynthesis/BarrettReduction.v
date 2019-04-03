(** * Push-Button Synthesis of Barrett Reduction *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.derive.Derive.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ErrorT.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Language.
Require Import Crypto.CStringification.
Require Import Crypto.Arithmetic.BarrettReduction.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Fancy.Compiler.
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
Import COperationSpecifications.BarrettReduction.

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Local Opaque reified_barrett_red_gen. (* needed for making [autorewrite] not take a very long time *)

Section rbarrett_red.
  Context (M machine_wordsize : Z).

  Let value_range := r[0 ~> (2^machine_wordsize - 1)%Z]%zrange.
  Let flag_range := r[0 ~> 1]%zrange.
  Let bound := Some value_range.
  Let mu := (2 ^ (2 * machine_wordsize)) / M.
  Let muLow := mu mod (2 ^ machine_wordsize).
  Let consts_list := [M; muLow].

  Definition possible_values_of_machine_wordsize
    := [1; machine_wordsize / 2; machine_wordsize; 2 * machine_wordsize]%Z.
  Let possible_values := possible_values_of_machine_wordsize.

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
  Local Hint Extern 1 => apply fancy_args_good: typeclass_instances. (* This is a kludge *)

  Lemma mut_correct :
    0 < machine_wordsize ->
    partition (uweight machine_wordsize) (1 + 1) (muLow + 2 ^ machine_wordsize) = [muLow; 1].
  Proof.
    intros; cbn. subst muLow.
    assert (0 < 2^machine_wordsize) by ZeroBounds.Z.zero_bounds.
    pose proof (Z.mod_pos_bound mu (2^machine_wordsize) ltac:(lia)).
    rewrite !uweight_S, weight_0; auto using uwprops with lia.
    autorewrite with zsimplify.
    Modulo.push_Zmod. autorewrite with zsimplify. Modulo.pull_Zmod.
    rewrite <-Modulo.Z.mod_pull_div by lia.
    autorewrite with zsimplify. RewriteModSmall.Z.rewrite_mod_small.
    reflexivity.
  Qed.
  Lemma Mt_correct :
    0 < machine_wordsize ->
    2^(machine_wordsize - 1) < M < 2^machine_wordsize ->
    partition (uweight machine_wordsize) 1 M = [M].
  Proof.
    intros; cbn. assert (0 < 2^(machine_wordsize-1)) by ZeroBounds.Z.zero_bounds.
    rewrite !uweight_S, weight_0; auto using uwprops with lia.
    autorewrite with zsimplify. RewriteModSmall.Z.rewrite_mod_small.
    reflexivity.
  Qed.

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := fold_right
         (fun '(b, e) k => if b:bool then Error e else k)
         res
         [
            ((negb (1 <? machine_wordsize))%Z, Pipeline.Value_not_ltZ "machine_wordsize ≤ 1" 1 machine_wordsize);
            ((negb (2 ^ (machine_wordsize-1) <? M))%Z, Pipeline.Value_not_ltZ "M ≤ 2^(machine_wordsize-1)" (2^(machine_wordsize-1)) M);
            ((negb (M <? 2 ^ machine_wordsize))%Z, Pipeline.Value_not_ltZ "2 ^ machine_wordsize ≤ M" M (2^machine_wordsize));
            ((negb (muLow + 2 ^ machine_wordsize =? ((2 ^ 2) ^ machine_wordsize) / M))%Z, Pipeline.Values_not_provably_equalZ "muLow + 2^machine_wordsize ≠ (2 ^ 2) ^ machine_wordsize) / M" (muLow + 2^machine_wordsize) (((2 ^ 2) ^ machine_wordsize) / M));
            (negb ((2 * (((2 ^ 2) ^ machine_wordsize) mod M) <=? 2 ^ (machine_wordsize + 1) - (muLow + 2 ^ machine_wordsize)))%Z, Pipeline.Value_not_leZ ("(2 * ((2 ^ 2) ^ machine_wordsize) mod M)  2 ^ (machine_wordsize + 1) - (muLow + 2 ^ machine_wordsize)") (2 * (((2 ^ 2) ^ machine_wordsize) mod M)) (2 ^ (machine_wordsize + 1) - (muLow + 2 ^ machine_wordsize))) ].

  Local Arguments Z.mul !_ !_.
  Local Ltac use_curve_good_t :=
    repeat first [ assumption
                 | progress cbv [EquivModulo.Z.equiv_modulo]
                 | progress rewrite ?Z.mul_0_r, ?Pos.mul_1_r, ?Z.mul_1_r in *
                 | reflexivity
                 | lia
                 | progress cbn in *
                 | progress intros
                 | solve [ auto with zarith ]
                 | rewrite Z.log2_pow2 by use_curve_good_t ].

  Context (curve_good : check_args (Success tt) = Success tt).

  Lemma use_curve_good
    : 1 < machine_wordsize
      /\ 2 ^ (machine_wordsize - 1) <= M < 2 ^ machine_wordsize
      /\ muLow + 2 ^ machine_wordsize = (2 ^ 2) ^ machine_wordsize / M
      /\ 2 ^ (machine_wordsize - 1) < M < 2 ^ machine_wordsize
      /\ 2 * ((2 ^ 2) ^ machine_wordsize mod M) <= 2 ^ (machine_wordsize + 1) - (muLow + 2 ^ machine_wordsize).
  Proof using curve_good.
    clear -curve_good.
    cbv [check_args fold_right] in curve_good.
    break_innermost_match_hyps; try discriminate.
    rewrite Bool.negb_false_iff in *.
    Z.ltb_to_lt.
    intros.
    repeat apply conj.
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
    { use_curve_good_t. }
  Qed.

  Definition barrett_red
    := Pipeline.BoundsPipeline
         false (* subst01 *)
         fancy_args (* fancy *)
         possible_values
         (reified_barrett_red_gen
            @ GallinaReify.Reify M
            @ GallinaReify.Reify machine_wordsize
            @ GallinaReify.Reify machine_wordsize
            @ GallinaReify.Reify 1%nat
            @ GallinaReify.Reify [muLow;1]
            @ GallinaReify.Reify [M])
         (bound, (bound, tt))
         bound.

  Definition sbarrett_red (prefix : string)
    : string * (Pipeline.ErrorT (list string * ToString.C.ident_infos))
    := Eval cbv beta in
        FromPipelineToString
          prefix "barrett_red" barrett_red
          (fun _ _ _ => @nil string).

  Local Ltac solve_barrett_red_preconditions :=
    repeat first [ lia
                 | assumption
                 | match goal with |- ?x = ?x => reflexivity end
                 | apply use_curve_good
                 | progress autorewrite with zsimplify
                 | progress intros
                 | progress cbv [weight]
                 | rewrite mut_correct
                 | rewrite Mt_correct
                 | rewrite uweight_eq_alt'
                 | rewrite Z.pow_mul_r by lia ].

  Local Strategy -100 [barrett_red]. (* needed for making Qed not take forever *)
  Lemma barrett_red_correct res (Hres : barrett_red = Success res)
    : barrett_red_correct machine_wordsize M (expr.Interp (@ident.gen_interp cast_oor) res).
  Proof using M curve_good.
    cbv [barrett_red_correct]; intros.
    assert (1 < machine_wordsize) by apply use_curve_good.
    pose proof (Z.mod_pos_bound mu (2^machine_wordsize) ltac:(lia)).
    rewrite <-Fancy.fancy_reduce_correct with (mu := muLow + 2^machine_wordsize) (width:=machine_wordsize) (sz:=1%nat) (mut:=[muLow;1]) (Mt:=[M]) by solve_barrett_red_preconditions.
    prove_correctness' ltac:(fun _ => idtac) use_curve_good.
    { cbv [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by bound is_bounded_by_bool value_range upper lower]. rewrite Bool.andb_true_iff, !Z.leb_le. lia. }
    { cbv [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by bound is_bounded_by_bool value_range upper lower]. rewrite Bool.andb_true_iff, !Z.leb_le. lia. }
    { cbn. econstructor. }
    { cbn. econstructor. }
    { cbn. econstructor. }
  Qed.
End rbarrett_red.
