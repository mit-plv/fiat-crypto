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
Require Import Crypto.Arithmetic.
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

Import Associational Positional Arithmetic.BarrettReduction.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Local Opaque reified_barrett_red_gen. (* needed for making [autorewrite] not take a very long time *)

Section rbarrett_red.
  Context (k M : Z) (n nout : nat)
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

  (** Note: If you change the name or type signature of this
        function, you will need to update the code in CLI.v *)
  Definition check_args {T} (res : Pipeline.ErrorT T)
    : Pipeline.ErrorT T
    := fold_right
         (fun '(b, e) k => if b:bool then Error e else k)
         res
         [
            ((negb (2 <=? k))%Z, Pipeline.Value_not_ltZ "k < 2" 2 k);
            ((n =? 0)%nat, Pipeline.Values_not_provably_distinctZ "n = 0" (Z.of_nat n) 0);
            ((negb (0 <? M))%Z, Pipeline.Value_not_ltZ "M ≤ 0" 0 M);
            (negb (muLow + 2 ^ k =? 2 ^ (2 * k) / M)%Z, Pipeline.Values_not_provably_equalZ "muLow + 2^k ≠ 2 ^ (2 * k) / M" (muLow + 2^k) (2 ^ (2 * k) / M));
            ((negb (0 <=? muLow))%Z, Pipeline.Value_not_leZ "muLow < 0" 0 muLow);
            ((negb (muLow <? 2 ^ k))%Z, Pipeline.Value_not_ltZ "2 ^ k ≤ muLow" muLow (2^k));
            ((negb (2 ^ (k-1) <? M))%Z, Pipeline.Value_not_ltZ "M ≤ 2^(k-1)" (2^(k-1)) M);
            ((negb (M <? 2 ^ k))%Z, Pipeline.Value_not_ltZ "2 ^ k ≤ M" M (2^k));
            (negb ((2 * (2 ^ (2 * k) mod M) <=? 2 ^ (k + 1) - (muLow + 2 ^ k)))%Z, Pipeline.Value_not_leZ ("(2 * (2 ^ (2 * k) mod M)  2 ^ (k + 1) - (muLow + 2 ^ k)") (2 * (2 ^ (2 * k) mod M)) (2 ^ (k + 1) - (muLow + 2 ^ k)));
            (negb (Z.of_nat n <=? k)%Z, Pipeline.Value_not_leZ "k < n" (Z.of_nat n) k);
            (negb (k =? machine_wordsize)%Z, Pipeline.Values_not_provably_equalZ "k ≠ machine_wordsize" k machine_wordsize);
            (negb (n =? 2)%nat, Pipeline.Values_not_provably_equalZ "n ≠ 2" (Z.of_nat n) 2);
            (negb (nout =? 2)%nat, Pipeline.Values_not_provably_equalZ "nout ≠ 2" (Z.of_nat nout) 2)].

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
    : 2 <= k
      /\ 0 < M
      /\ muLow + 2 ^ k = 2 ^ (2 * k) / M
      /\ 0 <= muLow < 2 ^ k
      /\ 2 ^ (k - 1) < M < 2 ^ k
      /\ 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - (muLow + 2 ^ k)
      /\ n <> 0%nat
      /\ Z.of_nat n <= k
      /\ k = machine_wordsize 
      /\ n = 2%nat
      /\ nout = 2%nat.
  Proof using curve_good.
    clear -curve_good.
    cbv [check_args fold_right] in curve_good.
    break_innermost_match_hyps; try discriminate.
    rewrite Bool.negb_false_iff in *.
    Z.ltb_to_lt.
    rewrite NPeano.Nat.eqb_neq in *.
    intros.
    repeat apply conj.
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

  Local Ltac solve_barrett_red_preconditions :=
    repeat first [ lia
                 | assumption
                 | apply use_curve_good
                 | progress autorewrite with zsimplify
                 | progress intros
                 | progress cbv [weight]
                 | rewrite Z.pow_mul_r by lia ].

  Local Strategy -100 [barrett_red]. (* needed for making Qed not take forever *)
  Lemma barrett_red_correct res (Hres : barrett_red = Success res)
    : barrett_red_correct k M (expr.Interp (@ident.gen_interp cast_oor) res).
  Proof using k M curve_good.
    cbv [barrett_red_correct]; intros.
    assert (2 <= k) by apply use_curve_good.
    rewrite <-barrett_reduce_correct with (muLow := muLow) (n:=n) (nout:=nout) by solve_barrett_red_preconditions.
    prove_correctness' ltac:(fun _ => idtac) use_curve_good.
    { congruence. }
    { cbv [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by bound is_bounded_by_bool value_range upper lower].
      subst k. rewrite Bool.andb_true_iff, !Z.leb_le. lia. }
    { cbv [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by bound is_bounded_by_bool value_range upper lower].
      subst k. rewrite Bool.andb_true_iff, !Z.leb_le. lia. }
  Qed.
End rbarrett_red.
