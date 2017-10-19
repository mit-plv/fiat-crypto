Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.CPS.
Require Import Crypto.Util.IdfunWithAlt.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.Tactics.VM.

Ltac make_parameterized_sig t :=
  refine (_ : { v : _ | v = t });
  eexists; cbv delta [t
                        B.limb ListUtil.sum ListUtil.sum_firstn
                        CPSUtil.Tuple.mapi_with_cps CPSUtil.Tuple.mapi_with'_cps CPSUtil.flat_map_cps CPSUtil.on_tuple_cps CPSUtil.fold_right_cps2
                        Decidable.dec Decidable.dec_eq_Z
                        id_tuple_with_alt id_tuple'_with_alt
                        Z.add_get_carry_full Z.mul_split
                        Z.add_get_carry_full_cps Z.mul_split_cps
                        Z.add_get_carry_cps];
  repeat autorewrite with pattern_runtime;
  reflexivity.

Notation parameterize_sig t := ltac:(let v := t in make_parameterized_sig v) (only parsing).

Ltac make_parameterized_from_sig t_sig :=
  let t := (eval cbv [proj1_sig t_sig] in (proj1_sig t_sig)) in
  let t := pattern_strip t in
  exact t.

Notation parameterize_from_sig t := ltac:(let v := t in make_parameterized_from_sig v) (only parsing).

Ltac make_parameterized_eq t t_sig :=
  let t := apply_patterned t in
  exact (proj2_sig t_sig : t = _).

Notation parameterize_eq t t_sig := ltac:(let v := t in let v_sig := t_sig in make_parameterized_eq v v_sig) (only parsing).

Ltac basesystem_partial_evaluation_RHS_fast :=
  repeat autorewrite with pattern_runtime;
  let t := match goal with |- _ _ ?t => t end in
  let t := pattern_strip t in
  let t1 := fresh "t1" in
  pose t as t1;
  let t1' := apply_patterned t1 in
  transitivity t1';
  [replace_with_vm_compute t1; clear t1|reflexivity].

Module B.
  Module Associational.
    (**
<<
#!/bin/bash
for i in eval multerm mul_cps mul split_cps split reduce_cps reduce negate_snd_cps negate_snd carryterm_cps carryterm carry_cps carry; do
    echo "    Definition ${i}_sig := parameterize_sig (@Core.B.Associational.${i}).";
    echo "    Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "    Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "    Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
echo "  End Associational."
echo "  Module Positional."
for i in to_associational_cps to_associational eval zeros add_to_nth_cps add_to_nth place_cps place from_associational_cps from_associational carry_cps carry chained_carries_cps chained_carries encode add_cps mul_cps reduce_cps carry_reduce_cps negate_snd_cps split_cps scmul_cps unbalanced_sub_cps sub_cps sub opp_cps Fencode Fdecode eval_from select_cps select; do
  echo "    Definition ${i}_sig := parameterize_sig (@Core.B.Positional.${i}).";
  echo "    Definition ${i} := parameterize_from_sig ${i}_sig.";
  echo "    Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
  echo "    Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
echo "  End Positional."
echo "End B."
echo ""
for i in modulo div; do
  echo "Definition ${i}_sig := parameterize_sig (@Core.${i}).";
  echo "Definition ${i} := parameterize_from_sig ${i}_sig.";
  echo "Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
  echo "Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
>> *)
    Definition eval_sig := parameterize_sig (@Core.B.Associational.eval).
    Definition eval := parameterize_from_sig eval_sig.
    Definition eval_eq := parameterize_eq eval eval_sig.
    Hint Rewrite <- eval_eq : pattern_runtime.

    Definition multerm_sig := parameterize_sig (@Core.B.Associational.multerm).
    Definition multerm := parameterize_from_sig multerm_sig.
    Definition multerm_eq := parameterize_eq multerm multerm_sig.
    Hint Rewrite <- multerm_eq : pattern_runtime.

    Definition mul_cps_sig := parameterize_sig (@Core.B.Associational.mul_cps).
    Definition mul_cps := parameterize_from_sig mul_cps_sig.
    Definition mul_cps_eq := parameterize_eq mul_cps mul_cps_sig.
    Hint Rewrite <- mul_cps_eq : pattern_runtime.

    Definition mul_sig := parameterize_sig (@Core.B.Associational.mul).
    Definition mul := parameterize_from_sig mul_sig.
    Definition mul_eq := parameterize_eq mul mul_sig.
    Hint Rewrite <- mul_eq : pattern_runtime.

    Definition split_cps_sig := parameterize_sig (@Core.B.Associational.split_cps).
    Definition split_cps := parameterize_from_sig split_cps_sig.
    Definition split_cps_eq := parameterize_eq split_cps split_cps_sig.
    Hint Rewrite <- split_cps_eq : pattern_runtime.

    Definition split_sig := parameterize_sig (@Core.B.Associational.split).
    Definition split := parameterize_from_sig split_sig.
    Definition split_eq := parameterize_eq split split_sig.
    Hint Rewrite <- split_eq : pattern_runtime.

    Definition reduce_cps_sig := parameterize_sig (@Core.B.Associational.reduce_cps).
    Definition reduce_cps := parameterize_from_sig reduce_cps_sig.
    Definition reduce_cps_eq := parameterize_eq reduce_cps reduce_cps_sig.
    Hint Rewrite <- reduce_cps_eq : pattern_runtime.

    Definition reduce_sig := parameterize_sig (@Core.B.Associational.reduce).
    Definition reduce := parameterize_from_sig reduce_sig.
    Definition reduce_eq := parameterize_eq reduce reduce_sig.
    Hint Rewrite <- reduce_eq : pattern_runtime.

    Definition negate_snd_cps_sig := parameterize_sig (@Core.B.Associational.negate_snd_cps).
    Definition negate_snd_cps := parameterize_from_sig negate_snd_cps_sig.
    Definition negate_snd_cps_eq := parameterize_eq negate_snd_cps negate_snd_cps_sig.
    Hint Rewrite <- negate_snd_cps_eq : pattern_runtime.

    Definition negate_snd_sig := parameterize_sig (@Core.B.Associational.negate_snd).
    Definition negate_snd := parameterize_from_sig negate_snd_sig.
    Definition negate_snd_eq := parameterize_eq negate_snd negate_snd_sig.
    Hint Rewrite <- negate_snd_eq : pattern_runtime.

    Definition carryterm_cps_sig := parameterize_sig (@Core.B.Associational.carryterm_cps).
    Definition carryterm_cps := parameterize_from_sig carryterm_cps_sig.
    Definition carryterm_cps_eq := parameterize_eq carryterm_cps carryterm_cps_sig.
    Hint Rewrite <- carryterm_cps_eq : pattern_runtime.

    Definition carryterm_sig := parameterize_sig (@Core.B.Associational.carryterm).
    Definition carryterm := parameterize_from_sig carryterm_sig.
    Definition carryterm_eq := parameterize_eq carryterm carryterm_sig.
    Hint Rewrite <- carryterm_eq : pattern_runtime.

    Definition carry_cps_sig := parameterize_sig (@Core.B.Associational.carry_cps).
    Definition carry_cps := parameterize_from_sig carry_cps_sig.
    Definition carry_cps_eq := parameterize_eq carry_cps carry_cps_sig.
    Hint Rewrite <- carry_cps_eq : pattern_runtime.

    Definition carry_sig := parameterize_sig (@Core.B.Associational.carry).
    Definition carry := parameterize_from_sig carry_sig.
    Definition carry_eq := parameterize_eq carry carry_sig.
    Hint Rewrite <- carry_eq : pattern_runtime.
  End Associational.
  Module Positional.
    Definition to_associational_cps_sig := parameterize_sig (@Core.B.Positional.to_associational_cps).
    Definition to_associational_cps := parameterize_from_sig to_associational_cps_sig.
    Definition to_associational_cps_eq := parameterize_eq to_associational_cps to_associational_cps_sig.
    Hint Rewrite <- to_associational_cps_eq : pattern_runtime.

    Definition to_associational_sig := parameterize_sig (@Core.B.Positional.to_associational).
    Definition to_associational := parameterize_from_sig to_associational_sig.
    Definition to_associational_eq := parameterize_eq to_associational to_associational_sig.
    Hint Rewrite <- to_associational_eq : pattern_runtime.

    Definition eval_sig := parameterize_sig (@Core.B.Positional.eval).
    Definition eval := parameterize_from_sig eval_sig.
    Definition eval_eq := parameterize_eq eval eval_sig.
    Hint Rewrite <- eval_eq : pattern_runtime.

    Definition zeros_sig := parameterize_sig (@Core.B.Positional.zeros).
    Definition zeros := parameterize_from_sig zeros_sig.
    Definition zeros_eq := parameterize_eq zeros zeros_sig.
    Hint Rewrite <- zeros_eq : pattern_runtime.

    Definition add_to_nth_cps_sig := parameterize_sig (@Core.B.Positional.add_to_nth_cps).
    Definition add_to_nth_cps := parameterize_from_sig add_to_nth_cps_sig.
    Definition add_to_nth_cps_eq := parameterize_eq add_to_nth_cps add_to_nth_cps_sig.
    Hint Rewrite <- add_to_nth_cps_eq : pattern_runtime.

    Definition add_to_nth_sig := parameterize_sig (@Core.B.Positional.add_to_nth).
    Definition add_to_nth := parameterize_from_sig add_to_nth_sig.
    Definition add_to_nth_eq := parameterize_eq add_to_nth add_to_nth_sig.
    Hint Rewrite <- add_to_nth_eq : pattern_runtime.

    Definition place_cps_sig := parameterize_sig (@Core.B.Positional.place_cps).
    Definition place_cps := parameterize_from_sig place_cps_sig.
    Definition place_cps_eq := parameterize_eq place_cps place_cps_sig.
    Hint Rewrite <- place_cps_eq : pattern_runtime.

    Definition place_sig := parameterize_sig (@Core.B.Positional.place).
    Definition place := parameterize_from_sig place_sig.
    Definition place_eq := parameterize_eq place place_sig.
    Hint Rewrite <- place_eq : pattern_runtime.

    Definition from_associational_cps_sig := parameterize_sig (@Core.B.Positional.from_associational_cps).
    Definition from_associational_cps := parameterize_from_sig from_associational_cps_sig.
    Definition from_associational_cps_eq := parameterize_eq from_associational_cps from_associational_cps_sig.
    Hint Rewrite <- from_associational_cps_eq : pattern_runtime.

    Definition from_associational_sig := parameterize_sig (@Core.B.Positional.from_associational).
    Definition from_associational := parameterize_from_sig from_associational_sig.
    Definition from_associational_eq := parameterize_eq from_associational from_associational_sig.
    Hint Rewrite <- from_associational_eq : pattern_runtime.

    Definition carry_cps_sig := parameterize_sig (@Core.B.Positional.carry_cps).
    Definition carry_cps := parameterize_from_sig carry_cps_sig.
    Definition carry_cps_eq := parameterize_eq carry_cps carry_cps_sig.
    Hint Rewrite <- carry_cps_eq : pattern_runtime.

    Definition carry_sig := parameterize_sig (@Core.B.Positional.carry).
    Definition carry := parameterize_from_sig carry_sig.
    Definition carry_eq := parameterize_eq carry carry_sig.
    Hint Rewrite <- carry_eq : pattern_runtime.

    Definition chained_carries_cps_sig := parameterize_sig (@Core.B.Positional.chained_carries_cps).
    Definition chained_carries_cps := parameterize_from_sig chained_carries_cps_sig.
    Definition chained_carries_cps_eq := parameterize_eq chained_carries_cps chained_carries_cps_sig.
    Hint Rewrite <- chained_carries_cps_eq : pattern_runtime.

    Definition chained_carries_sig := parameterize_sig (@Core.B.Positional.chained_carries).
    Definition chained_carries := parameterize_from_sig chained_carries_sig.
    Definition chained_carries_eq := parameterize_eq chained_carries chained_carries_sig.
    Hint Rewrite <- chained_carries_eq : pattern_runtime.

    Definition encode_sig := parameterize_sig (@Core.B.Positional.encode).
    Definition encode := parameterize_from_sig encode_sig.
    Definition encode_eq := parameterize_eq encode encode_sig.
    Hint Rewrite <- encode_eq : pattern_runtime.

    Definition add_cps_sig := parameterize_sig (@Core.B.Positional.add_cps).
    Definition add_cps := parameterize_from_sig add_cps_sig.
    Definition add_cps_eq := parameterize_eq add_cps add_cps_sig.
    Hint Rewrite <- add_cps_eq : pattern_runtime.

    Definition mul_cps_sig := parameterize_sig (@Core.B.Positional.mul_cps).
    Definition mul_cps := parameterize_from_sig mul_cps_sig.
    Definition mul_cps_eq := parameterize_eq mul_cps mul_cps_sig.
    Hint Rewrite <- mul_cps_eq : pattern_runtime.

    Definition reduce_cps_sig := parameterize_sig (@Core.B.Positional.reduce_cps).
    Definition reduce_cps := parameterize_from_sig reduce_cps_sig.
    Definition reduce_cps_eq := parameterize_eq reduce_cps reduce_cps_sig.
    Hint Rewrite <- reduce_cps_eq : pattern_runtime.

    Definition carry_reduce_cps_sig := parameterize_sig (@Core.B.Positional.carry_reduce_cps).
    Definition carry_reduce_cps := parameterize_from_sig carry_reduce_cps_sig.
    Definition carry_reduce_cps_eq := parameterize_eq carry_reduce_cps carry_reduce_cps_sig.
    Hint Rewrite <- carry_reduce_cps_eq : pattern_runtime.

    Definition negate_snd_cps_sig := parameterize_sig (@Core.B.Positional.negate_snd_cps).
    Definition negate_snd_cps := parameterize_from_sig negate_snd_cps_sig.
    Definition negate_snd_cps_eq := parameterize_eq negate_snd_cps negate_snd_cps_sig.
    Hint Rewrite <- negate_snd_cps_eq : pattern_runtime.

    Definition split_cps_sig := parameterize_sig (@Core.B.Positional.split_cps).
    Definition split_cps := parameterize_from_sig split_cps_sig.
    Definition split_cps_eq := parameterize_eq split_cps split_cps_sig.
    Hint Rewrite <- split_cps_eq : pattern_runtime.

    Definition scmul_cps_sig := parameterize_sig (@Core.B.Positional.scmul_cps).
    Definition scmul_cps := parameterize_from_sig scmul_cps_sig.
    Definition scmul_cps_eq := parameterize_eq scmul_cps scmul_cps_sig.
    Hint Rewrite <- scmul_cps_eq : pattern_runtime.

    Definition unbalanced_sub_cps_sig := parameterize_sig (@Core.B.Positional.unbalanced_sub_cps).
    Definition unbalanced_sub_cps := parameterize_from_sig unbalanced_sub_cps_sig.
    Definition unbalanced_sub_cps_eq := parameterize_eq unbalanced_sub_cps unbalanced_sub_cps_sig.
    Hint Rewrite <- unbalanced_sub_cps_eq : pattern_runtime.

    Definition sub_cps_sig := parameterize_sig (@Core.B.Positional.sub_cps).
    Definition sub_cps := parameterize_from_sig sub_cps_sig.
    Definition sub_cps_eq := parameterize_eq sub_cps sub_cps_sig.
    Hint Rewrite <- sub_cps_eq : pattern_runtime.

    Definition sub_sig := parameterize_sig (@Core.B.Positional.sub).
    Definition sub := parameterize_from_sig sub_sig.
    Definition sub_eq := parameterize_eq sub sub_sig.
    Hint Rewrite <- sub_eq : pattern_runtime.

    Definition opp_cps_sig := parameterize_sig (@Core.B.Positional.opp_cps).
    Definition opp_cps := parameterize_from_sig opp_cps_sig.
    Definition opp_cps_eq := parameterize_eq opp_cps opp_cps_sig.
    Hint Rewrite <- opp_cps_eq : pattern_runtime.

    Definition Fencode_sig := parameterize_sig (@Core.B.Positional.Fencode).
    Definition Fencode := parameterize_from_sig Fencode_sig.
    Definition Fencode_eq := parameterize_eq Fencode Fencode_sig.
    Hint Rewrite <- Fencode_eq : pattern_runtime.

    Definition Fdecode_sig := parameterize_sig (@Core.B.Positional.Fdecode).
    Definition Fdecode := parameterize_from_sig Fdecode_sig.
    Definition Fdecode_eq := parameterize_eq Fdecode Fdecode_sig.
    Hint Rewrite <- Fdecode_eq : pattern_runtime.

    Definition eval_from_sig := parameterize_sig (@Core.B.Positional.eval_from).
    Definition eval_from := parameterize_from_sig eval_from_sig.
    Definition eval_from_eq := parameterize_eq eval_from eval_from_sig.
    Hint Rewrite <- eval_from_eq : pattern_runtime.

    Definition select_cps_sig := parameterize_sig (@Core.B.Positional.select_cps).
    Definition select_cps := parameterize_from_sig select_cps_sig.
    Definition select_cps_eq := parameterize_eq select_cps select_cps_sig.
    Hint Rewrite <- select_cps_eq : pattern_runtime.

    Definition select_sig := parameterize_sig (@Core.B.Positional.select).
    Definition select := parameterize_from_sig select_sig.
    Definition select_eq := parameterize_eq select select_sig.
    Hint Rewrite <- select_eq : pattern_runtime.

  End Positional.
End B.

Definition modulo_sig := parameterize_sig (@Core.modulo).
Definition modulo := parameterize_from_sig modulo_sig.
Definition modulo_eq := parameterize_eq modulo modulo_sig.
Hint Rewrite <- modulo_eq : pattern_runtime.

Definition div_sig := parameterize_sig (@Core.div).
Definition div := parameterize_from_sig div_sig.
Definition div_eq := parameterize_eq div div_sig.
Hint Rewrite <- div_eq : pattern_runtime.
