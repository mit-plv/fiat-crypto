Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
Require Import Coq.Numbers.NatInt.NZDiv.
(** * Push-Button Synthesis Examples *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.C.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.BitcoinMultiplication.HelpfulFunctions.
Require Import Crypto.BitcoinMultiplication.OriginalMultiplicationAlgorithm.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional HelpfulFunctions.
Import ListNotations. Local Open Scope Z_scope.

Local Open Scope nat_scope.

(* want to start with i = 1 (up to l - 2, excludsive), so want to start with l_minus_2_minus_i = l - 2 - 1 *)
Fixpoint loop l weight s c l_minus_2_minus_i r0 :=
  match l_minus_2_minus_i with
  | O => r0
  | S l_minus_2_minus_i' =>
    let i := (l - 2) - l_minus_2_minus_i in
    let r1 := Associational.carry (weight (i + l)) (weight 1) r0 in
    let r2 := reduce_one s (weight (i + l)) (weight l) c r1 in
    let r3 := Associational.carry (weight i) (weight 1) r2 in
    loop l weight s c l_minus_2_minus_i' r3
  end.

Definition reduce' x1 x2 x3 x4 x5 := collect_terms (reduce_one x1 x2 x3 x4 x5).
Definition carry' x1 x2 x3 := collect_terms (Associational.carry x1 x2 x3).

Definition loop_body limbs weight s c i before :=
  let middle1 := carry' (weight (i + limbs)) (weight 1) before in
  let middle2 := reduce' s (weight (i + limbs)) (weight limbs) c middle1 in
  let after := carry' (weight i) (weight 1) middle2 in
  after.

Definition from_n_to_one n :=
  fold_right (fun (x :nat) l' => (length l' + 1) :: l') [] (repeat 0 n).

Compute (from_n_to_one 2).

Definition loop' limbs weight s c start :=
  fold_right (loop_body limbs weight s c) start (from_n_to_one (*(limbs - 2 - 1)*)2).

Definition mulmod_general limbs weight s c a b :=
  let l := limbs in
  let a_assoc := Positional.to_associational weight limbs a in
  let b_assoc := Positional.to_associational weight limbs b in
  let r0 := Associational.mul a_assoc b_assoc in
  let r0' := collect_terms r0 in
  let r1 := carry' (weight (2 * l - 2)) (weight 1) r0' in
  let r2 := reduce' s (weight (2 * l - 2)) (weight l) c r1 in
  let r3 := carry' (weight (l - 2)) (weight 1) r2 in
  let r4 := reduce' s (weight (2 * l - 1)) (weight l) c r3 in
  let r5 := carry' (weight (l - 1)) (weight 1) r4 in
  let r6 := carry' (weight l) (weight 1) r5 in
  let r7 := carry_down (weight l) (weight l / s) r6 in
  let r7' := collect_terms r7 in
  let r8 := carry' (weight (l - 1)) (Z.div s (weight (l - 1))) r7' in
  let r9 := reduce' s s s c r8 in
  let r10 := carry' (weight 0) (weight 1) r9 in
  let r11 := loop' l weight s c r10 in
  let r12 := reduce' s (weight (2 * l - 2)) (weight l) c r11 in
  let r13 := carry' (weight (l - 2)) (weight 1) r12 in
  Positional.from_associational weight l r13.

Local Open Scope Z_scope.

Notation "a ** b" := (Zpower_nat a b)
  (at level 41, right associativity).

Definition s := 2 ** 256.

Definition c := [(2 ** 32 + 977, 1)].

Definition prime : Z := s - Associational.eval c.

Definition limbs : nat := 5.

Definition weight n := (2 ** 52) ** n.

Definition a := repeat (2 ** 47) 5.
Definition b := repeat 3 5.

Import OriginalMultiplicationAlgorithm.

Compute (mulmod_general limbs weight s c a b).

Compute (mulmod a b).

Compute (Positional.eval weight limbs (mulmod a b) mod prime).
Compute (Positional.eval weight limbs (mulmod_general limbs weight s c a b) mod prime).
Compute ((Positional.eval weight limbs a * Positional.eval weight limbs b) mod prime).

Local Instance : split_mul_to_opt := None.
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := [].
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.

Local Existing Instance ToString.C.OutputCAPI.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Existing Instance default_output_options.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : inline_opt := true.
Local Instance : inline_internal_opt := true.
Local Instance : emit_primitives_opt := true.

Definition input_bounds := Some ((repeat (Some r[0 ~> 2 * m * (2^52 - 1)]%zrange) 4) ++ [Some r[0 ~> 2 * m * (2^48 - 1)]%zrange]).
Definition output_bounds := Some ((repeat (Some r[0 ~> 2 * M * (2^52 - 1)]%zrange) 4) ++ [Some r[0 ~> 2 * M * (2^48 - 1)]%zrange]).

Definition thing := mulmod_general limbs weight s c.

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "bitcoin_mul_u64"
        true true None [64; 128] 64
        ltac:(let r := Reify (mulmod_general limbs weight s c) in
              exact r)
               (fun _ _ => [])
               (input_bounds, (input_bounds, tt))
               output_bounds
               (None, (None, tt))
               None
   : Pipeline.ErrorT _).
