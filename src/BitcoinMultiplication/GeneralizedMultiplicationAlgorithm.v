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

(* want to start with i = 1, so want to start with l_minus_2_minus_i = l - 2 - 1 *)
Fixpoint loop l_minus_2_minus_i l weight s c r0 :=
  match l_minus_2_minus_i with
  | O => r0
  | S l_minus_2_minus_i' => 
    let i := (l - 2) - l_minus_2_minus_i in
    let r1 := Associational.carry (weight (i + l)) (weight 1) r0 in
    let r2 := reduce_one s (weight (i + l)) (weight l) c r1 in
    let r3 := Associational.carry (weight i) (weight 1) r2 in
    loop l_minus_2_minus_i' l weight s c r3
  end.

Definition mulmod_general limbs weight s c a b :=
  let l := limbs in
  let a_assoc := Positional.to_associational weight limbs a in
  let b_assoc := Positional.to_associational weight limbs b in
  let r0 := Associational.mul a_assoc b_assoc in
  let r1 := Associational.carry (weight (2 * l - 2)) (weight 1) r0 in
  let r2 := reduce_one s (weight (2 * l - 2)) (weight l) c r1 in
  let r3 := Associational.carry (weight (l - 2)) (weight 1) r2 in
  let r4 := reduce_one s (weight (2 * l - 1)) (weight l) c r3 in
  let r5 := Associational.carry (weight (l - 1)) (weight 1) r4 in
  let r6 := Associational.carry (weight l) (weight 1) r5 in
  let r7 := carry_down (weight l) (weight l / s) r6 in
  let r8 := Associational.carry (weight (l - 1)) (s / weight (l - 1)) r7 in
  let r9 := reduce_one s s s c r8 in
  let r10 := Associational.carry (weight 0) (weight 1) r9 in
  let r11 := loop (l - 2 - 1) l weight s c r10 in
  let r12 := reduce_one s (weight (2 * l - 2)) (weight l) c r11 in
  let r13 := Associational.carry (weight (l - 2)) (weight 1) r12 in
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
