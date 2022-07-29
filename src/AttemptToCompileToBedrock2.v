Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.NatInt.NZPow.
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
Require Import Crypto.Util.Tactics.MoveLetIn.
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
Require Import Bedrock.Field.Stringification.Stringification.
Import ListNotations.

Require Import Crypto.Arithmetic.DettmanMultiplication.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Local Coercion Z.of_nat : nat >-> Z.

(* Check mulmod_general. *)

Local Open Scope Z_scope.

Definition e : nat := 256.
Definition c : list (Z*Z) := [(1, 2 ^ 32 + 977)].
Lemma p_nz : 2 ^ e - Associational.eval c <> 0.
Proof. discriminate. Qed.
Definition limbs : nat := 5.
Definition limb_size : nat := 52.
Lemma limbs_gteq_3 : (limbs >= 3)%nat.
Proof. cbv [limbs]. lia. Qed.
Lemma e_small : (e <= limb_size * limbs)%nat.
Proof. cbv [limb_size limbs e]. lia. Qed.
Lemma e_big : (limb_size * (limbs - 1) <= e)%nat.
Proof. cbv [limb_size limbs e]. lia. Qed.

Definition mulmod := mulmod_general e c limbs limb_size.
(* Check mulmod. *)

(* Check eval_mulmod_general e c p_nz limbs limb_size limbs_gteq_3 e_small e_big. *)

Definition weight := fun n => (2 ^ limb_size) ^ n.
Definition prime := 2 ^ e - Associational.eval c.

Definition eval_mulmod : forall a b,
  (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (prime) =
  (Positional.eval weight limbs (mulmod a b)) mod (prime)
:= eval_mulmod_general e c p_nz limbs limb_size limbs_gteq_3 e_small e_big.






Local Instance : split_mul_to_opt := Some (64, 64).
Local Instance : split_multiret_to_opt := None.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := [].
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : only_signed_opt := false.
Local Instance : no_select_size_opt := None.
Local Existing Instance default_low_level_rewriter_method.
(* Print default_low_level_rewriter_method. *)
(* Print precomputed_decision_tree. *)

Local Existing Instance ToString.C.OutputCAPI.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Existing Instance default_output_options.
Print default_output_options.
(* Print default_output_options. *)
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.
Local Instance : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : inline_opt := true.
Local Instance : inline_internal_opt := true.
Local Instance : emit_primitives_opt := true.

Definition m := 1. (* input magnitude *)
Definition M := m / 2 + 1. (* output magnitude *)

Definition input_bounds := Some ((repeat (Some r[0 ~> 2 * m * (2^52 - 1)]%zrange) 4) ++ [Some r[0 ~> 2 * m * (2^48 - 1)]%zrange]).
Definition output_bounds := Some ((repeat (Some r[0 ~> 2 * M * (2^52 - 1)]%zrange) 4) ++ [Some r[0 ~> 2 * M * (2^48 - 1)]%zrange]).

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "bitcoin_mul_u64"
        true true None [0; 64; 128] 64
        ltac:(let r := Reify (mulmod) in
              exact r)
               (fun _ _ => [])
               (input_bounds, (input_bounds, tt))
               output_bounds
               (None, (None, tt))
               None
   : Pipeline.ErrorT _).

(* Check Pipeline.BoundsPipeline. *)

Local Existing Instance OutputBedrock2API.

Time Redirect "log" Compute
  (Pipeline.BoundsPipelineToString
     "fiat_" "bitcoin_mul_u64"
        true true None [64; 128] 64
        ltac:(let r := Reify (mulmod) in
              exact r)
               (fun _ _ => [])
               (input_bounds, (input_bounds, tt))
               output_bounds
               (None, (None, tt))
               None
   : Pipeline.ErrorT _).
