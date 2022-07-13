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


Import Stringification.C.
Import Stringification.C.Compilers.

Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

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

(*

* Implements arithmetic modulo FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F,
 *  represented as 5 uint64_t's in base 2^52, least significant first. Note that the limbs are allowed to
 *  contain >52 bits each.
 *
 *  Each field element has a 'magnitude' associated with it. Internally, a magnitude M means:
 *  - 2*M*(2^48-1) is the max (inclusive) of the most significant limb
 *  - 2*M*(2^52-1) is the max (inclusive) of the remaining limbs
 *
 *  Operations have different rules for propagating magnitude to their outputs. If an operation takes a
 *  magnitude M as a parameter, that means the magnitude of input field elements can be at most M (inclusive).
 *
 *  Each field element also has a 'normalized' flag. A field element is normalized if its magnitude is either
 *  0 or 1, and its value is already reduced modulo the order of the field.

...


...Therefore the output magnitude (M) has to be set such that:
     *     t0..t3: C * M >= C * (m/2 + 1/2)
     *         t4: D * M >= D * (m/2 + 1/4)
     *
     * It suffices for all limbs that, for any input magnitude m:
     *     M >= m/2 + 1/2
     *
     * and since we want the smallest such integer value for M:
     *     M == floor(m/2) + 1
     *)

Definition m := 1. (* input magnitude *)
Definition M := m / 2 + 1. (* output magnitude *)
Definition input_bounds := Some ((repeat (Some r[0 ~> 2 * m * (2^52 - 1)]%zrange) 4) ++ [Some r[0 ~> 2 * m * (2^48 - 1)]%zrange]).
Definition output_bounds := Some ((repeat (Some r[0 ~> 2 * M * (2^52 - 1)]%zrange) 4) ++ [Some r[0 ~> 2 * M * (2^48 - 1)]%zrange]).

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
