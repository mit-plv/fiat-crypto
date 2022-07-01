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
Import ListNotations.


Import Stringification.C.
Import Stringification.C.Compilers.

Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional HelpfulFunctions.
Import ListNotations. Local Open Scope Z_scope.


Notation "a ** b" := (Zpower_nat a b)
  (at level 41, right associativity).

Definition s := 2 ** 256.

Definition c := [(2 ** 32 + 977, 1)].

Definition prime : Z := s - Associational.eval c.

Definition limbs : nat := 5.

Definition weight n := (2 ** 52) ** n.

Lemma weight_0 : weight 0 = 1.
Proof. trivial. Qed.

Lemma weight_nz : forall i, weight i <> 0.
Proof.
  intros i. cbv [weight]. rewrite Zpower_nat_Z. apply Z.pow_nonzero.
  - rewrite Zpower_nat_Z. apply Z.pow_nonzero; lia.
  - lia.
Qed.

Lemma s_nz : s <> 0.
Proof. discriminate. Qed.

Lemma p_nz : s - Associational.eval c <> 0.
Proof. discriminate. Qed.

Lemma mod_is_zero : forall base (n m : nat), base <> 0 -> le n m -> (base ** m) mod (base ** n) = 0.
  intros base n m H1 H2. induction H2.
  - rewrite Z_mod_same_full. constructor.
  - rewrite Zpower_nat_succ_r. rewrite Z.mul_mod_full. rewrite IHle. rewrite Z.mul_0_r.
    apply Z.mod_0_l. rewrite Zpower_nat_Z. apply Z.pow_nonzero; lia.
Qed.

Definition mulmod (a b : list Z) (*: list Z*) :=
  let reduce' := fun x1 x2 x3 x4 x5 => collect_terms (reduce_one x1 x2 x3 x4 x5) in
  let carry' := fun x1 x2 x3 => collect_terms (Associational.carry x1 x2 x3) in
  let a_assoc := Positional.to_associational weight limbs a in
  let b_assoc := Positional.to_associational weight limbs b in
  let r0 := Associational.mul a_assoc b_assoc in
  let r0' := collect_terms r0 in
  let r1 := carry' (weight 8) (weight 1) r0' in
  let r2 := reduce' s (weight 8) (weight limbs) c r1 in
  let r3 := carry' (weight 3) (weight 1) r2 in
  let r4 := reduce' s (weight 9) (weight limbs) c r3 in
  let r5 := carry' (weight 4) (weight 1) r4 in
  let r6 := carry' (weight 5) (weight 1) r5 in
  let r7 := carry_down (weight 5) (weight 5 / s) r6 in
  let r7' := collect_terms r7 in
  let r8 := carry' (weight 4) (s / weight 4) r7' in
  let r9 := reduce' s s s c r8 in
  let r10 := carry' (weight 0) (weight 1) r9 in
  let r11 := carry' (weight 6) (weight 1) r10 in
  let r12 := reduce' s (weight 6) (weight limbs) c r11 in
  let r13 := carry' (weight 1) (weight 1) r12 in
  let r14 := carry' (weight 7) (weight 1) r13 in
  let r15 := reduce' s (weight 7) (weight limbs) c r14 in
  let r16 := carry' (weight 2) (weight 1) r15 in
  let r17 := reduce' s (weight 8) (weight limbs) c r16 in
  let r18 := carry' (weight 3) (weight 1) r17 in
  Positional.from_associational weight limbs r18.

Theorem mulmod_works (a b : list Z) :
        (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - Associational.eval c) =
        (Positional.eval weight limbs (mulmod a b)) mod (s - Associational.eval c).
Proof.
  cbv [mulmod].
  repeat (try rewrite Positional.eval_from_associational;
          try rewrite Positional.eval_to_associational;
          try rewrite Associational.eval_carry;
          try rewrite eval_reduce_one;
          try rewrite eval_carry_down;
          try rewrite eval_collect_terms).
  rewrite Associational.eval_mul. repeat rewrite Positional.eval_to_associational. reflexivity.
  all: try (left; discriminate); try discriminate; try reflexivity; try apply weight_nz.
Qed.



Definition a := repeat (2 ** 47) 5.
Definition b := repeat 3 5.

Compute (mulmod a b).

Compute (Positional.eval weight limbs (mulmod a b) mod prime).
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
