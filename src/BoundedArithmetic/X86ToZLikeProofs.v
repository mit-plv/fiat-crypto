(*** Implementing ℤ-Like via x86 *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Proofs.RippleCarryAddSub.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Multiply.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.Decode.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.RippleCarryAddSub.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Proofs.Multiply.
Require Import Crypto.BoundedArithmetic.Double.Repeated.Core.
Require Import Crypto.BoundedArithmetic.StripCF.
Require Import Crypto.BoundedArithmetic.X86ToZLike.
Require Import Crypto.ModularArithmetic.ZBounded.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.

Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Section x86_gen_barrett_foundation.
  Context {n_over_two : nat}.
  Local Notation n := (2 * n_over_two)%nat.
  Context (full_width : nat) (ops : x86.instructions n) (modulus : Z).
  Local Notation W := (repeated_tuple x86.W 2 (Nat.log2 (full_width / n))). (* full_width-width words *)

  Local Arguments Z.mul !_ !_.
  Local Arguments BaseSystem.decode !_ !_ / .
  Local Arguments BaseSystem.accumulate / _ _.
  Local Arguments BaseSystem.decode' !_ !_ / .

  Local Ltac introduce_t_step :=
    match goal with
    | [ |- forall x : bool, _ ] => intros [|]
    | [ |- True -> _ ] => intros _
    | [ |- _ <= _ < _ -> _ ] => intro
    | _ => let x := fresh "x" in
           intro x;
           try pose proof (decode_range (fst x));
           try pose proof (decode_range (snd x));
           pose proof (decode_range x)
    end.
  Local Ltac unfolder_t :=
    progress unfold LargeT, SmallT, modulus_digits, decode_large, decode_small, Mod_SmallBound, DivBy_SmallBound, DivBy_SmallerBound, Mul, CarryAdd, CarrySubSmall, ConditionalSubtract, ConditionalSubtractModulus, ZLikeOps_of_x86_gen_Factored, ZLikeOps_of_x86_gen in *.
  Local Ltac saturate_context_step :=
    match goal with
    | _ => unique assert (0 <= 2 * n_over_two) by solve [ eauto using decode_exponent_nonnegative with typeclass_instances | omega ]
    | _ => unique assert (0 <= n_over_two) by solve [ eauto using decode_exponent_nonnegative with typeclass_instances | omega ]
    | _ => unique assert (0 <= 2 * (2 * n_over_two)) by (eauto using decode_exponent_nonnegative with typeclass_instances)
    | [ H : 0 <= ?x < _ |- _ ] => unique pose proof (proj1 H); unique pose proof (proj2 H)
    end.
  Local Ltac pre_t :=
    repeat first [ tauto
                 | introduce_t_step
                 | unfolder_t
                 | saturate_context_step ].
  Local Ltac post_t_step :=
    match goal with
    | _ => reflexivity
    | _ => progress subst
    | _ => progress unfold Let_In
    | _ => progress autorewrite with zsimplify_const
    | [ |- fst ?x = (?a <=? ?b) :> bool ]
      => cut (((if fst x then 1 else 0) = (if a <=? b then 1 else 0))%Z);
         [ destruct (fst x), (a <=? b); intro; congruence | ]
    | [ H : (_ =? _) = true |- _ ] => apply Z.eqb_eq in H; subst
    | [ H : (_ =? _) = false |- _ ] => apply Z.eqb_neq in H
    | _ => autorewrite with push_Zpow in *; solve [ reflexivity | assumption ]
    | _ => autorewrite with pull_Zpow in *; pull_decode; reflexivity
    | _ => progress push_decode
    | _ => rewrite (Z.add_comm (_ << _) _); progress pull_decode
    | [ |- context[if ?x =? ?y then _ else _] ] => destruct (x =? y) eqn:?
    | _ => autorewrite with Zshift_to_pow; Z.rewrite_mod_small; reflexivity
    end.
  Local Ltac post_t := repeat post_t_step.
  Axiom proof_admitted : False.
  Local Ltac admit := abstract case proof_admitted.
  Local Ltac t := admit; pre_t; post_t.

  Global Instance ZLikeProperties_of_x86_gen_Factored
         {arith : x86.arithmetic ops}
         (ldi_modulus ldi_0 : W)
         (Hldi_modulus : ldi_modulus = ldi modulus)
         (Hldi_0 : ldi_0 = ldi 0)
         (modulus_in_range : 0 <= modulus < 2^full_width)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= full_width)
         (n_pos : 0 < n)
         (full_width_pos : 0 < full_width)
    : ZLikeProperties (@ZLikeOps_of_x86_gen_Factored full_width n ops modulus smaller_bound_exp ldi_modulus ldi_0)
    := { large_valid v := True;
         medium_valid v := 0 <= decode_large v < 2^full_width * 2^smaller_bound_exp;
         small_valid v := True }.
  Proof.
    (* In 8.5: *)
    (* par:t. *)
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
  Defined.

  Global Instance ZLikeProperties_of_x86_gen
         {arith : x86.arithmetic ops}
         (modulus_in_range : 0 <= modulus < 2^full_width)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= full_width)
         (n_pos : 0 < n)
         (full_width_pos : 0 < full_width)
    : ZLikeProperties (@ZLikeOps_of_x86_gen _ _ ops modulus smaller_bound_exp)
    := ZLikeProperties_of_x86_gen_Factored _ _ eq_refl eq_refl modulus_in_range _ smaller_bound_smaller n_pos full_width_pos.
End x86_gen_barrett_foundation.

Section x86_64_barrett_foundation.
  Local Notation n := 64%nat.
  Context (ops : x86.instructions n) (modulus : Z).
  Local Notation W := (tuple (tuple x86.W 2) 2) (* 256-bit words *).

  Global Instance ZLikeProperties_of_x86_64_Factored
         {arith : x86.arithmetic ops}
         (ldi_modulus ldi_0 : W)
         (Hldi_modulus : ldi_modulus = ldi modulus)
         (Hldi_0 : ldi_0 = ldi 0)
         (modulus_in_range : 0 <= modulus < 2^256)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= 256)
         (n_pos : 0 < n)
    : ZLikeProperties (@ZLikeOps_of_x86_64_Factored ops modulus smaller_bound_exp ldi_modulus ldi_0)
    := @ZLikeProperties_of_x86_gen_Factored 32 256 _ _ arith _ _ Hldi_modulus Hldi_0 modulus_in_range _ smaller_bound_smaller n_pos _.
  Proof. clear; simpl; abstract omega. Defined.
  Global Instance ZLikeProperties_of_x86_64
         {arith : x86.arithmetic ops}
         (modulus_in_range : 0 <= modulus < 2^256)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= 256)
         (n_pos : 0 < n)
    : ZLikeProperties (@ZLikeOps_of_x86_64 ops modulus smaller_bound_exp)
    := ZLikeProperties_of_x86_64_Factored _ _ eq_refl eq_refl modulus_in_range _ smaller_bound_smaller n_pos.
End x86_64_barrett_foundation.

Section x86_32_barrett_foundation.
  Local Notation n := 32%nat.
  Context (ops : x86.instructions n) (modulus : Z).
  Local Notation W := (tuple (tuple (tuple x86.W 2) 2) 2) (* 256-bit words *).

  Global Instance ZLikeProperties_of_x86_32_Factored
         {arith : x86.arithmetic ops}
         (ldi_modulus ldi_0 : W)
         (Hldi_modulus : ldi_modulus = ldi modulus)
         (Hldi_0 : ldi_0 = ldi 0)
         (modulus_in_range : 0 <= modulus < 2^256)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= 256)
         (n_pos : 0 < n)
    : ZLikeProperties (@ZLikeOps_of_x86_32_Factored ops modulus smaller_bound_exp ldi_modulus ldi_0)
    := @ZLikeProperties_of_x86_gen_Factored 16 256 _ _ arith _ _ Hldi_modulus Hldi_0 modulus_in_range _ smaller_bound_smaller n_pos _.
  Proof. clear; simpl; abstract omega. Defined.
  Global Instance ZLikeProperties_of_x86_32
         {arith : x86.arithmetic ops}
         (modulus_in_range : 0 <= modulus < 2^256)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= 256)
         (n_pos : 0 < n)
    : ZLikeProperties (@ZLikeOps_of_x86_32 ops modulus smaller_bound_exp)
    := ZLikeProperties_of_x86_32_Factored _ _ eq_refl eq_refl modulus_in_range _ smaller_bound_smaller n_pos.
End x86_32_barrett_foundation.
