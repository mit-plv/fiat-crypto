(*** Proving ℤ-Like via Architecture *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.LegacyArithmetic.Interface.
Require Import Crypto.LegacyArithmetic.InterfaceProofs.
Require Import Crypto.LegacyArithmetic.Double.Core.
Require Import Crypto.LegacyArithmetic.Double.Proofs.RippleCarryAddSub.
Require Import Crypto.LegacyArithmetic.Double.Proofs.Multiply.
Require Import Crypto.LegacyArithmetic.ArchitectureToZLike.
Require Import Crypto.LegacyArithmetic.ZBounded.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.LetIn.

Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Local Coercion Z.of_nat : nat >-> Z.

Section fancy_machine_p256_montgomery_foundation.
  Context {n_over_two : Z}.
  Local Notation n := (2 * n_over_two)%Z.
  Context (ops : fancy_machine.instructions n) (modulus : Z).

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
    progress unfold LargeT, SmallT, modulus_digits, decode_large, decode_small, Mod_SmallBound, DivBy_SmallBound, DivBy_SmallerBound, Mul, CarryAdd, CarrySubSmall, ConditionalSubtract, ConditionalSubtractModulus, ZLikeOps_of_ArchitectureBoundedOps, ZLikeOps_of_ArchitectureBoundedOps_Factored in *.
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
  Local Ltac t := pre_t; post_t.

  Global Instance ZLikeProperties_of_ArchitectureBoundedOps_Factored
         {arith : fancy_machine.arithmetic ops}
         ldi_modulus ldi_0
         (Hldi_modulus : ldi_modulus = ldi modulus)
         (Hldi_0 : ldi_0 = ldi 0)
         (modulus_in_range : 0 <= modulus < 2^n)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= n)
         (n_pos : 0 < n)
    : ZLikeProperties (ZLikeOps_of_ArchitectureBoundedOps_Factored ops modulus smaller_bound_exp ldi_modulus ldi_0)
    := { large_valid v := True;
         medium_valid v := 0 <= decode_large v < 2^n * 2^smaller_bound_exp;
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

  Global Instance ZLikeProperties_of_ArchitectureBoundedOps
         {arith : fancy_machine.arithmetic ops}
         (modulus_in_range : 0 <= modulus < 2^n)
         (smaller_bound_exp : Z)
         (smaller_bound_smaller : 0 <= smaller_bound_exp <= n)
         (n_pos : 0 < n)
    : ZLikeProperties (ZLikeOps_of_ArchitectureBoundedOps ops modulus smaller_bound_exp)
    := ZLikeProperties_of_ArchitectureBoundedOps_Factored _ _ eq_refl eq_refl modulus_in_range _ smaller_bound_smaller n_pos.
End fancy_machine_p256_montgomery_foundation.
