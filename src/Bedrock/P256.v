From Crypto.Bedrock.P256 Require Import Specs Platform Coord Jacobian.

Import Specs.NotationsCustomEntry Specs.coord Specs.point.

Import bedrock2.Syntax bedrock2.NotationsCustomEntry
LittleEndianList
ZArith.BinInt
BinInt BinNat Init.Byte
PrimeFieldTheorems ModInv
micromega.Lia
coqutil.Byte
Lists.List micromega.Lia
Jacobian
Coq.Strings.String Coq.Lists.List 
ProgramLogic WeakestPrecondition
ProgramLogic.Coercions
Word.Interface OfListWord Separation SeparationLogic
letexists
BasicC64Semantics
ListIndexNotations
SepAutoArray
symmetry
PeanoNat micromega.Lia
Tactics
UniquePose
micromega.Lia Word.Properties.

Import ListIndexNotations.
Local Open Scope list_index_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").
Local Notation "$ n" := (match word.of_Z n return word with w => w end) (at level 9, format "$ n").
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Coercion F.to_Z : F >-> Z.

Import coqutil.Map.Interface.
Import bedrock2.ToCString.
Import Macros.WithBaseName.
Import String List. Local Open Scope string_scope. Local Open Scope list_scope.


Axiom p256_coord_sqr : Syntax.func.
Axiom p256_coord_sqr_ok : forall functions, map.get functions "p256_coord_sqr" = Some p256_coord_sqr -> spec_of_p256_coord_sqr functions.

Axiom p256_coord_mul : Syntax.func.
Axiom p256_coord_mul_ok : forall functions, map.get functions "p256_coord_mul" = Some p256_coord_mul -> spec_of_p256_coord_mul functions.

Import shrd full_sub full_add full_mul memmove.

Definition platform := &[,
  full_add; full_sub; full_mul; shrd;
  br_value_barrier; br_declassify; br_broadcast_negative; br_broadcast_nonzero; br_broadcast_odd; br_cmov;  br_memcxor
  ].

Definition libc := &[, memmove; br_memcpy;  br_memset].

Local Definition c_func f : string := "static inline "++ c_func f.

Compute String.concat LF (List.map c_func platform).

Definition jacobian := &[,
 br_broadcast_odd;
 p256_coord_halve;

 p256_point_iszero;
 p256_point_double;
 p256_point_add_nz_nz_neq;
 p256_point_add_vartime_if_doubling
 ].

Compute String.concat LF (List.map c_func jacobian).

 (*
 p256_point_add_affine_nz_nz_neq;
 p256_point_add_affine_conditional

 sc_sub;
 sc_halve;
 fe_set_1;
  *)

Definition asm := &[, p256_coord_sqr; p256_coord_mul
 ].

Definition funcs := Eval cbv [List.app] in (jacobian ++ coord64 ++ asm ++ platform ++ libc)%list.

Ltac pose_correctness lem :=
  let funcs := match goal with |- _ (map.of_list ?funcs) => funcs end in
  let H := fresh in
  pose proof (lem (map.of_list funcs)) as H;
  unfold ProgramLogic.program_logic_goal_for in H;
  repeat lazymatch type of H with
    | map.get (map.of_list ?e) ?f = Some _ -> _ => specialize (H eq_refl)
      || let t := type of H in fail 1 "function" f "not found in environment" e
    | ?P -> _ => match goal with HH : P |- _ => specialize (H HH) end
      || let t := type of H in fail 1 "unsolved premises" t
    end.

Local Existing Instance memmove.spec_of_memmove.
#[export] Instance spec_of_memmove : spec_of "memmove". apply memmove.spec_of_memmove. Defined.

Lemma link_jacobian  : spec_of_p256_point_add_vartime_if_doubling (map.of_list funcs).
Proof.
  pose_correctness full_add_ok.
  pose_correctness full_sub_ok.
  pose_correctness full_mul_ok.
  pose_correctness value_barrier_ok.
  pose_correctness br_declassify_ok.
  pose_correctness br_broadcast_negative_ok.
  pose_correctness br_broadcast_nonzero_ok.
  pose_correctness br_cmov_ok.
  pose_correctness br_broadcast_odd_ok.

  pose_correctness memmove.memmove_ok.
  pose proof br_memcpy_ok (map.of_list funcs) eq_refl ltac:(assumption).
  pose_correctness br_memset_ok.
  pose_correctness br_memcxor_ok.

  pose_correctness shrd_ok.
  pose_correctness u256_shr_ok.
  pose_correctness u256_set_p256_minushalf_conditional_ok.

  pose_correctness p256_coord_add_ok.
  pose_correctness p256_coord_sub_nonmont_ok.
  pose_correctness p256_coord_sub_ok.
  pose_correctness fiat_coord_nonzero_ok.
  pose_correctness p256_coord_halve_ok.

  pose_correctness p256_coord_sqr_ok.
  pose_correctness p256_coord_mul_ok.
  
  pose_correctness p256_point_iszero_ok.
  pose_correctness p256_point_double_ok.

  pose_correctness p256_point_add_nz_nz_neq_ok.

  pose_correctness p256_point_add_vartime_if_doubling_ok.

  trivial.
Qed.

Print Assumptions link_jacobian.
