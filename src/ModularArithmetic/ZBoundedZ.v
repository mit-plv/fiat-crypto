(*** ℤ can be a bounded ℤ-Like type *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.ModularArithmetic.ZBounded.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.

Local Open Scope Z_scope.

Global Instance ZZLikeOps small_bound_exp smaller_bound_exp modulus : ZLikeOps (2^small_bound_exp) (2^smaller_bound_exp) modulus
  := { LargeT := Z;
       SmallT := Z;
       modulus_digits := modulus;
       decode_large x := x;
       decode_small x := x;
       Mod_SmallBound x := Z.pow2_mod x small_bound_exp;
       DivBy_SmallBound x := Z.shiftr x small_bound_exp;
       DivBy_SmallerBound x := Z.shiftr x smaller_bound_exp;
       Mul x y := (x * y)%Z;
       CarryAdd x y := dlet xpy := x + y in
                       ((2^small_bound_exp * 2^small_bound_exp <=? xpy), Z.pow2_mod xpy (2 * small_bound_exp));
       CarrySubSmall x y := dlet xmy := x - y in (xmy <? 0, Z.pow2_mod xmy small_bound_exp);
       ConditionalSubtract b x := dlet x := x in if b then Z.pow2_mod (x - modulus) small_bound_exp else x;
       ConditionalSubtractModulus x := dlet x := x in if x <? modulus then x else x - modulus }.

Local Arguments Z.mul !_ !_.

Class cls_is_true (x : bool) := build_is_true : x = true.
Hint Extern 1 (cls_is_true ?b) => vm_compute; reflexivity : typeclass_instances.

Local Ltac pre_t :=
  unfold cls_is_true, Let_In in *; Z.ltb_to_lt;
  match goal with
  | [ H : ?smaller_bound_exp <= ?small_bound_exp |- _ ]
    => is_var smaller_bound_exp; is_var small_bound_exp;
       assert (2^smaller_bound_exp <= 2^small_bound_exp) by auto with zarith;
       assert (2^small_bound_exp * 2^smaller_bound_exp <= 2^small_bound_exp * 2^small_bound_exp) by auto with zarith
  end.

Local Ltac t_step :=
  first [ progress simpl in *
        | progress intros
        | progress autorewrite with push_Zpow Zshift_to_pow in *
        | rewrite Z.pow2_mod_spec by omega
        | progress Z.ltb_to_lt
        | progress unfold Let_In in *
        | solve [ auto with zarith ]
        | nia
        | progress break_match ].
Local Ltac t := pre_t; repeat t_step.

Global Instance ZZLikeProperties {small_bound_exp smaller_bound_exp modulus}
       {Hss : cls_is_true (0 <=? smaller_bound_exp)}
       {Hs : cls_is_true (0 <=? small_bound_exp)}
       {Hs_ss : cls_is_true (smaller_bound_exp <=? small_bound_exp)}
       {Hmod0 : cls_is_true (0 <=? modulus)}
       {Hmod1 : cls_is_true (modulus <? 2^small_bound_exp)}
  : ZLikeProperties (@ZZLikeOps small_bound_exp smaller_bound_exp modulus)
  := { large_valid x := 0 <= x < 2^(2*small_bound_exp);
       medium_valid x := 0 <= x < 2^(small_bound_exp + smaller_bound_exp);
       small_valid x := 0 <= x < 2^small_bound_exp }.
Proof.
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
