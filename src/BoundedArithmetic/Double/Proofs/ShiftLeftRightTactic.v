Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope Z_scope.

Local Arguments Z.pow !_ !_.
Local Arguments Z.mul !_ !_.

Ltac shift_left_right_t :=
  repeat match goal with
         | [ |- ?x = ?x ] => reflexivity
         | [ |- Z.testbit ?x ?n = Z.testbit ?x ?n' ] => apply f_equal; try omega
         | [ |- orb (Z.testbit ?x _) (Z.testbit ?y _) = orb (Z.testbit ?x _) (Z.testbit ?y _) ]
           => apply f_equal2
         | _ => progress Z.ltb_to_lt
         | _ => progress subst
         | _ => progress unfold AutoRewrite.rewrite_eq
         | _ => progress intros
         | _ => omega
         | _ => solve [ trivial ]
         | _ => progress break_match_step ltac:(fun _ => idtac)
         | [ |- context[Z.lor (?x >> ?count) (Z.pow2_mod (?y << (?n - ?count)) ?n)] ]
           => unique assert (0 <= Z.lor (x >> count) (Z.pow2_mod (y << (n - count)) n) < 2 ^ n) by (autorewrite with Zshift_to_pow; auto with zarith nia)
         | _ => progress push_decode
         | [ |- context[Interface.decode (fst ?x)] ] => is_var x; destruct x; simpl in *
         | [ |- context[@Interface.decode ?n ?W ?d ?x] ] => is_var x; generalize dependent (@Interface.decode n W d x); intros
         | _ => progress Z.rewrite_mod_small
         | _ => progress autorewrite with convert_to_Ztestbit
         | _ => progress autorewrite with zsimplify_fast
         | [ |- _ = _ :> Z ] => apply Z.bits_inj'; intros
         | _ => progress autorewrite with Ztestbit_full
         | _ => progress autorewrite with bool_congr
         | [ |- Z.testbit _ (?x - ?y + (?y - ?z)) = false ]
           => autorewrite with zsimplify
         | [ H : 0 <= ?x < 2^?n |- Z.testbit ?x ?n' = false ]
           => assert (n <= n') by auto with zarith; progress Ztestbit
         | _ => progress Ztestbit_full
         end.
