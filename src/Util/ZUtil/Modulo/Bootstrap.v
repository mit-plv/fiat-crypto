(** Basic lemmas about [Z.modulo] for bootstrapping various tactics *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma mod_0_r_eq a b : b = 0 -> a mod b = 
  ltac:(match eval hnf in (1 mod 0) with | 0 => exact 0 | _ => exact a end).
  Proof. intro; subst; auto with zarith. Qed.
#[global]
  Hint Resolve mod_0_r_eq : zarith.
#[global]
  Hint Rewrite mod_0_r_eq using assumption : zsimplify.

  Lemma div_mod_cases x y : ((x = y * (x / y) + x mod y /\ (y < x mod y <= 0 \/ 0 <= x mod y < y))
                             \/ (y = 0 /\ x / y = 0 /\ x mod y = ltac:(match eval hnf in (1 mod 0) with | 0 => exact 0 | _ => exact x end))).
  Proof.
    destruct (Z_zerop y); [ right; subst; auto with zarith | left ]; subst.
    split; [ apply Z.div_mod; assumption | ].
    destruct (Z_dec' y 0) as [ [H|H] | H]; [ left | right | congruence ].
    { apply Z.mod_neg_bound; assumption. }
    { apply Z.mod_pos_bound; assumption. }
  Qed.
End Z.
