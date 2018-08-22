Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Local Open Scope Z_scope.

Ltac push_Zmod_step :=
  match goal with
  | _ => progress autorewrite with push_Zmod
  | [ |- context[(?x * ?y) mod ?z] ]
    => first [ rewrite (Z.mul_mod_push x y z) by Z.NoZMod
            | rewrite (Z.mul_mod_l_push x y z) by Z.NoZMod
            | rewrite (Z.mul_mod_r_push x y z) by Z.NoZMod ]
  | [ |- context[(?x + ?y) mod ?z] ]
    => first [ rewrite (Z.add_mod_push x y z) by Z.NoZMod
            | rewrite (Z.add_mod_l_push x y z) by Z.NoZMod
            | rewrite (Z.add_mod_r_push x y z) by Z.NoZMod ]
  | [ |- context[(?x - ?y) mod ?z] ]
    => first [ rewrite (Z.sub_mod_push x y z) by Z.NoZMod
            | rewrite (Z.sub_mod_l_push x y z) by Z.NoZMod
            | rewrite (Z.sub_mod_r_push x y z) by Z.NoZMod ]
  | [ |- context[(-?y) mod ?z] ]
    => rewrite (Z.opp_mod_mod_push y z) by Z.NoZMod
  | [ |- context[(?p^?q) mod ?z] ]
    => rewrite (Z.pow_mod_push p q z) by Z.NoZMod
  end.
Ltac push_Zmod := repeat push_Zmod_step.

Ltac push_Zmod_hyps_step :=
  match goal with
  | _ => progress autorewrite with push_Zmod in * |-
  | [ H : context[(?x * ?y) mod ?z] |- _ ]
    => first [ rewrite (Z.mul_mod_push x y z) in H by Z.NoZMod
            | rewrite (Z.mul_mod_l_push x y z) in H by Z.NoZMod
            | rewrite (Z.mul_mod_r_push x y z) in H by Z.NoZMod ]
  | [ H : context[(?x + ?y) mod ?z] |- _ ]
    => first [ rewrite (Z.add_mod_push x y z) in H by Z.NoZMod
            | rewrite (Z.add_mod_l_push x y z) in H by Z.NoZMod
            | rewrite (Z.add_mod_r_push x y z) in H by Z.NoZMod ]
  | [ H : context[(?x - ?y) mod ?z] |- _ ]
    => first [ rewrite (Z.sub_mod_push x y z) in H by Z.NoZMod
            | rewrite (Z.sub_mod_l_push x y z) in H by Z.NoZMod
            | rewrite (Z.sub_mod_r_push x y z) in H by Z.NoZMod ]
  | [ H : context[(-?y) mod ?z] |- _ ]
    => rewrite (Z.opp_mod_mod_push y z) in H by Z.NoZMod
  | [ H : context[(?p^?q) mod ?z] |- _ ]
    => rewrite (Z.pow_mod_push p q z) in H by Z.NoZMod
  end.
Ltac push_Zmod_hyps := repeat push_Zmod_hyps_step.

Ltac has_no_mod x z :=
  lazymatch x with
  | context[_ mod z] => fail
  | _ => idtac
  end.
Ltac pull_Zmod_step :=
  match goal with
  | [ |- context[((?x mod ?z) * (?y mod ?z)) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.mul_mod_full x y z)
  | [ |- context[((?x mod ?z) * ?y) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.mul_mod_l x y z)
  | [ |- context[(?x * (?y mod ?z)) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.mul_mod_r x y z)
  | [ |- context[((?x mod ?z) + (?y mod ?z)) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.add_mod_full x y z)
  | [ |- context[((?x mod ?z) + ?y) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.add_mod_l x y z)
  | [ |- context[(?x + (?y mod ?z)) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.add_mod_r x y z)
  | [ |- context[((?x mod ?z) - (?y mod ?z)) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.sub_mod_full x y z)
  | [ |- context[((?x mod ?z) - ?y) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.sub_mod_l x y z)
  | [ |- context[(?x - (?y mod ?z)) mod ?z] ]
    => has_no_mod x z; has_no_mod y z;
      rewrite <- (Z.sub_mod_r x y z)
  | [ |- context[(-(?y mod ?z)) mod ?z] ]
    => has_no_mod y z;
      rewrite <- (Z.opp_mod_mod y z)
  | [ |- context[((?x mod ?z)^?y) mod ?z] ]
    => has_no_mod x z;
      rewrite <- (Z.pow_mod_full x y z)
  | [ |- context[(?x mod ?z) mod ?z] ]
    => rewrite (Zmod_mod x z)
  | _ => progress autorewrite with pull_Zmod
  end.
Ltac pull_Zmod := repeat pull_Zmod_step.
