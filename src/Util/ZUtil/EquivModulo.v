Require Import Coq.Classes.Morphisms.
Require Import Coq.Structures.Equalities.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Modulo.
Local Open Scope Z_scope.

Module Z.
  Section equiv_modulo.
    Context (N : Z).
    Definition equiv_modulo x y := x mod N = y mod N.
    Local Infix "==" := equiv_modulo.

    Local Instance equiv_modulo_Reflexive : Reflexive equiv_modulo := fun _ => Logic.eq_refl.
    Local Instance equiv_modulo_Symmetric : Symmetric equiv_modulo := fun _ _ => @Logic.eq_sym _ _ _.
    Local Instance equiv_modulo_Transitive : Transitive equiv_modulo := fun _ _ _ => @Logic.eq_trans _ _ _ _.

    Local Instance mul_mod_Proper : Proper (equiv_modulo ==> equiv_modulo ==> equiv_modulo) Z.mul.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance add_mod_Proper : Proper (equiv_modulo ==> equiv_modulo ==> equiv_modulo) Z.add.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance sub_mod_Proper : Proper (equiv_modulo ==> equiv_modulo ==> equiv_modulo) Z.sub.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance opp_mod_Proper : Proper (equiv_modulo ==> equiv_modulo) Z.opp.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance pow_mod_Proper : Proper (equiv_modulo ==> eq ==> equiv_modulo) Z.pow.
    Proof.
      intros ?? H ???; subst; hnf in H |- *.
      rewrite Z.mod_pow_full, H, <- Z.mod_pow_full; reflexivity.
    Qed.

    Local Instance modulo_equiv_modulo_Proper
      : Proper (equiv_modulo ==> (fun x y => x = N /\ N = y) ==> Logic.eq) Z.modulo.
    Proof.
      repeat intro; hnf in *; intuition congruence.
    Qed.
    Local Instance eq_to_ProperProxy : ProperProxy (fun x y : Z => x = N /\ N = y) N.
    Proof. split; reflexivity. Qed.

    Lemma div_to_inv_modulo a x x' : x > 0 -> x * x' mod N = 1 mod N -> (a / x) == ((a - a mod x) * x').
    Proof using Type.
      intros H xinv.
      replace (a / x) with ((a / x) * 1) by lia.
      change (x * x' == 1) in xinv.
      rewrite <- xinv.
      replace ((a / x) * (x * x')) with ((x * (a / x)) * x') by lia.
      rewrite Z.mul_div_eq by assumption.
      reflexivity.
    Qed.
  End equiv_modulo.
  Hint Rewrite div_to_inv_modulo using solve [ eassumption | lia ] : zstrip_div.

  Module EquivModuloInstances (dummy : Nop). (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4973 *)
    Existing Instance equiv_modulo_Reflexive.
    Existing Instance eq_Reflexive. (* prioritize [Reflexive eq] *)
    Existing Instance equiv_modulo_Symmetric.
    Existing Instance equiv_modulo_Transitive.
    Existing Instance mul_mod_Proper.
    Existing Instance add_mod_Proper.
    Existing Instance sub_mod_Proper.
    Existing Instance opp_mod_Proper.
    Existing Instance pow_mod_Proper.
    Existing Instance modulo_equiv_modulo_Proper.
    Existing Instance eq_to_ProperProxy.
  End EquivModuloInstances.
  Module RemoveEquivModuloInstances (dummy : Nop).
    Global Remove Hints equiv_modulo_Reflexive equiv_modulo_Symmetric equiv_modulo_Transitive mul_mod_Proper add_mod_Proper sub_mod_Proper opp_mod_Proper pow_mod_Proper modulo_equiv_modulo_Proper eq_to_ProperProxy : typeclass_instances.
  End RemoveEquivModuloInstances.
End Z.

(** Change [_ mod _ = _ mod _] to [Z.equiv_modulo _ _ _] *)
Ltac Zmod_to_equiv_modulo :=
  repeat match goal with
         | [ H : context T[?x mod ?M = ?y mod ?M] |- _ ]
           => let T' := context T[Z.equiv_modulo M x y] in change T' in H
         | [ |- context T[?x mod ?M = ?y mod ?M] ]
           => let T' := context T[Z.equiv_modulo M x y] in change T'
         end.
