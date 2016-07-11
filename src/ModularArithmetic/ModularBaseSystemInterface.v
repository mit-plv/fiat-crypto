Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.Util.Tuple Crypto.Util.CaseUtil.
Require Import ZArith.
Require Import Crypto.Algebra.
Import Group.
Import PseudoMersenneBaseParams PseudoMersenneBaseParamProofs.

Generalizable All Variables.
Section s.
  Context `{prm:PseudoMersenneBaseParams m} {sc : SubtractionCoefficient m prm}.
  Context {k_ c_} (pfk : k = k_) (pfc:c = c_).
  Local Notation base := (Pow2Base.base_from_limb_widths limb_widths).

  Definition fe := tuple Z (length base).

  Definition mul  (x y:fe) : fe :=
    carry_mul_opt_cps k_ c_ (from_list_default 0%Z (length base))
      (to_list _ x) (to_list _ y).

  Definition add : fe -> fe -> fe.
    refine (on_tuple2 add_opt _).
    abstract (intros; rewrite add_opt_correct, add_length_exact; case_max; omega).
  Defined.

  Definition sub : fe -> fe -> fe.
    refine (on_tuple2 sub_opt _).
    abstract (intros; rewrite sub_opt_correct; apply length_sub; rewrite ?coeff_length; auto).
  Defined.

  Arguments to_list {_ _} _.
  Definition phi (a : fe) : ModularArithmetic.F m := decode (to_list a).
  Definition phi_inv (a : ModularArithmetic.F m) : fe :=
    from_list_default 0%Z _ (encode a).

  Lemma phi_inv_spec : forall a, phi (phi_inv a) = a.
  Proof.
    intros; cbv [phi_inv phi].
    erewrite from_list_default_eq.
    rewrite to_list_from_list.
    apply ModularBaseSystemProofs.encode_rep.
    Grab Existential Variables.
    apply ModularBaseSystemProofs.encode_rep.
  Qed.

  Definition eq (x y : fe) : Prop := phi x = phi y.

  Definition zero : fe := phi_inv (ModularArithmetic.ZToField 0).

  Definition opp (x : fe) : fe := phi_inv (ModularArithmetic.opp (phi x)).

  Lemma add_correct : forall a b,
    to_list (add a b) = BaseSystem.add (to_list a) (to_list b).
  Proof.
    intros; cbv [add on_tuple2].
    rewrite to_list_from_list.
    apply add_opt_correct.
  Qed.

  Lemma add_phi : forall a b : fe,
    phi (add a b) = ModularArithmetic.add (phi a) (phi b).
  Proof.
    intros; cbv [phi].
    rewrite add_correct.
    apply ModularBaseSystemProofs.add_rep; auto using decode_rep, length_to_list.
  Qed.

  Lemma mul_correct : forall a b,
    to_list (mul a b) = carry_mul (to_list a) (to_list b).
  Proof.
    intros; cbv [mul].
    rewrite carry_mul_opt_cps_correct by assumption.
    erewrite from_list_default_eq.
    apply to_list_from_list.
    Grab Existential Variables.
    apply carry_mul_length; apply length_to_list.
  Qed.

  Lemma mul_phi : forall a b : fe,
    phi (mul a b) = ModularArithmetic.mul (phi a) (phi b).
  Proof.
    intros; cbv beta delta [phi].
    rewrite mul_correct.
    apply carry_mul_rep; auto using decode_rep, length_to_list.
  Qed.

End s.
