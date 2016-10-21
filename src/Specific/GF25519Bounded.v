Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Assembly.GF25519BoundedInstantiation.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.


Local Ltac bounded_t opW blem :=
  apply blem; apply is_bounded_proj1_fe25519.

Local Ltac define_binop f g opW blem :=
  refine (exist_fe25519W (opW (proj1_fe25519W f) (proj1_fe25519W g)) _);
  abstract bounded_t opW blem.
Local Ltac define_unop f opW blem :=
  refine (exist_fe25519W (opW (proj1_fe25519W f)) _);
  abstract bounded_t opW blem.

Definition addW (f g : fe25519W) : fe25519W := interp_bexpr radd f g.
Definition subW (f g : fe25519W) : fe25519W := interp_bexpr rsub f g.
Definition mulW (f g : fe25519W) : fe25519W := interp_bexpr rmul f g.
Definition oppW (f : fe25519W) : fe25519W := interp_uexpr ropp f.
Definition freezeW (f : fe25519W) : fe25519W := interp_uexpr rfreeze f.
Definition powW (f : fe25519W) chain := fold_chain_opt (proj1_fe25519W one) mulW chain [f].
Definition invW (f : fe25519W) : fe25519W
  := Eval cbv -[Let_In fe25519W mulW] in powW f (chain inv_ec).

Definition add (f g : fe25519) : fe25519.
Proof. define_binop f g addW radd_correct_and_bounded. Defined.
Definition sub (f g : fe25519) : fe25519.
Proof. define_binop f g subW rsub_correct_and_bounded. Defined.
Definition mul (f g : fe25519) : fe25519.
Proof. define_binop f g mulW rmul_correct_and_bounded. Defined.
Definition opp (f : fe25519) : fe25519.
Proof. define_unop f oppW ropp_correct_and_bounded. Defined.
Definition freeze (f : fe25519) : fe25519.
Proof. define_unop f freezeW rfreeze_correct_and_bounded. Defined.

Lemma powW_correct_and_bounded chain : iunop_correct_and_bounded (fun x => powW x chain) (fun x => pow x chain).
Proof.
  cbv [powW pow].
  intro x; intros; apply (fold_chain_opt_gen fe25519WToZ is_bounded [x]).
  { reflexivity. }
  { reflexivity. }
  { intros; progress rewrite <- ?mul_correct,
            <- ?(fun X Y => proj1 (rmul_correct_and_bounded _ _ X Y)) by assumption.
    apply rmul_correct_and_bounded; assumption. }
  { intros; symmetry; apply rmul_correct_and_bounded; assumption. }
  { intros [|?]; autorewrite with simpl_nth_default;
      (assumption || reflexivity). }
Qed.

Lemma invW_correct_and_bounded : iunop_correct_and_bounded invW inv.
Proof.
  intro f.
  assert (H : forall f, invW f = powW f (chain inv_ec))
    by abstract (cbv -[Let_In fe25519W mulW]; reflexivity).
  rewrite !H.
  rewrite inv_correct.
  cbv [inv_opt].
  rewrite <- pow_correct.
  apply powW_correct_and_bounded.
Qed.

Definition pow (f : fe25519) (chain : list (nat * nat)) : fe25519.
Proof. define_unop f (fun x => powW x chain) powW_correct_and_bounded. Defined.
Definition inv (f : fe25519) : fe25519.
Proof. define_unop f invW invW_correct_and_bounded. Defined.

Local Ltac unop_correct_t op opW rop_correct_and_bounded :=
  cbv [op opW]; rewrite proj1_fe25519_exist_fe25519W;
  rewrite (fun X => proj1 (rop_correct_and_bounded _ X)) by apply is_bounded_proj1_fe25519;
  try reflexivity.
Local Ltac binop_correct_t op opW rop_correct_and_bounded :=
  cbv [op opW]; rewrite proj1_fe25519_exist_fe25519W;
  rewrite (fun X Y => proj1 (rop_correct_and_bounded _ _ X Y)) by apply is_bounded_proj1_fe25519;
  try reflexivity.

Lemma add_correct (f g : fe25519) : proj1_fe25519 (add f g) = carry_add (proj1_fe25519 f) (proj1_fe25519 g).
Proof. binop_correct_t add addW radd_correct_and_bounded. Qed.
Lemma sub_correct (f g : fe25519) : proj1_fe25519 (sub f g) = carry_sub (proj1_fe25519 f) (proj1_fe25519 g).
Proof. binop_correct_t sub subW rsub_correct_and_bounded. Qed.
Lemma mul_correct (f g : fe25519) : proj1_fe25519 (mul f g) = GF25519.mul (proj1_fe25519 f) (proj1_fe25519 g).
Proof. binop_correct_t mul mulW rmul_correct_and_bounded. Qed.
Lemma opp_correct (f : fe25519) : proj1_fe25519 (opp f) = carry_opp (proj1_fe25519 f).
Proof. unop_correct_t opp oppW ropp_correct_and_bounded. Qed.
Lemma freeze_correct (f : fe25519) : proj1_fe25519 (freeze f) = GF25519.freeze (proj1_fe25519 f).
Proof. unop_correct_t freeze freezeW rfreeze_correct_and_bounded. Qed.
Lemma pow_correct (f : fe25519) chain : proj1_fe25519 (pow f chain) = GF25519.pow (proj1_fe25519 f) chain.
Proof. unop_correct_t pow pow (powW_correct_and_bounded chain). Qed.
Lemma inv_correct (f : fe25519) : proj1_fe25519 (inv f) = GF25519.inv (proj1_fe25519 f).
Proof. unop_correct_t inv inv invW_correct_and_bounded. Qed.

Import Morphisms.

Lemma field25519 : @field fe25519 eq zero one opp add sub mul inv div.
Proof.
  assert (Reflexive eq) by (repeat intro; reflexivity).
  eapply (Field.field_from_redundant_representation
            (fieldF:=Specific.GF25519.carry_field25519)
            (phi':=proj1_fe25519)).
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { intros; rewrite opp_correct; reflexivity. }
  { intros; rewrite add_correct; reflexivity. }
  { intros; rewrite sub_correct; reflexivity. }
  { intros; rewrite mul_correct; reflexivity. }
  { intros; rewrite inv_correct; reflexivity. }
  { cbv [div]; intros; rewrite proj1_fe25519_exist_fe25519; reflexivity. }
Qed.

Local Opaque proj1_fe25519 exist_fe25519 proj1_fe25519W exist_fe25519W.
Lemma homomorphism_F25519 :
  @Ring.is_homomorphism
    (F modulus) Logic.eq F.one F.add F.mul
    fe25519 eq one add mul encode.
Proof.
  pose proof homomorphism_carry_F25519 as H.
  destruct H as [ [H0 H1] H2 H3].
  econstructor; [ econstructor | | ];
    cbv [eq encode]; repeat intro;
      rewrite ?add_correct, ?mul_correct, ?proj1_fe25519_exist_fe25519, ?proj1_fe25519_exist_fe25519W, ?proj1_fe25519W_exist_fe25519 in *.
  { rewrite H0; reflexivity. }
  { apply H1; assumption. }
  { rewrite H2; reflexivity. }
  { reflexivity. }
Qed.

(** TODO: pack, unpack, sqrt *)
