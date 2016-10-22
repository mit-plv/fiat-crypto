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
Require Import Crypto.Util.Bool.
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

Local Opaque Let_In.
Local Arguments interp_radd / _ _.
Local Arguments interp_rsub / _ _.
Local Arguments interp_rmul / _ _.
Local Arguments interp_ropp / _.
Local Arguments interp_rfreeze / _.
Definition addW (f g : fe25519W) : fe25519W := Eval simpl in interp_radd f g.
Definition subW (f g : fe25519W) : fe25519W := Eval simpl in interp_rsub f g.
Definition mulW (f g : fe25519W) : fe25519W := Eval simpl in interp_rmul f g.
Definition oppW (f : fe25519W) : fe25519W := Eval simpl in interp_ropp f.
Definition freezeW (f : fe25519W) : fe25519W := Eval simpl in interp_rfreeze f.
Local Transparent Let_In.
Definition powW (f : fe25519W) chain := fold_chain_opt (proj1_fe25519W one) mulW chain [f].
Definition invW (f : fe25519W) : fe25519W
  := Eval cbv -[Let_In fe25519W mulW] in powW f (chain inv_ec).

Local Ltac port_correct_and_bounded interp opW rop rop_cb :=
  change opW with (interp rop);
  intros; apply rop_cb; assumption.
Local Ltac bport_correct_and_bounded := port_correct_and_bounded interp_bexpr.
Local Ltac uport_correct_and_bounded := port_correct_and_bounded interp_uexpr.

Lemma addW_correct_and_bounded : ibinop_correct_and_bounded addW carry_add.
Proof. bport_correct_and_bounded addW radd radd_correct_and_bounded. Qed.
Lemma subW_correct_and_bounded : ibinop_correct_and_bounded subW carry_sub.
Proof. bport_correct_and_bounded subW rsub rsub_correct_and_bounded. Qed.
Lemma mulW_correct_and_bounded : ibinop_correct_and_bounded mulW mul.
Proof. bport_correct_and_bounded mulW rmul rmul_correct_and_bounded. Qed.
Lemma oppW_correct_and_bounded : iunop_correct_and_bounded oppW carry_opp.
Proof. uport_correct_and_bounded oppW ropp ropp_correct_and_bounded. Qed.
Lemma freezeW_correct_and_bounded : iunop_correct_and_bounded freezeW freeze.
Proof. uport_correct_and_bounded freezeW rfreeze rfreeze_correct_and_bounded. Qed.

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

Definition fieldwisebW_sig (f g : fe25519W)
  : { b | b = GF25519.fieldwiseb (fe25519WToZ f) (fe25519WToZ g) }.
Proof.
  hnf in f, g; destruct_head' prod.
  eexists.
  cbv [GF25519.fieldwiseb fe25519WToZ].
  rewrite !word64eqb_Zeqb.
  reflexivity.
Defined.

Definition fieldwisebW (f g : fe25519W) : bool :=
  Eval cbv beta iota delta [proj1_sig fieldwisebW_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    let '(g0, g1, g2, g3, g4, g5, g6, g7, g8, g9) := g in
    proj1_sig (fieldwisebW_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)
                               (g0, g1, g2, g3, g4, g5, g6, g7, g8, g9)).

Lemma fieldwisebW_correct f g
  : fieldwisebW f g = GF25519.fieldwiseb (fe25519WToZ f) (fe25519WToZ g).
Proof.
  set (f' := f); set (g' := g).
  hnf in f, g; destruct_head' prod.
  exact (proj2_sig (fieldwisebW_sig f' g')).
Qed.

Local Arguments freezeW : simpl never.

Definition eqbW_sig (f g : fe25519W)
  : { b | is_bounded (fe25519WToZ f) = true
          -> is_bounded (fe25519WToZ g) = true
          -> b = GF25519.eqb (fe25519WToZ f) (fe25519WToZ g) }.
Proof.
  pose proof (fun pf => proj1 (freezeW_correct_and_bounded f pf)) as frf.
  pose proof (fun pf => proj1 (freezeW_correct_and_bounded g pf)) as frg.
  hnf in f, g; destruct_head' prod.
  eexists.
  unfold GF25519.eqb.
  simpl @fe25519WToZ in *; cbv beta iota.
  intros.
  rewrite <- frf, <- frg by assumption.
  rewrite <- fieldwisebW_correct.
  reflexivity.
Defined.

Definition eqbW (f g : fe25519W) : bool :=
  Eval cbv beta iota delta [proj1_sig eqbW_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    let '(g0, g1, g2, g3, g4, g5, g6, g7, g8, g9) := g in
    proj1_sig (eqbW_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)
                               (g0, g1, g2, g3, g4, g5, g6, g7, g8, g9)).

Lemma eqbW_correct f g
  : is_bounded (fe25519WToZ f) = true
    -> is_bounded (fe25519WToZ g) = true
    -> eqbW f g = GF25519.eqb (fe25519WToZ f) (fe25519WToZ g).
Proof.
  set (f' := f); set (g' := g).
  hnf in f, g; destruct_head' prod.
  exact (proj2_sig (eqbW_sig f' g')).
Qed.

Definition sqrt_m1W : fe25519W :=
  Eval vm_compute in fe25519ZToW sqrt_m1.

Definition sqrtW_sig
  : { sqrtW | iunop_correct_and_bounded sqrtW GF25519.sqrt }.
Proof.
  eexists.
  unfold GF25519.sqrt.
  intros; rewrite <- (fun pf => proj1 (powW_correct_and_bounded _ _ pf)) by assumption.
  match goal with
  | [ |- context G[dlet x := fe25519WToZ ?v in @?f x] ]
    => let G' := context G[dlet x := v in f (fe25519WToZ x)] in
       cut G'; cbv beta;
         [ cbv [Let_In]; exact (fun x => x) | ]
  end.
  split.
  { etransitivity.
    Focus 2. {
      apply Proper_Let_In_nd_changebody_eq; intros.
      set_evars.
      change sqrt_m1 with (fe25519WToZ sqrt_m1W).
      rewrite <- !(fun X Y => proj1 (mulW_correct_and_bounded _ _ X Y)), <- eqbW_correct, (pull_bool_if fe25519WToZ)
        by repeat match goal with
                  | _ => progress subst
                  | [ |- is_bounded (fe25519WToZ ?op) = true ]
                    => lazymatch op with
                       | mulW _ _ => apply mulW_correct_and_bounded
                       | powW _ _ => apply powW_correct_and_bounded
                       | sqrt_m1W => vm_compute; reflexivity
                       | _ => assumption
                       end
                  end.
      subst_evars; reflexivity.
    } Unfocus.
    lazymatch goal with
    | [ |- context G[dlet x := ?v in fe25519WToZ (@?f x)] ]
      => let G' := context G[fe25519WToZ (dlet x := v in f x)] in
         cut G'; cbv beta;
           [ cbv [Let_In]; exact (fun x => x) | apply f_equal ]
    end.
    reflexivity. }
  { cbv [Let_In].
    break_if.
    { apply powW_correct_and_bounded; assumption. }
    { apply mulW_correct_and_bounded; [ vm_compute; reflexivity | ].
      apply powW_correct_and_bounded; assumption. } }
Defined.

Definition sqrtW (f : fe25519W) : fe25519W :=
  Eval cbv beta iota delta [proj1_sig sqrtW_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig sqrtW_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9).

Lemma sqrtW_correct_and_bounded : iunop_correct_and_bounded sqrtW GF25519.sqrt.
Proof.
  intro f.
  set (f' := f).
  hnf in f; destruct_head' prod.
  assert (H : sqrtW f' = proj1_sig sqrtW_sig f')
    by (subst f'; cbv beta iota delta [proj1_sig sqrtW_sig sqrtW]; reflexivity).
  rewrite H.
  exact (proj2_sig sqrtW_sig f').
Qed.

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

Definition pow (f : fe25519) (chain : list (nat * nat)) : fe25519.
Proof. define_unop f (fun x => powW x chain) powW_correct_and_bounded. Defined.
Definition inv (f : fe25519) : fe25519.
Proof. define_unop f invW invW_correct_and_bounded. Defined.
Definition sqrt (f : fe25519) : fe25519.
Proof. define_unop f sqrtW sqrtW_correct_and_bounded. Defined.

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
Lemma sqrt_correct (f : fe25519) : proj1_fe25519 (sqrt f) = GF25519.sqrt (proj1_fe25519 f).
Proof. unop_correct_t sqrt sqrt sqrtW_correct_and_bounded. Qed.

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

(** TODO: pack, unpack *)
