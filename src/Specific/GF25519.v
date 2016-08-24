Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN precomputation. *)

Definition modulus : Z := 2^255 - 19.
Lemma prime_modulus : prime modulus. Admitted.
Definition int_width := 32%Z.

Instance params25519 : PseudoMersenneBaseParams modulus.
  construct_params prime_modulus 10%nat 255.
Defined.

Definition fe25519 := Eval compute in (tuple Z (length limb_widths)).

Definition mul2modulus : fe25519 :=
  Eval compute in (from_list_default 0%Z (length limb_widths) (construct_mul2modulus params25519)).

Instance subCoeff : SubtractionCoefficient.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus).
  vm_decide.
Defined.

Instance carryChain : CarryChain limb_widths.
  apply Build_CarryChain with (carry_chain := ([0;1;2;3;4;5;6;7;8;9;0;1])%nat).
  intros.
  repeat (destruct H as [|H]; [subst; vm_compute; repeat constructor | ]).
  contradiction H.
Defined.

Definition freezePreconditions25519 : freezePreconditions params25519 int_width.
Proof.
  constructor; compute_preconditions.
Defined.

(* Wire format for [pack] and [unpack] *)
Definition wire_widths := Eval compute in (repeat 32 7 ++ 31 :: nil).

Definition wire_digits := Eval compute in (tuple Z (length wire_widths)).

Lemma wire_widths_nonneg : forall w, In w wire_widths -> 0 <= w.
Proof.
  intros.
  repeat (destruct H as [|H]; [subst; vm_compute; congruence | ]).
  contradiction H.
Qed.

Lemma bits_eq : sum_firstn limb_widths (length limb_widths) = sum_firstn wire_widths (length wire_widths).
Proof.
  reflexivity.
Qed.

Lemma modulus_gt_2 : 2 < modulus. Proof. cbv; congruence. Qed.

(* Temporarily, we'll use addition chains equivalent to double-and-add. This is pending
   finding the real, more optimal chains from previous work. *)
Fixpoint pow2Chain'' p (pow2_index acc_index : nat) chain_acc : list (nat * nat) :=
  match p with
  | xI p' => pow2Chain'' p' 1 0
               (chain_acc ++ (pow2_index, pow2_index) :: (0%nat, S acc_index) :: nil)
  | xO p' => pow2Chain'' p' 0 (S acc_index)
               (chain_acc ++ (pow2_index, pow2_index)::nil)
  | xH => (chain_acc ++ (pow2_index, pow2_index) :: (0%nat, S acc_index) :: nil)
  end.

Fixpoint pow2Chain' p index  :=
  match p with
  | xI p' => pow2Chain'' p' 0 0 (repeat (0,0)%nat index)
  | xO p' => pow2Chain' p' (S index)
  | xH => repeat (0,0)%nat index
  end.

Definition pow2_chain p :=
  match p with
  | xH => nil
  | _ => pow2Chain' p 0
  end.

Definition invChain := Eval compute in pow2_chain (Z.to_pos (modulus - 2)).

Instance ic : InvExponentiationChain.
  apply Build_InvExponentiationChain with (chain := invChain).
  reflexivity.
Defined.

(* END precomputation *) 

(* Precompute k, c, zero, and one *)
Definition k_ := Eval compute in k.
Definition c_ := Eval compute in c.
Definition one_ := Eval compute in one.
Definition zero_ := Eval compute in zero.
Definition k_subst : k = k_ := eq_refl k_.
Definition c_subst : c = c_ := eq_refl c_.
Definition one_subst : one = one_ := eq_refl one_.
Definition zero_subst : zero = zero_ := eq_refl zero_.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Z.lor Let_In.

Definition app_7 {T} (f : wire_digits) (P : wire_digits -> T) : T.
Proof.
  cbv [wire_digits] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Definition app_7_correct {T} f (P : wire_digits -> T) : app_7 f P = P f.
Proof.
  intros.
  cbv [wire_digits] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  reflexivity.
Qed.

Definition app_10 {T} (f : fe25519) (P : fe25519 -> T) : T.
Proof.
  cbv [fe25519] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Definition app_10_correct {T} f (P : fe25519 -> T) : app_10 f P = P f.
Proof.
  intros.
  cbv [fe25519] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  reflexivity.
Qed.

Definition appify2 {T} (op : fe25519 -> fe25519 -> T) (f g : fe25519) :=
  app_10 f (fun f0 => (app_10 g (fun g0 => op f0 g0))).

Lemma appify2_correct : forall {T} op f g, @appify2 T op f g = op f g.
Proof.
  intros. cbv [appify2].
  etransitivity; apply app_10_correct.
Qed.

Definition add_sig (f g : fe25519) :
  { fg : fe25519 | fg = add_opt f g}.
Proof.
  eexists.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition add (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj1_sig (add_sig f g).

Definition add_correct (f g : fe25519)
  : add f g = add_opt f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (add_sig f g).

Definition sub_sig (f g : fe25519) :
  { fg : fe25519 | fg = sub_opt f g}.
Proof.
  eexists.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition sub (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj1_sig (sub_sig f g).

Definition sub_correct (f g : fe25519)
  : sub f g = sub_opt f g :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj2_sig (sub_sig f g).

(* For multiplication, we add another layer of definition so that we can
   rewrite under the [let] binders. *)
Definition mul_simpl_sig (f g : fe25519) :
  { fg : fe25519 | fg = carry_mul_opt k_ c_ f g}.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv. (* N.B. The slow part of this is computing with [Z_div_opt].
               It would be much faster if we could take advantage of
               the form of [base_from_limb_widths] when doing
               division, so we could do subtraction instead. *)
  autorewrite with zsimplify_fast.
  reflexivity.
Defined.

Definition mul_simpl (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_simpl_sig] in
  let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
  let '(g0, g1, g2, g3, g4, g5, g6, g7, g8, g9) := g in
  proj1_sig (mul_simpl_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)
                           (g0, g1, g2, g3, g4, g5, g6, g7, g8, g9)).

Definition mul_simpl_correct (f g : fe25519)
  : mul_simpl f g = carry_mul_opt k_ c_ f g.
Proof.
  pose proof (proj2_sig (mul_simpl_sig f g)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Qed.

Definition mul_sig (f g : fe25519) :
  { fg : fe25519 | fg = carry_mul_opt k_ c_ f g}.
Proof.
  eexists.
  rewrite <-mul_simpl_correct.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition mul (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_sig] in
  proj1_sig (mul_sig f g).

Definition mul_correct (f g : fe25519)
  : mul f g = carry_mul_opt k_ c_ f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (mul_sig f g).

Definition inv_sig (f : fe25519) :
  { g : fe25519 | g = inv_opt k_ c_ one_ f }.
Proof.
  eexists.
  cbv [inv_opt pow_opt].
  transitivity (@fold_chain_opt (tuple Z (length limb_widths)) one_ mul chain [f]).
  Focus 2. {
    rewrite fold_chain_opt_correct.
    rewrite <-one_subst.
    etransitivity; [ | symmetry; apply fold_chain_opt_correct ].
    apply Proper_fold_chain; auto.
    intros; cbv [eq]; subst.
    apply mul_correct.
  } Unfocus.
  cbv - [mul].
  reflexivity.
Defined.

Definition inv (f : fe25519) : fe25519
  := Eval cbv beta iota delta [proj1_sig inv_sig] in proj1_sig (inv_sig f).

Definition inv_correct (f : fe25519)
  : inv f = inv_opt k_ c_ one_ f
  := Eval cbv beta iota delta [proj2_sig inv_sig] in proj2_sig (inv_sig f).

Definition mbs_field := modular_base_system_field modulus_gt_2.

Import Morphisms.

Lemma field25519 : @field fe25519 eq zero one opp add sub mul inv div.
Proof.
  pose proof (Equivalence_Reflexive : Reflexive eq).
  eapply (Field.equivalent_operations_field (fieldR := mbs_field)).
  Grab Existential Variables.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros; rewrite mul_correct.
    rewrite carry_mul_opt_correct by auto using k_subst, c_subst.
    cbv [eq].
    rewrite carry_mul_rep by reflexivity.
    rewrite mul_rep; reflexivity.
  + intros; rewrite sub_correct, sub_opt_correct; reflexivity.
  + intros; rewrite add_correct, add_opt_correct; reflexivity.
  + intros; rewrite inv_correct, inv_opt_correct; reflexivity.
  + reflexivity.
Qed.

Lemma homomorphism_F25519 :
  @Ring.is_homomorphism
    (F modulus) Logic.eq F.one F.add F.mul
    fe25519 eq one add mul encode.
Proof.
  econstructor.
  + econstructor; [ | apply encode_Proper].
    intros; cbv [eq].
    rewrite add_correct, add_opt_correct, add_rep; apply encode_rep.
  + intros; cbv [eq].
    rewrite mul_correct, carry_mul_opt_correct, carry_mul_rep
      by auto using k_subst, c_subst, encode_rep.
    apply encode_rep.
  + reflexivity.
Qed.


Definition pack_simpl_sig (f : fe25519) :
  { f' | f' = pack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv [pack_opt].
  repeat (rewrite <-convert'_opt_correct;
          cbv - [from_list_default_opt Pow2BaseProofs.convert']).
  repeat progress rewrite ?Z.shiftl_0_r, ?Z.shiftr_0_r, ?Z.land_0_l, ?Z.lor_0_l, ?Z.land_same_r.
  cbv [from_list_default_opt].
  reflexivity.
Defined.

Definition pack_simpl (f : fe25519) :=
  Eval cbv beta iota delta [proj1_sig pack_simpl_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig (pack_simpl_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)).

Definition pack_simpl_correct (f : fe25519)
  : pack_simpl f = pack_opt params25519 wire_widths_nonneg bits_eq f.
Proof.
  pose proof (proj2_sig (pack_simpl_sig f)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Qed.

Definition pack_sig (f : fe25519) :
  { f' | f' = pack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  eexists.
  rewrite <-pack_simpl_correct.
  rewrite <-(@app_10_correct wire_digits).
  cbv.
  reflexivity.
Defined.

Definition pack (f : fe25519) : wire_digits :=
  Eval cbv beta iota delta [proj1_sig pack_sig] in proj1_sig (pack_sig f).

Definition pack_correct (f : fe25519)
  : pack f = pack_opt params25519 wire_widths_nonneg bits_eq f
  := Eval cbv beta iota delta [proj2_sig pack_sig] in proj2_sig (pack_sig f).

Definition unpack_simpl_sig (f : wire_digits) :
  { f' | f' = unpack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  cbv [wire_digits] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv [unpack_opt].
  repeat (
      rewrite <-convert'_opt_correct;
      cbv - [from_list_default_opt Pow2BaseProofs.convert']).
  repeat progress rewrite ?Z.shiftl_0_r, ?Z.shiftr_0_r, ?Z.land_0_l, ?Z.lor_0_l, ?Z.land_same_r.
  cbv [from_list_default_opt].
  reflexivity.
Defined.

Definition unpack_simpl (f : wire_digits) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig unpack_simpl_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7) := f in
    proj1_sig (unpack_simpl_sig (f0, f1, f2, f3, f4, f5, f6, f7)).

Definition unpack_simpl_correct (f : wire_digits)
  : unpack_simpl f = unpack_opt params25519 wire_widths_nonneg bits_eq f.
Proof.
  pose proof (proj2_sig (unpack_simpl_sig f)).
  cbv [wire_digits] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Qed.

Definition unpack_sig (f : wire_digits) :
  { f' | f' = unpack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  eexists.
  rewrite <-unpack_simpl_correct.
  rewrite <-(@app_7_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition unpack (f : wire_digits) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig unpack_sig] in proj1_sig (unpack_sig f).

Definition unpack_correct (f : wire_digits)
  : unpack f = unpack_opt params25519 wire_widths_nonneg bits_eq f
  := Eval cbv beta iota delta [proj2_sig pack_sig] in proj2_sig (unpack_sig f).

(* TODO: This file should eventually contain the following operations:
   inv
   opp
   zero
   one
   eq
*)
