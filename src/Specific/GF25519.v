Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN PseudoMersenneBaseParams instance construction. *)

Definition modulus : Z := 2^255 - 19.
Lemma prime_modulus : prime modulus. Admitted.
Definition int_width := 32%Z.

Instance params25519 : PseudoMersenneBaseParams modulus.
  construct_params prime_modulus 10%nat 255.
Defined.

Definition fe25519 := Eval compute in (tuple Z (length limb_widths)).

Definition mul2modulus := 
  Eval compute in (from_list_default 0%Z (length limb_widths) (construct_mul2modulus params25519)).

Instance subCoeff : SubtractionCoefficient modulus params25519.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus).
  apply ZToField_eqmod.
  cbv; reflexivity.
Defined.

Definition freezePreconditions25519 : freezePreconditions params25519 int_width.
Proof.
  constructor; compute_preconditions.
Defined.

(* END PseudoMersenneBaseParams instance construction. *)

(* Precompute k and c *)
Definition k_ := Eval compute in k.
Definition c_ := Eval compute in c.
Definition k_subst : k = k_ := eq_refl k_.
Definition c_subst : c = c_ := eq_refl c_.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Let_In.

Definition app_10 (f : fe25519) (P : fe25519 -> fe25519) : fe25519.
Proof.
  cbv [fe25519] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Lemma app_10_correct : forall f P, app_10 f P = P f.
Proof.
  intros.
  cbv [fe25519] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  reflexivity.
Qed.

Definition appify2 (op : fe25519 -> fe25519 -> fe25519) (f g : fe25519):= 
  app_10 f (fun f0 => (app_10 g (fun g0 => op f0 g0))).

Lemma appify2_correct : forall op f g, appify2 op f g = op f g.
Proof.
  intros. cbv [appify2].
  etransitivity; apply app_10_correct.
Qed.

Definition add_sig (f g : fe25519) :
  { fg : fe25519 | fg = ModularBaseSystem.add f g}.
Proof.
  eexists.
  rewrite <-appify2_correct.
  cbv.
  reflexivity.
Defined.

Definition add (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj1_sig (add_sig f g).

Definition add_correct (f g : fe25519)
  : add f g = ModularBaseSystem.add f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (add_sig f g). (* Coq 8.4 : 10s *)

Definition sub_sig (f g : fe25519) :
  { fg : fe25519 | fg = ModularBaseSystem.sub mul2modulus f g}.
Proof.
  eexists.
  rewrite <-appify2_correct.
  cbv.
  reflexivity.
Defined.

Definition sub (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj1_sig (sub_sig f g).

Definition sub_correct (f g : fe25519)
  : sub f g = ModularBaseSystem.sub mul2modulus f g :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj2_sig (sub_sig f g).

(* For multiplication, we add another layer of definition so that we can
   rewrite under the [let] binders. *)
Definition mul_simpl_sig (f g : fe25519) :
  { fg : fe25519 | fg = ModularBaseSystem.mul f g}.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  rewrite <-mul_opt_correct with (k_ := k_) (c_ := c_) by auto.
  cbv.
  autorewrite with zsimplify.
  reflexivity.
Defined.

Definition mul_simpl (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_simpl_sig] in
  proj1_sig (mul_simpl_sig f g).

Definition mul_simpl_correct (f g : fe25519)
  : mul_simpl f g = ModularBaseSystem.mul f g :=
  Eval cbv beta iota delta [proj1_sig mul_simpl_sig] in
  proj2_sig (mul_simpl_sig f g).

Definition mul_sig (f g : fe25519) :
  { fg : fe25519 | fg = ModularBaseSystem.mul f g}.
Proof.
  eexists.
  rewrite <-mul_simpl_correct.
  rewrite <-appify2_correct.
  cbv.
  reflexivity.
Defined.

Definition mul (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_sig] in
  proj1_sig (mul_sig f g).

Definition mul_correct (f g : fe25519)
  : mul f g = ModularBaseSystem.mul f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (mul_sig f g).

Definition decode := Eval compute in ModularBaseSystem.decode.

Import Morphisms.

Lemma field25519 : @field fe25519 eq zero one opp add sub mul inv div.
Proof.
  pose proof (Equivalence_Reflexive : Reflexive eq).
  eapply (Field.isomorphism_to_subfield_field (phi := decode)
    (fieldR := PrimeFieldTheorems.field_modulo (prime_q := prime_modulus))).
  Grab Existential Variables.
  + intros; change decode with ModularBaseSystem.decode; apply encode_rep.
  + intros; change decode with ModularBaseSystem.decode; apply encode_rep.
  + intros; change decode with ModularBaseSystem.decode; apply encode_rep.
  + intros; change decode with ModularBaseSystem.decode; apply encode_rep.
  + intros; change decode with ModularBaseSystem.decode.
    rewrite mul_correct; apply mul_rep; reflexivity.
  + intros; change decode with ModularBaseSystem.decode.
    rewrite sub_correct; apply sub_rep; try reflexivity.
    rewrite <- coeff_mod. reflexivity.
  + intros; change decode with ModularBaseSystem.decode.
    rewrite add_correct; apply add_rep; reflexivity.
  + intros; change decode with ModularBaseSystem.decode; apply encode_rep.
  + cbv [eq zero one]. change decode with ModularBaseSystem.decode.
    rewrite !encode_rep. intro A.
    eapply (PrimeFieldTheorems.Fq_1_neq_0 (prime_q := prime_modulus)). congruence.
  + trivial.
  + repeat intro. cbv [div]. congruence.
  + repeat intro. cbv [inv]. congruence.
  + repeat intro. cbv [eq] in *. rewrite !mul_correct, !mul_rep by reflexivity; congruence.
  + repeat intro. cbv [eq] in *. rewrite !sub_correct. rewrite !sub_rep by
      (rewrite <-?coeff_mod; reflexivity); congruence.
  + repeat intro. cbv [eq] in *. rewrite !add_correct, !add_rep by reflexivity; congruence.
  + repeat intro. cbv [opp]. congruence.
  + cbv [eq]. auto using ModularArithmeticTheorems.F_eq_dec.
  + apply (eq_Equivalence (prm := params25519)).
Qed.


(*
Local Transparent Let_In.
Eval cbv iota beta delta [proj1_sig mul Let_In] in (fun f0 f1 f2 f3 f4  g0 g1 g2 g3 g4 => proj1_sig (mul (f4,f3,f2,f1,f0) (g4,g3,g2,g1,g0))).
*)

(* TODO: This file should eventually contain the following operations:
   toBytes
   fromBytes
   inv
   opp
   sub
   zero
   one
   eq
*)