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
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tower.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Require Crypto.Spec.Ed25519.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN precomputation. *)

Definition modulus : positive := Eval compute in (2^255 - 19)%positive.
Definition prime_modulus : prime modulus := Crypto.Spec.Ed25519.prime_q.
Definition int_width := 64%Z.
Definition freeze_input_bound := 32%Z.

Instance params25519 : PseudoMersenneBaseParams modulus.
  construct_params prime_modulus 10%nat 255.
Defined.

Definition length_fe25519 := Eval compute in length limb_widths.
Definition fe25519 := Eval compute in (tuple Z length_fe25519).

Definition mul2modulus : fe25519 :=
  Eval compute in (from_list_default 0%Z (length limb_widths) (construct_mul2modulus params25519)).

Instance subCoeff : SubtractionCoefficient.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus).
  vm_decide.
Defined.

Instance carryChain : CarryChain limb_widths.
  apply Build_CarryChain with (carry_chain := (rev [0;1;2;3;4;5;6;7;8;9;0;1])%nat).
  intros.
  repeat (destruct H as [|H]; [subst; vm_compute; repeat constructor | ]).
  contradiction H.
Defined.

Definition freezePreconditions25519 : FreezePreconditions freeze_input_bound int_width.
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

(* From Daniel Bernstein's "ref" implementation (Public Domain) *)
Definition invChain := [(0, 0); (0, 0); (0, 0); (0, 3); (0, 3); (0, 0); (0, 2); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 5); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 10); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 20); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 42); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 50); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 100); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 202); (0, 0); (0, 0); (0, 0); (0, 0); (0, 0); (0, 259)]%nat.

Instance inv_ec : ExponentiationChain (modulus - 2).
  apply Build_ExponentiationChain with (chain := invChain); vm_decide_no_check.
Defined.

(* Note : use caution copying square root code to other primes. The (modulus / 8 + 1) chains are
   for primes that are 5 mod 8; if the prime is 3 mod 4 then use (modulus / 4 + 1). *)
Definition sqrtChain := Eval compute in pow2_chain (Z.to_pos (modulus / 8 + 1)).

Instance sqrt_ec : ExponentiationChain (modulus / 8 + 1).
  apply Build_ExponentiationChain with (chain := sqrtChain).
  reflexivity.
Defined.

Arguments chain {_ _ _} _.

(* END precomputation *)

(* Precompute constants *)
Definition k_ := Eval compute in k.
Definition k_subst : k = k_ := eq_refl k_.

Definition c_ := Eval compute in c.
Definition c_subst : c = c_ := eq_refl c_.

Definition one_ := Eval compute in one.
Definition one_subst : one = one_ := eq_refl one_.

Definition zero_ := Eval compute in zero.
Definition zero_subst : zero = zero_ := eq_refl zero_.

Definition modulus_digits_ := Eval compute in ModularBaseSystemList.modulus_digits.
Definition modulus_digits_subst : ModularBaseSystemList.modulus_digits = modulus_digits_ := eq_refl modulus_digits_.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Z.lor Let_In Z.eqb Z.ltb Z.leb ModularBaseSystemListZOperations.neg ModularBaseSystemListZOperations.cmovl ModularBaseSystemListZOperations.cmovne.

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

Definition appify9 {T} (op : fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> T) (x0 x1 x2 x3 x4 x5 x6 x7 x8 : fe25519) :=
  app_10 x0 (fun x0' =>
  app_10 x1 (fun x1' =>
  app_10 x2 (fun x2' =>
  app_10 x3 (fun x3' =>
  app_10 x4 (fun x4' =>
  app_10 x5 (fun x5' =>
  app_10 x6 (fun x6' =>
  app_10 x7 (fun x7' =>
  app_10 x8 (fun x8' =>
                     op x0' x1' x2' x3' x4' x5' x6' x7' x8'))))))))).

Lemma appify9_correct : forall {T} op x0 x1 x2 x3 x4 x5 x6 x7 x8,
    @appify9 T op x0 x1 x2 x3 x4 x5 x6 x7 x8 = op x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  intros. cbv [appify9].
  repeat (etransitivity; [ apply app_10_correct | ]); reflexivity.
Qed.

Definition uncurry_unop_fe25519 {T} (op : fe25519 -> T)
  := Eval compute in Tuple.uncurry (n:=length_fe25519) op.
Definition curry_unop_fe25519 {T} op : fe25519 -> T
  := Eval compute in fun f => app_10 f (Tuple.curry (n:=length_fe25519) op).

Fixpoint uncurry_n_op_fe25519 {T} n
  : forall (op : Tower.tower_nd fe25519 T n),
    Tower.tower_nd Z T (n * length_fe25519)
  := match n
           return (forall (op : Tower.tower_nd fe25519 T n),
                      Tower.tower_nd Z T (n * length_fe25519))
     with
     | O => fun x => x
     | S n' => fun f => uncurry_unop_fe25519 (fun x => @uncurry_n_op_fe25519 _ n' (f x))
     end.

Definition uncurry_binop_fe25519 {T} (op : fe25519 -> fe25519 -> T)
  := Eval compute in uncurry_n_op_fe25519 2 op.
Definition curry_binop_fe25519 {T} op : fe25519 -> fe25519 -> T
  := Eval compute in appify2 (fun f => curry_unop_fe25519 (curry_unop_fe25519 op f)).

Definition uncurry_unop_wire_digits {T} (op : wire_digits -> T)
  := Eval compute in Tuple.uncurry (n:=length wire_widths) op.
Definition curry_unop_wire_digits {T} op : wire_digits -> T
  := Eval compute in fun f => app_7 f (Tuple.curry (n:=length wire_widths) op).

Definition uncurry_9op_fe25519 {T} (op : fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> T)
  := Eval compute in uncurry_n_op_fe25519 9 op.
Definition curry_9op_fe25519 {T} op : fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> fe25519 -> T
  := Eval compute in
      appify9 (fun x0 x1 x2 x3 x4 x5 x6 x7 x8
               => curry_unop_fe25519 (curry_unop_fe25519 (curry_unop_fe25519 (curry_unop_fe25519 (curry_unop_fe25519 (curry_unop_fe25519 (curry_unop_fe25519 (curry_unop_fe25519 (curry_unop_fe25519 op x0) x1) x2) x3) x4) x5) x6) x7) x8).

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

Definition carry_add_sig (f g : fe25519) :
  { fg : fe25519 | fg = carry_add_opt f g}.
Proof.
  eexists.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  autorewrite with zsimplify_fast zsimplify_Z_to_pos; cbv. (* FIXME: The speed of this rewrite depends on the fact that we have 10 limbs; there are some lemmas in [zsimplify_Z_to_pos] which are specific to 10. *)
  autorewrite with zsimplify_Z_to_pos; cbv.
  reflexivity.
Defined.

Definition carry_add (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig carry_add_sig] in
  proj1_sig (carry_add_sig f g).

Definition carry_add_correct (f g : fe25519)
  : carry_add f g = carry_add_opt f g :=
  Eval cbv beta iota delta [proj1_sig carry_add_sig] in
  proj2_sig (carry_add_sig f g).

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

Definition carry_sub_sig (f g : fe25519) :
  { fg : fe25519 | fg = carry_sub_opt f g}.
Proof.
  eexists.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  autorewrite with zsimplify_fast zsimplify_Z_to_pos; cbv. (* FIXME: The speed of this rewrite depends on the fact that we have 10 limbs; there are some lemmas in [zsimplify_Z_to_pos] which are specific to 10. *)
  autorewrite with zsimplify_Z_to_pos; cbv.
  reflexivity.
Defined.

Definition carry_sub (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig carry_sub_sig] in
  proj1_sig (carry_sub_sig f g).

Definition carry_sub_correct (f g : fe25519)
  : carry_sub f g = carry_sub_opt f g :=
  Eval cbv beta iota delta [proj1_sig carry_sub_sig] in
  proj2_sig (carry_sub_sig f g).

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
  autorewrite with zsimplify_fast zsimplify_Z_to_pos; cbv. (* FIXME: The speed of this rewrite depends on the fact that we have 10 limbs; there are some lemmas in [zsimplify_Z_to_pos] which are specific to 10. *)
  autorewrite with zsimplify_Z_to_pos; cbv.
  reflexivity.
Defined.

Definition mul (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_sig] in
  proj1_sig (mul_sig f g).

Definition mul_correct (f g : fe25519)
  : mul f g = carry_mul_opt k_ c_ f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (mul_sig f g).

Definition opp_sig (f : fe25519) :
  { g : fe25519 | g = opp_opt f }.
Proof.
  eexists.
  cbv [opp_opt].
  rewrite <-sub_correct.
  rewrite zero_subst.
  cbv [sub].
  reflexivity.
Defined.

Definition opp (f : fe25519) : fe25519
  := Eval cbv beta iota delta [proj1_sig opp_sig] in proj1_sig (opp_sig f).

Definition opp_correct (f : fe25519)
  : opp f = opp_opt f
  := Eval cbv beta iota delta [proj2_sig add_sig] in proj2_sig (opp_sig f).

Definition carry_opp_sig (f : fe25519) :
  { g : fe25519 | g = carry_opp_opt f }.
Proof.
  eexists.
  cbv [carry_opp_opt].
  rewrite <-carry_sub_correct.
  rewrite zero_subst.
  cbv [carry_sub].
  reflexivity.
Defined.

Definition carry_opp (f : fe25519) : fe25519
  := Eval cbv beta iota delta [proj1_sig carry_opp_sig] in proj1_sig (carry_opp_sig f).

Definition carry_opp_correct (f : fe25519)
  : carry_opp f = carry_opp_opt f
  := Eval cbv beta iota delta [proj2_sig add_sig] in proj2_sig (carry_opp_sig f).

Definition pow (f : fe25519) chain := fold_chain_opt one_ mul chain [f].

Lemma pow_correct (f : fe25519) : forall chain, pow f chain = pow_opt k_ c_ one_ f chain.
Proof.
  cbv [pow pow_opt]; intros.
  rewrite !fold_chain_opt_correct.
  apply Proper_fold_chain; try reflexivity.
  intros; subst; apply mul_correct.
Qed.

(* Now that we have [pow], we can compute sqrt of -1 for use
   in sqrt function (this is not needed unless the prime is
   5 mod 8) *)
Local Transparent Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Z.lor Let_In Z.eqb Z.ltb andb.

Definition sqrt_m1 := Eval vm_compute in (pow (encode (F.of_Z _ 2)) (pow2_chain (Z.to_pos ((modulus - 1) / 4)))).

Lemma sqrt_m1_correct : rep (mul sqrt_m1 sqrt_m1) (F.opp 1%F).
Proof.
  cbv [rep].
  apply F.eq_to_Z_iff.
  vm_compute.
  reflexivity.
Qed.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Z.lor Let_In Z.eqb Z.ltb andb.

Definition inv_sig (f : fe25519) :
  { g : fe25519 | g = inv_opt k_ c_ one_ f }.
Proof.
  eexists; cbv [inv_opt].
  rewrite <-pow_correct.
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

Local Existing Instance prime_modulus.

Lemma field25519_and_homomorphisms
  : @field fe25519 eq zero_ one_ opp add sub mul inv div
    /\ @Ring.is_homomorphism
         (F modulus) Logic.eq F.one F.add F.mul
         fe25519 eq one_ add mul encode
    /\ @Ring.is_homomorphism
         fe25519 eq one_ add mul
         (F modulus) Logic.eq F.one F.add F.mul
         decode.
Proof.
  eapply @Field.field_and_homomorphism_from_redundant_representation.
  { exact (F.field_modulo _). }
  { apply encode_rep. }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { intros; rewrite opp_correct, opp_opt_correct; apply opp_rep; reflexivity. }
  { intros; rewrite add_correct, add_opt_correct; apply add_rep; reflexivity. }
  { intros; rewrite sub_correct, sub_opt_correct; apply sub_rep; reflexivity. }
  { intros; rewrite mul_correct, carry_mul_opt_correct by reflexivity; apply carry_mul_rep; reflexivity. }
  { intros; rewrite inv_correct, inv_opt_correct by reflexivity; apply inv_rep; reflexivity. }
  { intros; apply encode_rep. }
Qed.

Definition field25519 : @field fe25519 eq zero_ one_ opp add sub mul inv div := proj1 field25519_and_homomorphisms.

Lemma carry_field25519_and_homomorphisms
  : @field fe25519 eq zero_ one_ carry_opp carry_add carry_sub mul inv div
    /\ @Ring.is_homomorphism
         (F modulus) Logic.eq F.one F.add F.mul
         fe25519 eq one_ carry_add mul encode
    /\ @Ring.is_homomorphism
         fe25519 eq one_ carry_add mul
         (F modulus) Logic.eq F.one F.add F.mul
         decode.
Proof.
  eapply @Field.field_and_homomorphism_from_redundant_representation.
  { exact (F.field_modulo _). }
  { apply encode_rep. }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { intros; rewrite carry_opp_correct, carry_opp_opt_correct, carry_opp_rep; apply opp_rep; reflexivity. }
  { intros; rewrite carry_add_correct, carry_add_opt_correct, carry_add_rep; apply add_rep; reflexivity. }
  { intros; rewrite carry_sub_correct, carry_sub_opt_correct, carry_sub_rep; apply sub_rep; reflexivity. }
  { intros; rewrite mul_correct, carry_mul_opt_correct by reflexivity; apply carry_mul_rep; reflexivity. }
  { intros; rewrite inv_correct, inv_opt_correct by reflexivity; apply inv_rep; reflexivity. }
  { intros; apply encode_rep. }
Qed.

Definition carry_field25519 : @field fe25519 eq zero_ one_ carry_opp carry_add carry_sub mul inv div := proj1 carry_field25519_and_homomorphisms.

Lemma homomorphism_F25519_encode
  : @Ring.is_homomorphism (F modulus) Logic.eq F.one F.add F.mul fe25519 eq one add mul encode.
Proof. apply field25519_and_homomorphisms. Qed.

Lemma homomorphism_F25519_decode
  : @Ring.is_homomorphism fe25519 eq one add mul (F modulus) Logic.eq F.one F.add F.mul decode.
Proof. apply field25519_and_homomorphisms. Qed.


Lemma homomorphism_carry_F25519_encode
  : @Ring.is_homomorphism (F modulus) Logic.eq F.one F.add F.mul fe25519 eq one carry_add mul encode.
Proof. apply carry_field25519_and_homomorphisms. Qed.

Lemma homomorphism_carry_F25519_decode
  : @Ring.is_homomorphism fe25519 eq one carry_add mul (F modulus) Logic.eq F.one F.add F.mul decode.
Proof. apply carry_field25519_and_homomorphisms. Qed.

Definition ge_modulus_sig (f : fe25519) :
  { b : Z | b = ge_modulus_opt (to_list 10 f) }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists; cbv [ge_modulus_opt].
  rewrite !modulus_digits_subst.
  cbv.
  reflexivity.
Defined.

Definition ge_modulus (f : fe25519) : Z :=
  Eval cbv beta iota delta [proj1_sig ge_modulus_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig (ge_modulus_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)).

Definition ge_modulus_correct (f : fe25519) :
  ge_modulus f = ge_modulus_opt (to_list 10 f).
Proof.
  pose proof (proj2_sig (ge_modulus_sig f)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Defined.

Definition prefreeze_sig (f : fe25519) :
  { f' : fe25519 | f' = from_list_default 0 10 (carry_full_3_opt c_ (to_list 10 f)) }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv - [from_list_default].
  (* TODO(jgross,jadep): use Reflective linearization here? *)
  repeat (
       set_evars; rewrite app_Let_In_nd; subst_evars;
       eapply Proper_Let_In_nd_changebody; [reflexivity|intro]).
  cbv [from_list_default from_list_default'].
  reflexivity.
Defined.

Definition prefreeze (f : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig prefreeze_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig (prefreeze_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)).

Definition prefreeze_correct (f : fe25519)
  : prefreeze f = from_list_default 0 10 (carry_full_3_opt c_ (to_list 10 f)).
Proof.
  pose proof (proj2_sig (prefreeze_sig f)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Defined.

Definition postfreeze_sig (f : fe25519) :
  { f' : fe25519 | f' = from_list_default 0 10 (conditional_subtract_modulus_opt (int_width := int_width) (to_list 10 f)) }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists; cbv [freeze_opt int_width].
  cbv [to_list to_list'].
  cbv [conditional_subtract_modulus_opt].
  rewrite !modulus_digits_subst.
  cbv - [from_list_default].
  (* TODO(jgross,jadep): use Reflective linearization here? *)
  repeat (
       set_evars; rewrite app_Let_In_nd; subst_evars;
       eapply Proper_Let_In_nd_changebody; [reflexivity|intro]).
  cbv [from_list_default from_list_default'].
  reflexivity.
Defined.

Definition postfreeze (f : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig postfreeze_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig (postfreeze_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)).

Definition postfreeze_correct (f : fe25519)
  : postfreeze f = from_list_default 0 10 (conditional_subtract_modulus_opt (int_width := int_width) (to_list 10 f)).
Proof.
  pose proof (proj2_sig (postfreeze_sig f)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Defined.

Definition freeze (f : fe25519) : fe25519 :=
  dlet x := prefreeze f in
  postfreeze x.

Local Transparent Let_In.
Definition freeze_correct (f : fe25519)
  : freeze f = from_list_default 0 10 (freeze_opt (int_width := int_width) c_ (to_list 10 f)).
Proof.
  cbv [freeze_opt freeze Let_In].
  rewrite prefreeze_correct.
  rewrite postfreeze_correct.
  match goal with
    |- appcontext [to_list _ (from_list_default _ ?n ?xs)] =>
    assert (length xs = n) as pf; [ | rewrite from_list_default_eq with (pf0 := pf) ] end.
  { rewrite carry_full_3_opt_correct; repeat rewrite ModularBaseSystemListProofs.length_carry_full; auto using length_to_list. }
  rewrite to_list_from_list.
  reflexivity.
Qed.
Local Opaque Let_In.

Definition fieldwiseb_sig (f g : fe25519) :
  { b | b = @fieldwiseb Z Z 10 Z.eqb f g }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv.
  reflexivity.
Defined.

Definition fieldwiseb (f g : fe25519) : bool
  := Eval cbv beta iota delta [proj1_sig fieldwiseb_sig] in
      let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
      let '(g0, g1, g2, g3, g4, g5, g6, g7, g8, g9) := g in
      proj1_sig (fieldwiseb_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)
                                (g0, g1, g2, g3, g4, g5, g6, g7, g8, g9)).

Lemma fieldwiseb_correct (f g : fe25519)
  : fieldwiseb f g = @Tuple.fieldwiseb Z Z 10 Z.eqb f g.
Proof.
  set (f' := f); set (g' := g).
  hnf in f, g; destruct_head' prod.
  exact (proj2_sig (fieldwiseb_sig f' g')).
Qed.

Definition eqb_sig (f g : fe25519) :
  { b | b = eqb int_width f g }.
Proof.
  cbv [eqb].
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv [ModularBaseSystem.freeze int_width].
  rewrite <-!from_list_default_eq with (d := 0).
  rewrite <-!(freeze_opt_correct c_) by auto using length_to_list.
  rewrite <-!freeze_correct.
  rewrite <-fieldwiseb_correct.
  reflexivity.
Defined.

Definition eqb (f g : fe25519) : bool
  := Eval cbv beta iota delta [proj1_sig eqb_sig] in
      let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
      let '(g0, g1, g2, g3, g4, g5, g6, g7, g8, g9) := g in
      proj1_sig (eqb_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)
                         (g0, g1, g2, g3, g4, g5, g6, g7, g8, g9)).

Lemma eqb_correct (f g : fe25519)
  : eqb f g = ModularBaseSystem.eqb int_width f g.
Proof.
  set (f' := f); set (g' := g).
  hnf in f, g; destruct_head' prod.
  exact (proj2_sig (eqb_sig f' g')).
Qed.

Definition sqrt_sig (powf powf_squared f : fe25519) :
  { f' : fe25519 | f' = sqrt_5mod8_opt (int_width := int_width) k_ c_ sqrt_m1 powf powf_squared f}.
Proof.
  eexists.
  cbv [sqrt_5mod8_opt int_width].
  apply Proper_Let_In_nd_changebody; [reflexivity|intro].
  set_evars. rewrite <-!mul_correct, <-eqb_correct. subst_evars.
  reflexivity.
Defined.

Definition sqrt (powf powf_squared f : fe25519) : fe25519
  := Eval cbv beta iota delta [proj1_sig sqrt_sig] in proj1_sig (sqrt_sig powf powf_squared f).

Definition sqrt_correct (powf powf_squared f : fe25519)
  : sqrt powf powf_squared f = sqrt_5mod8_opt k_ c_ sqrt_m1 powf powf_squared f
  := Eval cbv beta iota delta [proj2_sig sqrt_sig] in proj2_sig (sqrt_sig powf powf_squared f).

Definition pack_simpl_sig (f : fe25519) :
  { f' | f' = pack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv [pack_opt].
  repeat (rewrite <-convert'_opt_correct;
          cbv - [from_list_default_opt Conversion.convert']).
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
      cbv - [from_list_default_opt Conversion.convert']).
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
