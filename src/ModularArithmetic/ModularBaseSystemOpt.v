Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.BaseSystem Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil Crypto.Util.CaseUtil.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.QArith.QArith Coq.QArith.Qround.
Require Import Crypto.Tactics.VerdiTactics.
Local Open Scope Z.

Class SubtractionCoefficient (m : Z) (prm : PseudoMersenneBaseParams m) := {
  coeff : BaseSystem.digits;
  coeff_length : (length coeff = length PseudoMersenneBaseParamProofs.base)%nat;
  coeff_mod: (BaseSystem.decode PseudoMersenneBaseParamProofs.base coeff) mod m = 0
}.

(* Computed versions of some functions. *)

Definition Z_add_opt := Eval compute in Z.add.
Definition Z_sub_opt := Eval compute in Z.sub.
Definition Z_mul_opt := Eval compute in Z.mul.
Definition Z_div_opt := Eval compute in Z.div.
Definition Z_pow_opt := Eval compute in Z.pow.
Definition Z_opp_opt := Eval compute in Z.opp.
Definition Z_shiftl_opt := Eval compute in Z.shiftl.
Definition Z_shiftl_by_opt := Eval compute in Z_shiftl_by.

Definition nth_default_opt {A} := Eval compute in @nth_default A.
Definition set_nth_opt {A} := Eval compute in @set_nth A.
Definition map_opt {A B} := Eval compute in @map A B.
Definition full_carry_chain_opt := Eval compute in @full_carry_chain.
Definition length_opt := Eval compute in length.
Definition base_opt := Eval compute in @base.
Definition max_ones_opt := Eval compute in @max_ones.
Definition max_bound_opt := Eval compute in @max_bound.
Definition minus_opt := Eval compute in minus.

Definition Let_In {A P} (x : A) (f : forall y : A, P y)
  := let y := x in f y.

(* Some automation that comes in handy when constructing base parameters *)
Ltac opt_step :=
  match goal with
  | [ |- _ = match ?e with nil => _ | _ => _ end :> ?T ]
    => refine (_ : match e with nil => _ | _ => _ end = _);
       destruct e
  end.

Ltac brute_force_indices limb_widths := intros; unfold sum_firstn, limb_widths; simpl in *;
  repeat match goal with
  | _ => progress simpl in *
  | _ => reflexivity
  | [H : (S _ < S _)%nat |- _ ] => apply lt_S_n in H
  | [H : (?x + _ < _)%nat |- _ ] => is_var x; destruct x
  | [H : (?x < _)%nat |- _ ] => is_var x; destruct x
  | _ => omega
  end.


Definition limb_widths_from_len len k := Eval compute in
  (fix loop i prev :=
    match i with
    | O => nil
    | S i' => let x := (if (Z.eq_dec ((k * Z.of_nat (len - i + 1)) mod (Z.of_nat len)) 0)
                        then (k * Z.of_nat (len - i + 1)) / Z.of_nat len
                        else (k * Z.of_nat (len - i + 1)) / Z.of_nat len + 1)in
      x - prev:: (loop i' x)
    end) len 0.

Ltac construct_params prime_modulus len k :=
  let lw := fresh "lw" in set (lw := limb_widths_from_len len k);
  cbv in lw;
  eapply Build_PseudoMersenneBaseParams with (limb_widths := lw);
  [ abstract (apply fold_right_and_True_forall_In_iff; simpl; repeat (split; [omega |]); auto)
  | abstract (unfold limb_widths; cbv; congruence)
  | abstract brute_force_indices lw
  | abstract apply prime_modulus
  | abstract brute_force_indices lw].

Definition construct_mul2modulus {m} (prm : PseudoMersenneBaseParams m) : digits :=
  match limb_widths with
  | nil => nil
  | x :: tail =>
      2 ^ (x + 1) - (2 * c) :: map (fun w => 2 ^ (w + 1) - 2) tail
  end.

Ltac compute_preconditions :=
  cbv; intros; repeat match goal with H : _ \/ _ |- _  =>
    destruct H; subst; [ congruence | ] end; (congruence || omega).

Ltac subst_precondition := match goal with
  | [H : ?P, H' : ?P -> _ |- _] => specialize (H' H); clear H
end.

Ltac kill_precondition H :=
  forward H; [abstract (try exact eq_refl; clear; cbv; intros; repeat break_or_hyp; intuition)|];
  subst_precondition.

Section Carries.
  Context `{prm : PseudoMersenneBaseParams}
    (* allows caller to precompute k and c *)
    (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_).

  Definition carry_opt_sig
             (i : nat) (b : digits)
    : { d : digits | (i < length limb_widths)%nat -> d = carry i b }.
  Proof.
    eexists ; intros.
    cbv [carry].
    rewrite <- pull_app_if_sumbool.
    cbv beta delta
      [carry carry_and_reduce carry_simple add_to_nth log_cap
       pow2_mod Z.ones Z.pred
       PseudoMersenneBaseParams.limb_widths].
    change @base with @base_opt.
    change @nth_default with @nth_default_opt in *.
    change @set_nth with @set_nth_opt in *.
    lazymatch goal with
    | [ |- _ = (if ?br then ?c else ?d) ]
      => let x := fresh "x" in let y := fresh "y" in evar (x:digits); evar (y:digits); transitivity (if br then x else y); subst x; subst y
    end.
    2:cbv zeta.
    2:break_if; reflexivity.

    change @nth_default with @nth_default_opt.
    rewrite c_subst.
    change @set_nth with @set_nth_opt.
    change @map with @map_opt.
    rewrite <- @beq_nat_eq_nat_dec.
    reflexivity.
  Defined.

  Definition carry_opt i b
    := Eval cbv beta iota delta [proj1_sig carry_opt_sig] in proj1_sig (carry_opt_sig i b).

  Definition carry_opt_correct i b : (i < length limb_widths)%nat -> carry_opt i b = carry i b := proj2_sig (carry_opt_sig i b).

  Definition carry_sequence_opt_sig (is : list nat) (us : digits)
    : { b : digits | (forall i, In i is -> i < length base)%nat -> b = carry_sequence is us }.
  Proof.
    eexists. intros H.
    cbv [carry_sequence].
    transitivity (fold_right carry_opt us is).
    Focus 2.
    { induction is; [ reflexivity | ].
      simpl; rewrite IHis, carry_opt_correct.
      - reflexivity.
      - rewrite base_length in H.
        apply H; apply in_eq.
      - intros. apply H. right. auto.
      }
    Unfocus.
    reflexivity.
  Defined.

  Definition carry_sequence_opt is us := Eval cbv [proj1_sig carry_sequence_opt_sig] in
                                          proj1_sig (carry_sequence_opt_sig is us).

  Definition carry_sequence_opt_correct is us
    : (forall i, In i is -> i < length base)%nat -> carry_sequence_opt is us = carry_sequence is us
    := proj2_sig (carry_sequence_opt_sig is us).

  Definition carry_opt_cps_sig
             {T}
             (i : nat)
             (f : digits -> T)
             (b : digits)
    : { d : T |  (i < length base)%nat -> d = f (carry i b) }.
  Proof.
    eexists. intros H.
    rewrite <- carry_opt_correct by (rewrite base_length in H; assumption).
    cbv beta iota delta [carry_opt].
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (nth_default_opt 0%Z b i) in RHS) with ?RHSf _ => RHSf end in
    change (LHS = Let_In (nth_default_opt 0%Z b i) RHSf).
    change Z.shiftl with Z_shiftl_opt.
    change (-1) with (Z_opp_opt 1).
    change Z.add with Z_add_opt at 5 9 17 21.
    reflexivity.
  Defined.

  Definition carry_opt_cps {T} i f b
    := Eval cbv beta iota delta [proj1_sig carry_opt_cps_sig] in proj1_sig (@carry_opt_cps_sig T i f b).

  Definition carry_opt_cps_correct {T} i f b :
    (i < length base)%nat ->
    @carry_opt_cps T i f b = f (carry i b)
    := proj2_sig (carry_opt_cps_sig i f b).

  Definition carry_sequence_opt_cps2_sig {T} (is : list nat) (us : digits)
     (f : digits -> T)
    : { b : T | (forall i, In i is -> i < length base)%nat -> b = f (carry_sequence is us) }.
  Proof.
    eexists.
    cbv [carry_sequence].
    transitivity (fold_right carry_opt_cps f (List.rev is) us).
    Focus 2.
    {
      assert (forall i, In i (rev is) -> i < length base)%nat as Hr. {
        subst. intros. rewrite <- in_rev in *. auto. }
      remember (rev is) as ris eqn:Heq.
      rewrite <- (rev_involutive is), <- Heq.
      clear H Heq is.
      rewrite fold_left_rev_right.
      revert us; induction ris; [ reflexivity | ]; intros.
      { simpl.
        rewrite <- IHris; clear IHris; [|intros; apply Hr; right; assumption].
        rewrite carry_opt_cps_correct; [reflexivity|].
        apply Hr; left; reflexivity.
        } }
    Unfocus.
    reflexivity.
  Defined.

  Definition carry_sequence_opt_cps2 {T} is us (f : digits -> T) :=
    Eval cbv [proj1_sig carry_sequence_opt_cps2_sig] in
      proj1_sig (carry_sequence_opt_cps2_sig is us f).

  Definition carry_sequence_opt_cps2_correct {T} is us (f : digits -> T)
    : (forall i, In i is -> i < length base)%nat -> carry_sequence_opt_cps2 is us f = f (carry_sequence is us)
    := proj2_sig (carry_sequence_opt_cps2_sig is us f).

  Definition carry_sequence_opt_cps_sig (is : list nat) (us : digits)
    : { b : digits | (forall i, In i is -> i < length base)%nat -> b = carry_sequence is us }.
  Proof.
    eexists.
    cbv [carry_sequence].
    transitivity (fold_right carry_opt_cps id (List.rev is) us).
    Focus 2.
    {
      assert (forall i, In i (rev is) -> i < length base)%nat as Hr. {
        subst. intros. rewrite <- in_rev in *. auto. }
      remember (rev is) as ris eqn:Heq.
      rewrite <- (rev_involutive is), <- Heq.
      clear H Heq is.
      rewrite fold_left_rev_right.
      revert us; induction ris; [ reflexivity | ]; intros.
      { simpl.
        rewrite <- IHris; clear IHris; [|intros; apply Hr; right; assumption].
        rewrite carry_opt_cps_correct; [reflexivity|].
        apply Hr; left; reflexivity.
        } }
    Unfocus.
    reflexivity.
  Defined.

  Definition carry_sequence_opt_cps is us := Eval cbv [proj1_sig carry_sequence_opt_cps_sig] in
                                              proj1_sig (carry_sequence_opt_cps_sig is us).

  Definition carry_sequence_opt_cps_correct is us
    : (forall i, In i is -> i < length base)%nat -> carry_sequence_opt_cps is us = carry_sequence is us
    := proj2_sig (carry_sequence_opt_cps_sig is us).


  Lemma carry_sequence_opt_cps_rep
       : forall (is : list nat) (us : list Z) (x : F modulus),
         (forall i : nat, In i is -> i < length base)%nat ->
         rep us x -> rep (carry_sequence_opt_cps is us) x.
  Proof.
    intros.
    rewrite carry_sequence_opt_cps_correct by assumption.
    apply carry_sequence_rep; eauto using rep_length.
  Qed.

  Lemma full_carry_chain_bounds : forall i, In i full_carry_chain -> (i < length base)%nat.
  Proof.
    unfold full_carry_chain; rewrite <-base_length; intros.
    apply make_chain_lt; auto.
  Qed.

  Definition carry_full_opt_sig (us : digits) : { b : digits | b = carry_full us }.
  Proof.
    eexists.
    cbv [carry_full].
    change @full_carry_chain with full_carry_chain_opt.
    rewrite <-carry_sequence_opt_cps_correct by (auto; apply full_carry_chain_bounds).
    reflexivity.
  Defined.

  Definition carry_full_opt (us : digits) : digits
    := Eval cbv [proj1_sig carry_full_opt_sig] in proj1_sig (carry_full_opt_sig us).

  Definition carry_full_opt_correct us : carry_full_opt us = carry_full us :=
    proj2_sig (carry_full_opt_sig us).

  Definition carry_full_opt_cps_sig
             {T}
             (f : digits -> T)
             (us : digits)
    : { d : T | d = f (carry_full us) }.
  Proof.
    eexists.
    rewrite <- carry_full_opt_correct.
    cbv beta iota delta [carry_full_opt].
    rewrite carry_sequence_opt_cps_correct by apply full_carry_chain_bounds.
    rewrite <-carry_sequence_opt_cps2_correct by apply full_carry_chain_bounds.
    reflexivity.
  Defined.

  Definition carry_full_opt_cps {T} (f : digits -> T) (us : digits) : T
    := Eval cbv [proj1_sig carry_full_opt_cps_sig] in proj1_sig (carry_full_opt_cps_sig f us).

  Definition carry_full_opt_cps_correct {T} us (f : digits -> T) :
    carry_full_opt_cps f us = f (carry_full us) :=
    proj2_sig (carry_full_opt_cps_sig f us).

End Carries.

Section Addition.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient modulus prm}.

  Definition add_opt_sig (us vs : digits) : { b : digits | b = add us vs }.
  Proof.
    eexists.
    cbv [BaseSystem.add].
    reflexivity.
  Defined.

  Definition add_opt (us vs : digits) : digits
    := Eval cbv [proj1_sig add_opt_sig] in proj1_sig (add_opt_sig us vs).

  Definition add_opt_correct us vs
    : add_opt us vs = add us vs
    := proj2_sig (add_opt_sig us vs).
End Addition.

Section Subtraction.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient modulus prm}.

  Definition sub_opt_sig (us vs : digits) : { b : digits | b = sub coeff coeff_mod us vs }.
  Proof.
    eexists.
    cbv [BaseSystem.add ModularBaseSystem.sub BaseSystem.sub].
    reflexivity.
  Defined.

  Definition sub_opt (us vs : digits) : digits
    := Eval cbv [proj1_sig sub_opt_sig] in proj1_sig (sub_opt_sig us vs).

  Definition sub_opt_correct us vs
    : sub_opt us vs = sub coeff coeff_mod us vs
    := proj2_sig (sub_opt_sig us vs).
End Subtraction.

Section Multiplication.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient modulus prm}
    (* allows caller to precompute k and c *)
    (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_).
  Definition mul_bi'_step
             (mul_bi' : nat -> digits -> list Z -> list Z)
             (i : nat) (vsr : digits) (bs : list Z)
    : list Z
    := match vsr with
       | [] => []
       | v :: vsr' => (v * crosscoef bs i (length vsr'))%Z :: mul_bi' i vsr' bs
       end.

  Definition mul_bi'_opt_step_sig
             (mul_bi' : nat -> digits -> list Z -> list Z)
             (i : nat) (vsr : digits) (bs : list Z)
    : { l : list Z | l = mul_bi'_step mul_bi' i vsr bs }.
  Proof.
    eexists.
    cbv [mul_bi'_step].
    opt_step.
    { reflexivity. }
    { cbv [crosscoef ext_base base].
      change Z.div with Z_div_opt.
      change Z.mul with Z_mul_opt at 2.
      change @nth_default with @nth_default_opt.
      reflexivity. }
  Defined.

  Definition mul_bi'_opt_step
             (mul_bi' : nat -> digits -> list Z -> list Z)
             (i : nat) (vsr : digits) (bs : list Z)
    : list Z
    := Eval cbv [proj1_sig mul_bi'_opt_step_sig] in
        proj1_sig (mul_bi'_opt_step_sig mul_bi' i vsr bs).

  Fixpoint mul_bi'_opt
           (i : nat) (vsr : digits) (bs : list Z) {struct vsr}
    : list Z
    := mul_bi'_opt_step mul_bi'_opt i vsr bs.

  Definition mul_bi'_opt_correct
             (i : nat) (vsr : digits) (bs : list Z)
    : mul_bi'_opt i vsr bs = mul_bi' bs i vsr.
  Proof.
    revert i; induction vsr as [|vsr vsrs IHvsr]; intros.
    { reflexivity. }
    { simpl mul_bi'.
      rewrite <- IHvsr; clear IHvsr.
      unfold mul_bi'_opt, mul_bi'_opt_step.
      apply f_equal2; [ | reflexivity ].
      cbv [crosscoef ext_base base].
      change Z.div with Z_div_opt.
      change Z.mul with Z_mul_opt at 2.
      change @nth_default with @nth_default_opt.
      reflexivity. }
  Qed.

  Definition mul'_step
             (mul' : digits -> digits -> list Z -> digits)
             (usr vs : digits) (bs : list Z)
    : digits
    := match usr with
       | [] => []
       | u :: usr' => add (mul_each u (mul_bi bs (length usr') vs)) (mul' usr' vs bs)
       end.

  Lemma map_zeros : forall a n l,
    map (Z.mul a) (zeros n ++ l) = zeros n ++ map (Z.mul a) l.
  Admitted.

  Definition mul'_opt_step_sig
             (mul' : digits -> digits -> list Z -> digits)
             (usr vs : digits) (bs : list Z)
    : { d : digits | d = mul'_step mul' usr vs bs }.
  Proof.
    eexists.
    cbv [mul'_step].
    match goal with
    | [ |- _ = match ?e with nil => _ | _ => _ end :> ?T ]
      => refine (_ : match e with nil => _ | _ => _ end = _);
           destruct e
    end.
    { reflexivity. }
    { cbv [mul_each mul_bi].
      rewrite <- mul_bi'_opt_correct.
      rewrite map_zeros.
      change @map with @map_opt.
      cbv [zeros].
      reflexivity. }
  Defined.

  Definition mul'_opt_step
             (mul' : digits -> digits -> list Z -> digits)
             (usr vs : digits) (bs : list Z)
    : digits
    := Eval cbv [proj1_sig mul'_opt_step_sig] in proj1_sig (mul'_opt_step_sig mul' usr vs bs).

  Fixpoint mul'_opt
           (usr vs : digits) (bs : list Z)
    : digits
    := mul'_opt_step mul'_opt usr vs bs.

  Definition mul'_opt_correct
           (usr vs : digits) (bs : list Z)
    : mul'_opt usr vs bs = mul' bs usr vs.
  Proof.
    revert vs; induction usr as [|usr usrs IHusr]; intros.
    { reflexivity. }
    { simpl.
      rewrite <- IHusr; clear IHusr.
      apply f_equal2; [ | reflexivity ].
      cbv [mul_each mul_bi].
      rewrite map_zeros.
      rewrite <- mul_bi'_opt_correct.
      reflexivity. }
  Qed.

  Definition mul_opt_sig (us vs : digits) : { b : digits | b = mul us vs }.
  Proof.
    eexists.
    cbv [BaseSystem.mul mul mul_each mul_bi mul_bi' zeros ext_base reduce].
    rewrite <- mul'_opt_correct.
    change @base with base_opt.
    rewrite map_shiftl by apply k_nonneg.
    rewrite c_subst.
    rewrite k_subst.
    change @map with @map_opt.
    change @Z_shiftl_by with @Z_shiftl_by_opt.
    reflexivity.
  Defined.

  Definition mul_opt (us vs : digits) : digits
    := Eval cbv [proj1_sig mul_opt_sig] in proj1_sig (mul_opt_sig us vs).

  Definition mul_opt_correct us vs
    : mul_opt us vs = mul us vs
    := proj2_sig (mul_opt_sig us vs).

  Definition carry_mul_opt_sig {T:digits->Type} (f:forall d:digits, T d) (us vs : digits) : { x | x = f (carry_mul us vs) }.
  Proof.
    eexists.
    cbv [carry_mul].
    (* FIXME
    erewrite <-carry_full_opt_cps_correct by eauto.
    erewrite <-mul_opt_correct.
    reflexivity.
   *)
  Defined.

  Definition carry_mul_opt_cps {T} (f:forall d:digits, T d) (us vs : digits) : T (carry_mul us vs)
    := Eval cbv [proj1_sig carry_mul_opt_sig] in proj1_sig (carry_mul_opt_sig f us vs).

  Definition carry_mul_opt_cps_correct {T} (f:forall d:digits, T d) (us vs : digits)
    : carry_mul_opt_cps f us vs = f (carry_mul us vs)
    := proj2_sig (carry_mul_opt_sig f us vs).
End Multiplication.

Record freezePreconditions {modulus} (prm : PseudoMersenneBaseParams modulus) int_width :=
mkFreezePreconditions {
    lt_1_length_base : (1 < length base)%nat;
    int_width_pos : 0 < int_width;
    int_width_compat : forall w, In w limb_widths -> w <= int_width;
    c_pos : 0 < c;
    c_reduce1 : c * (Z.ones (int_width - log_cap (pred (length base)))) < max_bound 0 + 1;
    c_reduce2 : c <= max_bound 0 - c;
    two_pow_k_le_2modulus : 2 ^ k <= 2 * modulus
}.
Local Hint Resolve lt_1_length_base int_width_pos int_width_compat c_pos
    c_reduce1 c_reduce2 two_pow_k_le_2modulus.

Section Canonicalization.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient modulus prm}
    (* allows caller to precompute k and c *)
    (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_)
    {int_width} (preconditions : freezePreconditions prm int_width).

  Definition modulus_digits_opt_sig :
    { b : digits | b = modulus_digits }.
  Proof.
    eexists.
    cbv beta iota delta [modulus_digits modulus_digits' app].
    change @max_bound with max_bound_opt.
    rewrite c_subst.
    change length with length_opt.
    change minus with minus_opt.
    change Z.add with Z_add_opt.
    change Z.sub with Z_sub_opt.
    change @base with base_opt.
    reflexivity.
  Defined.

  Definition modulus_digits_opt : digits
    := Eval cbv [proj1_sig modulus_digits_opt_sig] in proj1_sig (modulus_digits_opt_sig).

  Definition modulus_digits_opt_correct
    : modulus_digits_opt = modulus_digits
    := proj2_sig (modulus_digits_opt_sig).


  Definition carry_full_3_opt_cps_sig
             {T} (f : digits -> T)
             (us : digits)
    : { d : T | d = f (carry_full (carry_full (carry_full us))) }.
  Proof.
    eexists.
    transitivity (carry_full_opt_cps c_ (carry_full_opt_cps c_ (carry_full_opt_cps c_ f)) us).
    Focus 2. {
      rewrite !carry_full_opt_cps_correct by assumption; reflexivity.
    }
    Unfocus.
    reflexivity.
  Defined.

  Definition carry_full_3_opt_cps {T} (f : digits -> T) (us : digits) : T
    := Eval cbv [proj1_sig carry_full_3_opt_cps_sig] in proj1_sig (carry_full_3_opt_cps_sig f us).

  Definition carry_full_3_opt_cps_correct {T} (f : digits -> T) us :
    carry_full_3_opt_cps f us = f (carry_full (carry_full (carry_full us))) :=
    proj2_sig (carry_full_3_opt_cps_sig f us).

  Definition freeze_opt_sig (us : digits) :
    { b : digits | b = freeze us }.
  Proof.
    eexists.
    cbv [freeze].
    cbv [and_term].
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (isFull (carry_full (carry_full (carry_full us)))) in RHS) with ?RHSf _ => RHSf end in
    change (LHS = Let_In (isFull(carry_full (carry_full (carry_full us)))) RHSf).
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (carry_full (carry_full (carry_full us))) in RHS) with ?RHSf _ => RHSf end in
    rewrite <-carry_full_3_opt_cps_correct with (f := RHSf).
    cbv beta iota delta [and_term isFull isFull'].
    change length with length_opt.
    change @max_bound with max_bound_opt.
    rewrite c_subst.
    change @max_ones with max_ones_opt.
    change @base with base_opt.
    change minus with minus_opt.
    change @map with @map_opt.
    change Z.sub with Z_sub_opt at 1.
    rewrite <-modulus_digits_opt_correct.
    reflexivity.
  Defined.

  Definition freeze_opt (us : digits) : digits
    := Eval cbv beta iota delta [proj1_sig freeze_opt_sig] in proj1_sig (freeze_opt_sig us).

  Definition freeze_opt_correct us
    : freeze_opt us = freeze us
    := proj2_sig (freeze_opt_sig us).
End Canonicalization.
