Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseRep.
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

(* Computed versions of some functions. *)

Definition Z_add_opt := Eval compute in Z.add.
Definition Z_sub_opt := Eval compute in Z.sub.
Definition Z_mul_opt := Eval compute in Z.mul.
Definition Z_div_opt := Eval compute in Z.div.
Definition Z_pow_opt := Eval compute in Z.pow.
Definition Z_shiftl_by_opt := Eval compute in Z_shiftl_by.

Definition nth_default_opt {A} := Eval compute in @nth_default A.
Definition set_nth_opt {A} := Eval compute in @set_nth A.
Definition map_opt {A B} := Eval compute in @map A B.
Definition base_from_limb_widths_opt := Eval compute in base_from_limb_widths.

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

Definition Let_In {A P} (x : A) (f : forall y : A, P y)
  := let y := x in f y.

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
       pow2_mod Z.ones Z.pred base
       PseudoMersenneBaseParams.limb_widths].
    change @nth_default with @nth_default_opt in *.
    change @set_nth with @set_nth_opt in *.
    lazymatch goal with
    | [ |- _ = (if ?br then ?c else ?d) ]
      => let x := fresh "x" in let y := fresh "y" in evar (x:digits); evar (y:digits); transitivity (if br then x else y); subst x; subst y
    end.
    Focus 2.
    cbv zeta.
    break_if; reflexivity.

    change @nth_default with @nth_default_opt.
    rewrite c_subst.
    change @set_nth with @set_nth_opt.
    change @map with @map_opt.
    rewrite <- @beq_nat_eq_nat_dec.
    change base_from_limb_widths with base_from_limb_widths_opt.
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
    reflexivity.
  Defined.

  Definition carry_opt_cps {T} i f b
    := Eval cbv beta iota delta [proj1_sig carry_opt_cps_sig] in proj1_sig (@carry_opt_cps_sig T i f b).

  Definition carry_opt_cps_correct {T} i f b :
    (i < length base)%nat ->
    @carry_opt_cps T i f b = f (carry i b)
    := proj2_sig (carry_opt_cps_sig i f b).

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
         length us = length base ->
         rep us x -> rep (carry_sequence_opt_cps is us) x.
  Proof.
    intros.
    rewrite carry_sequence_opt_cps_correct by assumption.
    apply carry_sequence_rep; assumption.
  Qed.

End Carries.

Section Addition.
  Context `{prm : PseudoMersenneBaseParams}.

  Definition add_opt_sig (us vs : T) : { b : digits | b = add us vs }.
  Proof.
    eexists.
    cbv [BaseSystem.add].
    reflexivity.
  Defined.

  Definition add_opt (us vs : T) : digits
    := Eval cbv [proj1_sig add_opt_sig] in proj1_sig (add_opt_sig us vs).

  Definition add_opt_correct us vs
    : add_opt us vs = add us vs
    := proj2_sig (add_opt_sig us vs).

  Lemma add_opt_rep:
    forall (u v : T) (x y : F modulus), rep u x -> rep v y -> rep (add_opt u v) (x + y)%F.
  Proof.
    intros.
    rewrite add_opt_correct.
    auto using add_rep.
  Qed.

End Addition.

Section Multiplication.
  Context `{prm : PseudoMersenneBaseParams}
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

  Definition mul_opt_sig (us vs : T) : { b : digits | b = mul us vs }.
  Proof.
    eexists.
    cbv [BaseSystem.mul mul mul_each mul_bi mul_bi' zeros ext_base reduce].
    rewrite <- mul'_opt_correct.
    cbv [base PseudoMersenneBaseParams.limb_widths].
    rewrite map_shiftl by apply k_nonneg.
    rewrite c_subst.
    rewrite k_subst.
    change @map with @map_opt.
    change base_from_limb_widths with base_from_limb_widths_opt.  
    change @Z_shiftl_by with @Z_shiftl_by_opt.
    reflexivity.
  Defined.

  Definition mul_opt (us vs : T) : digits
    := Eval cbv [proj1_sig mul_opt_sig] in proj1_sig (mul_opt_sig us vs).

  Definition mul_opt_correct us vs
    : mul_opt us vs = mul us vs
    := proj2_sig (mul_opt_sig us vs).

  Lemma mul_opt_rep:
    forall (u v : T) (x y : F modulus), rep u x -> rep v y -> rep (mul_opt u v) (x * y)%F.
  Proof.
    intros.
    rewrite mul_opt_correct.
    auto using mul_rep.
  Qed.

  Definition carry_mul_opt 
             (is : list nat)
             (us vs : list Z)
             : list Z
    := carry_sequence_opt_cps c_ is (mul_opt us vs).

  Lemma carry_mul_opt_correct
    : forall (is : list nat) (us vs : list Z) (x  y: F modulus),
      rep us x -> rep vs y ->
      (forall i : nat, In i is -> i < length base)%nat ->
      length (mul_opt us vs) = length base ->
      rep (carry_mul_opt is us vs) (x*y)%F.
  Proof.
    intros is us vs x y; intros.
    change (carry_mul_opt _ _ _) with (carry_sequence_opt_cps c_ is (mul_opt us vs)).
    apply carry_sequence_opt_cps_rep, mul_opt_rep; auto.
  Qed.
End Multiplication.
