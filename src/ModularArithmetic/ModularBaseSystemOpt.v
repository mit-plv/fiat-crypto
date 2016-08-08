Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemList.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil Crypto.Util.CaseUtil.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.QArith.QArith Coq.QArith.Qround.
Require Import Crypto.Tactics.VerdiTactics.
Require Export Crypto.Util.FixCoqMistakes.
Local Open Scope Z.

Class SubtractionCoefficient (m : Z) (prm : PseudoMersenneBaseParams m) := {
  coeff : tuple Z (length limb_widths);
  coeff_mod: decode coeff = 0%F
}.

(* Computed versions of some functions. *)

Definition Z_add_opt := Eval compute in Z.add.
Definition Z_sub_opt := Eval compute in Z.sub.
Definition Z_mul_opt := Eval compute in Z.mul.
Definition Z_div_opt := Eval compute in Z.div.
Definition Z_pow_opt := Eval compute in Z.pow.
Definition Z_opp_opt := Eval compute in Z.opp.
Definition Z_ones_opt := Eval compute in Z.ones.
Definition Z_shiftl_opt := Eval compute in Z.shiftl.
Definition Z_shiftl_by_opt := Eval compute in Z.shiftl_by.

Definition nth_default_opt {A} := Eval compute in @nth_default A.
Definition set_nth_opt {A} := Eval compute in @set_nth A.
Definition update_nth_opt {A} := Eval compute in @update_nth A.
Definition map_opt {A B} := Eval compute in @map A B.
Definition full_carry_chain_opt := Eval compute in @Pow2Base.full_carry_chain.
Definition length_opt := Eval compute in length.
Definition base_from_limb_widths_opt := Eval compute in @Pow2Base.base_from_limb_widths.
Definition minus_opt := Eval compute in minus.
Definition max_ones_opt := Eval compute in @max_ones.
Definition from_list_default_opt {A} := Eval compute in (@from_list_default A).

Definition Let_In {A P} (x : A) (f : forall y : A, P y)
  := let y := x in f y.

(* Some automation that comes in handy when constructing base parameters *)
Ltac opt_step :=
  match goal with
  | [ |- _ = match ?e with nil => _ | _ => _ end :> ?T ]
    => refine (_ : match e with nil => _ | _ => _ end = _);
       destruct e
  end.

Definition limb_widths_from_len_step loop len k :=
  (fun i prev =>
    match i with
    | O => nil
    | S i' => let x := (if (Z.eqb ((k * Z.of_nat (len - i + 1)) mod (Z.of_nat len)) 0)
                        then (k * Z.of_nat (len - i + 1)) / Z.of_nat len
                        else (k * Z.of_nat (len - i + 1)) / Z.of_nat len + 1)in
      x - prev:: (loop i' x)
    end).
Definition limb_widths_from_len len k :=
  (fix loop i prev := limb_widths_from_len_step loop len k i prev) len 0.

Definition brute_force_indices0 lw : bool
  := List.fold_right
       andb true
       (List.map
          (fun i
           => List.fold_right
                andb true
                (List.map
                   (fun j
                    => sum_firstn lw (i + j) <=? sum_firstn lw i + sum_firstn lw j)
                   (seq 0 (length lw - i))))
          (seq 0 (length lw))).

Lemma brute_force_indices_correct0 lw
  : brute_force_indices0 lw = true -> forall i j : nat,
      (i + j < length lw)%nat -> sum_firstn lw (i + j) <= sum_firstn lw i + sum_firstn lw j.
Proof.
  unfold brute_force_indices0.
  progress repeat setoid_rewrite fold_right_andb_true_map_iff.
  setoid_rewrite in_seq.
  setoid_rewrite Z.leb_le.
  eauto with omega.
Qed.

Definition brute_force_indices1 lw : bool
  := List.fold_right
       andb true
       (List.map
          (fun i
           => List.fold_right
                andb true
                (List.map
                   (fun j
                    => let w_sum := sum_firstn lw in
                       sum_firstn lw (length lw) + w_sum (i + j - length lw)%nat <=? w_sum i + w_sum j)
                   (seq (length lw - i) (length lw - (length lw - i)))))
          (seq 1 (length lw - 1))).

Lemma brute_force_indices_correct1 lw
  : brute_force_indices1 lw = true -> forall i j : nat,
  (i < length lw)%nat ->
  (j < length lw)%nat ->
  (i + j >= length lw)%nat ->
  let w_sum := sum_firstn lw in
  sum_firstn lw (length lw) + w_sum (i + j - length lw)%nat <= w_sum i + w_sum j.
Proof.
  unfold brute_force_indices1.
  progress repeat setoid_rewrite fold_right_andb_true_map_iff.
  setoid_rewrite in_seq.
  setoid_rewrite Z.leb_le.
  eauto with omega.
Qed.

Ltac construct_params prime_modulus len k :=
  let lwv := (eval cbv in (limb_widths_from_len len k)) in
  let lw := fresh "lw" in pose lwv as lw;
  eapply Build_PseudoMersenneBaseParams with (limb_widths := lw);
  [ abstract (apply fold_right_and_True_forall_In_iff; simpl; repeat (split; [omega |]); auto)
  | abstract (cbv; congruence)
  | abstract (refine (@brute_force_indices_correct0 lw _); vm_cast_no_check (eq_refl true))
  | abstract apply prime_modulus
  | abstract (cbv; congruence)
  | abstract (refine (@brute_force_indices_correct1 lw _); vm_cast_no_check (eq_refl true))].

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
  Local Notation base := (Pow2Base.base_from_limb_widths limb_widths).
  Local Notation digits := (tuple Z (length limb_widths)).

  Definition carry_gen_opt_sig fc fi i us
    : { d : list Z | (0 <= fi (S (fi i)) < length us)%nat ->
                     d = carry_gen limb_widths fc fi i us}.
  Proof.
    eexists; intros.
    cbv beta iota delta [carry_gen carry_single Z.pow2_mod].
    rewrite add_to_nth_set_nth.
    change @nth_default with @nth_default_opt in *.
    change @set_nth with @set_nth_opt in *.
    change Z.ones with Z_ones_opt.
    rewrite set_nth_nth_default by assumption.
    rewrite <- @beq_nat_eq_nat_dec.
    reflexivity.
  Defined.

  Definition carry_gen_opt fc fi i us := Eval cbv [proj1_sig carry_gen_opt_sig] in
                                                   proj1_sig (carry_gen_opt_sig fc fi i us).

  Definition carry_gen_opt_correct fc fi i us
    : (0 <= fi (S (fi i)) < length us)%nat ->
      carry_gen_opt fc fi i us = carry_gen limb_widths fc fi i us
    := proj2_sig (carry_gen_opt_sig fc fi i us).

  Definition carry_opt_sig
             (i : nat) (b : list Z)
    : { d : list Z | (length b = length limb_widths)
                     -> (i < length limb_widths)%nat
                     -> d = carry i b }.
  Proof.
    eexists ; intros.
    cbv [carry].
    rewrite <-pull_app_if_sumbool.
    cbv beta delta
      [carry carry_and_reduce carry_simple].
    lazymatch goal with
    | [ |- _ = (if ?br then ?c else ?d) ]
      => let x := fresh "x" in let y := fresh "y" in evar (x:list Z); evar (y:list Z); transitivity (if br then x else y); subst x; subst y
    end.
    Focus 2. {
      cbv zeta.
      break_if; rewrite <-carry_gen_opt_correct by (omega ||
          (replace (length b) with (length limb_widths) by congruence;
           apply Nat.mod_bound_pos; omega)); reflexivity.
    } Unfocus.
    rewrite c_subst.
    rewrite <- @beq_nat_eq_nat_dec.
    cbv [carry_gen_opt].
    reflexivity.
  Defined.

  Definition carry_opt is us := Eval cbv [proj1_sig carry_opt_sig] in
                                          proj1_sig (carry_opt_sig is us).

  Definition carry_opt_correct i us
    : length us = length limb_widths
      -> (i < length limb_widths)%nat
      -> carry_opt i us = carry i us
    := proj2_sig (carry_opt_sig i us).

  Definition carry_sequence_opt_sig (is : list nat) (us : list Z)
    : { b : list Z | (length us = length limb_widths)
                     -> (forall i, In i is -> i < length limb_widths)%nat
                     -> b = carry_sequence is us }.
  Proof.
    eexists. intros H.
    cbv [carry_sequence].
    transitivity (fold_right carry_opt us is).
    Focus 2.
    { induction is; [ reflexivity | ].
      simpl; rewrite IHis, carry_opt_correct.
      - reflexivity.
      - fold (carry_sequence is us). auto using length_carry_sequence.
      - auto using in_eq.
      - intros. auto using in_cons.
      }
    Unfocus.
    reflexivity.
  Defined.

  Definition carry_sequence_opt is us := Eval cbv [proj1_sig carry_sequence_opt_sig] in
                                          proj1_sig (carry_sequence_opt_sig is us).

  Definition carry_sequence_opt_correct is us
    : (length us = length limb_widths)
      -> (forall i, In i is -> i < length limb_widths)%nat
      -> carry_sequence_opt is us = carry_sequence is us
    := proj2_sig (carry_sequence_opt_sig is us).

  Definition carry_gen_opt_cps_sig
             {T} fc fi
             (i : nat)
             (f : list Z -> T)
             (b : list Z)
    : { d : T | (0 <= fi (S (fi i)) < length b)%nat -> d = f (carry_gen limb_widths fc fi i b) }.
  Proof.
    eexists. intros H.
    rewrite <-carry_gen_opt_correct by assumption.
    cbv beta iota delta [carry_gen_opt].
    match goal with |- appcontext[?a & Z_ones_opt _] =>
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (a) in RHS) with ?RHSf _ => RHSf end in
    change (LHS = Let_In (a) RHSf) end.
    reflexivity.
  Defined.

  Definition carry_gen_opt_cps {T} fc fi i f b
    := Eval cbv beta iota delta [proj1_sig carry_gen_opt_cps_sig] in
                                 proj1_sig (@carry_gen_opt_cps_sig T fc fi i f b).

  Definition carry_gen_opt_cps_correct {T} fc fi i f b :
   (0 <= fi (S (fi i)) < length b)%nat ->
    @carry_gen_opt_cps T fc fi i f b = f (carry_gen limb_widths fc fi i b)
    := proj2_sig (carry_gen_opt_cps_sig fc fi i f b).

  Definition carry_opt_cps_sig
             {T}
             (i : nat)
             (f : list Z -> T)
             (b : list Z)
    : { d : T | (length b = length limb_widths)
                 -> (i < length limb_widths)%nat
                 -> d = f (carry i b) }.
  Proof.
    eexists. intros.
    cbv beta delta
      [carry carry_and_reduce carry_simple].
    rewrite <-pull_app_if_sumbool.
    lazymatch goal with
    | [ |- _ = ?f (if ?br then ?c else ?d) ]
      => let x := fresh "x" in let y := fresh "y" in evar (x:T); evar (y:T); transitivity (if br then x else y); subst x; subst y
    end.
    Focus 2. {
      cbv zeta.
      break_if; rewrite <-carry_gen_opt_cps_correct by (omega ||
          (replace (length b) with (length limb_widths) by congruence;
           apply Nat.mod_bound_pos; omega)); reflexivity.
    } Unfocus.
    rewrite c_subst.
    rewrite <- @beq_nat_eq_nat_dec.
    reflexivity.
  Defined.

  Definition carry_opt_cps {T} i f b
    := Eval cbv beta iota delta [proj1_sig carry_opt_cps_sig] in proj1_sig (@carry_opt_cps_sig T i f b).

  Definition carry_opt_cps_correct {T} i f b :
    (length b = length limb_widths)
    -> (i < length limb_widths)%nat
    -> @carry_opt_cps T i f b = f (carry i b)
    := proj2_sig (carry_opt_cps_sig i f b).

  Definition carry_sequence_opt_cps_sig {T} (is : list nat) (us : list Z)
     (f : list Z -> T)
    : { b : T | (length us = length limb_widths)
                -> (forall i, In i is -> i < length limb_widths)%nat
                -> b = f (carry_sequence is us) }.
  Proof.
    eexists.
    cbv [carry_sequence].
    transitivity (fold_right carry_opt_cps f (List.rev is) us).
    Focus 2.
    {
      assert (forall i, In i (rev is) -> i < length limb_widths)%nat as Hr. {
        subst. intros. rewrite <- in_rev in *. auto. }
      remember (rev is) as ris eqn:Heq.
      rewrite <- (rev_involutive is), <- Heq in H0 |- *.
      clear H0 Heq is.
      rewrite fold_left_rev_right.
      revert H. revert us; induction ris; [ reflexivity | ]; intros.
      { simpl.
        rewrite <- IHris; clear IHris;
          [|intros; apply Hr; right; assumption|auto using length_carry].
        rewrite carry_opt_cps_correct; [reflexivity|congruence|].
        apply Hr; left; reflexivity.
        } }
    Unfocus.
    cbv [carry_opt_cps].
    reflexivity.
  Defined.

  Definition carry_sequence_opt_cps {T} is us (f : list Z -> T) :=
    Eval cbv [proj1_sig carry_sequence_opt_cps_sig] in
      proj1_sig (carry_sequence_opt_cps_sig is us f).

  Definition carry_sequence_opt_cps_correct {T} is us (f : list Z -> T)
    : (length us = length limb_widths)
      -> (forall i, In i is -> i < length limb_widths)%nat
      -> carry_sequence_opt_cps is us f = f (carry_sequence is us)
    := proj2_sig (carry_sequence_opt_cps_sig is us f).

  Lemma full_carry_chain_bounds : forall i, In i (Pow2Base.full_carry_chain limb_widths) ->
    (i < length limb_widths)%nat.
  Proof.
    unfold Pow2Base.full_carry_chain; intros.
    apply Pow2BaseProofs.make_chain_lt; auto.
  Qed.

  Definition carry_full_opt_sig (us : digits) : { b : digits | b = carry_full us }.
  Proof.
    eexists.
    cbv [carry_full ModularBaseSystemList.carry_full].
    rewrite <-from_list_default_eq with (d := 0).
    rewrite <-carry_sequence_opt_cps_correct by (rewrite ?length_to_list; auto; apply full_carry_chain_bounds).
    change @Pow2Base.full_carry_chain with full_carry_chain_opt.
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
    rewrite carry_sequence_opt_cps_correct by (apply length_to_list || apply full_carry_chain_bounds).
    match goal with |- ?LHS = ?f (?g (carry_sequence ?is ?us)) =>
      change (LHS = (fun x => f (g x)) (carry_sequence is us)) end.
    rewrite <-carry_sequence_opt_cps_correct by (apply length_to_list || apply full_carry_chain_bounds).
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
  Local Notation digits := (tuple Z (length limb_widths)).

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
  Local Notation digits := (tuple Z (length limb_widths)).

  Definition sub_opt_sig (us vs : digits) : { b : digits | b = sub coeff us vs }.
  Proof.
    eexists.
    cbv [BaseSystem.add ModularBaseSystem.sub BaseSystem.sub].
    reflexivity.
  Defined.

  Definition sub_opt (us vs : digits) : digits
    := Eval cbv [proj1_sig sub_opt_sig] in proj1_sig (sub_opt_sig us vs).

  Definition sub_opt_correct us vs
    : sub_opt us vs = sub coeff us vs
    := proj2_sig (sub_opt_sig us vs).
End Subtraction.

Section Multiplication.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient modulus prm}
    (* allows caller to precompute k and c *)
    (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_).
  Local Notation digits := (tuple Z (length limb_widths)).

  Definition mul_bi'_step
             (mul_bi' : nat -> list Z -> list Z -> list Z)
             (i : nat) (vsr : list Z) (bs : list Z)
    : list Z
    := match vsr with
       | [] => []
       | v :: vsr' => (v * crosscoef bs i (length vsr'))%Z :: mul_bi' i vsr' bs
       end.

  Definition mul_bi'_opt_step_sig
             (mul_bi' : nat -> list Z -> list Z -> list Z)
             (i : nat) (vsr : list Z) (bs : list Z)
    : { l : list Z | l = mul_bi'_step mul_bi' i vsr bs }.
  Proof.
    eexists.
    cbv [mul_bi'_step].
    opt_step.
    { reflexivity. }
    { cbv [crosscoef].
      change Z.div with Z_div_opt.
      change Z.mul with Z_mul_opt at 2.
      change @nth_default with @nth_default_opt.
      reflexivity. }
  Defined.

  Definition mul_bi'_opt_step
             (mul_bi' : nat -> list Z -> list Z -> list Z)
             (i : nat) (vsr : list Z) (bs : list Z)
    : list Z
    := Eval cbv [proj1_sig mul_bi'_opt_step_sig] in
        proj1_sig (mul_bi'_opt_step_sig mul_bi' i vsr bs).

  Fixpoint mul_bi'_opt
           (i : nat) (vsr : list Z) (bs : list Z) {struct vsr}
    : list Z
    := mul_bi'_opt_step mul_bi'_opt i vsr bs.

  Definition mul_bi'_opt_correct
             (i : nat) (vsr : list Z) (bs : list Z)
    : mul_bi'_opt i vsr bs = mul_bi' bs i vsr.
  Proof.
    revert i; induction vsr as [|vsr vsrs IHvsr]; intros.
    { reflexivity. }
    { simpl mul_bi'.
      rewrite <- IHvsr; clear IHvsr.
      unfold mul_bi'_opt, mul_bi'_opt_step.
      apply f_equal2; [ | reflexivity ].
      cbv [crosscoef].
      change Z.div with Z_div_opt.
      change Z.mul with Z_mul_opt at 2.
      change @nth_default with @nth_default_opt.
      reflexivity. }
  Qed.

  Definition mul'_step
             (mul' : list Z -> list Z -> list Z -> list Z)
             (usr vs : list Z) (bs : list Z)
    : list Z
    := match usr with
       | [] => []
       | u :: usr' => BaseSystem.add (mul_each u (mul_bi bs (length usr') vs)) (mul' usr' vs bs)
       end.

  Lemma map_zeros : forall a n l,
    map (Z.mul a) (zeros n ++ l) = zeros n ++ map (Z.mul a) l.
  Proof.
    induction n; simpl; [ reflexivity | intros; apply f_equal2; [ omega | congruence ] ].
  Qed.

  Definition mul'_opt_step_sig
             (mul' : list Z -> list Z -> list Z -> list Z)
             (usr vs : list Z) (bs : list Z)
    : { d : list Z | d = mul'_step mul' usr vs bs }.
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
             (mul' : list Z -> list Z -> list Z -> list Z)
             (usr vs : list Z) (bs : list Z)
    : list Z
    := Eval cbv [proj1_sig mul'_opt_step_sig] in proj1_sig (mul'_opt_step_sig mul' usr vs bs).

  Fixpoint mul'_opt
           (usr vs : list Z) (bs : list Z)
    : list Z
    := mul'_opt_step mul'_opt usr vs bs.

  Definition mul'_opt_correct
           (usr vs : list Z) (bs : list Z)
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
      cbv [zeros].
      reflexivity. }
  Qed.

  Definition mul_opt_sig (us vs : digits) : { b : digits | b = mul us vs }.
  Proof.
    eexists.
    cbv [mul ModularBaseSystemList.mul BaseSystem.mul mul_each mul_bi mul_bi' zeros reduce].
    rewrite <- from_list_default_eq with (d := 0%Z).
    change (@from_list_default Z) with (@from_list_default_opt Z).
    apply f_equal.
    rewrite ext_base_alt by auto using limb_widths_pos with zarith.
    rewrite <- mul'_opt_correct.
    change @Pow2Base.base_from_limb_widths with base_from_limb_widths_opt.
    rewrite Z.map_shiftl by apply k_nonneg.
    rewrite c_subst.
    fold k; rewrite k_subst.
    change @map with @map_opt.
    change @Z.shiftl_by with @Z_shiftl_by_opt.
    reflexivity.
  Defined.

  Definition mul_opt (us vs : digits) : digits
    := Eval cbv [proj1_sig mul_opt_sig] in proj1_sig (mul_opt_sig us vs).

  Definition mul_opt_correct us vs
    : mul_opt us vs = mul us vs
    := proj2_sig (mul_opt_sig us vs).

  Definition carry_mul_opt_sig {T} (f:digits -> T)
    (us vs : digits) : { x | x = f (carry_mul us vs) }.
  Proof.
    eexists.
    cbv [carry_mul].
    erewrite <-carry_full_opt_cps_correct by eauto.
    erewrite <-mul_opt_correct.
    cbv [carry_full_opt_cps mul_opt].
    erewrite from_list_default_eq.
    rewrite to_list_from_list.
    reflexivity.
    Grab Existential Variables.
    rewrite mul'_opt_correct.
    distr_length.
    assert (0 < length limb_widths)%nat by (pose proof limb_widths_nonnil; destruct limb_widths; congruence || simpl; omega).
    rewrite Min.min_l; rewrite !length_to_list; break_match; try omega.
    rewrite Max.max_l; omega.
  Defined.

  Definition carry_mul_opt_cps {T} (f:digits -> T) (us vs : digits) : T
    := Eval cbv [proj1_sig carry_mul_opt_sig] in proj1_sig (carry_mul_opt_sig f us vs).

  Definition carry_mul_opt_cps_correct {T} (f:digits -> T) (us vs : digits)
    : carry_mul_opt_cps f us vs = f (carry_mul us vs)
    := proj2_sig (carry_mul_opt_sig f us vs).

  Definition carry_mul_opt := carry_mul_opt_cps id.

  Definition carry_mul_opt_correct (us vs : digits)
    : carry_mul_opt us vs = carry_mul us vs :=
    carry_mul_opt_cps_correct id us vs.

End Multiplication.

Section with_base.
  Context {modulus} (prm : PseudoMersenneBaseParams modulus).
  Local Notation base := (Pow2Base.base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).

  Record freezePreconditions int_width :=
    mkFreezePreconditions {
        lt_1_length_base : (1 < length base)%nat;
        int_width_pos : 0 < int_width;
        int_width_compat : forall w, In w limb_widths -> w <= int_width;
        c_pos : 0 < c;
        c_reduce1 : c * (Z.ones (int_width - log_cap (pred (length base)))) < 2 ^ log_cap 0;
        c_reduce2 : c < 2 ^ log_cap 0 - c;
        two_pow_k_le_2modulus : 2 ^ k <= 2 * modulus
      }.
End with_base.
Local Hint Resolve lt_1_length_base int_width_pos int_width_compat c_pos
    c_reduce1 c_reduce2 two_pow_k_le_2modulus.

Section Canonicalization.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient modulus prm}
    (* allows caller to precompute k and c *)
    (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_)
    {int_width} (preconditions : freezePreconditions prm int_width).
  Local Notation digits := (tuple Z (length limb_widths)).

  Definition encodeZ_opt := Eval compute in Pow2Base.encodeZ.

  Definition modulus_digits_opt_sig :
    { b : list Z | b = modulus_digits }.
  Proof.
    eexists.
    cbv beta iota delta [modulus_digits].
    change Pow2Base.encodeZ with encodeZ_opt.
    reflexivity.
  Defined.

  Definition modulus_digits_opt : list Z
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
    cbv [freeze conditional_subtract_modulus].
    rewrite <-from_list_default_eq with (d := 0%Z).
    change (@from_list_default Z) with (@from_list_default_opt Z).
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (to_list (length limb_widths) (carry_full (carry_full (carry_full us)))) in RHS) with ?RHSf _ => RHSf end in
    change (LHS = Let_In (to_list (length limb_widths)  (carry_full (carry_full (carry_full us)))) RHSf).
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (carry_full (carry_full (carry_full us))) in RHS) with ?RHSf _ => RHSf end in
    rewrite <-carry_full_3_opt_cps_correct with (f := RHSf).
    cbv beta iota delta [ge_modulus ge_modulus'].
    change length with length_opt.
    change (nth_default 0 modulus_digits) with (nth_default_opt 0 modulus_digits_opt).
    change @max_ones with max_ones_opt.
    change @Pow2Base.base_from_limb_widths with base_from_limb_widths_opt.
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
(*
  Lemma freeze_opt_canonical: forall us vs x,
    @pre_carry_bounds _ _ int_width us -> rep us x ->
    @pre_carry_bounds _ _ int_width vs -> rep vs x ->
    freeze_opt us = freeze_opt vs.
  Proof.
    intros.
    rewrite !freeze_opt_correct.
    eapply freeze_canonical with (B := int_width); eauto.
  Qed.

  Lemma freeze_opt_preserves_rep : forall us x, rep us x ->
    rep (freeze_opt us) x.
  Proof.
    intros.
    rewrite freeze_opt_correct.
    eapply freeze_preserves_rep; eauto.
  Qed.

  Lemma freeze_opt_spec : forall us vs x, rep us x -> rep vs x ->
    @pre_carry_bounds _ _ int_width us ->
    @pre_carry_bounds _ _ int_width vs ->
    (rep (freeze_opt us) x /\ freeze_opt us = freeze_opt vs).
  Proof.
    split; eauto using freeze_opt_canonical.
    auto using freeze_opt_preserves_rep.
  Qed.
*)
End Canonicalization.
