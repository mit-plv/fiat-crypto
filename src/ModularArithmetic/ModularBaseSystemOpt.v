Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.ModularArithmetic.Conversion.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemList.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.AdditionChainExponentiation.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil Crypto.Util.CaseUtil.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.QArith.QArith Coq.QArith.Qround.
Require Import Crypto.Tactics.VerdiTactics.
Require Export Crypto.Util.FixCoqMistakes.
Local Open Scope Z.

(* Computed versions of some functions. *)

Definition plus_opt := Eval compute in plus.

Definition Z_add_opt := Eval compute in Z.add.
Definition Z_sub_opt := Eval compute in Z.sub.
Definition Z_mul_opt := Eval compute in Z.mul.
Definition Z_div_opt := Eval compute in Z.div.
Definition Z_pow_opt := Eval compute in Z.pow.
Definition Z_opp_opt := Eval compute in Z.opp.
Definition Z_min_opt := Eval compute in Z.min.
Definition Z_ones_opt := Eval compute in Z.ones.
Definition Z_of_nat_opt := Eval compute in Z.of_nat.
Definition Z_le_dec_opt := Eval compute in Z_le_dec.
Definition Z_lt_dec_opt := Eval compute in Z_lt_dec.
Definition Z_shiftl_opt := Eval compute in Z.shiftl.
Definition Z_shiftl_by_opt := Eval compute in Z.shiftl_by.

Definition nth_default_opt {A} := Eval compute in @nth_default A.
Definition set_nth_opt {A} := Eval compute in @set_nth A.
Definition update_nth_opt {A} := Eval compute in @update_nth A.
Definition map_opt {A B} := Eval compute in @List.map A B.
Definition full_carry_chain_opt := Eval compute in @Pow2Base.full_carry_chain.
Definition length_opt := Eval compute in length.
Definition base_from_limb_widths_opt := Eval compute in @Pow2Base.base_from_limb_widths.
Definition minus_opt := Eval compute in minus.
Definition max_ones_opt := Eval compute in @max_ones.
Definition from_list_default_opt {A} := Eval compute in (@from_list_default A).
Definition sum_firstn_opt {A} := Eval compute in (@sum_firstn A).
Definition zeros_opt := Eval compute in (@zeros).
Definition bit_index_opt := Eval compute in bit_index.
Definition digit_index_opt := Eval compute in digit_index.

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
      2 ^ (x + 1) - (2 * c) :: List.map (fun w => 2 ^ (w + 1) - 2) tail
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

  Definition carry_full_opt_sig (us : list Z) :
    { b : list Z | (length us = length limb_widths)
                   -> b = carry_full us }.
  Proof.
    eexists;  cbv [carry_full]; intros.
    match goal with |- ?LHS = ?RHS => change (LHS = id RHS) end.
    rewrite <-carry_sequence_opt_cps_correct with (f := id)  by (auto; apply full_carry_chain_bounds).
    change @Pow2Base.full_carry_chain with full_carry_chain_opt.
    reflexivity.
  Defined.

  Definition carry_full_opt (us : list Z) : list Z
    := Eval cbv [proj1_sig carry_full_opt_sig] in proj1_sig (carry_full_opt_sig us).

  Definition carry_full_opt_correct us
    : length us = length limb_widths
      -> carry_full_opt us = carry_full us
    := proj2_sig (carry_full_opt_sig us).

  Definition carry_full_opt_cps_sig
             {T}
             (f : list Z -> T)
             (us : list Z)
    : { d : T | length us = length limb_widths
                -> d = f (carry_full us) }.
  Proof.
    eexists; intros.
    rewrite <- carry_full_opt_correct by auto.
    cbv beta iota delta [carry_full_opt].
    rewrite carry_sequence_opt_cps_correct by (auto || apply full_carry_chain_bounds).
    match goal with |- ?LHS = ?f (?g (carry_sequence ?is ?us)) =>
      change (LHS = (fun x => f (g x)) (carry_sequence is us)) end.
    rewrite <-carry_sequence_opt_cps_correct by (auto || apply full_carry_chain_bounds).
    reflexivity.
  Defined.

  Definition carry_full_opt_cps {T} (f : list Z -> T) (us : list Z) : T
    := Eval cbv [proj1_sig carry_full_opt_cps_sig] in proj1_sig (carry_full_opt_cps_sig f us).

  Definition carry_full_opt_cps_correct {T} us (f : list Z -> T)
    : length us = length limb_widths
      -> carry_full_opt_cps f us = f (carry_full us)
    := proj2_sig (carry_full_opt_cps_sig f us).

End Carries.

Section Addition.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient}.
  Local Notation digits := (tuple Z (length limb_widths)).

  Definition add_opt_sig (us vs : digits) : { b : digits | b = add us vs }.
  Proof.
    eexists.
    reflexivity.
  Defined.

  Definition add_opt (us vs : digits) : digits
    := Eval cbv [proj1_sig add_opt_sig] in proj1_sig (add_opt_sig us vs).

  Definition add_opt_correct us vs
    : add_opt us vs = add us vs
    := proj2_sig (add_opt_sig us vs).
End Addition.

Section Subtraction.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient}.
  Local Notation digits := (tuple Z (length limb_widths)).

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

  Definition opp_opt_sig (us : digits) : { b : digits | b = opp coeff coeff_mod us }.
  Proof.
    eexists.
    cbv [opp].
    rewrite <-sub_opt_correct.
    reflexivity.
  Defined.

  Definition opp_opt (us : digits) : digits
    := Eval cbv [proj1_sig opp_opt_sig] in proj1_sig (opp_opt_sig us).

  Definition opp_opt_correct us
    : opp_opt us = opp coeff coeff_mod us
    := proj2_sig (opp_opt_sig us).

End Subtraction.

Section Multiplication.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient} {cc : CarryChain limb_widths}
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
    List.map (Z.mul a) (zeros n ++ l) = zeros n ++ List.map (Z.mul a) l.
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
      change @List.map with @map_opt.
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
    change @List.map with @map_opt.
    change @Z.shiftl_by with @Z_shiftl_by_opt.
    reflexivity.
  Defined.

  Definition mul_opt (us vs : digits) : digits
    := Eval cbv [proj1_sig mul_opt_sig] in proj1_sig (mul_opt_sig us vs).

  Definition mul_opt_correct us vs
    : mul_opt us vs = mul us vs
    := proj2_sig (mul_opt_sig us vs).

  Definition carry_mul_opt_sig {T} (f:digits -> T)
    (us vs : digits) : { x | x = f (carry_mul carry_chain us vs) }.
  Proof.
    eexists.
    cbv [carry_mul].
    rewrite <- from_list_default_eq with (d := 0%Z).
    change @from_list_default with @from_list_default_opt.
    erewrite <-carry_sequence_opt_cps_correct by eauto using carry_chain_valid, length_to_list.
    erewrite <-mul_opt_correct.
    cbv [carry_sequence_opt_cps mul_opt].
    erewrite from_list_default_eq.
    rewrite to_list_from_list.
    reflexivity.
    Grab Existential Variables.
    rewrite mul'_opt_correct.
    distr_length.
    assert (0 < length limb_widths)%nat by (pose proof limb_widths_nonnil; destruct limb_widths; congruence || simpl; omega).
    rewrite Min.min_l; break_match; try omega.
    rewrite Max.max_l; omega.
  Defined.

  Definition carry_mul_opt_cps {T} (f:digits -> T) (us vs : digits) : T
    := Eval cbv [proj1_sig carry_mul_opt_sig] in proj1_sig (carry_mul_opt_sig f us vs).

  Definition carry_mul_opt_cps_correct {T} (f:digits -> T) (us vs : digits)
    : carry_mul_opt_cps f us vs = f (carry_mul carry_chain us vs)
    := proj2_sig (carry_mul_opt_sig f us vs).

  Definition carry_mul_opt := carry_mul_opt_cps id.

  Definition carry_mul_opt_correct (us vs : digits)
    : carry_mul_opt us vs = carry_mul carry_chain us vs :=
    carry_mul_opt_cps_correct id us vs.

End Multiplication.

Import Morphisms.
Global Instance Proper_fold_chain {T} {Teq} {Teq_Equivalence : Equivalence Teq}
  : Proper (Logic.eq
              ==> (fun f g => forall x1 x2 y1 y2 : T, Teq x1 x2 -> Teq y1 y2 -> Teq (f x1 y1) (g x2 y2))
              ==> Logic.eq
              ==> SetoidList.eqlistA Teq
              ==> Teq) fold_chain.
Proof.
  do 9 intro.
  subst; induction y1; repeat intro;
    unfold fold_chain; fold @fold_chain.
  + inversion H; assumption || reflexivity.
  + destruct a.
    apply IHy1.
    econstructor; try assumption.
    apply H0; eapply Proper_nth_default; eauto; reflexivity.
Qed.

Section PowInv.
  Context `{prm : PseudoMersenneBaseParams}
          (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_)
          {cc : CarryChain limb_widths}.
  Local Notation digits := (tuple Z (length limb_widths)).
  Context (one_ : digits) (one_subst : one = one_).

  Fixpoint fold_chain_opt {T} (id : T) op chain acc :=
  match chain with
  | [] => match acc with
          | [] => id
          | ret :: _ => ret
          end
  | (i, j) :: chain' =>
      Let_In (op (nth_default id acc i) (nth_default id acc j))
      (fun ijx => fold_chain_opt id op chain' (ijx :: acc))
  end.

  Lemma fold_chain_opt_correct : forall {T} (id : T) op chain acc,
    fold_chain_opt id op chain acc = fold_chain id op chain acc.
  Proof.
    reflexivity.
  Qed.

  Definition pow_opt_sig x chain :
    {y | eq y (ModularBaseSystem.pow x chain)}.
  Proof.
    eexists.
    cbv beta iota delta [ModularBaseSystem.pow].
    transitivity (fold_chain one_ (carry_mul_opt k_ c_) chain [x]).
    Focus 2. {
      apply Proper_fold_chain; auto; try reflexivity.
      cbv [eq]; intros.
      rewrite carry_mul_opt_correct by assumption.
      rewrite carry_mul_rep, mul_rep by reflexivity.
      congruence.
    } Unfocus.
    rewrite <-fold_chain_opt_correct.
    reflexivity.
  Defined.

  Definition pow_opt x chain : digits
    := Eval cbv [proj1_sig pow_opt_sig] in (proj1_sig (pow_opt_sig x chain)).

  Definition pow_opt_correct x chain
    : eq (pow_opt x chain) (ModularBaseSystem.pow x chain)
    := Eval cbv [proj2_sig pow_opt_sig] in (proj2_sig (pow_opt_sig x chain)).

  Context {ec : ExponentiationChain (modulus - 2)}.

  Definition inv_opt_sig x:
    {y | eq y (inv chain chain_correct x)}.
  Proof.
    eexists.
    cbv [inv].
    rewrite <-pow_opt_correct.
    reflexivity.
  Defined.

  Definition inv_opt x : digits
    := Eval cbv [proj1_sig inv_opt_sig] in (proj1_sig (inv_opt_sig x)).

  Definition inv_opt_correct x
    : eq (inv_opt x) (inv chain chain_correct x)
    := Eval cbv [proj2_sig inv_opt_sig] in (proj2_sig (inv_opt_sig x)).
End PowInv.

Section Conversion.

  Definition convert'_opt_sig {lwA lwB}
             (nonnegA : forall x, In x lwA -> 0 <= x)
             (nonnegB : forall x, In x lwB -> 0 <= x)
             bits_fit inp i out :
    { y | y = convert' nonnegA nonnegB bits_fit inp i out}.
  Proof.
    eexists.
    rewrite convert'_equation.
    change sum_firstn with @sum_firstn_opt.
    change length with length_opt.
    change Z_le_dec with Z_le_dec_opt.
    change Z.of_nat with Z_of_nat_opt.
    change digit_index with digit_index_opt.
    change bit_index with bit_index_opt.
    change Z.min with Z_min_opt.
    change (nth_default 0 lwA) with (nth_default_opt 0 lwA).
    change (nth_default 0 lwB) with (nth_default_opt 0 lwB).
    cbv [update_by_concat_bits concat_bits Z.pow2_mod].
    change Z.ones with Z_ones_opt.
    change @update_nth with @update_nth_opt.
    change plus with plus_opt.
    change Z.sub with Z_sub_opt.
    reflexivity.
  Defined.

  Definition convert'_opt {lwA lwB}
             (nonnegA : forall x, In x lwA -> 0 <= x)
             (nonnegB : forall x, In x lwB -> 0 <= x)
             bits_fit inp i out :=
    Eval cbv [proj1_sig convert'_opt_sig] in
      proj1_sig (convert'_opt_sig nonnegA nonnegB bits_fit inp i out).

  Definition convert'_opt_correct {lwA lwB}
             (nonnegA : forall x, In x lwA -> 0 <= x)
             (nonnegB : forall x, In x lwB -> 0 <= x)
             bits_fit inp i out :
    convert'_opt nonnegA nonnegB bits_fit inp i out = convert' nonnegA nonnegB bits_fit inp i out :=
    Eval cbv [proj2_sig convert'_opt_sig] in
      proj2_sig (convert'_opt_sig nonnegA nonnegB bits_fit inp i out).

  Context {modulus} (prm : PseudoMersenneBaseParams modulus)
          {target_widths} (target_widths_nonneg : forall x, In x target_widths -> 0 <= x) (bits_eq : sum_firstn limb_widths (length limb_widths) = sum_firstn target_widths (length target_widths)).
  Local Notation digits := (tuple Z (length limb_widths)).
  Local Notation target_digits := (tuple Z (length target_widths)).

  Definition pack_opt_sig (x : digits) : { y | y = pack target_widths_nonneg bits_eq x}.
  Proof.
    eexists.
    cbv [pack].
    rewrite <- from_list_default_eq with (d := 0%Z).
    change @from_list_default with @from_list_default_opt.
    cbv [ModularBaseSystemList.pack convert].
    change length with length_opt.
    change sum_firstn with @sum_firstn_opt.
    change zeros with zeros_opt.
    reflexivity.
  Defined.

  Definition pack_opt (x : digits) : target_digits :=
    Eval cbv [proj1_sig pack_opt_sig] in proj1_sig (pack_opt_sig x).

  Definition pack_correct (x : digits) :
    pack_opt x = pack target_widths_nonneg bits_eq x
    := Eval cbv [proj2_sig pack_opt_sig] in proj2_sig (pack_opt_sig x).

  Definition unpack_opt_sig (x : target_digits) : { y | y = unpack target_widths_nonneg bits_eq x}.
  Proof.
    eexists.
    cbv [unpack].
    rewrite <- from_list_default_eq with (d := 0%Z).
    change @from_list_default with @from_list_default_opt.
    cbv [ModularBaseSystemList.unpack convert].
    change length with length_opt.
    change sum_firstn with @sum_firstn_opt.
    change zeros with zeros_opt.
    reflexivity.
  Defined.

  Definition unpack_opt (x : target_digits) : digits :=
    Eval cbv [proj1_sig unpack_opt_sig] in proj1_sig (unpack_opt_sig x).

  Definition unpack_correct (x : target_digits) :
    unpack_opt x = unpack target_widths_nonneg bits_eq x
    := Eval cbv [proj2_sig unpack_opt_sig] in proj2_sig (unpack_opt_sig x).

End Conversion.

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
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient}
    (* allows caller to precompute k and c *)
    (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_)
    {int_width} (preconditions : freezePreconditions prm int_width).
  Local Notation digits := (tuple Z (length limb_widths)).

  Definition carry_full_3_opt_cps_sig
             {T} (f : list Z -> T)
             (us : list Z)
    : { d : T | length us = length limb_widths
                 -> d = f (carry_full (carry_full (carry_full us))) }.
  Proof.
    eexists.
    transitivity (carry_full_opt_cps c_ (carry_full_opt_cps c_ (carry_full_opt_cps c_ f)) us).
    Focus 2. {
      rewrite !carry_full_opt_cps_correct; repeat (autorewrite with distr_length; rewrite ?length_carry_full; auto).
    }
    Unfocus.
    reflexivity.
  Defined.

  Definition carry_full_3_opt_cps {T} (f : list Z -> T) (us : list Z) : T
    := Eval cbv [proj1_sig carry_full_3_opt_cps_sig] in proj1_sig (carry_full_3_opt_cps_sig f us).

  Definition carry_full_3_opt_cps_correct {T} (f : list Z -> T) us
    : length us = length limb_widths
      -> carry_full_3_opt_cps f us = f (carry_full (carry_full (carry_full us)))
    := proj2_sig (carry_full_3_opt_cps_sig f us).

  Definition conditional_subtract_modulus_opt_sig (f : list Z) (cond : bool) :
    { g | g = conditional_subtract_modulus f cond}.
  Proof.
    eexists.
    cbv [conditional_subtract_modulus].
    match goal with |- appcontext[if cond then ?a else ?b] =>
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (if cond then a else b) in RHS) with ?RHSf _ => RHSf end in
    change (LHS = Let_In (if cond then a else b) RHSf) end.
    cbv [map2 map].
    change @max_ones with max_ones_opt.
    reflexivity.
  Defined.

  Definition conditional_subtract_modulus_opt f cond : list Z
    := Eval cbv [proj1_sig conditional_subtract_modulus_opt_sig] in proj1_sig (conditional_subtract_modulus_opt_sig f cond).

  Definition conditional_subtract_modulus_opt_correct f cond
    : conditional_subtract_modulus_opt f cond = conditional_subtract_modulus f cond
    := Eval cbv [proj2_sig conditional_subtract_modulus_opt_sig] in proj2_sig (conditional_subtract_modulus_opt_sig f cond).

  Definition freeze_opt_sig (us : list Z) :
    { b : list Z | length us = length limb_widths
                   -> b = ModularBaseSystemList.freeze us }.
  Proof.
    eexists.
    cbv [ModularBaseSystemList.freeze].
    rewrite <-conditional_subtract_modulus_opt_correct.
    intros.
    let LHS := match goal with |- ?LHS = ?RHS => LHS end in
    let RHS := match goal with |- ?LHS = ?RHS => RHS end in
    let RHSf := match (eval pattern (carry_full (carry_full (carry_full us))) in RHS) with ?RHSf _ => RHSf end in
    rewrite <-carry_full_3_opt_cps_correct with (f := RHSf) by auto.
    cbv beta iota delta [ge_modulus ge_modulus'].
    change length with length_opt.
    change nth_default with @nth_default_opt.
    change @Pow2Base.base_from_limb_widths with base_from_limb_widths_opt.
    change minus with minus_opt.
    reflexivity.
  Defined.

  Definition freeze_opt (us : list Z) : list Z
    := Eval cbv beta iota delta [proj1_sig freeze_opt_sig] in proj1_sig (freeze_opt_sig us).

  Definition freeze_opt_correct us
    : length us = length limb_widths
      -> freeze_opt us = ModularBaseSystemList.freeze us
    := proj2_sig (freeze_opt_sig us).

End Canonicalization.

Section SquareRoots.
  Context `{prm : PseudoMersenneBaseParams}.
  Context {cc : CarryChain limb_widths}.
  Local Notation digits := (tuple Z (length limb_widths)).
          (* allows caller to precompute k and c *)
  Context (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_)
          (one_ : digits) (one_subst : one = one_).

  (* TODO : where should this lemma go? Alternatively, is there a standard-library
     tactic/lemma for this? *)
  Lemma if_equiv : forall {A} (eqA : A -> A -> Prop) (x0 x1 : bool) y0 y1 z0 z1,
    x0 = x1 -> eqA y0 y1 -> eqA z0 z1 ->
    eqA (if x0 then y0 else z0) (if x1 then y1 else z1).
  Proof.
    intros; repeat break_if; congruence.
  Qed.

  Section SquareRoot3mod4.
  Context {ec : ExponentiationChain (modulus / 4 + 1)}.

  Definition sqrt_3mod4_opt_sig (us : digits) :
    { vs : digits | eq vs (sqrt_3mod4 chain chain_correct us)}.
  Proof.
    eexists; cbv [sqrt_3mod4].
    apply @pow_opt_correct; eassumption.
  Defined.

  Definition sqrt_3mod4_opt us := Eval cbv [proj1_sig sqrt_3mod4_opt_sig] in
    proj1_sig (sqrt_3mod4_opt_sig us).

  Definition sqrt_3mod4_opt_correct us
    : eq (sqrt_3mod4_opt us) (sqrt_3mod4 chain chain_correct us)
    := Eval cbv [proj2_sig sqrt_3mod4_opt_sig] in proj2_sig (sqrt_3mod4_opt_sig us).

  End SquareRoot3mod4.

  Import Morphisms.
  Global Instance eqb_Proper : Proper (eq ==> eq ==> Logic.eq) ModularBaseSystem.eqb. Admitted.

  Section SquareRoot5mod8.
  Context {ec : ExponentiationChain (modulus / 8 + 1)}.
  Context (sqrt_m1 : digits) (sqrt_m1_correct : rep (mul sqrt_m1 sqrt_m1) (F.opp 1%F)).

  Definition sqrt_5mod8_opt_sig (us : digits) :
    { vs : digits |
      eq vs (sqrt_5mod8 (carry_mul_opt k_ c_) (pow_opt k_ c_ one_) chain chain_correct sqrt_m1 us)}.
  Proof.
    eexists; cbv [sqrt_5mod8].
    let LHS := match goal with |- eq ?LHS ?RHS => LHS end in
    let RHS := match goal with |- eq ?LHS ?RHS => RHS end in
    let RHSf := match (eval pattern (pow_opt k_ c_ one_ us chain) in RHS) with ?RHSf _ => RHSf end in
    change (eq LHS (Let_In (pow_opt k_ c_ one_ us chain) RHSf)).
    reflexivity.
  Defined.

  Definition sqrt_5mod8_opt us := Eval cbv [proj1_sig sqrt_5mod8_opt_sig] in
    proj1_sig (sqrt_5mod8_opt_sig us).

  Definition sqrt_5mod8_opt_correct us
    : eq (sqrt_5mod8_opt us) (ModularBaseSystem.sqrt_5mod8 _ _ chain chain_correct sqrt_m1 us)
    := Eval cbv [proj2_sig sqrt_5mod8_opt_sig] in proj2_sig (sqrt_5mod8_opt_sig us).

  End SquareRoot5mod8.

End SquareRoots.
