Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseRep.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.BaseSystem Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.QArith.QArith Coq.QArith.Qround.
Require Import Crypto.Tactics.VerdiTactics.
Close Scope Q.
Local Open Scope Z.

Definition modulus : Z := 2^255 - 19.
Lemma prime_modulus : prime modulus. Admitted.

(* Begin proofs to construct PseudoMersenneBaseParams instance. *)

Definition limb_widths : list Z := [26;25;26;25;26;25;26;25;26;25].

(* TODO : move to ListUtil *)
Lemma fold_right_and_True_forall_In_iff : forall {T} (l : list T) (P : T -> Prop),
  (forall x, In x l -> P x) <-> fold_right and True (map P l).
Proof.
  induction l; intros; simpl; try tauto.
  rewrite <- IHl.
  intuition (subst; auto).
Qed.

Ltac brute_force_indices := intros; unfold sum_firstn, limb_widths; simpl in *;
  repeat match goal with
  | _ => progress simpl in *
  | _ => reflexivity
  | [H : (S _ < S _)%nat |- _ ] => apply lt_S_n in H
  | [H : (?x + _ < _)%nat |- _ ] => is_var x; destruct x
  | [H : (?x < _)%nat |- _ ] => is_var x; destruct x
  | _ => omega
  end.

Instance params25519 : PseudoMersenneBaseParams modulus := { limb_widths := limb_widths }.
Proof.
  + abstract (apply fold_right_and_True_forall_In_iff; simpl; repeat (split; [omega |]); auto).
  + abstract (unfold limb_widths; congruence).
  + abstract brute_force_indices.
  + abstract apply prime_modulus.
  + abstract brute_force_indices.
Defined.

Ltac twoIndices i j base :=
    intros;
    assert (In i (seq 0 (length base))) by nth_tac;
    assert (In j (seq 0 (length base))) by nth_tac;
    repeat match goal with [ x := _ |- _ ] => subst x end;
    simpl in *; repeat break_or_hyp; try omega; vm_compute; reflexivity.

Definition Z_add_opt := Eval compute in Z.add.
Definition Z_sub_opt := Eval compute in Z.sub.
Definition Z_mul_opt := Eval compute in Z.mul.
Definition Z_div_opt := Eval compute in Z.div.
Definition Z_pow_opt := Eval compute in Z.pow.

Definition nth_default_opt {A} := Eval compute in @nth_default A.
Definition set_nth_opt {A} := Eval compute in @set_nth A.
Definition map_opt {A B} := Eval compute in @map A B.
Definition base_from_limb_widths_opt := Eval compute in base_from_limb_widths.
Definition k_opt := Eval compute in k.
Definition c_opt := Eval compute in c.


Ltac opt_step :=
  match goal with
  | [ |- _ = match ?e with nil => _ | _ => _ end :> ?T ]
    => refine (_ : match e with nil => _ | _ => _ end = _);
       destruct e
  end.

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

Definition Z_shiftl_by n a := Z.shiftl a n.
Definition Z_shiftl_by_opt := Eval compute in Z_shiftl_by.

Lemma Z_shiftl_by_mul_pow2 : forall n a, 0 <= n -> Z.mul (2 ^ n) a = Z_shiftl_by n a.
Proof.
  intros.
  unfold Z_shiftl_by.
  rewrite Z.shiftl_mul_pow2 by assumption.
  apply Z.mul_comm.
Qed.

Lemma map_shiftl : forall n l, 0 <= n -> map (Z.mul (2 ^ n)) l = map (Z_shiftl_by n) l.
Proof.
  intros; induction l; auto using Z_shiftl_by_mul_pow2.
  simpl.
  rewrite IHl.
  f_equal.
  apply Z_shiftl_by_mul_pow2.
  assumption.
Qed.

Definition mul_opt_sig (us vs : T) : { b : digits | b = mul us vs }.
Proof.
  eexists.
  cbv [BaseSystem.mul mul mul_each mul_bi mul_bi' zeros ext_base reduce].
  rewrite <- mul'_opt_correct.
  cbv [base PseudoMersenneBaseParams.limb_widths].
  rewrite map_shiftl by apply k_nonneg.
  change k with k_opt.
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

Lemma beq_nat_eq_nat_dec {R} (x y : nat) (a b : R)
  : (if EqNat.beq_nat x y then a else b) = (if eq_nat_dec x y then a else b).
Proof.
  destruct (eq_nat_dec x y) as [H|H];
    [ rewrite (proj2 (@beq_nat_true_iff _ _) H); reflexivity
    | rewrite (proj2 (@beq_nat_false_iff _ _) H); reflexivity ].
Qed.

Lemma pull_app_if_sumbool {A B X Y} (b : sumbool X Y) (f g : A -> B) (x : A)
  : (if b then f x else g x) = (if b then f else g) x.
Proof.
  destruct b; reflexivity.
Qed.

Lemma map_nth_default_always {A B} (f : A -> B) (n : nat) (x : A) (l : list A)
  : nth_default (f x) (map f l) n = f (nth_default x l n).
Proof.
  revert n; induction l; simpl; intro n; destruct n; [ try reflexivity.. ].
  nth_tac.
Qed.

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
  change c with c_opt.
  change @set_nth with @set_nth_opt.
  change @map with @map_opt.
  rewrite <- @beq_nat_eq_nat_dec.
  change base_from_limb_widths with base_from_limb_widths_opt.
  reflexivity.
Defined.


Definition carry_opt i b
  := Eval cbv beta iota delta [proj1_sig carry_opt_sig] in proj1_sig (carry_opt_sig i b).

Definition carry_opt_correct i b : (i < length base)%nat -> carry_opt i b = carry i b := proj2_sig (carry_opt_sig i b).

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
    - apply H; apply in_eq.
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

Definition Let_In {A P} (x : A) (f : forall y : A, P y)
  := let y := x in f y.

Definition carry_opt_cps_sig
           {T}
           (i : nat)
           (f : digits -> T)
           (b : digits)
  : { d : T |  (i < length base)%nat -> d = f (carry i b) }.
Proof.
  eexists. intros H.
  rewrite <- carry_opt_correct by assumption.
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

Lemma mul_opt_rep:
  forall (u v : T) (x y : F modulus), rep u x -> rep v y -> rep (mul_opt u v) (x * y)%F.
Proof.
  intros.
  rewrite mul_opt_correct.
  auto using mul_rep.
Qed.

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

Definition carry_mul_opt 
           (is : list nat)
           (us vs : list Z)
           : list Z
  := carry_sequence_opt_cps is (mul_opt us vs).



Lemma carry_mul_opt_correct
  : forall (is : list nat) (us vs : list Z) (x  y: F modulus),
    rep us x -> rep vs y ->
    (forall i : nat, In i is -> i < length base)%nat ->
    length (mul_opt us vs) = length base ->
    rep (carry_mul_opt is us vs) (x*y)%F.
Proof.
  intros is us vs x y; intros.
  change (carry_mul_opt _ _ _) with (carry_sequence_opt_cps is (mul_opt us vs)).
  apply carry_sequence_opt_cps_rep, mul_opt_rep; auto.
Qed.


Local Open Scope nat_scope.
Lemma GF25519Base25Point5_mul_reduce_formula :
  forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
    {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                      -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                      -> rep ls (f*g)%F}.
Proof.
  eexists.
  intros f g Hf Hg.

  pose proof (carry_mul_opt_correct [0;9;8;7;6;5;4;3;2;1;0]_ _ _ _ Hf Hg) as Hfg.
  forward Hfg; [abstract (clear; cbv; intros; repeat break_or_hyp; intuition)|].
  specialize (Hfg H); clear H.
  forward Hfg; [exact eq_refl|].
  specialize (Hfg H); clear H.

  set (p := params25519) in Hfg at 1.
  change (params25519) with p at 1.
  set (fg := (f * g)%F) in Hfg |- * .

  Opaque Z.shiftl
  Pos.iter
  Z.div2
  Pos.div2
  Pos.div2_up
  Pos.succ
  Z.land
  Z.of_N
  Pos.land
  N.ldiff
  Pos.pred_N
  Pos.pred_double
  Z.opp Z.mul Pos.mul Let_In digits Z.add Pos.add Z.pos_sub.

  Time let T := match type of Hfg with @rep _ _ ?T _ => T end in
  let T' := (eval cbv [
     carry_mul_opt
     mul_opt mul'_opt firstn skipn map_opt
     limb_widths base_from_limb_widths_opt 
     k_opt Z_shiftl_by_opt
     length rev app c zeros
     mul'_opt_step mul_bi'_opt add
     mul_bi'_opt_step
     nth_default_opt nth_error plus
     Z_div_opt Z_mul_opt
     params25519


     carry_sequence_opt_cps carry_opt_cps fold_right
     List.app List.rev length
     base limb_widths base_from_limb_widths_opt
     nth_default_opt set_nth_opt pred beq_nat id c_opt
     Z.shiftr
   ] in T) in
  replace T with T' in Hfg.  
  Time 2:abstract ( clear;
    compute; reflexivity).
  change (Z.shiftl 1 26 + -1)%Z with 67108863%Z in Hfg.
  change (Z.shiftl 1 25 + -1)%Z with 33554431%Z in Hfg.
  repeat rewrite ?Z.mul_1_r, ?Z.add_0_l, ?Z.add_assoc, ?Z.mul_assoc in Hfg.

  exact Hfg.
Time Defined.

Extraction "/tmp/test.ml" GF25519Base25Point5_mul_reduce_formula.
(* It's easy enough to use extraction to get the proper nice-looking formula.
 * More Ltac acrobatics will be needed to get out that formula for further use in Coq.
 * The easiest fix will be to make the proof script above fully automated,
 * using [abstract] to contain the proof part. *)

