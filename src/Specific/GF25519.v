Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystem Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.QArith.QArith Coq.QArith.Qround.
Require Import Crypto.Tactics.VerdiTactics.
Close Scope Q.

Ltac twoIndices i j base :=
    intros;
    assert (In i (seq 0 (length base))) by nth_tac;
    assert (In j (seq 0 (length base))) by nth_tac;
    repeat match goal with [ x := _ |- _ ] => subst x end;
    simpl in *; repeat break_or_hyp; try omega; vm_compute; reflexivity.

Module Base25Point5_10limbs <: BaseCoefs.
  Local Open Scope Z_scope.
  Definition log_base := Eval compute in map (fun i => (Qceiling (Z_of_nat i *255 # 10))) (seq 0 10).
  Definition base := map (fun x => 2 ^ x) log_base.

  Lemma base_positive : forall b, In b base -> b > 0.
  Proof.
    compute; intuition; subst; intuition.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    auto.
  Qed.

  Lemma base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    twoIndices i j base.
  Qed.
End Base25Point5_10limbs.

Module Modulus25519 <: PrimeModulus.
  Local Open Scope Z_scope.
  Definition modulus : Z := 2^255 - 19.
  Lemma prime_modulus : prime modulus. Admitted.
End Modulus25519.

Module F25519Base25Point5Params <: PseudoMersenneBaseParams Base25Point5_10limbs Modulus25519.
  Import Base25Point5_10limbs.
  Import Modulus25519.
  Local Open Scope Z_scope.
  (* TODO: do we actually want B and M "up there" in the type parameters? I was
  * imagining writing something like "Paramter Module M : Modulus". *)

  Definition k := 255.
  Definition c := 19.
  Lemma modulus_pseudomersenne :
    modulus = 2^k - c.
  Proof.
    auto.
  Qed.

  Lemma base_matches_modulus :
    forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat).
  Proof.
    twoIndices i j base.
  Qed.

  Lemma base_succ : forall i, ((S i) < length base)%nat ->
    let b := nth_default 0 base in
    b (S i) mod b i = 0.
  Proof.
    intros; twoIndices i (S i) base.
  Qed.

  Lemma base_tail_matches_modulus:
    2^k mod nth_default 0 base (pred (length base)) = 0.
  Proof.
    auto.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1.
  Proof.
    auto.
  Qed.

  Lemma k_nonneg : 0 <= k.
  Proof.
    rewrite Zle_is_le_bool; auto.
  Qed.

  Lemma base_range : forall i, 0 <= nth_default 0 log_base i <= k.
  Proof.
    intros i.
    destruct (lt_dec i (length log_base)) as [H|H].
    { repeat (destruct i as [|i]; [cbv; intuition; discriminate|simpl in H; try omega]). }
    { rewrite nth_default_eq, nth_overflow by omega. cbv. intuition; discriminate. }
  Qed.

  Lemma base_monotonic: forall i : nat, (i < pred (length log_base))%nat ->
      (0 <= nth_default 0 log_base i <= nth_default 0 log_base (S i)).
  Proof.
  intros i H.
  repeat (destruct i; [cbv; intuition; congruence|]); 
      contradict H; cbv; firstorder.
  Qed.      
End F25519Base25Point5Params.

Module F25519Base25Point5 := PseudoMersenneBase Base25Point5_10limbs Modulus25519 F25519Base25Point5Params.

Section F25519Base25Point5Formula.
  Import F25519Base25Point5 Base25Point5_10limbs F25519Base25Point5 F25519Base25Point5Params.

Definition Z_add_opt := Eval compute in Z.add.
Definition Z_sub_opt := Eval compute in Z.sub.
Definition Z_mul_opt := Eval compute in Z.mul.
Definition Z_div_opt := Eval compute in Z.div.
Definition Z_pow_opt := Eval compute in Z.pow.

Definition nth_default_opt {A} := Eval compute in @nth_default A.
Definition map_opt {A B} := Eval compute in @map A B.

Ltac opt_step :=
  match goal with
  | [ |- _ = match ?e with nil => _ | _ => _ end :> ?T ]
    => refine (_ : match e with nil => _ | _ => _ end = _);
       destruct e
  end.

Definition E_mul_bi'_step
           (mul_bi' : nat -> E.digits -> list Z)
           (i : nat) (vsr : E.digits)
  : list Z
  := match vsr with
     | [] => []
     | v :: vsr' => (v * E.crosscoef i (length vsr'))%Z :: mul_bi' i vsr'
     end.

Definition E_mul_bi'_opt_step_sig
           (mul_bi' : nat -> E.digits -> list Z)
           (i : nat) (vsr : E.digits)
  : { l : list Z | l = E_mul_bi'_step mul_bi' i vsr }.
Proof.
  eexists.
  cbv [E_mul_bi'_step].
  opt_step.
  { reflexivity. }
  { cbv [E.crosscoef EC.base Base25Point5_10limbs.base].
    change Z.div with Z_div_opt.
    change Z.pow with Z_pow_opt.
    change Z.mul with Z_mul_opt at 2 3 4 5.
    change @nth_default with @nth_default_opt.
    change @map with @map_opt.
    reflexivity. }
Defined.

Definition E_mul_bi'_opt_step
           (mul_bi' : nat -> E.digits -> list Z)
           (i : nat) (vsr : E.digits)
  : list Z
  := Eval cbv [proj1_sig E_mul_bi'_opt_step_sig] in
      proj1_sig (E_mul_bi'_opt_step_sig mul_bi' i vsr).

Fixpoint E_mul_bi'_opt
         (i : nat) (vsr : E.digits) {struct vsr}
  : list Z
  := E_mul_bi'_opt_step E_mul_bi'_opt i vsr.

Definition E_mul_bi'_opt_correct
           (i : nat) (vsr : E.digits)
  : E_mul_bi'_opt i vsr = E.mul_bi' i vsr.
Proof.
  revert i; induction vsr as [|vsr vsrs IHvsr]; intros.
  { reflexivity. }
  { simpl E.mul_bi'.
    rewrite <- IHvsr; clear IHvsr.
    unfold E_mul_bi'_opt, E_mul_bi'_opt_step.
    apply f_equal2; [ | reflexivity ].
    cbv [E.crosscoef EC.base Base25Point5_10limbs.base].
    change Z.div with Z_div_opt.
    change Z.pow with Z_pow_opt.
    change Z.mul with Z_mul_opt at 2.
    change @nth_default with @nth_default_opt.
    change @map with @map_opt.
    reflexivity. }
Qed.

Definition E_mul'_step
           (mul' : E.digits -> E.digits -> E.digits)
           (usr vs : E.digits)
  : E.digits
  := match usr with
     | [] => []
     | u :: usr' => E.add (E.mul_each u (E.mul_bi (length usr') vs)) (mul' usr' vs)
     end.

Definition E_mul'_opt_step_sig
           (mul' : E.digits -> E.digits -> E.digits)
           (usr vs : E.digits)
  : { d : E.digits | d = E_mul'_step mul' usr vs }.
Proof.
  eexists.
  cbv [E_mul'_step].
  match goal with
  | [ |- _ = match ?e with nil => _ | _ => _ end :> ?T ]
    => refine (_ : match e with nil => _ | _ => _ end = _);
         destruct e
  end.
  { reflexivity. }
  { cbv [E.mul_each E.mul_bi].
    rewrite <- E_mul_bi'_opt_correct.
    reflexivity. }
Defined.

Definition E_mul'_opt_step
           (mul' : E.digits -> E.digits -> E.digits)
           (usr vs : E.digits)
  : E.digits
  := Eval cbv [proj1_sig E_mul'_opt_step_sig] in proj1_sig (E_mul'_opt_step_sig mul' usr vs).

Fixpoint E_mul'_opt
         (usr vs : E.digits)
  : E.digits
  := E_mul'_opt_step E_mul'_opt usr vs.

Definition E_mul'_opt_correct
         (usr vs : E.digits)
  : E_mul'_opt usr vs = E.mul' usr vs.
Proof.
  revert vs; induction usr as [|usr usrs IHusr]; intros.
  { reflexivity. }
  { simpl.
    rewrite <- IHusr; clear IHusr.
    apply f_equal2; [ | reflexivity ].
    cbv [E.mul_each E.mul_bi].
    rewrite <- E_mul_bi'_opt_correct.
    reflexivity. }
Qed.

Definition mul_opt_sig (us vs : T) : { b : B.digits | b = mul us vs }.
Proof.
  eexists.
  cbv [mul E.mul E.mul_each E.mul_bi E.mul_bi' E.zeros EC.base reduce].
  rewrite <- E_mul'_opt_correct.
  reflexivity.
Defined.

Definition mul_opt (us vs : T) : B.digits
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

Definition log_cap_opt_sig
           (i : nat)
  : { z : Z | i < length (Base25Point5_10limbs.log_base) -> (2^z)%Z = cap i }.
Proof.
  eexists.
  cbv [cap Base25Point5_10limbs.base].
  intros.
  rewrite map_length in *.
  erewrite map_nth_default; [|assumption].
  instantiate (2 := 0%Z).
  (** For the division of maps of (2 ^ _) over lists, replace it with 2 ^ (_ - _) *)
  
  lazymatch goal with
  | [ |- _ = (if eq_nat_dec ?a ?b then (2^?x/2^?y)%Z else (nth_default 0 (map (fun x => (2^x)%Z) ?ls) ?si / 2^?d)%Z)  ]
    => transitivity (2^if eq_nat_dec a b then (x-y)%Z else nth_default 0 ls si - d)%Z;
        [ apply f_equal | break_if ]
  end.
  
  Focus 2.
  apply Z.pow_sub_r; [clear;firstorder|apply base_range].
  Focus 2.
  erewrite map_nth_default by (omega); instantiate (1 := 0%Z).
  rewrite <- Z.pow_sub_r; [ reflexivity | .. ].
    { clear; abstract firstorder. }
    { apply base_monotonic. omega. }
  Unfocus.
  rewrite <-beq_nat_eq_nat_dec.
  change Z.sub with Z_sub_opt.
  change @nth_default with @nth_default_opt.
  change @map with @map_opt.
  reflexivity.
Defined.

Definition log_cap_opt (i : nat)
  := Eval cbv [proj1_sig log_cap_opt_sig] in proj1_sig (log_cap_opt_sig i).

Definition log_cap_opt_correct (i : nat)
  : i < length Base25Point5_10limbs.log_base -> (2^log_cap_opt i = cap i)%Z
  := proj2_sig (log_cap_opt_sig i).

Definition carry_opt_sig
           (i : nat) (b : B.digits)
  : { d : B.digits | i < length Base25Point5_10limbs.log_base -> d = carry i b }.
Proof.
  eexists ; intros.
  cbv [carry].
  rewrite <- pull_app_if_sumbool.
  cbv beta delta [carry_and_reduce carry_simple add_to_nth Base25Point5_10limbs.base].
  rewrite map_length.
  repeat lazymatch goal with
         | [ |- context[cap ?i] ]
           => replace (cap i) with (2^log_cap_opt i)%Z by (apply log_cap_opt_correct; assumption)
  end.
  lazymatch goal with
  | [ |- _ = (if ?br then ?c else ?d) ]
    => let x := fresh "x" in let y := fresh "y" in evar (x:B.digits); evar (y:B.digits); transitivity (if br then x else y); subst x; subst y
  end.
  Focus 2.
  cbv zeta.
  break_if;
    rewrite <- Z.land_ones, <- Z.shiftr_div_pow2 by (
        pose proof (base_range i); pose proof (base_monotonic i);
        change @nth_default with @nth_default_opt in *;
        cbv beta delta [log_cap_opt]; rewrite beq_nat_eq_nat_dec; break_if; change Z_sub_opt with Z.sub; omega);
    reflexivity.
  change @nth_default with @nth_default_opt.
  change @map with @map_opt.
  rewrite <- @beq_nat_eq_nat_dec.
  reflexivity.
Defined.

Definition carry_opt i b
  := Eval cbv beta iota delta [proj1_sig carry_opt_sig] in proj1_sig (carry_opt_sig i b).

Definition carry_opt_correct i b : i < length Base25Point5_10limbs.log_base -> carry_opt i b = carry i b := proj2_sig (carry_opt_sig i b).

Definition carry_sequence_opt_sig (is : list nat) (us : B.digits)
  : { b : B.digits | (forall i, In i is -> i < length Base25Point5_10limbs.log_base) -> b = carry_sequence is us }.
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
  : (forall i, In i is -> i < length Base25Point5_10limbs.log_base) -> carry_sequence_opt is us = carry_sequence is us
  := proj2_sig (carry_sequence_opt_sig is us).

Definition Let_In {A P} (x : A) (f : forall y : A, P y)
  := let y := x in f y.

Definition carry_opt_cps_sig
           {T}
           (i : nat)
           (f : B.digits -> T)
           (b : B.digits)
  : { d : T |  i < length Base25Point5_10limbs.log_base -> d = f (carry i b) }.
Proof.
  eexists. intros H.
  rewrite <- carry_opt_correct by assumption.
  cbv beta iota delta [carry_opt].
  (* TODO: how to match the goal here? Alternatively, rewrite under let binders in carry_opt_sig and remove cbv zeta and restore original match from jgross's commit *)
  lazymatch goal with [ |- ?LHS = _ ] =>
  change (LHS = Let_In (nth_default_opt 0%Z b i) (fun di => (f (if beq_nat i (pred (length Base25Point5_10limbs.log_base))
      then
       set_nth 0
         (c *
          Z.shiftr (di) (log_cap_opt i) +
          nth_default_opt 0
            (set_nth i (Z.land di (Z.ones (log_cap_opt i)))
               b) 0)%Z
         (set_nth i (Z.land (nth_default_opt 0%Z b i) (Z.ones (log_cap_opt i))) b)
      else
       set_nth (S i)
         (Z.shiftr (di) (log_cap_opt i) +
          nth_default_opt 0
            (set_nth i (Z.land (di) (Z.ones (log_cap_opt i)))
               b) (S i))%Z
         (set_nth i (Z.land (nth_default_opt 0%Z b i) (Z.ones (log_cap_opt i))) b)))))
  end.
  reflexivity.
Defined.

Definition carry_opt_cps {T} i f b
  := Eval cbv beta iota delta [proj1_sig carry_opt_cps_sig] in proj1_sig (@carry_opt_cps_sig T i f b).

Definition carry_opt_cps_correct {T} i f b :
  i < length Base25Point5_10limbs.log_base ->
  @carry_opt_cps T i f b = f (carry i b)
  := proj2_sig (carry_opt_cps_sig i f b).

Definition carry_sequence_opt_cps_sig (is : list nat) (us : B.digits)
  : { b : B.digits | (forall i, In i is -> i < length Base25Point5_10limbs.log_base) -> b = carry_sequence is us }.
Proof.
  eexists.
  cbv [carry_sequence].
  transitivity (fold_right carry_opt_cps id (List.rev is) us).
  Focus 2.
  { 
    assert (forall i, In i (rev is) -> i < length Base25Point5_10limbs.log_base) as Hr. {
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
  : (forall i, In i is -> i < length Base25Point5_10limbs.log_base) -> carry_sequence_opt_cps is us = carry_sequence is us
  := proj2_sig (carry_sequence_opt_cps_sig is us).

Lemma mul_opt_rep:
  forall (u v : T) (x y : F Modulus25519.modulus), rep u x -> rep v y -> rep (mul_opt u v) (x * y)%F.
Proof.
  intros.
  rewrite mul_opt_correct.
  auto using mul_rep.
Qed.

Lemma carry_sequence_opt_cps_rep
     : forall (is : list nat) (us : list Z) (x : F Modulus25519.modulus),
       (forall i : nat, In i is -> i < length Base25Point5_10limbs.base) ->
       length us = length Base25Point5_10limbs.base ->
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
  := Eval cbv [B.add
    E.add E.mul E.mul' E.mul_bi E.mul_bi' E.mul_each E.zeros EC.base E_mul'_opt
    E_mul'_opt_step E_mul_bi'_opt E_mul_bi'_opt_step
    List.app List.rev Z_div_opt Z_mul_opt Z_pow_opt
    Z_sub_opt app beq_nat log_cap_opt carry_opt_cps carry_sequence_opt_cps error firstn
    fold_left fold_right id length map map_opt mul mul_opt nth_default nth_default_opt
    nth_error plus pred reduce rev seq set_nth skipn value base] in 
    carry_sequence_opt_cps is (mul_opt us vs).

Lemma carry_mul_opt_correct
  : forall (is : list nat) (us vs : list Z) (x  y: F Modulus25519.modulus),
    rep us x -> rep vs y ->
    (forall i : nat, In i is -> i < length Base25Point5_10limbs.base) ->
    length (mul_opt us vs) = length base ->
    rep (carry_mul_opt is us vs) (x*y)%F.
Proof.
  intros is us vs x y; intros.
  change (carry_mul_opt _ _ _) with (carry_sequence_opt_cps is (mul_opt us vs)).
  apply carry_sequence_opt_cps_rep, mul_opt_rep; auto.
Qed.
  

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

    cbv [log_base map k c carry_mul_opt] in Hfg.
    cbv beta iota delta [Let_In] in Hfg.
    rewrite ?Z.mul_0_l, ?Z.mul_0_r, ?Z.mul_1_l, ?Z.mul_1_r, ?Z.add_0_l, ?Z.add_0_r in Hfg.
    rewrite ?Z.mul_assoc, ?Z.add_assoc in Hfg.
    exact Hfg.
  Time Defined.
End F25519Base25Point5Formula.

Extraction "/tmp/test.ml" GF25519Base25Point5_mul_reduce_formula.
(* It's easy enough to use extraction to get the proper nice-looking formula.
 * More Ltac acrobatics will be needed to get out that formula for further use in Coq.
 * The easiest fix will be to make the proof script above fully automated,
 * using [abstract] to contain the proof part. *)
