Require Import Galois GaloisTheory Galois.BaseSystem Galois.ModularBaseSystem.
Require Import List Util.ListUtil.
Import ListNotations.
Require Import ZArith.ZArith Zpower ZArith Znumtheory.
Require Import QArith.QArith QArith.Qround.
Require Import VerdiTactics.
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

Module Modulus25519 <: Modulus.
  Local Open Scope Z_scope.
  Definition two_255_19 := two_p 255 - 19.
  Lemma two_255_19_prime : prime two_255_19. Admitted.
  Definition prime25519 := exist _ two_255_19 two_255_19_prime.
  Definition modulus := prime25519.
End Modulus25519.

Module GF25519Base25Point5Params <: PseudoMersenneBaseParams Base25Point5_10limbs Modulus25519.
  Import Base25Point5_10limbs.
  Import Modulus25519.
  Local Open Scope Z_scope.
  (* TODO: do we actually want B and M "up there" in the type parameters? I was
  * imagining writing something like "Paramter Module M : Modulus". *)

  Definition k := 255.
  Definition c := 19.
  Lemma modulus_pseudomersenne :
    primeToZ modulus = 2^k - c.
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
End GF25519Base25Point5Params.

Module GF25519Base25Point5 := GFPseudoMersenneBase Base25Point5_10limbs Modulus25519 GF25519Base25Point5Params.

Ltac expand_list ls :=
  let Hlen := fresh "Hlen" in
  match goal with [H: ls = ?lsdef |- _ ] =>
      assert (Hlen:length ls=length lsdef) by (f_equal; exact H)
  end;
  simpl in Hlen;
  repeat progress (let n:=fresh ls in destruct ls as [|n ]; try solve [revert Hlen; clear; discriminate]);
  clear Hlen.

Ltac letify r :=
  match goal with
  | [ H' : r = _ |- _ ] =>
    match goal with
    | [ H : ?x = ?e |- _ ] =>
      is_var x;
      match goal with (* only letify equations that appear nowhere other than r *)
      | _ => clear H H' x; fail 1
      | _ => fail 2
      end || idtac;
      pattern x in H';
      match type of H' with
      | (fun z => r = @?e' z) x =>
        let H'' := fresh "H" in
        assert (H'' : r = let x := e in e' x) by
          (* congruence is slower for every subsequent letify *)
          (rewrite H'; subst x; reflexivity);
        clear H'; subst x; rename H'' into H'; cbv beta in H'
      end
    end
  end.

Ltac expand_list_equalities := repeat match goal with
  | [H: (?x::?xs = ?y::?ys) |- _ ] =>
      let eq_head := fresh "Heq" x in
      assert (x = y) as eq_head by (eauto using cons_eq_head);
      assert (xs = ys) by (eauto using cons_eq_tail);
      clear H
  | [H:?x = ?x|-_] => clear H
end.

Section GF25519Base25Point5Formula.
  Import GF25519Base25Point5.
  Import Field.

  Hint Rewrite
    Z.mul_0_l
    Z.mul_0_r
    Z.mul_1_l
    Z.mul_1_r
    Z.add_0_l
    Z.add_0_r
    Z.add_assoc
    Z.mul_assoc
    : Z_identities.

  Ltac deriveModularMultiplicationWithCarries carryscript :=
  let h := fresh "h" in
  let fg := fresh "fg" in
  let Hfg := fresh "Hfg" in
  intros;
  repeat match goal with
  | [ Hf: rep ?fs ?f, Hg: rep ?gs ?g |- rep _ ?ret ] =>
      remember (carry_sequence carryscript (mul fs gs)) as fg;
      assert (rep fg ret) as Hfg; [subst fg; apply carry_sequence_rep, mul_rep; eauto|]
  | [ H: In ?x carryscript |- ?x < ?bound ] => abstract (revert H; clear; cbv; intros; repeat break_or_hyp; intuition)
  | [ Heqfg: fg = carry_sequence _ (mul _ _) |- rep _ ?ret ] =>
      (* expand bignum multiplication *)
      cbv [plus
        seq rev app length map fold_right fold_left skipn firstn nth_default nth_error value error
        mul reduce B.add Base25Point5_10limbs.base GF25519Base25Point5Params.c
        E.add E.mul E.mul' E.mul_each E.mul_bi E.mul_bi' E.zeros EC.base] in Heqfg;
      repeat match goal with [H:context[E.crosscoef ?a ?b] |- _ ] => (* do this early for speed *)
          let c := fresh "c" in set (c := E.crosscoef a b) in H; compute in c; subst c end;
      autorewrite with Z_identities in Heqfg;
      (* speparate out carries *)
      match type of Heqfg with fg = carry_sequence _ ?hdef => remember hdef as h end;
      (* one equation per limb *)
      expand_list h; expand_list_equalities;
      (* expand carry *)
      cbv [GF25519Base25Point5.carry_sequence fold_right rev app] in Heqfg
  | [H1: ?a = ?b, H2: ?b = ?c |- _ ] => subst a
  | [Hfg: context[carry ?i (?x::?xs)] |- _ ] => (* simplify carry *)
      let cr := fresh "cr" in
      remember (carry i (x::xs)) as cr in Hfg;
      match goal with [ Heq : cr = ?crdef |- _ ] =>
          (* is there any simpler way to do this? *)
          cbv [carry carry_simple carry_and_reduce] in Heq;
          simpl eq_nat_dec in Heq; cbv iota beta in Heq;
          cbv [set_nth nth_default nth_error value add_to_nth] in Heq;
          expand_list cr; expand_list_equalities
      end
  | [H: context[cap ?i] |- _ ] => let c := fresh "c" in remember (cap i) as c in H;
      match goal with [Heqc: c = cap i |- _ ] =>
          (* is there any simpler way to do this? *)
          unfold cap, Base25Point5_10limbs.base in Heqc;
          simpl eq_nat_dec in Heqc;
          cbv [nth_default nth_error value error] in Heqc;
          simpl map in Heqc;
          cbv [GF25519Base25Point5Params.k] in Heqc
      end;
      subst c;
      repeat rewrite Zdiv_1_r in H;
      repeat rewrite two_power_pos_equiv in H;
      repeat rewrite <- Z.pow_sub_r in H by (abstract (clear; firstorder));
      repeat rewrite <- Z.land_ones in H by (abstract (apply Z.leb_le; reflexivity));
      repeat rewrite <- Z.shiftr_div_pow2 in H by (abstract (apply Z.leb_le; reflexivity));
      simpl Z.sub in H;
      unfold  GF25519Base25Point5Params.c in H
  | [H: context[Z.ones ?l] |- _ ] =>
          (* postponing this to the main loop makes the autorewrite slow *)
        let c := fresh "c" in set (c := Z.ones l) in H; compute in c; subst c
  | [ |- _ ] => abstract (solve [auto])
  | [ |- _ ] => progress intros
  end.

  Lemma GF25519Base25Point5_mul_reduce_formula :
    forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
      g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
      {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                        -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                        -> rep ls (f*g)%GF}.
  Proof.

    eexists.

    let carryscript := constr:(rev [0;1;2;3;4;5;6;7;8;9;0]) in
    let h := fresh "h" in
  let fg := fresh "fg" in
  let Hfg := fresh "Hfg" in
  intros;
  lazymatch goal with
  | [ Hf: rep ?fs ?f, Hg: rep ?gs ?g |- rep _ ?ret ] =>
      remember (carry_sequence carryscript (mul fs gs)) as fg;
      assert (rep fg ret) as Hfg; [subst fg; apply carry_sequence_rep, mul_rep; eauto|]
  end.
    intros.
  let carryscript := constr:(rev [0;1;2;3;4;5;6;7;8;9;0]) in
  match goal with
  | [ H: In ?x carryscript |- ?x < ?bound ] => abstract (revert H; clear; cbv; intros; repeat break_or_hyp; intuition)
end.
Print mul.
Print E.mul'.
Print E.crosscoef.
Print E.mul'.

Print E.mul_bi'.

Ltac opt_step :=
  match goal with
  | [ |- _ = match ?e with nil => _ | _ => _ end :> ?T ]
    => refine (_ : match e with nil => _ | _ => _ end = _);
       destruct e
  end.

Definition nth_default_opt {A} := Eval compute in @nth_default A.

Definition E_mul_bi'_step
           (mul_bi' : nat -> E.digits -> list Z)
           (i : nat) (vsr : E.digits)
  : list Z
  := match vsr with
     | [] => []
     | v :: vsr' => (v * E.crosscoef i (length vsr'))%Z :: mul_bi' i vsr'
     end.

Definition Z_div_opt := Eval compute in Z.div.
Definition Z_mul_opt := Eval compute in Z.mul.

Definition E_mul_bi'_opt_step_sig
           (mul_bi' : nat -> E.digits -> list Z)
           (i : nat) (vsr : E.digits)
  : { l : list Z | l = E_mul_bi'_step mul_bi' i vsr }.
Proof.
  eexists.
  cbv [E_mul_bi'_step].
  opt_step.
  { reflexivity. }
  { cbv [E.crosscoef].
    change Z.div with Z_div_opt.
    change Z.mul with Z_mul_opt at 2.
    let c := (eval compute in EC.base) in
    change EC.base with c.
    change @nth_default with @nth_default_opt.
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
  { simpl.
    rewrite <- IHvsr; clear IHvsr.
    apply f_equal2; [ | reflexivity ].
    cbv [E.crosscoef].
    change Z_div_opt with Z.div.
    change Z_mul_opt with Z.mul.
    let c := (eval compute in EC.base) in
    change EC.base with c.
    change @nth_default with @nth_default_opt.
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

rewrite <- mul_opt_correct in Heqfg.
Set Printing Depth 1000000.
let carryscript := constr:(rev [0;1;2;3;4;5;6;7;8;9;0]) in
match goal with
| [ Heqfg: fg = carry_sequence _ (mul_opt _ _) |- rep _ ?ret ] =>
      (* expand bignum multiplication *)
      cbv [plus
        seq rev app length map fold_right fold_left skipn firstn nth_default nth_error value error
        mul reduce B.add Base25Point5_10limbs.base GF25519Base25Point5Params.c
        E.add E.mul E.mul' E.mul_each E.mul_bi E.mul_bi' E.zeros EC.base mul_opt length E_mul'_opt E_mul'_opt_step plus E_mul_bi'_opt E_mul_bi'_opt_step nth_default_opt Z_div_opt Z_mul_opt Base25Point5_10limbs.log_base] in Heqfg;
        autorewrite with Z_identities in Heqfg
end.


Print carry.

Lemma beq_nat_eq_nat_dec {R} (x y : nat) (a b : R)
  : (if EqNat.beq_nat x y then a else b) = (if eq_nat_dec x y then a else b).
Proof.
  destruct (eq_nat_dec x y) as [H|H];
    [ rewrite (proj2 (@beq_nat_true_iff _ _) H); reflexivity
    | rewrite (proj2 (@beq_nat_false_iff _ _) H); reflexivity ].
Qed.

Lemma pull_app_if_bool {A B} (b : bool) (f g : A -> B) (x : A)
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

Definition Z_pow_opt := Eval compute in Z.pow.
Definition Z_sub_opt := Eval compute in Z.sub.
Definition map_opt {A B} := Eval compute in @map A B.
Definition cap_opt_sig
           (i : nat)
  : { z : Z | z = cap i }.
Proof.
  eexists.
  cbv [cap Base25Point5_10limbs.base].
  rewrite <- beq_nat_eq_nat_dec.
Local Arguments beq_nat !_ !_.
Local Arguments Compare_dec.leb !_ !_.
Lemma beq_to_leb_specialized i ls k
  : (if beq_nat i (pred (length ls))
     then k / nth_default 0 ls i
     else nth_default 0 ls (S i) / nth_default 0 ls i)%Z
    = (if Compare_dec.leb (pred (length ls)) i
       then k / nth_default 0 ls i
       else nth_default 0 ls (S i) / nth_default 0 ls i)%Z.
Proof.
  destruct ls as [|? ls]; destruct i as [|i]; simpl; try reflexivity.
  { unfold nth_default; simpl.
    rewrite !Zdiv_0_r; reflexivity. }
  { destruct ls as [|? ls]; simpl; reflexivity. }
  { destruct (beq_nat (S i) (length ls)) eqn:H';
    [ apply beq_nat_true in H'
    | apply beq_nat_false in H' ].
    { destruct ls; simpl in *; [ congruence | inversion H'; clear H'; subst ].
      rewrite leb_correct by reflexivity.
      reflexivity. }
    { generalize dependent (S i); clear i; intro i; intros;
      destruct (Compare_dec.leb (length ls) i) eqn:H;
        [ apply leb_complete in H
        | apply leb_complete_conv in H ].
      { rewrite !nth_default_out_of_bounds by (simpl; omega).
        rewrite !Zdiv_0_r; reflexivity. }
      { reflexivity. } } }
Qed.
  rewrite beq_to_leb_specialized.
  match goal with
  | [ |- _ = if _ then ?f (nth_default ?d ?ls ?i) else _ ]
    => rewrite <- (map_nth_default_always f i d ls)
  end.
  rewrite map_map, Zdiv_0_r.
  (** For the division of maps of (2 ^ _) over lists, replace it with 2 ^ (_ - _) *)
  lazymatch goal with
  | [ |- _ = (if Compare_dec.leb ?a ?b then ?c else (nth_default 0 (map (fun x => 2 ^ x) ?ls) ?i / nth_default 0 (map (fun x => 2 ^ x) ?ls) ?j)%Z) ]
    => transitivity (if Compare_dec.leb a b then c else 2 ^ (nth_default 0 ls i - nth_default 0 ls j))%Z;
         [
         | let H := fresh in
           destruct (Compare_dec.leb a b) eqn:H;
           [ apply leb_complete in H; reflexivity
           | apply leb_complete_conv in H;
             rewrite map_length in H;
             let f := constr:(fun x => 2 ^ x)%Z in
             rewrite (map_nth_default _ _ f i 0%Z 0%Z ls), (map_nth_default _ _ f j 0%Z 0%Z ls) by omega ] ]
  end.
  Focus 2.
  { (** TODO: need sortedness for side conditions *)
    rewrite <- Z.pow_sub_r; [ reflexivity | .. ].
    { clear; abstract firstorder. }
    { unfold Base25Point5_10limbs.log_base, nth_default;
      do 11 (simpl; try (clear i; clear; abstract firstorder);
             try destruct i as [|i]; simpl);
      try (clear; abstract firstorder).
      simpl in *.
      exfalso; omega. } }
  Unfocus.
  (** To do this with the other case, you'd need to know that every element of log_base <= GF25519Base25Point5Params.k, or something like that.  Here's the starter code: *)
  lazymatch goal with
  | [ |- _ = (if Compare_dec.leb ?a ?b then nth_default 0%Z (map ?f ?ls) ?i else ?c) ]
    => etransitivity;
         [
         | refine (_ : (if Compare_dec.leb a b then nth_default 0%Z (map _ ls) i else c) = _);
           instantiate (* propogate evar instantiations between goals *);
           let H := fresh in
           destruct (Compare_dec.leb a b) eqn:H;
           [ apply leb_complete in H; apply f_equal2; [ | reflexivity ]
           | reflexivity ] ]
  end.
  Focus 2.
  { (** Here, you'd use a lemma that says [(forall x, In x ls -> f x = g x) -> map f ls = map g ls] *)
    (** Then, you'd rewrite with [Z.pow_sub_r] using the condition mentioned above.  For now, we just use [change] and [reflexivity] instead. *)
    change Z.div with Z_div_opt.
    change Z.pow with Z_pow_opt.
    reflexivity. }
  Unfocus.
  change Z.pow with Z_pow_opt at 1.
  change Z.sub with Z_sub_opt.
  change @nth_default with @nth_default_opt.
  change @map with @map_opt.
  reflexivity.
Defined.

Definition cap_opt (i : nat)
  := Eval cbv [proj1_sig cap_opt_sig] in proj1_sig (cap_opt_sig i).

Definition cap_opt_correct (i : nat)
  : cap_opt i = cap i
  := proj2_sig (cap_opt_sig i).

Definition carry_opt_sig
           (i : nat) (b : B.digits)
  : { d : B.digits | d = carry i b }.
Proof.
  eexists.
  cbv [carry].
  rewrite <- beq_nat_eq_nat_dec, <- pull_app_if_bool.
  cbv beta delta [carry_and_reduce carry_simple add_to_nth Base25Point5_10limbs.base].
  change @nth_default with @nth_default_opt.
  change @map with @map_opt.
  repeat match goal with
         | [ |- context[cap ?i] ]
           => replace (cap i) with (cap_opt i) by (rewrite cap_opt_correct; reflexivity)
         end.
  reflexivity.
Defined.

Definition carry_opt i b
  := Eval cbv beta iota delta [proj1_sig carry_opt_sig] in proj1_sig (carry_opt_sig i b).

Definition carry_opt_correct i b : carry_opt i b = carry i b := proj2_sig (carry_opt_sig i b).

Definition carry_sequence_opt_sig (is : list nat) (us : B.digits)
  : { b : B.digits | b = carry_sequence is us }.
Proof.
  eexists.
  cbv [carry_sequence].
  transitivity (fold_right carry_opt us is).
  Focus 2.
  { induction is; [ reflexivity | ].
    simpl; rewrite IHis, carry_opt_correct.
    reflexivity. }
  Unfocus.
  reflexivity.
Defined.

Definition carry_sequence_opt is us := Eval cbv [proj1_sig carry_sequence_opt_sig] in
                                        proj1_sig (carry_sequence_opt_sig is us).

Definition carry_sequence_opt_correct is us
  : carry_sequence_opt is us = carry_sequence is us
  := proj2_sig (carry_sequence_opt_sig is us).

Definition Let_In {A P} (x : A) (f : forall y : A, P y)
  := let y := x in f y.

Definition carry_opt_cps_sig
           {T}
           (i : nat)
           (f : B.digits -> T)
           (b : B.digits)
  : { d : T | d = f (carry i b) }.
Proof.
  eexists.
  rewrite <- carry_opt_correct.
  cbv beta iota delta [carry_opt].
  lazymatch goal with
  | [ |- ?LHS = ?f (if ?b
                    then let di := ?dv in @?A di
                    else let di := ?dv in @?B di) ]
    => change (LHS = Let_In dv (fun di => f (if b then A di else B di)))
  end.
  cbv beta.
  reflexivity.
Defined.

Definition carry_opt_cps {T} i f b
  := Eval cbv beta iota delta [proj1_sig carry_opt_cps_sig] in proj1_sig (@carry_opt_cps_sig T i f b).

Definition carry_opt_cps_correct {T} i f b : @carry_opt_cps T i f b = f (carry i b)
  := proj2_sig (carry_opt_cps_sig i f b).

Definition carry_sequence_opt_cps_sig (is : list nat) (us : B.digits)
  : { b : B.digits | b = carry_sequence is us }.
Proof.
  eexists.
  cbv [carry_sequence].
  transitivity (fold_right carry_opt_cps id (List.rev is) us).
  Focus 2.
  { remember (rev is) as ris eqn:Heq.
    rewrite <- (rev_involutive is), <- Heq.
    clear Heq is.
    rewrite fold_left_rev_right.
    revert us; induction ris; [ reflexivity | ]; intros.
    { simpl.
      rewrite <- IHris; clear IHris.
      rewrite carry_opt_cps_correct.
      reflexivity. } }
  Unfocus.
  reflexivity.
Defined.

Definition carry_sequence_opt_cps is us := Eval cbv [proj1_sig carry_sequence_opt_cps_sig] in
                                            proj1_sig (carry_sequence_opt_cps_sig is us).

Definition carry_sequence_opt_cps_correct is us
  : carry_sequence_opt_cps is us = carry_sequence is us
  := proj2_sig (carry_sequence_opt_cps_sig is us).
(*match goal with [ Heqfg: fg = carry_sequence _ ?hdef |- _ ] => remember hdef as h end;
  (* one equation per limb *)
  expand_list h; expand_list_equalities.
      cbv [GF25519Base25Point5.carry_sequence fold_right rev app] in Heqfg.*)

rewrite <- carry_sequence_opt_cps_correct in Heqfg.
cbv beta iota delta [carry_sequence_opt_cps fold_right List.rev List.app] in Heqfg.
cbv [carry_opt_cps Compare_dec.leb beq_nat pred length Base25Point5_10limbs.log_base nth_default_opt set_nth cap_opt Z_div_opt Z_div_opt Z_pow_opt Z_sub_opt GF25519Base25Point5Params.k GF25519Base25Point5Params.c id map_opt] in Heqfg.


(*** HERE *)

unfold carry_opt_cps at 1 in Heqfg.
cbv [Compare_dec.leb beq_nat pred length Base25Point5_10limbs.log_base nth_default_opt set_nth Z_div_opt Z_div_opt Z_pow_opt Z_sub_opt GF25519Base25Point5Params.k GF25519Base25Point5Params.c id map_opt] in Heqfg.
cbv [cap_opt pred length Base25Point5_10limbs.log_base map_opt nth_default_opt] in Heqfg.
cbv beta iota delta [Let_In] in Heqfg.


      subst c;
      repeat rewrite Zdiv_1_r in H;
      repeat rewrite two_power_pos_equiv in H;
      repeat rewrite <- Z.pow_sub_r in H by (abstract (clear; firstorder));
      repeat rewrite <- Z.land_ones in H by (abstract (apply Z.leb_le; reflexivity));
      repeat rewrite <- Z.shiftr_div_pow2 in H by (abstract (apply Z.leb_le; reflexivity));
      simpl Z.sub in H;
      unfold  GF25519Base25Point5Params.c in H
  | [H: context[Z.ones ?l] |- _ ] =>
          (* postponing this to the main loop makes the autorewrite slow *)
        let c := fresh "c" in set (c := Z.ones l) in H; compute in c; subst c
  | [ |- _ ] => abstract (solve [auto])
  | [ |- _ ] => progress intros


unfold carry_opt_cps at 1 in Heqfg.
cbv [beq_nat pred length Base25Point5_10limbs.base nth_default_opt set_nth cap_opt Z_div_opt Z_pow_opt GF25519Base25Point5Params.k] in Heqfg.

Print cap.
  Print set_nth.
  Print carry_and_reduce.
  cbv [Base25Point5_10limbs.base].
  Focus 2.
  SearchAbout beq_nat.



  SearchAbout EqNat.beq_nat.




Print carry_sequence.

Print fold_right.
Definition fold_right_let {A B} (f : B -> A -> A) (a0 : A)
  := fix fold_right_let (l : list B) : A :=
       match l with
       | nil => a0
       | b :: t => Let_In b (fun b' => f b (fold_right_let t))
       end.

Definition fold_right_let_correct
  : @fold_right_let = @fold_right.
Proof.
  cbv [fold_right_let fold_right Let_In].
  reflexivity.
Qed.

cbv [carry_sequence fold_right] in Heqfg.
Print carry.

rewrite <- fold_right_let_correct in Heqfg.
cbv [fold_right_let] in Heqfg.
cbv beta delta [Let_In] in Heqfg.
change @fold_right with @fold_right_let in Heqfg.

Definition carry_sequence_opt_sig
           (is : list nat) (us : B.digits)
  : { b : B.digits | b = carry_sequence is us }.
Proof.
  eexists.
  cbv [carry_sequence].


Print Z.mul.
Print Z.div.
      repeat match goal with [H:context[E.crosscoef ?a ?b] |- _ ] => (* do this early for speed *)
          let c := fresh "c" in set (c := E.crosscoef a b) in H; compute in c; subst c end;
      autorewrite with Z_identities in Heqfg;
      (* speparate out carries *)
      match type of Heqfg with fg = carry_sequence _ ?hdef => remember hdef as h end;
      (* one equation per limb *)
      expand_list h; expand_list_equalities;
      (* expand carry *)
      cbv [GF25519Base25Point5.carry_sequence fold_right rev app] in Heqfg
  end.



    Time deriveModularMultiplicationWithCarries (rev [0;1;2;3;4;5;6;7;8;9;0]).
    (* pretty-print: sh -c "tr -d '\n' | tr 'Z' '\n' | tr -d \% | sed 's:\s\s*\*\s\s*:\*:g' | column -o' ' -t" *)

    Time repeat letify fg; subst fg; eauto.
  Time Defined.
End GF25519Base25Point5Formula.

Extraction "/tmp/test.ml" GF25519Base25Point5_mul_reduce_formula.
(* It's easy enough to use extraction to get the proper nice-looking formula.
 * More Ltac acrobatics will be needed to get out that formula for further use in Coq.
 * The easiest fix will be to make the proof script above fully automated,
 * using [abstract] to contain the proof part. *)
