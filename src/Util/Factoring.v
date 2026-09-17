From Corelib Require Import Program.Wf.
Require Import Crypto.Util.Pos.
From Stdlib Require Import List Sorted Permutation Lists.Finite. Import ListNotations.
From Stdlib Require Import Zdivisibility ZArith Lia.
Require Import Crypto.Util.ListUtil.Repeat.
Require Import Crypto.Util.ListUtil.Sorted.
Require Import Crypto.Util.ListUtil.Permutation.
Require Import Crypto.Util.ZUtil.Coprime.
Require Import Crypto.Util.ZUtil.Divide.
Require Import Crypto.Util.ZUtil.Pos.
Require Import Crypto.Util.NUtil.Pos.
#[local] Open Scope positive_scope.
#[local] Coercion Z.pos : positive >-> Z.
#[local] Coercion N.pos : positive >-> N.
#[local] Coercion Z.of_N : N >-> Z.

#[local] Lemma fst_pair [A B] a b : fst (@pair A B a b) = a. Proof. reflexivity. Qed.
#[local] Lemma snd_pair [A B] a b : snd (@pair A B a b) = b. Proof. reflexivity. Qed.

(* ** [val p n] finds largest k s.t. [p^k] divides [n] *)

#[local] Open Scope N_scope.

#[local] Definition val_subterm p n (val : forall m, Pos.lt m n -> N) : N :=
  match N.pos_div_eucl n p with
  | (N.pos m, 0) => if Pos.lt_dec m n then N.succ (val m ltac:(trivial)) else 0
  |  _ => 0
  end.
Definition val (p : positive) : positive -> N :=
  Fix (Acc_intro_generator 64 Pos.lt_wf) _ (val_subterm p).

Lemma val_step p n : val p n = ltac:(
  let y := eval cbv beta delta [val_subterm] in (val_subterm p n (fun y _ => val p y)) in
  exact y).
Proof.
  cbv [val val_subterm].
  rewrite Init.Wf.Fix_eq; [reflexivity|]; intros.
  repeat match goal with |- context[match ?x with _ => _ end] => destruct x end;
    repeat (eapply H || f_equal || trivial).
Qed.

Lemma val_1_r p : val p 1 = 0.
Proof. repeat (case p as []; trivial). Qed.

Lemma val_1_l n : val 1 n = 0.
Proof.
  rewrite val_step, N.pos_div_eucl_pos_as_div_mod, N.div_1_r, N.mod_1_r.
  case Pos.lt_dec; lia.
Qed.

Lemma val_0_iff' (p n : positive) : val p n = 0 <-> (p = xH \/ n mod p <> 0).
Proof.
  rewrite val_step, N.pos_div_eucl_pos_as_div_mod.
  repeat match goal with |- context[match ?x with _ => _ end] => destruct x eqn:? end;
  zify; Z.to_euclidean_division_equations; nia.
Qed.

Lemma val_0_iff p n (H : p <> xH) : val p n = 0 <-> n mod p <> 0.
Proof. rewrite val_0_iff'; lia. Qed.

Lemma val_0_iff_divide p n (H : p <> xH) : val p n = 0 <-> ~ (p | n).
Proof. rewrite val_0_iff, N.Lcm0.mod_divide; trivial; reflexivity. Qed.

Lemma val_mul p n (H : p <> xH) : val p (Pos.mul p n) = N.succ (val p n).
Proof.
  rewrite val_step, N.pos_div_eucl_pos_as_div_mod.
  rewrite N.pos_mul, N.mul_comm, N.div_mul, N.Div0.mod_mul by lia.
  case Pos.lt_dec; nia.
Qed.

Lemma val_mul_pow (p k n : positive) (H : p <> xH) : val p (p ^ k * n) = k + val p n.
Proof.
  induction k using Pos.peano_ind;
    rewrite ?Pos.pow_1_r, ?Pos.pow_succ_r, <-?Pos.mul_assoc, ?val_mul; lia.
Qed.

Lemma divide_val (p n : positive) : (p ^ val p n | n).
Proof.
  induction n using (well_founded_induction Pos.lt_wf); rewrite val_step; cbv [id].
  assert ((p ^ 0 | n)). { rewrite N.pow_0_r. apply N.divide_1_l. }
  repeat match goal with |- context[match ?x with _ => _ end] => destruct x eqn:? end; trivial.
  epose proof N.pos_div_eucl_spec _ _ as E. rewrite Heqp0 in E; subst; rewrite E.
  rewrite N.pow_succ_r, ?N.add_0_r, N.mul_comm; try eapply N.mul_divide_cancel_r; eauto; lia.
Qed.

Lemma divide'_val (p n : positive) : ( Pos.of_N (p ^ val p n) | n)%positive.
Proof.
  case (divide_val p n) as [q Hq]. exists (Pos.of_N q).
  enough (q * p ^ val p n = Pos.of_N q * Pos.of_N (p ^ val p n))%N by nia.
  rewrite ?N.pos_of_N_pos; lia.
Qed.

Lemma le_val_iff k p n (H : p <> xH) : k <= val p n <-> ( p^k | n ).
Proof.
  split.
  { case (divide_val p n) as [q ->]. exists (q*p^(val p n - k)).
    rewrite <-N.mul_assoc, <-N.pow_add_r, N.sub_add; trivial. }
  { inversion 1 as [[|q] ?]; case k as [|k] in *; try lia.
    assert (n = q * p ^ k)%positive as -> by lia.
    rewrite Pos.mul_comm, val_mul_pow; try lia. }
Qed.

Lemma powdivide_as_val (p : positive) k (n : positive) :
  (p^k | n) <-> (p = xH \/ k <= val p n).
Proof.
  case (Pos.eq_dec p xH) as [->|];
    rewrite ?N.pow_1_l, ?le_val_iff by trivial; intuition apply N.divide_1_l.
Qed.

Lemma val_iff k p n (H : p <> xH) : val p n = k <-> (p^k|n) /\ ~(p^N.succ k|n).
Proof. rewrite !powdivide_as_val; lia. Qed.

Lemma divide_as_val (p : positive) (n : positive) :
  (p | n) <-> (p = xH \/ 1 <= val p n).
Proof. rewrite <-(N.pow_1_r p). rewrite powdivide_as_val; lia. Qed.

Lemma ndivide_val (p n : positive) (H : p <> xH) k (Hk : val p n < k) : ~ ( p ^ k | n).
Proof. rewrite <-le_val_iff; try lia. Qed.

Lemma ndivide_val_succ (p n : positive) (H : p <> xH) : ~ ( p * p ^ val p n | n).
Proof. rewrite <-N.pow_succ_r, <-le_val_iff; try lia. Qed.

Lemma ndivide_val_div (p n : positive) (H : p <> xH) : ~ ( p | n / p ^ val p n ).
Proof.
  intros [x X]; case (divide_val p n) as [q Hq].
  rewrite Hq, N.div_mul in X by lia; rewrite X in Hq.
  eapply (ndivide_val_succ p n); trivial; exists x; lia.
Qed.

(** * Factorization into prime powers *)

#[local] Open Scope positive_scope.

Definition ppfactor_lt := MR Pos.lt (uncurry Pos.sub).

Lemma ppfactor_wf : well_founded ppfactor_lt.
Proof. apply measure_wf, Pos.lt_wf. Qed.

Definition ppfactor_subterm (n_i : positive * positive) (ppfactor : forall m_j, ppfactor_lt m_j n_i -> list (positive * positive))
  : list (positive * positive).
Proof.
simple refine (
  let n := fst n_i in let i := Pos.succ (snd n_i) in
  if Pos.lt_dec n (i*i) then if Pos.eqb 1 n then [] else [(n, 1)] else
  let k := val i n in
  let j := if N.odd i then Pos.succ i else i in
  if N.eq_dec 0 k    then ppfactor (n, j) _
  else (i, Pos.of_N k) :: ppfactor (Pos.of_N (n/i^k), j) _);
clear ppfactor; abstract (
 cbv [ppfactor_lt MR uncurry]; subst n; destruct n_i as [n i']; cbn [fst snd] in *; try solve
 [ subst i; case N.odd in *; lia
 | case (divide'_val i n) as [q Eq]; case N.odd in *; zify; Z.div_mod_to_equations; nia]).
Defined.

Definition ppfactor_rec : positive * positive -> list (positive * positive) :=
  Fix (Acc_intro_generator 64 ppfactor_wf) _ ppfactor_subterm.

Lemma ppfactor_rec_step p : ppfactor_rec p = ltac:(
  let y := eval cbv beta delta [ppfactor_subterm] in (ppfactor_subterm p (fun y _ => ppfactor_rec y)) in
  exact y).
Proof.
  cbv [ppfactor_rec ppfactor_subterm].
  rewrite Init.Wf.Fix_eq; [reflexivity|]; intros.
  repeat match goal with |- context[match ?x with _ => _ end] => destruct x end;
    repeat (eapply H || f_equal || trivial).
Defined.

Definition ppfactor p := ppfactor_rec (p, 1).

(*
Compute ppfactor 24.
Compute ppfactor 1311.
Compute ppfactor (2^16-1).
Compute ppfactor (2^16+1).
Time Compute ppfactor (2^32-1). (* 0.003s *)
Time Compute ppfactor (2^32+1). (* 0.02s *)
Time Compute ppfactor (2^31+1). (* 0.3s *)
Time Compute ppfactor (2^31-1). (* 0.6s *)
Time Compute ppfactor (2^46-1). (* 3.2s *)
*)

Lemma fold_right_nil [A B] (f : B -> A -> A) a : fold_right f a nil = a.
Proof. reflexivity. Qed.

Lemma fold_right_cons [A B] (f : B -> A -> A) a x xs :
  fold_right f a (x::xs) = f x (fold_right f a xs). Proof. reflexivity. Qed.

Local Notation Π := (fold_right Pos.mul 1).

Lemma prod_app ps qs : Π (ps ++ qs) = Π ps * Π qs.
Proof. induction ps; cbn [fold_right app]; rewrite ?IHps, ?Pos.mul_assoc, ?Pos.mul_1_l; trivial. Qed.

Lemma prod_concat ps : Π (concat ps) = Π (map Π ps).
Proof. induction ps; cbn [fold_right concat map]; rewrite ?prod_app; congruence. Qed.

Lemma prod_repeat q c : Π (repeat q (Pos.to_nat c)) = q ^ c.
Proof.
  induction c using Pos.peano_ind; trivial.
  rewrite ?Pos2Nat.inj_succ, ?Pos.pow_succ_r; cbn [repeat fold_right]; congruence.
Qed.

Lemma divide_in_prod ps : Forall (fun p => (p | Π ps)) ps.
Proof.
  induction ps; cbn [fold_right concat map]; constructor; trivial.
  { apply Pos.divide_mul_l. exists 1. lia. }
  { eapply Forall_impl; eauto; cbv beta; intros q [y ->]; exists (a*y); lia. }
Qed.

Lemma prod_ppfactor_rec p i : Π (map (uncurry Pos.pow) (ppfactor_rec (p, i))) = p.
Proof.
  change p with (fst (p, i)) at 2;
  induction (p, i) as [[p' i']IH] using (well_founded_induction ppfactor_wf);
    clear i p; rename p' into p; rewrite ppfactor_rec_step; cbn [fst snd].
  set (Pos.succ i') as i.
  set (if N.odd _ then _ else _) as j; assert (i' < j) by (case N.odd in *; subst i; lia).
  repeat match goal with |- context[match ?x with _ => _ end] => destruct x eqn:? end;
  repeat (cbn [uncurry (* map -- Qed timeout *)]; rewrite ?fold_right_nil, ?fold_right_cons, ?map_cons);
    rewrite ?IH; cbn [fst snd];
    try rapply ppfactor_subterm_subproof; try rapply ppfactor_subterm_subproof0; trivial;
    try apply Pos.eqb_eq in Heqb; try lia.
  case (divide_val i p) as [q Hq].
  rewrite Hq, N.div_mul, Pos.mul_comm by lia.
  enough (Pos.of_N q * i ^ Pos.of_N (val i p) = p)%N by lia;
    rewrite ?N.pos_of_N_pos; lia.
Qed.

Lemma prod_ppfactor p : Π (map (uncurry Pos.pow) (ppfactor p)) = p.
Proof. apply prod_ppfactor_rec. Qed.

Lemma Private_ppfactor_rec_correct
  (n i : positive) (ps := map fst (ppfactor_rec (n, i))) :
  (forall d, 1 < d -> (d | fst (n, i)) -> Pos.succ (snd (n, i)) <= d)%Z ->
  StronglySorted Pos.lt ps /\ Forall (fun p => Z.prime (Z.pos p) /\ ( snd (n, i) < p <= fst (n, i))) ps.
Proof.
  induction (n, i) as [[n' i']IH] using (well_founded_induction ppfactor_wf);
    clear n i; rename n' into n; subst ps; rewrite ppfactor_rec_step; cbn [fst snd].
  intros I; case Pos.lt_dec as []. (* base case *)
  { case (Pos.eqb_spec 1 n) as []; repeat split; cbn [map fst];
      intuition eauto using SSorted_cons, SSorted_nil;
      try apply Forall_cons; try apply Forall_nil; split.
    { split; [lia|]; intros a?[b ?].
      pose proof I a ltac:(lia) ltac:(exists b; lia).
      pose proof I b ltac:(nia) ltac:(exists a; lia). nia. }
    { pose proof (I n ltac:(lia) ltac:(reflexivity)); lia. } }
  set (Pos.succ i') as i in *. (* bound variables *)
  set (if N.odd _ then _ else _) as j';
    assert (j' = i'+1 \/ j'=i'+2) by (case N.odd in *; subst i; lia).
  case (divide'_val i n) as [q Hq].
  set (val i n) as k in *.
  assert (q = Pos.of_N (n / i ^ k)). { zify; Z.div_mod_to_equations; nia. }
  assert (forall d, (1 < d)%Z -> (d | n) -> d <> i -> (Pos.succ j' <= d))%Z as I_.
  { intros a ? [b ab] ?. pose proof (I a ltac:(lia) ltac:(exists b; trivial)).
    case N.odd eqn:E; [|lia]. rewrite <-N.even_succ, N.even_spec in E.
    case E as [j]. enough (a <> Pos.succ i) by lia; intro.
    unshelve epose proof (I 2 _ ltac:(exists (b*j)%Z)); lia. }
  case N.eq_dec as []; rewrite ?map_cons.
  { case (IH (n, j') ltac:(try rapply ppfactor_subterm_subproof; trivial)) as (A&B);
      clear IH; cbn [fst snd] in *. (* recursive case withot division *)
    { intros; apply I_; trivial. (* invariant preserved: i wasn't a ppfactor *)
      intros ->; case (proj1 (val_0_iff_divide i n ltac:(lia)) ltac:(lia)).
      case H2 as [b ?];  exists (Z.to_N b); lia. }
    eapply conj, Forall_impl; eauto; intuition lia. }
  (* recursive case with division *) eassert (I' : _); try
    case (IH (Pos.of_N (n / i ^ k), j') ltac:(rapply ppfactor_subterm_subproof0; trivial) I') as (A&B);
      clear IH; rewrite ?fst_pair, ?snd_pair in * (* cbn -> Qed timeout *).
  { (* invariant restored: i is no longer a facter  *)
    intros ? ? Hb; apply I_; trivial; case Hb as [b]. { exists (b*i^k)%Z; nia. }
    intros->. subst k. apply (ndivide_val_succ i n); [|exists (Z.to_N b)];nia. }
  eassert (O : _ ); [|split; constructor; [trivial|exact O|split;[|nia]| ] ].
  { (* range of recursive ppfactors *) epose proof divide_in_prod _ as D;
    erewrite (prod_ppfactor_rec (Pos.of_N (n / i ^ k)) j'), Forall_map in D.
    eapply Forall_map in B. epose proof Forall_and B D as F; cbv beta in *.
    eapply Forall_map, Forall_impl, F; clear A D F; intros [f e] ([]&x&Hx);
      cbv [fst snd uncurry] in *.
    unshelve epose proof I f _ _; try nia.
    exists (Pos.of_N (i ^ k)*x*(f^Pos.pred_N e))%N.
    enough (f^e = f * f ^ Pos.pred_N e)%N by nia.
    replace (N.pos e) with (N.succ (N.pred e)) by lia.
    rewrite N.pow_succ_r'; f_equal; lia. }
  { (* found a ppfactor *) split; try lia.
    intros a ? [b]. unshelve epose proof I a _ ltac:(exists (q*a^(k-1)*b^k)%Z); try nia.
    enough (i ^ k = (a * a ^ (k - 1)) * b ^ k :> Z)%Z by lia.
    rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred, <-Z.pow_mul_l by lia; f_equal; lia. }
  { eapply Forall_impl, B; intuition nia. }
Qed.

Lemma Sorted_ppfactor n : Sorted Pos.lt (map fst (ppfactor n)).
Proof. eapply StronglySorted_Sorted, Private_ppfactor_rec_correct; cbn [fst snd]; lia. Qed.

Lemma NoDup_ppfactor n : NoDup (ppfactor n).
Proof.
  eapply NoDup_StronglySorted with (R:=fun a b=>fst a<fst b),
    Sorted_StronglySorted, Sorted_map, Sorted_ppfactor ; repeat intro; try lia.
Qed.

Local Notation prime := (fun p => Z.prime (Z.pos p)).

Lemma fst_ppfactor n : Forall (fun p => prime p /\ 2 <= p <= n) (map fst (ppfactor n)).
Proof. eapply Forall_impl, Private_ppfactor_rec_correct; cbn [fst snd]; intuition lia. Qed.

Lemma prime_ppfactor n : Forall prime (map fst (ppfactor n)).
Proof. eapply Forall_impl, fst_ppfactor; cbv beta; intuition idtac. Qed.

Lemma range_ppfactor n : Forall (fun p => 2 <= p <= n) (map fst (ppfactor n)).
Proof. eapply Forall_impl, fst_ppfactor; cbv beta; intuition idtac. Qed.

Lemma ppfactor_inj a b (H : ppfactor a = ppfactor b) : a = b.
Proof. rewrite <-(prod_ppfactor a), <-(prod_ppfactor b); congruence. Qed.

(** * Factorization into primes *)

Local Notation expand := (flat_map (fun '(p, k) => repeat p (Pos.to_nat k))).
Definition factor n := expand (ppfactor n).

#[local] Lemma prod_expand xs : Π (expand xs) = Π (map (uncurry Pos.pow) xs).
Proof.
  erewrite flat_map_concat_map, prod_concat, map_map, map_ext; trivial.
  intros []; apply prod_repeat.
Qed.

Lemma prod_factor n : Π (factor n) = n.
Proof. rewrite <-prod_ppfactor, <-prod_expand; trivial. Qed.

#[local] Lemma Forall_expand [A] (P : A -> Prop) xs :
  Forall P (expand xs) <-> Forall P (map fst xs).
Proof.
  rewrite flat_map_concat_map, Forall_concat, !Forall_map, !Forall_forall.
  split; intros H [] I; specialize (H _ I); cbn [fst] in *;
    eauto using Forall_repeat.
  destruct repeat eqn:? in H.
  { apply (f_equal (@length _)) in Heql; rewrite repeat_length in Heql;
     cbn [length] in Heql; lia. }
  eapply repeat_eq_cons in Heql; intuition subst. inversion_clear H; trivial.
Qed.

Lemma prime_factor n : Forall prime (factor n).
Proof. eapply Forall_expand, Forall_impl, prime_ppfactor; eauto. Qed.

Lemma range_factor n : Forall (fun p => 2 <= p <= n) (factor n).
Proof. eapply Forall_expand, Forall_impl, range_ppfactor; eauto. Qed.

Lemma Sorted_factor n : Sorted Pos.le (factor n).
Proof.
  pose proof Sorted_ppfactor n as H.
  eapply Sorted_StronglySorted in H; try rapply Pos.lt_trans.
  cbv [factor]; set (ppfactor n) as pps in *; clearbody pps.
  induction pps as [|[p k]]; cbn [repeat flat_map]; trivial.
  inversion_clear H as [| x y Hsort Hlt  ].
  eapply StronglySorted_Sorted, StronglySorted_app; repeat split;
    try eapply Sorted_StronglySorted; try rapply Pos.le_trans;
    eauto using Sorted_repeat, Pos.le_refl.
  eapply Forall_forall; intros ? ->%repeat_spec.
  eapply Forall_forall; intros q [[] [H ->%repeat_spec]]%in_flat_map.
  eapply Forall_forall in Hlt; [|eapply in_map, H]; eauto using Pos.lt_le_incl.
Qed.

Lemma factor_inj a b (H : factor a = factor b) : a = b.
Proof. rewrite <-(prod_factor a), <-(prod_factor b); congruence. Qed.

(** Euler's totient function *)

Definition totientpp p e := Pos.pow_pred p e * Pos.pred p.
Definition totient n := Π (map (uncurry totientpp) (ppfactor n)).

(*
Compute totient 1.
Compute totient 9.
Compute totient 20.
Compute totient 80.
Compute totient 90.
Compute totient 352.
Time Compute totient (2^46-1).
*)

(** * Fundamental theorem of arithmetic *)

Lemma prime_product_1 ps : Forall prime ps -> Π ps = 1 -> ps = nil.
Proof.
  destruct 1; cbn; intuition idtac.
  eapply Z.prime_ge_2 in H.
  nia.
Qed.

Lemma prime_divisor_of_prime_product :
  forall p qs, prime p -> Forall prime qs -> (p | Π qs)%Z -> In p qs.
Proof.
  induction 2 as [|q qs]; cbn [fold_right]; intros.
  { apply Z.prime_ge_2 in H; apply Z.divide_1_r_abs in H0; lia. }
  rewrite Pos2Z.inj_mul in *.
  case (Pos.eq_dec p q) as [->|]. { eauto using in_eq. }
  eapply or_intror, IHForall, Z.gauss, Z.coprime_prime_prime; eauto; lia.
Qed.

Lemma prime_divisor_of_prime_power_product q pps (Hq : prime q)
  (Hp : Forall prime (map fst pps)) (Hd : (q | Π (map (uncurry Pos.pow) pps))%Z)
  : In q (map fst pps).
Proof.
  unshelve epose proof prime_divisor_of_prime_product q (expand pps) _ _ _ as H;
    rewrite ?prod_expand; try apply Forall_expand; trivial.
  rewrite in_flat_map in H; case H as ([p k]&?&->%repeat_spec).
  apply in_map_iff; exists (p, k); eauto.
Qed.

Lemma fundamental_theorem_of_arithmetic_Permutation' ps :
  Forall prime ps -> forall qs, Forall prime qs -> Π ps = Π qs -> Permutation ps qs.
Proof.
  induction 1 as [|p ps]; cbn [fold_right]; intros.
  { eapply prime_product_1 in H; subst; trivial; lia. }
  epose proof prime_divisor_of_prime_product p qs ltac:(trivial) ltac:(trivial) ltac:(exists(Π ps);lia).
  eapply in_split in H3; case H3 as (qs0&qs1&?); subst qs.
  eapply perm_trans, Permutation_middle; try apply perm_skip, IHForall.
  { eapply Permutation_Forall in H1; try (symmetry; eapply Permutation_middle);
     inversion_clear H1; trivial. }
  { pose proof Z.prime_ge_2 _ H.
    symmetry in H2; erewrite fold_right_Permutation in H2;
      try (symmetry; eapply Permutation_middle); cbn [fold_right] in *; nia. }
Qed.

Lemma fundamental_theorem_of_arithmetic_Permutation (a : positive) ps :
  Forall prime ps -> Π ps = a -> Permutation ps (factor a).
Proof.
  intros;eapply fundamental_theorem_of_arithmetic_Permutation';
    rewrite ?prod_factor; eauto using prime_factor.
Qed.

Lemma fundamental_theorem_of_arithmetic (a : positive) ps :
  Sorted Pos.le ps -> Forall prime ps -> Π ps = a -> ps = factor a.
Proof.
  intros; eapply (Sorted_Permutation_unique Pos.le);
    try eapply fundamental_theorem_of_arithmetic_Permutation;
    eauto using Sorted_factor; cbv [Relations_1.Transitive]; lia.
Qed.

Lemma factor_complete p n : prime p -> (p | n) -> In p (factor n).
Proof.
  intros Hp [n' Hq].
  unshelve epose proof fundamental_theorem_of_arithmetic_Permutation n (p::factor n') _ _;
    rewrite ?fold_right_cons, ?prod_factor; auto using prime_factor; try lia.
  eauto using Permutation_in, in_eq.
Qed.

Lemma factor_prime p (H : prime p) : factor p = [p].
Proof.
  symmetry; eapply fundamental_theorem_of_arithmetic;
    auto; apply Pos.mul_1_r.
Qed.

Lemma factor_prime_power p (H : prime p) k :
  factor (p^k) = repeat p (Pos.to_nat k).
Proof.
  symmetry; eapply fundamental_theorem_of_arithmetic;
    auto using Sorted_repeat, Forall_repeat, Pos.le_refl, prod_repeat.
Qed.

Lemma NoDup_ppfactor' n : NoDup (map (uncurry Pos.pow) (ppfactor n)).
Proof.
  eapply Injective_map_NoDup_in, NoDup_ppfactor.
  intros [p e] [q k]; cbn [uncurry]; intros A B E.
  eapply Forall_forall in A; try eapply Forall_map, prime_ppfactor.
  eapply Forall_forall in B; try eapply Forall_map, prime_ppfactor.
  eapply (f_equal factor) in E; rewrite 2factor_prime_power in E by trivial.
  eapply repeat_inj in E; intuition subst; f_equal; lia.
Qed.

Lemma factor_mul_Permutation a b : Permutation (factor (a*b)) (factor a ++ factor b).
Proof.
  rewrite <-(prod_factor a) at 1; rewrite <-(prod_factor b) at 1;
  specialize (prime_factor b); specialize (prime_factor a).
  intros. symmetry. eapply fundamental_theorem_of_arithmetic_Permutation.
  { eapply Forall_app; eauto. } { rewrite ?prod_app, ?prod_factor; trivial. }
Qed.

Lemma divide_factor n : Forall (fun d => (d | n)) (factor n).
Proof.
  rewrite <-(prod_factor n); rewrite prod_factor at 1.
    generalize (factor n) as xs; induction xs;
    rewrite ?fold_right_nil, ?fold_right_cons; constructor.
  { exists (Π xs). lia. }
  { eapply Forall_impl, IHxs; intros x [y ?]; exists (a*y); lia. }
Qed.

Lemma in_factor p n : In p (factor n) <-> prime p /\ (p | n).
Proof.
  pose proof proj1 (Forall_forall _ _) (prime_factor n).
  pose proof proj1 (Forall_forall _ _) (divide_factor n).
  intuition auto using factor_complete.
Qed.

Lemma disjoint_factor_coprime (a b : positive) (H : Pos.gcd a b = 1)
  p (Ha : In p (factor a)) (Hb : In p (factor b)) : False.
Proof.
  apply (f_equal Z.pos) in H; rewrite Pos2Z.inj_gcd in H.
  pose proof (proj1 (Forall_forall _ _) (range_factor _)) _ Ha; cbv beta in *.
  apply (proj1 (Forall_forall _ _) (divide_factor _)), Z.divide_Zpos in Ha.
  apply (proj1 (Forall_forall _ _) (divide_factor _)), Z.divide_Zpos in Hb.
  epose proof Z.gcd_greatest _ _ _ Ha Hb as D; rewrite H in *.
  apply Z.divide_1_r in D; lia.
Qed.

#[local] Opaque Z.gcd.

Lemma factor_ind (P : positive -> Prop)
  (init : P 1)
  (step : forall n p, P n -> prime p ->
    (forall q, prime q -> Z.divide q n -> q <= p) -> P (n * p))
  : forall n, P n.
Proof.
  intros n; revert step; revert init.
  rewrite <-(prod_factor n).
  specialize (Sorted_factor n); cbv zeta.
  specialize (prime_factor n); cbv zeta.
  specialize (range_factor n); cbv zeta.
  set (factor n) as ps; clearbody ps.
  induction ps as [|p ps] using rev_ind; cbn; trivial.
  rewrite prod_app; cbn [map fold_right]; rewrite Pos.mul_1_r.
  intros [A H']%Forall_app [B H]%Forall_app C ? ?; inversion_clear H.
  eapply Sorted_StronglySorted in C; try exact Pos.le_trans.
  eapply StronglySorted_app in C; case C as (?&C&?).
  eapply step; eauto; try eapply IHps; eauto using StronglySorted_Sorted.
  intros q ? ?%prime_divisor_of_prime_product; eauto.
  eapply Forall_forall in H; eauto. inversion_clear H; eauto.
Qed.

Lemma N_factor_ind (P : N -> Prop)
  (zero : P N0)
  (init : P (N.pos 1))
  (step : forall n p, P n -> prime p ->
    (forall q, prime q -> Z.divide q n -> q <= p) -> P (n * p)%N)
  : forall n, P n.
Proof.
  unshelve epose proof factor_ind (fun p => P p) _ _; cbv beta; eauto.
  { intros. rewrite N.pos_mul; eauto. }
  destruct n; eauto.
Qed.

Lemma Z_factor_ind (P : Z -> Prop)
  (zero : P Z0)
  (init : P (Z.pos 1))
  (step : forall n p, P n -> prime p ->
    (forall q, prime q -> Z.divide q n -> q <= p) -> P (n * p)%Z)
  (opp : forall n : positive, P n -> P (Z.neg n))
  : forall n, P n.
Proof.
  unshelve epose proof factor_ind (fun p => P p) _ _; cbv beta; eauto.
  { intros. rewrite Pos2Z.inj_mul; eauto. }
  destruct n; eauto.
Qed.

Lemma ppfactor_ind (P : positive -> Prop)
  (init : P 1)
  (step : forall n p k, P n -> prime p -> Z.gcd n p = xH ->
    (forall q, prime q -> Z.divide q n -> q < p) -> P (n * p ^ k))
  : forall n, P n.
Proof.
  intros n; revert step; revert init.
  rewrite <-(prod_ppfactor n).
  specialize (Sorted_ppfactor n); cbv zeta.
  specialize (prime_ppfactor n); cbv zeta.
  specialize (range_ppfactor n); cbv zeta.
  set (ppfactor n) as pps; clearbody pps.
  induction pps as [|[p k]] using rev_ind; cbn; trivial.
  rewrite map_app, map_cons; cbn [map].
  rewrite map_app, map_cons, prod_app; cbn [map fold_right uncurry].
  rewrite Pos.mul_1_r.
  intros H H0 H1 **.
  eapply Forall_app in H; case H as [? [[] _]%Forall_cons_iff]; cbn [fst snd] in *.
  eapply Forall_app in H0; case H0 as [? [? _]%Forall_cons_iff]; cbn [fst snd] in *.
  eapply Sorted_StronglySorted in H1; try exact Pos.lt_trans.
  eapply StronglySorted_app in H1; case H1 as (?&?&?).
  eapply step; eauto using Forall_app.
  eapply IHpps; eauto using Forall_app;
    try split; eauto using StronglySorted_Sorted.
  { rewrite Z.gcd_comm. apply Z.coprime_prime_l; trivial.
    intros X%prime_divisor_of_prime_power_product; trivial.
    eapply Forall_forall in H1; eauto; inversion H1; lia. }
  { intros q Hq Hd%prime_divisor_of_prime_power_product; trivial.
    eapply Forall_forall in H1; eauto; inversion H1; trivial. }
Qed.

#[local] Lemma Private_in_ppfactor_val p k n : In (p, k) (ppfactor n) -> val p n = N.pos k.
Proof.
  intros H.
  pose proof proj1 (Forall_forall _ _) (fst_ppfactor n) _ (in_map fst _ (p, k) H) as [Hp _]; cbn [fst] in Hp.
  pose proof Z.prime_ge_2 _ Hp.
  assert (ND : NoDup (map fst (ppfactor n)))
    by (eapply NoDup_StronglySorted, Sorted_StronglySorted, Sorted_ppfactor; repeat intro; lia).
  pose proof prime_ppfactor n as HF.
  pose proof prod_ppfactor n as E.
  case (in_split _ _ H) as (l1&l2&E'); rewrite E' in E, ND, HF; clear E' H.
  rewrite map_app, map_cons, prod_app in E; cbn [map fold_right uncurry] in E.
  rewrite map_app, map_cons in ND, HF; cbn [map fst] in ND, HF.
  set (m := Π (map (uncurry Pos.pow) l1) * Π (map (uncurry Pos.pow) l2)).
  assert (n = p ^ k * m) as -> by (subst m; rewrite <-E; nia).
  rewrite val_mul_pow by lia.
  enough (val p m = 0%N) by lia.
  apply val_0_iff_divide; try lia; intros Hd.
  apply N.divide_pos_pos, Z.divide_pos_pos in Hd.
  eapply (NoDup_remove_2 _ _ _ ND).
  rewrite <-map_app; eapply prime_divisor_of_prime_power_product; trivial.
  { rewrite map_app; apply Forall_app in HF; apply Forall_app; intuition eauto using Forall_inv_tail. }
  subst m; rewrite map_app, prod_app; trivial.
Qed.

Lemma in_ppfactor p k n : In (p, k) (ppfactor n) <-> prime p /\ val p n = N.pos k.
Proof.
  split.
  { intros H; split; auto using Private_in_ppfactor_val.
    pose proof proj1 (Forall_forall _ _) (fst_ppfactor n) _ (in_map fst _ (p, k) H) as [Hp _]; exact Hp. }
  intros [Hp Hk].
  assert (Hd : (N.pos p | N.pos n)%N) by (apply divide_as_val; right; lia).
  apply N.divide_pos_pos, Z.divide_pos_pos in Hd.
  rewrite <-(prod_ppfactor n) in Hd.
  apply prime_divisor_of_prime_power_product in Hd; auto using prime_ppfactor.
  apply in_map_iff in Hd; case Hd as [[q j] [Hq Hqj]]; cbn [fst] in Hq; subst q.
  pose proof Private_in_ppfactor_val p j n Hqj as Hj.
  assert (j = k) as -> by lia; exact Hqj.
Qed.
