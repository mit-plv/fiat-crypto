
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Import List.
Require Import ZArith.
Require Import Zorder.
Require Import ZCAux.
Require Import LucasLehmer.
Require Import Pocklington.
Require Import ZCmisc.
Require Import Pmod.

Definition dec_prime := list (positive * positive).

Inductive singleCertif : Set :=
 | Proof_certif : forall N:positive, prime N -> singleCertif
 | Lucas_certif : forall (n:positive) (p: Z), singleCertif
 | Pock_certif : forall N a : positive, dec_prime -> positive -> singleCertif
 | SPock_certif : forall N a : positive, dec_prime -> singleCertif
 | Ell_certif: forall (N S: positive) (l: list (positive * positive))
                      (A B x y: Z), singleCertif.

Definition Certif := list singleCertif.

Definition nprim sc :=
 match sc with
 | Proof_certif n _ => n
 | Lucas_certif n _ => n
 | Pock_certif n _ _ _ => n
 | SPock_certif n _ _ => n
 | Ell_certif n _ _ _ _ _ _ => n

 end.

Open Scope positive_scope.
Open Scope P_scope.

Fixpoint pow (a p:positive) {struct p} : positive :=
 match p with
 | xH => a
 | xO p' =>let z := pow a p' in square z
 | xI p' => let z := pow a p' in square z * a
 end.

Definition mkProd' (l:dec_prime) :=
  fold_right (fun (k:positive*positive) r => times (fst k) r) 1%positive l.

Definition mkProd_pred (l:dec_prime) :=
  fold_right (fun (k:positive*positive) r =>
    if ((snd k) ?= 1)%P then r else times (pow (fst k) (Ppred (snd k))) r)
  1%positive l.

Definition mkProd (l:dec_prime) :=
  fold_right (fun (k:positive*positive) r => times (pow (fst k) (snd k)) r) 1%positive l.

(* [pow_mod a m n] return [a^m mod n] *)
Fixpoint pow_mod (a m n : positive) {struct m} : N :=
  match m with
  | xH => (a mod n)%P
  | xO m' =>
    let z := pow_mod a m' n in
    match z with
    | N0 => 0%N
    | Npos z' => ((square z') mod n)%P
    end
  | xI m' =>
    let z := pow_mod a m' n in
    match z with
    | N0 => 0%N
    | Npos z' => (((square z') * a)%P mod n)%P
    end
  end.

Definition Npow_mod a m n :=
  match a with
  | N0 => 0%N
  | Npos a => pow_mod a m n
  end.

(* [fold_pow_mod a [q1,_;...;qn,_]] b = a ^(q1*...*qn) mod b *)
(* invariant a mod N = a *)
Definition fold_pow_mod a l n :=
  fold_left
    (fun a' (qp:positive*positive) =>  Npow_mod a' (fst qp) n)
    l a.

Definition times_mod x y n :=
  match x, y with
  | N0, _ => N0
  | _, N0 => N0
  | Npos x, Npos y => ((x * y)%P mod n)
  end.

Definition Npred_mod p n :=
  match p with
  | N0 => Npos (Ppred n)
  | Npos p =>
      if (p ?= 1) then N0
      else Npos (Ppred p)
   end.

Fixpoint all_pow_mod (prod a : N) (l:dec_prime) (n:positive) {struct l}: N*N :=
  match l with
  | nil => (prod,a)
  | (q,_) :: l =>
    let m := Npred_mod (fold_pow_mod a l n) n in
    all_pow_mod (times_mod prod m n) (Npow_mod a q n) l n
  end.

Fixpoint pow_mod_pred (a:N) (l:dec_prime) (n:positive) {struct l} : N :=
  match l with
  | nil => a
  | (q,p)::l =>
    if (p ?= 1) then pow_mod_pred a l n
    else
      let a' := iter_pos _ (fun x => Npow_mod x q n) a (Ppred p) in
      pow_mod_pred a' l n
  end.

Definition is_odd p :=
  match p with
  | xO _ => false
  | _     => true
  end.

Definition is_even p :=
   match p with
  | xO _ => true
  | _       => false
  end.

Definition check_s_r s r sqrt :=
 match s with
 | N0 => true
 | Npos p =>
    match (Zminus (square r) (xO (xO (xO p)))) with
    | Zpos x =>
       let sqrt2 := square sqrt in
       let sqrt12 := square (Psucc sqrt)  in
       if sqrt2 ?< x then x ?< sqrt12
       else false
    | Zneg _ => true
    | Z0 => false
    end
  end.

Definition test_pock N a dec sqrt :=
  if (2 ?< N) then
    let Nm1 := Ppred N in
    let F1 := mkProd dec in
    match Nm1 / F1 with
    | (Npos R1, N0) =>
      if is_odd R1 then
        if is_even F1 then
          if (1 ?< a) then
            let (s,r') := (R1 / (xO F1))in
            match r' with
            | Npos r =>
	      let A := pow_mod_pred (pow_mod a R1 N) dec N in
              match all_pow_mod 1%N A dec N with
              | (Npos p, Npos aNm1) =>
                if (aNm1 ?= 1) then
                  if gcd p N ?= 1 then
                    if check_s_r s r sqrt then
		      (N ?< (times ((times ((xO F1)+r+1) F1) + r) F1) + 1)
                    else false
                  else false
                else false
              | _ => false
              end
            | _ => false
            end
	  else false
        else false
      else false
    | _=> false
    end
  else false.

Fixpoint is_in (p : positive) (lc : Certif) {struct lc} : bool :=
  match lc with
  | nil => false
  | c :: l => if p ?= (nprim c) then true else is_in p l
  end.

Fixpoint all_in (lc : Certif) (lp : dec_prime) {struct lp} : bool :=
  match lp with
  | nil => true
  | (p,_) :: lp =>
    if all_in lc lp
    then is_in p lc
    else false
  end.

Definition gt2 n :=
  match n with
  | Zpos p => (2 ?< p)%positive
  | _ => false
  end.

Fixpoint test_Certif (lc : Certif) : bool :=
  match lc with
  | nil => true
  | (Proof_certif _ _) :: lc => test_Certif lc
  | (Lucas_certif n p) :: lc =>
     if test_Certif lc then
     if gt2 p then
       match Mp p with
       | Zpos n' =>
          if (n ?= n') then
            match SS p with
            | Z0 => true
            | _ => false
             end
          else false
      | _ => false
      end
    else false
    else false
  | (Pock_certif n a dec sqrt) :: lc =>
    if test_pock n a dec sqrt then
     if all_in lc dec then test_Certif lc else false
    else false
(* Shoudl be done later to do it with Z *)
  | (SPock_certif n a dec) :: lc => false
  | (Ell_certif _ _ _ _ _ _ _):: lc => false
  end.

Lemma pos_eq_1_spec :
  forall p,
    if (p ?= 1)%P then p = xH
    else (1 < p).
Proof.
 unfold Zlt;destruct p;simpl; auto; red;reflexivity.
Qed.

Open Scope Z_scope.
Lemma mod_unique : forall b q1 r1 q2 r2,
     0 <= r1 < b ->
     0 <= r2 < b ->
     b * q1 + r1 = b * q2 + r2 ->
     q1 = q2 /\ r1 = r2.
Proof with auto with zarith.
 intros b q1 r1 q2 r2 H1 H2 H3.
 assert (r2 = (b * q1 + r1) -b*q2).  rewrite H3;ring.
 assert (b*(q2 - q1) = r1 - r2 ).  rewrite H;ring.
 assert (-b < r1 - r2 < b). omega.
 destruct (Ztrichotomy q1 q2) as [H5 | [H5 | H5]].
  assert (q2 - q1 >= 1).  omega.
  assert (r1- r2 >= b).
  rewrite <- H0.
  pattern b at 2; replace b with (b*1).
  apply Zmult_ge_compat_l; omega.  ring.
  elimtype False; omega.
  split;trivial. rewrite H;rewrite H5;ring.
  assert (r1- r2 <= -b).
  rewrite <- H0.
  replace (-b) with (b*(-1)); try (ring;fail).
  apply Zmult_le_compat_l; omega.
  elimtype False; omega.
Qed.

Lemma Zge_0_pos : forall p:positive, p>= 0.
Proof.
 intros;unfold Zge;simpl;intro;discriminate.
Qed.

Lemma Zge_0_pos_add : forall p:positive, p+p>= 0.
Proof.
 intros;simpl;apply Zge_0_pos.
Qed.

Hint Resolve Zpower_gt_0 Zlt_0_pos Zge_0_pos Zlt_le_weak Zge_0_pos_add: zmisc.

Hint Rewrite  Zpos_mult Zpower_mult Zpower_1_r Zmod_mod Zpower_exp
            times_Zmult square_Zmult Psucc_Zplus: zmisc.

Ltac mauto :=
  trivial;autorewrite with zmisc;trivial;auto with zmisc zarith.

Lemma mod_lt : forall a (b:positive), a mod b < b.
Proof.
  intros a b;destruct (Z_mod_lt a b);mauto.
Qed.
Hint Resolve mod_lt : zmisc.

Lemma Zmult_mod_l : forall (n:positive) a b, (a mod n * b) mod n = (a * b) mod n.
Proof with mauto.
 intros;rewrite Zmult_mod ... rewrite (Zmult_mod a) ...
Qed.

Lemma Zmult_mod_r : forall (n:positive) a b, (a * (b mod n)) mod n = (a * b) mod n.
Proof with mauto.
 intros;rewrite Zmult_mod ... rewrite (Zmult_mod a) ...
Qed.

Lemma Zminus_mod_l : forall (n:positive) a b, (a mod n - b) mod n = (a - b) mod n.
Proof with mauto.
 intros;rewrite Zminus_mod ... rewrite (Zminus_mod a) ...
Qed.

Lemma Zminus_mod_r : forall (n:positive) a b, (a - (b mod n)) mod n = (a - b) mod n.
Proof with mauto.
 intros;rewrite Zminus_mod ... rewrite (Zminus_mod a) ...
Qed.

Hint Rewrite Zmult_mod_l Zmult_mod_r Zminus_mod_l Zminus_mod_r : zmisc.
Hint Rewrite <- Zpower_mod : zmisc.

Lemma Pmod_Zmod : forall a b, Z_of_N (a mod b)%P = a mod b.
Proof.
 intros a b; rewrite Pmod_div_eucl.
 assert (b>0). mauto.
 unfold Zmod; assert (H1 := Z_div_mod a b H).
 destruct (Zdiv_eucl a b) as (q2, r2).
 assert (H2 := div_eucl_spec a b).
 assert (Z_of_N (fst (a / b)%P) = q2 /\ Z_of_N (snd (a/b)%P) = r2).
 destruct H1;destruct H2.
 apply mod_unique with b;mauto.
 split;mauto.
 unfold Zle;destruct (snd (a / b)%P);intro;discriminate.
 rewrite <- H0;symmetry;rewrite Zmult_comm;trivial.
 destruct H0;auto.
Qed.
Hint Rewrite Pmod_Zmod : zmisc.

Lemma Zpower_0 : forall p : positive, 0^p = 0.
Proof.
 intros;simpl;destruct p;unfold Zpower_pos;simpl;trivial.
 generalize (iter_pos Z (Z.mul 0) 1 p).
 induction p;simpl;trivial.
Qed.

Lemma pow_Zpower : forall a p, Zpos (pow a p) = a ^ p.
Proof.
 induction p; mauto; simpl; mauto; rewrite IHp; mauto.
Qed.
Hint Rewrite pow_Zpower : zmisc.

Lemma pow_mod_spec : forall n a m, Z_of_N (pow_mod a m n) = a^m mod n.
Proof.
 induction m; mauto; simpl; intros; mauto.
 rewrite Zmult_mod; auto with zmisc.
 rewrite (Zmult_mod (a^m)(a^m)); auto with zmisc.
 rewrite <- IHm; mauto.
 destruct (pow_mod a m n); mauto.
 rewrite (Zmult_mod (a^m)(a^m)); auto with zmisc.
 rewrite <- IHm. destruct (pow_mod a m n);simpl; mauto.
Qed.
Hint Rewrite pow_mod_spec Zpower_0 : zmisc.

Lemma Npow_mod_spec : forall a p n, Z_of_N (Npow_mod a p n) = a^p mod n.
Proof.
 intros a p n;destruct a; mauto; simpl; mauto.
Qed.
Hint Rewrite Npow_mod_spec : zmisc.

Lemma iter_Npow_mod_spec : forall n q p a,
  Z_of_N (iter_pos N (fun x : N => Npow_mod x q n) a p) = a^q^p mod n.
Proof.
 induction p; mauto; intros; simpl Pos.iter; mauto; repeat rewrite IHp.
 rewrite (Zpower_mod ((a ^ q ^ p) ^ q ^ p));auto with zmisc.
 rewrite (Zpower_mod (a ^ q ^ p)); mauto.
 mauto.
Qed.
Hint Rewrite iter_Npow_mod_spec : zmisc.

Lemma fold_pow_mod_spec : forall (n:positive) l (a:N),
  Z_of_N a = a mod n ->
  Z_of_N (fold_pow_mod a l n) = a^(mkProd' l) mod n.
Proof.
 unfold fold_pow_mod;induction l; simpl fold_left; simpl mkProd';
  intros; mauto.
 rewrite IHl; mauto.
Qed.
Hint Rewrite fold_pow_mod_spec : zmisc.

Lemma pow_mod_pred_spec : forall (n:positive) l (a:N),
  Z_of_N a = a mod n ->
  Z_of_N (pow_mod_pred a l n) = a^(mkProd_pred l) mod n.
Proof.
 unfold pow_mod_pred;induction l;simpl mkProd;intros; mauto.
 destruct a as (q,p).
 simpl mkProd_pred.
 destruct (p ?= 1)%P; rewrite IHl; mauto; simpl.
Qed.
Hint Rewrite pow_mod_pred_spec : zmisc.

Lemma mkProd_pred_mkProd : forall l,
   (mkProd_pred l)*(mkProd' l) = mkProd l.
Proof.
 induction l;simpl;intros; mauto.
 generalize (pos_eq_1_spec (snd a)); destruct  (snd a ?= 1)%P;intros.
 rewrite H; mauto.
 replace (mkProd_pred l * (fst a * mkProd' l)) with
     (fst a *(mkProd_pred l * mkProd' l));try ring.
  rewrite IHl; mauto.
 rewrite Zmult_assoc. rewrite times_Zmult.
 rewrite (Zmult_comm (pow (fst a) (Ppred (snd a)) * mkProd_pred l)).
 rewrite Zmult_assoc. rewrite pow_Zpower.  rewrite <-Ppred_Zminus;trivial.
 rewrite <- Zpower_Zsucc; try omega.
 replace (Zsucc (snd a - 1)) with ((snd a - 1)+1).
 replace ((snd a - 1)+1) with (Zpos (snd a)); mauto.
 rewrite <- IHl;repeat rewrite Zmult_assoc; mauto.
 destruct (snd a - 1);trivial.
 assert (1 < snd a); auto with zarith.
Qed.
Hint Rewrite mkProd_pred_mkProd : zmisc.

Lemma lt_Zmod : forall p n, 0 <= p < n -> p mod n = p.
Proof.
  intros a b H.
  assert ( 0 <= a mod b < b).
   apply Z_mod_lt; mauto.
  destruct (mod_unique b (a/b) (a mod b) 0 a H0 H); mauto.
  rewrite <- Z_div_mod_eq; mauto.
Qed.

Lemma Npred_mod_spec : forall p n, Z_of_N p < Zpos n ->
    1 < Zpos n -> Z_of_N (Npred_mod p n) = (p - 1) mod n.
Proof.
 destruct p;intros;simpl.
 rewrite <- Ppred_Zminus; auto.
 apply Zmod_unique with (q := -1); mauto.
 assert (H1 := pos_eq_1_spec p);destruct (p?=1)%P.
 rewrite H1; mauto.
 unfold Z_of_N;rewrite <- Ppred_Zminus; auto.
 simpl in H;symmetry; apply (lt_Zmod (p-1) n).
 assert (1 < p); auto with zarith.
Qed.
Hint Rewrite Npred_mod_spec : zmisc.

Lemma times_mod_spec : forall x y n, Z_of_N (times_mod x y n) = (x * y) mod n.
Proof.
 intros; destruct x; mauto.
 destruct y;simpl; mauto.
Qed.
Hint Rewrite times_mod_spec : zmisc.

Lemma snd_all_pow_mod :
 forall n l (prod a :N),
  a mod (Zpos n) = a ->
  Z_of_N (snd (all_pow_mod prod a l n)) = (a^(mkProd' l)) mod n.
Proof.
 induction l; simpl all_pow_mod; simpl mkProd';intros; mauto.
 destruct a as (q,p).
 rewrite IHl; mauto.
Qed.

Lemma fold_aux : forall a N (n:positive) l prod,
  fold_left
     (fun (r : Z) (k : positive * positive) =>
      r * (a ^(N / fst k) - 1) mod n) l (prod mod n) mod n =
  fold_left
     (fun (r : Z) (k : positive * positive) =>
      r * (a^(N / fst k) - 1)) l prod mod n.
Proof.
 induction l;simpl;intros; mauto.
Qed.

Lemma fst_all_pow_mod :
 forall (n a:positive) l  (R:positive) (prod A :N),
  1 < n ->
  Z_of_N prod = prod mod n ->
  Z_of_N A = a^R mod n ->
  Z_of_N (fst (all_pow_mod prod A l n)) =
    (fold_left
      (fun r (k:positive*positive) =>
        (r * (a ^ (R* mkProd' l / (fst k)) - 1))) l prod) mod n.
Proof.
 induction l;simpl;intros; mauto.
 destruct a0 as (q,p);simpl.
 assert (Z_of_N A = A mod n).
  rewrite H1; mauto.
 rewrite (IHl (R * q)%positive); mauto; mauto.
 pattern (q * mkProd' l) at 2;rewrite (Zmult_comm q).
 repeat rewrite Zmult_assoc.
 rewrite Z_div_mult;auto with zmisc zarith.
 rewrite <- fold_aux.
 rewrite <- (fold_aux a (R * q * mkProd' l) n l (prod * (a ^ (R * mkProd' l) - 1)))...
 assert ( ((prod * (A ^ mkProd' l - 1)) mod n) =
              ((prod * ((a ^ R) ^ mkProd' l - 1)) mod n)).
  repeat rewrite (Zmult_mod prod);auto with zmisc.
  rewrite Zminus_mod;auto with zmisc.
  rewrite (Zminus_mod ((a ^ R) ^ mkProd' l));auto with zmisc.
  rewrite (Zpower_mod (a^R));auto with zmisc.  rewrite H1; mauto.
 rewrite H3; mauto.
 rewrite H1; mauto.
Qed.

Lemma is_odd_Zodd : forall p, is_odd p = true -> Zodd p.
Proof.
 destruct p;intros;simpl;trivial;discriminate.
Qed.

Lemma is_even_Zeven : forall p, is_even p = true -> Zeven p.
Proof.
 destruct p;intros;simpl;trivial;discriminate.
Qed.

Lemma lt_square : forall x y, 0 < x  -> x < y -> x*x < y*y.
Proof.
 intros; apply Zlt_trans with (x*y).
 apply Zmult_lt_compat_l;trivial.
 apply Zmult_lt_compat_r;trivial. omega.
Qed.

Lemma le_square : forall x y, 0 <= x  -> x <= y -> x*x <= y*y.
Proof.
 intros; apply Zle_trans with (x*y).
 apply Zmult_le_compat_l;trivial.
 apply Zmult_le_compat_r;trivial. omega.
Qed.

Lemma borned_square : forall x y, 0 <= x -> 0 <= y ->
                             x*x < y*y < (x+1)*(x+1) -> False.
Proof.
 intros;destruct (Z_lt_ge_dec x y) as [z|z].
 assert (x + 1 <= y). omega.
 assert (0 <= x+1). omega.
 assert (H4 := le_square _ _ H3 H2). omega.
 assert (H4 := le_square _ _ H0 (Zge_le _ _ z)). omega.
Qed.

Lemma not_square : forall (sqrt:positive) n, sqrt * sqrt < n < (sqrt+1)*(sqrt + 1) -> ~(isSquare n).
Proof.
 intros sqrt n H (y,H0).
 destruct (Z_lt_ge_dec 0 y).
 apply (borned_square sqrt y);mauto.
 assert (y*y = (-y)*(-y)). ring. rewrite H1 in H0;clear H1.
 apply (borned_square sqrt (-y));mauto.
Qed.

Ltac spec_dec :=
 repeat match goal with
 | [H:(?x ?= ?y)%P = _ |- _] =>
      generalize (is_eq_spec x y);
      rewrite H;clear H; autorewrite with zmisc;
      intro
  | [H:(?x ?< ?y)%P = _ |- _] =>
      generalize (is_lt_spec x y);
      rewrite H; clear H; autorewrite with zmisc;
      intro
  end.

Ltac elimif :=
 match goal with
 | [H: (if ?b then _ else _) = _ |- _] =>
      let H1 := fresh "H" in
      (CaseEq b;intros H1; rewrite H1 in H;
      try discriminate H); elimif
 | _ => spec_dec
 end.

Lemma check_s_r_correct : forall s r sqrt, check_s_r s r sqrt = true ->
          Z_of_N s = 0 \/ ~ isSquare (r * r - 8 * s).
Proof.
 unfold check_s_r;intros.
 destruct s as [|s]; trivial;auto.
 right;CaseEq (square r - xO (xO (xO s)));[intros H1|intros p1 H1| intros p1 H1];
   rewrite H1 in H;try discriminate H.
 elimif.
 assert (Zpos (xO (xO (xO s))) = 8 * s).  repeat rewrite Zpos_xO_add;ring.
 generalizeclear H1; rewrite H2;mauto;intros.
 apply (not_square sqrt).
 simpl Z.of_N; rewrite H1;auto.
 intros (y,Heq).
 generalize H1 Heq;mauto.
 unfold Z_of_N.
 match goal with |- ?x = _ -> ?y = _ -> _ =>
   replace x with y; try ring
 end.
 intros Heq1;rewrite Heq1;intros Heq2.
 destruct y;discriminate Heq2.
Qed.

Lemma in_mkProd_prime_div_in :
  forall p:positive,  prime p ->
  forall (l:dec_prime),
    (forall k, In k l -> prime (fst k)) ->
    Zdivide p (mkProd l) -> exists n,In (p, n) l.
Proof.
 induction l;simpl mkProd; simpl In; mauto.
 intros _ H1; absurd (p <= 1).
 apply Zlt_not_le; apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
 apply Zdivide_le; auto with zarith.
 intros.
 case prime_mult with (2 := H1); auto with zarith; intros H2.
 exists (snd a);left.
 destruct a;simpl in *.
 assert (Zpos p = Zpos p0).
   rewrite (prime_div_Zpower_prime p1 p p0); mauto.
   apply (H0 (p0,p1));auto.
 inversion H3; auto.
 destruct IHl as (n,H3); mauto.
 exists n; auto.
Qed.

Lemma gcd_Zis_gcd : forall a b:positive, (Zis_gcd b a (gcd b a)%P).
Proof.
 intros a;assert (Hacc := Zwf_pos a);induction Hacc;rename x into a;intros.
 generalize (div_eucl_spec b a); mauto.
 rewrite <- (Pmod_div_eucl b a).
 CaseEq (b mod a)%P;[intros Heq|intros r Heq]; intros (H1,H2).
 simpl in H1;rewrite Zplus_0_r in H1.
 rewrite (gcd_mod0 _ _ Heq).
 constructor;mauto.
 apply Zdivide_intro with (fst (b/a)%P);trivial.
 rewrite (gcd_mod _ _ _ Heq).
 rewrite H1;apply Zis_gcd_sym.
 rewrite Zmult_comm;apply Zis_gcd_for_euclid2;simpl in *.
 apply Zis_gcd_sym;auto.
Qed.

Lemma test_pock_correct : forall N a dec sqrt,
   (forall k, In k dec -> prime (Zpos (fst k))) ->
   test_pock N a dec sqrt = true ->
   prime N.
Proof.
 unfold test_pock;intros.
 elimif.
 generalize (div_eucl_spec (Ppred N) (mkProd dec));
 destruct ((Ppred N) / (mkProd dec))%P as (R1,n); mauto;intros (H2,H3).
 destruct R1 as [|R1];try discriminate H0.
 destruct n;try discriminate H0.
 elimif.
 generalize (div_eucl_spec R1 (xO (mkProd dec)));
 destruct ((R1 / xO (mkProd dec))%P) as (s,r'); mauto;intros (H7,H8).
 destruct r' as [|r];try discriminate H0.
 generalize (fst_all_pow_mod N a dec (R1*mkProd_pred dec) 1
         (pow_mod_pred (pow_mod a R1 N) dec N)).
 generalize (snd_all_pow_mod N dec 1 (pow_mod_pred (pow_mod a R1 N) dec N)).
 destruct (all_pow_mod 1 (pow_mod_pred (pow_mod a R1 N) dec N) dec N) as
  (prod,aNm1); mauto; simpl Z_of_N.
 destruct prod as [|prod];try discriminate H0.
 destruct aNm1 as [|aNm1];try discriminate H0;elimif.
 simpl in H3; simpl in H2.
 rewrite <- Ppred_Zminus in H2;try omega.
 rewrite <- Zmult_assoc;rewrite mkProd_pred_mkProd.
 intros H12;assert (a^(N-1) mod N = 1).
  pattern 1 at 2;rewrite <- H9;symmetry.
  simpl Z.of_N in H12.
  rewrite H2; rewrite H12; mauto.
  rewrite <- Zpower_mult; mauto.
  clear H12.
 intros H14.
 match type of H14 with _ -> _ -> _ -> ?X =>
  assert (H12:X); try apply H14; clear H14
 end; mauto.
 rewrite Zmod_small; mauto.
 assert (1 < mkProd dec).
  assert (H14 := Zlt_0_pos (mkProd dec)).
  assert (1 <= mkProd dec); mauto.
  destruct (Zle_lt_or_eq _ _ H15); mauto.
  inversion H16. rewrite <- H18 in H5;discriminate H5.
 simpl in H8.
 assert (Z_of_N s = R1 / (2 * mkProd dec) /\ Zpos r =  R1 mod (2 * mkProd dec)).
  apply mod_unique with (2 * mkProd dec);auto with zarith.
 revert H8; mauto.
 apply Z_mod_lt; mauto.
 rewrite <- Z_div_mod_eq; mauto; rewrite H7.
 simpl fst; simpl snd; simpl Z_of_N.
 ring.
 destruct H15 as (H15,Heqr).
 apply PocklingtonExtra with (F1:=mkProd dec) (R1:=R1) (m:=1);
  auto with zmisc zarith.
 rewrite H2; mauto.
 apply is_even_Zeven; auto.
 apply is_odd_Zodd; auto.
 intros p; case p; clear p.
 intros HH; contradict HH.
 apply not_prime_0.
 2: intros p (V1, _); contradict V1; apply Zle_not_lt; red; simpl; intros;
     discriminate.
 intros p Hprime Hdec; exists (Zpos a);repeat split; auto with zarith.
 apply Zis_gcd_gcd; auto with zarith.
 change (rel_prime (a ^ ((N - 1) / p) - 1) N).
 match type of H12 with _ = ?X mod _ =>
   apply rel_prime_div with (p := X); auto with zarith
 end.
 apply rel_prime_mod_rev; auto with zarith.
 red.
 pattern 1 at 3; rewrite <- H10; rewrite <- H12.
 apply Pmod.gcd_Zis_gcd.
 destruct (in_mkProd_prime_div_in _ Hprime _ H Hdec) as (q,Hin).
 revert H2; mauto; intro H2.
 rewrite <- H2.
 match goal with |- context [fold_left ?f _ _] =>
   apply (ListAux.fold_left_invol_in _ _ f (fun k => Zdivide (a ^ ((N - 1) / p) - 1) k))
     with (b := (p, q)); auto with zarith
 end.
 rewrite <- Heqr.
 generalizeclear H0; ring_simplify
    (((mkProd dec + mkProd dec + r + 1) * mkProd dec + r) * mkProd dec + 1)
    ((1 * mkProd dec + 1) * (2 * mkProd dec * mkProd dec + (r - 1) * mkProd dec + 1)); mauto.
 rewrite <- H15;rewrite <- Heqr.
 apply check_s_r_correct with sqrt; mauto.
Qed.

Lemma is_in_In :
  forall p lc, is_in p lc = true -> exists c, In c lc /\ p = nprim c.
Proof.
 induction lc;simpl;try (intros;discriminate).
 intros;elimif.
 exists a;split;auto. inversion H0;trivial.
 destruct (IHlc H) as [c [H1 H2]];exists c;auto.
Qed.

Lemma all_in_In :
 forall lc lp, all_in lc lp = true ->
 forall pq, In pq lp -> exists c, In c lc /\ fst pq = nprim c.
Proof.
 induction lp;simpl. intros H pq HF;elim HF.
 intros;destruct a;elimif.
 destruct H0;auto.
 rewrite <- H0;simpl;apply is_in_In;trivial.
Qed.

Lemma test_Certif_In_Prime :
  forall lc, test_Certif lc = true ->
   forall c, In c lc -> prime (nprim c).
Proof with mauto.
 induction lc;simpl;intros. elim H0.
 destruct H0.
 subst c;destruct a;simpl...
 elimif.
 CaseEq (Mp p);[intros Heq|intros N' Heq|intros N' Heq];rewrite Heq in H;
  try discriminate H. elimif.
 CaseEq (SS p);[intros Heq'|intros N'' Heq'|intros N'' Heq'];rewrite Heq' in H;
  try discriminate H.
 rewrite H2;rewrite <- Heq.
apply LucasLehmer;trivial.
(destruct p; try discriminate H1).
simpl in H1; generalize (is_lt_spec 2 p); rewrite H1; auto.
elimif.
apply (test_pock_correct N a d p); mauto.
 intros k Hin;destruct (all_in_In _ _ H1 _ Hin) as (c,(H2,H3)).
 rewrite H3;auto.
discriminate.
discriminate.
 destruct a;elimif;auto.
discriminate.
discriminate.
Qed.

Lemma Pocklington_refl :
  forall c lc, test_Certif (c::lc) = true -> prime (nprim c).
Proof.
 intros c lc Heq;apply test_Certif_In_Prime with (c::lc);trivial;simpl;auto.
Qed.
