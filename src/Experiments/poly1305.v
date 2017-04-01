Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra. Import Monoid.
Require Import Crypto.Util.Tactics.
Require Import Coq.Lists.List Coq.Lists.SetoidList Crypto.Util.ListUtil.

Section Monoid.
    Context {T eq op id} {monoid:@monoid T eq op id}.
    Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "*" := op.
    Local Infix "=" := eq : eq_scope.
    Local Open Scope eq_scope.

    (** add Section Sum from poly1305 *)
    Fixpoint downfrom n: list nat :=
      match n with
      | O => nil
      | S n' => n' :: downfrom n'
      end.
    Definition seq_from_to a b : list nat := map (fun i => (b-i)%nat) (downfrom (b+1-a)%nat).

    Definition sum : list T -> T := List.fold_right op id.

    Definition sum_from_to a b (f:nat->T) : T := sum (List.map f (seq_from_to a b)).

    Lemma left_more_sum:
      forall a b f, (a > b)%nat -> sum_from_to a b f = id.
    Proof.
      intros. unfold sum_from_to, sum,seq_from_to.
      (*replace (Nat.sub (Nat.add b 1) a) with O.*)
      assert (B: (Logic.eq (b+1-a) 0)%nat).
      Require Import Omega. omega.
      rewrite B.
      simpl. reflexivity.
    Qed.

    Global Instance Proper_sum : Proper (eqlistA eq ==> eq) sum.
    Proof.
      repeat intro. induction H.
      - reflexivity.
      - simpl sum. rewrite H, IHeqlistA. reflexivity.
    Qed.

    Global Instance Proper_sum_from_to : Proper (Logic.eq==>Logic.eq==>(pointwise_relation _ eq) ==> eq) sum_from_to.
    Proof.
      cbv [Proper pointwise_relation respectful].
      repeat intro; subst.
      unfold sum_from_to.
      apply Proper_sum.
      apply (Proper_map(RA:=Logic.eq)).
      - repeat intro. subst. apply H1.
      - reflexivity.
    Qed.

    Lemma downfrom_S n : Logic.eq (downfrom (S n)) (n :: downfrom n). reflexivity. Qed.

    Lemma sum_app a b : sum (a ++ b) = sum a * sum b.
    Proof.
      induction a.
      - simpl. rewrite left_identity. reflexivity.
      - simpl. rewrite IHa. rewrite associative. reflexivity.
    Qed.

    Lemma seq_from_to_S_r a b (H:(a<=b)%nat) : Logic.eq (seq_from_to a (S b)) (List.app (seq_from_to a b) (S b::nil)).
    Proof.
      cbv [seq_from_to].
      replace (S b + 1 - a)%nat with (S (b+1-a)) by omega.
      remember (b + 1 - a)%nat as l. generalize dependent a; generalize dependent b; induction l; intros.
      - reflexivity.
      - rewrite downfrom_S, map_cons.
        destruct (dec (Logic.eq b a)).
        + replace l with O by omega. simpl. reflexivity.
        + destruct b; try omega; [].
          specialize (IHl (S b) (S a) ltac:(omega) ltac:(omega)).
          rewrite IHl. rewrite downfrom_S, map_cons.
          replace (S (S b) - S l)%nat with ((S b - l))%nat by omega.
          reflexivity.
    Qed.

    Lemma sum_one_more:
      forall (a b:nat) f (H: (a<=S b)%nat), eq (sum_from_to a (S b) f) ((sum_from_to a b f) * (f (S b))).
    Proof.
      intros. destruct (dec (Logic.eq a (S b))).
      - rewrite e. setoid_replace (sum_from_to (S b) b f) with id.
        +rewrite left_identity. unfold sum_from_to, map, seq_from_to.
         replace (S b + 1 - S b)%nat with 1%nat by omega. simpl.
         rewrite right_identity. reflexivity.
        + rewrite <- left_more_sum. reflexivity. omega.
      - unfold sum_from_to. rewrite seq_from_to_S_r. rewrite map_app. rewrite sum_app.
        simpl. rewrite right_identity. reflexivity. omega.
    Qed.
End Monoid.
Arguments sum {_} _ _ _.
Arguments sum_from_to {_} _ _ _ _ _.
 Section Homomorphism.
    Context {T  EQ OP ID} {monoidT:  @monoid T  EQ OP ID }.
    Context {T' eq op id} {monoidT': @monoid T' eq op id }.
    Context {phi:T->T'}.
    Local Infix "=" := eq. Local Infix "=" := eq : type_scope.
    Class is_homomorphism :=
      {
        homomorphism : forall a b,  phi (OP a b) = op (phi a) (phi b);

        is_homomorphism_phi_proper : Proper (respectful EQ eq) phi
      }.
    Global Existing Instance is_homomorphism_phi_proper.
    Context{phi_is_homomorphism: is_homomorphism}.
    Lemma homomorphism_sum l:
       eq (phi (sum OP ID l)) (sum op id (map phi l)).
    Proof.
      induction l.
      - simpl. admit.
      - simpl. rewrite homomorphism. rewrite IHl. reflexivity.
    Admitted.
    Lemma homomorphism_sum_from_to f a b:
      eq (phi (sum_from_to OP ID a b (fun i => f i))) (sum_from_to op id a b (fun i => phi (f i))).
    Proof.
      unfold sum_from_to. rewrite <-(map_map _ phi). apply homomorphism_sum.
    Qed.
 End Homomorphism.

Section m_prime.
  Context (m:positive).
  Context (prime_m: Znumtheory.prime (m)).
  Context (m_not_zero: (Z.pos m <> 0)%Z).
  Let sum_from_toZ := sum_from_to Z.add 0%Z.
  Let sum_from_to_F_m := sum_from_to (T:= F (m)) F.add 0%F.
  Let to_F_m := F.of_Z m.

  Local Notation "x ^ z" := (F.pow x (Z.to_N z)) : F_scope.

Lemma seq_from_to_same a:
  (seq_from_to a a) =  (a::nil).
Proof.
  unfold seq_from_to.
  replace (a+1-a) with 1 by omega.
  unfold downfrom.
  simpl. replace (a-0) with a by omega.
  reflexivity.
Qed.

Lemma seq_from_to_smaller a b:
  b < a -> seq_from_to a b = nil.
Proof.
  unfold seq_from_to.
  intros.
  replace (b+1-a) with 0 by omega.
  intuition eauto.
Qed.

Lemma seq_from_to_range a b:
  forall x, List.In x (seq_from_to a b) -> ((a <= x) /\ (x <= b))%nat.
Proof.
  destruct(dec (a <= b)).
  - intros. induction b.
    replace a with 0 in * by omega.
    cbv in H.
    omega.

    simpl in H.
    destruct(dec (a = S b)); subst.
    rewrite seq_from_to_same in H.
    inversion H. omega. inversion H0.

    specialize_by omega.
    Print Ltac specialize_by'.
    rewrite seq_from_to_S_r in H.
    destruct(dec (x = S b));subst.
    omega.
    apply in_app_or in H.
    destruct H.
    intuition eauto.
    destruct H.
    omega.
    destruct H.
    omega.

  - rewrite seq_from_to_smaller.
    intros. destruct H. omega.
Qed.

Lemma sum_from_to_change_func {T} (add:T->T->T) (zero:T) a b f g (H : forall i, (a <= i)%nat -> (i <= b)%nat -> f i = g i):
  sum_from_to add zero a b f = sum_from_to add zero a b g.
Proof.
  unfold sum_from_to.
  f_equal.
  pose proof seq_from_to_range a b as HI.
  eapply List.Forall_forall in HI.
  induction HI.
  reflexivity.
  simpl map. f_equal.
  - eapply H; omega.
  - eassumption.
Qed.

(* TODO(andreser): move this to ModularArithmeticTheorems so others can use it as well *)
Lemma F_pow_succ (r: F m) (n:N) : (F.pow r (N.succ n))%F = ((F.pow r  n) * r)%F.
Proof.
  rewrite <- N.add_1_r. rewrite F.pow_add_r. rewrite F.pow_1_r. reflexivity.
Qed.


  Definition Poly_m (c: nat -> Z) (r : Z) (q:nat): F (m)
  := sum_from_to_F_m 1 q (fun i => (to_F_m (c i)) * (to_F_m r)^(Z.of_nat q + 1 - Z.of_nat i)%Z)%F.

Fixpoint sum_times_F_m (q:nat) (r:Z) (c: nat -> Z): F (m) :=
  match q with
  | 0%nat => to_F_m 0
  | S q' => ((sum_times_F_m q' r c) + to_F_m (c q)) * (to_F_m r)
  end.
Definition Poly_m' (c: nat -> Z) (r : Z) (q :nat): F (m)
  := (sum_times_F_m q r c).

Theorem check_poly_m c r q : Poly_m c r q = Poly_m' c r q.
Proof.
  unfold Poly_m, Poly_m'.
  induction q.
  - apply left_more_sum.
    omega.
  - simpl sum_times_F_m.
    unfold sum_from_to_F_m.
    rewrite sum_one_more.
    setoid_rewrite Nat2Z.inj_succ.
    setoid_rewrite (Z.add_succ_l (Z.of_nat q) 1).
    replace (Z.succ (Z.of_nat q + 1) - Z.succ (Z.of_nat q))%Z with 1%Z by omega.
    setoid_rewrite Z.sub_succ_l at 1.

    (* TODO: debug setoid_rewrite, then use setoid_rewrite here *)
    pose (F_pow_succ (to_F_m r)).
    etransitivity.
    eapply f_equal2.
    eapply sum_from_to_change_func.
    SearchAbout N.add F.pow.
    SearchAbout Z.succ N.succ.
    intros.
    rewrite Z2N.inj_succ.
    rewrite F_pow_succ.
    pose proof (associative(op:=@F.mul m)) as RW; rewrite RW. (* TODO(jgross): why do we need to pose proof this? *)
    reflexivity.

    omega.

    rewrite F.pow_1_r. reflexivity.

    rewrite <-(@homomorphism_sum_from_to
          _ _ _ _ _
          _ _ _ _ _
          (fun x : F (m) => (x * to_F_m r)%F)).
    unfold sum_from_to_F_m in IHq.
    rewrite IHq.
    (* TODO(andreser): use fsatz here*)
    IntegralDomain.nsatz; eapply one_neq_zero.

    split; intros; ((IntegralDomain.nsatz; eapply one_neq_zero) || exact _).
    omega.
Qed.

Lemma F_powZ_of_Z (x n:Z) : (1 <= n)%Z -> ((F.of_Z m x)^n)%F = F.of_Z m (x^n)%Z.
Proof.
  intros. rewrite F.of_Z_pow.
  rewrite <- F.of_Z_mod.
  repeat f_equal. rewrite Z2N.id. reflexivity.
  omega.
Qed.

(* TODO(andreser): do we want to move these somewhere more common? *)
Local Instance monoid_Z_mod {m} (H:m<>0%Z):
  @monoid Z (fun a b : Z => (a mod m)%Z = (b mod m)%Z) Z.add 0%Z.
Proof.
  all:repeat split; cbv [Proper respectful Symmetric Transitive] in *; intros; subst; try congruence.
  - f_equal. omega.
  - f_equal. omega.
  - rewrite Z.add_mod.
    rewrite H0,H1.
    rewrite <- Z.add_mod.
    reflexivity.
    apply H. apply H.
Qed.
Local Instance mod_is_homomorphism {m} (H:m<>0%Z):
  @is_homomorphism Z (fun a b : Z => (a mod m)%Z = (b mod m)%Z) Z.add Z
   (fun a b : Z => (a mod m)%Z = (b mod m)%Z) Z.add (fun x : Z => (x mod m)%Z).
Proof.
  all:repeat split; cbv [Proper respectful Symmetric Transitive] in *; intros; subst; try congruence.
  rewrite <- Z.add_mod. rewrite <- Pre.Z_mod_mod. reflexivity.
  apply H.
Qed.
Local Instance Fm_is_homomorphism {m} :
  @is_homomorphism (F m) (@eq (F m)) (@F.add m) Z (fun a b : Z => (a mod m)%Z = (b mod m)%Z)
   Z.add (@F.to_Z m).
Proof.
  all:repeat split; cbv [Proper respectful Symmetric Transitive] in *; intros; subst; try congruence.
  rewrite F.to_Z_add. rewrite <- Pre.Z_mod_mod. reflexivity.
Qed.

Theorem check_mod1305 c r q :
                           (* TODO: give this a name, move to a spec file *)
  F.to_Z (Poly_m c r q) =  (sum_from_toZ 1 q (fun i => (c i) * r^(Z.of_nat q + 1 - Z.of_nat i)) mod (m))%Z.
Proof.
  unfold Poly_m, sum_from_to_F_m, sum_from_toZ.
  rewrite <-F.mod_to_Z.
  cbv beta delta [to_F_m].
  (*all:set (m := (2^130-5)%Z) in *.*)
  erewrite (fun pf => @homomorphism_sum_from_to
          _ _ _ _ _
          _ (fun a b => Logic.eq (a mod m)%Z (b mod m)%Z) Z.add Z.zero pf
          (F.to_Z)).
  etransitivity.
  - eapply f_equal2; [|reflexivity].
    eapply sum_from_to_change_func.
    intros.
    setoid_rewrite (F_powZ_of_Z (r) (Z.of_nat q + 1 - Z.of_nat i)).
    reflexivity.
    omega.
  - (* TODO(jgross): why does setoid_rewrite <-F.of_Z_mul not work here *)
    etransitivity.
    eapply f_equal2.
    eapply Proper_sum_from_to. reflexivity. reflexivity.
    intro.
    rewrite <-F.of_Z_mul.
    reflexivity.
    reflexivity.
    setoid_rewrite (F.to_Z_of_Z (c _ * _)).
    erewrite <- (fun pf => @homomorphism_sum_from_to
             _ _ _ _ _
             _ (fun a b => Logic.eq (a mod m)%Z (b mod m)%Z) _ _ pf
             (fun x: Z =>(x mod m)%Z)).
    rewrite Zmod_mod.
    reflexivity.
    apply monoid_Z_mod. trivial.
    apply mod_is_homomorphism. trivial.
  - apply monoid_Z_mod. trivial.
  - apply Fm_is_homomorphism.
Qed.