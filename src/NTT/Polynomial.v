From Coq Require Import List Permutation.
From Coq Require Program.Tactics Program.Wf.
From Coq.Classes Require Import Morphisms.
From Crypto.Util Require Import Decidable ListUtil.
From Crypto.Algebra Require Import Hierarchy Ring Field.

Section Permutation_fold_right.
  (* TODO: move to ListUtil *)
  Lemma fold_right_permutation {A B} (R:B->B->Prop) `{RelationClasses.Equivalence B R}
    (f:A->B->B) (b: B) `{Hf : forall x, Morphisms.Proper (Morphisms.respectful R R) (f x)} (l1 l2: list A):
    (forall j1 a1 j2 a2 b,
        j1 <> j2 -> nth_error l1 j1 = Some a1 -> nth_error l1 j2 = Some a2 ->
        R (f a1 (f a2 b)) (f a2 (f a1 b))) ->
    Permutation l1 l2 -> R (fold_right f b l1) (fold_right f b l2).
  Proof.
    intros Hf'. induction 1.
    - simpl. reflexivity.
    - simpl. rewrite IHPermutation; [reflexivity|].
      intros. apply (Hf' (S j1) _ (S j2)); auto.
    - simpl. apply (Hf' O _ (S O)); auto.
    - etransitivity.
      + apply IHPermutation1, Hf'.
      + apply IHPermutation2. intros j1 a1 j2 a2 b' ? ? ?.
        destruct (proj1 (Permutation_nth_error _ _) H0_) as (Hlen & g & Hinj & Hg).
        apply (Hf' (g j1) _ (g j2)); try rewrite <- Hg; auto.
  Qed.
End Permutation_fold_right.
Section NoDup.
  (* TODO: move to ListUtil *)
  Lemma NoDup_app {A} (l1 l2: list A):
    NoDup (l1 ++ l2) <-> NoDup l1 /\ (forall x, In x l1 -> ~ In x l2) /\ NoDup l2.
  Proof.
    induction l1; simpl.
    - split; intros.
      + split; [apply NoDup_nil|].
        split; auto.
      + destruct H as (? & ? & ?); auto.
    - split; intros.
      + inversion H; subst; clear H.
        apply IHl1 in H3. destruct H3 as (? & ? & ?).
        split; [apply NoDup_cons; auto; intro; apply H2; apply in_app_iff; left; auto|].
        split; auto.
        intros. destruct H3 as [<-|?]; [|apply H0; auto].
        intro; apply H2. apply in_app_iff; right; auto.
      + destruct H as (Hl1 & Hin & Hl2).
        inversion Hl1; subst; clear Hl1.
        apply NoDup_cons; [|apply IHl1; repeat split; auto].
        intro X. apply in_app_iff in X. destruct X; [elim H1; auto|].
        eapply Hin; eauto.
  Qed.
  Lemma NoDup_map {A B} (l: list A) (f: A -> B):
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
  Proof.
    intro Hinj. induction 1; [apply NoDup_nil|].
    simpl. apply NoDup_cons.
    - intro Hin. apply in_map_iff in Hin.
      destruct Hin as (y & Heq & Hin).
      apply H. rewrite (Hinj x y); auto.
      left; auto. right; auto.
    - apply IHNoDup. intros; apply Hinj; auto; right; auto.
  Qed.
End NoDup.
Section Forall2.
  Global Instance Forall2_Equivalence {A: Type} {R} `{Equivalence A R}:
    Equivalence (Forall2 R).
  Proof.
    constructor.
    - intro. destruct x; [constructor|].
      rewrite (Forall2_forall_iff _ _ _ a a ltac:(reflexivity)).
      intros. reflexivity.
    - intros x y He. induction He; [constructor|].
      constructor; auto. symmetry; auto.
    - intros x y z Hl. revert z. induction Hl; intros; auto.
      inversion H1; subst; clear H1. constructor; auto.
      transitivity y; auto.
  Qed.
  Lemma Forall2_Forall_combine {A B: Type} (R: A -> B -> Prop) (l1: list A) (l2: list B):
    Forall2 R l1 l2 ->
    Forall (fun '(a, b) => R a b) (combine l1 l2).
  Proof. induction 1; intros; simpl; constructor; auto. Qed.
  Lemma Forall2_app_inv {A B: Type} (R: A -> B -> Prop) (l1 l2: list A) (l1' l2': list B):
    length l1 = length l1' ->
    Forall2 R (l1 ++ l2) (l1' ++ l2') ->
    Forall2 R l1 l1' /\ Forall2 R l2 l2'.
  Proof.
    revert l1' l2 l2'. induction l1; simpl; intros l1' l2 l2' Hl HF.
    - symmetry in Hl; apply length0_nil in Hl; subst l1'.
      simpl in HF. split; [constructor|auto].
    - destruct l1' as [|b l1']; [simpl in Hl; congruence|].
      simpl in Hl. simpl in HF. inversion HF; subst; clear HF.
      split; [constructor; auto|]; apply (IHl1 l1' l2 l2' ltac:(congruence) H4).
  Qed.
End Forall2.

Section Bigop.
  Context {A:Type} {eq:A->A->Prop} {op:A->A->A} {id:A} {inv:A->A} {group: @commutative_group A eq op id inv}.

  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.

  (* Iteratively apply op over a sequence indexed by a list of indices of some type I *)
  Definition bigop {I} (idx: list I) (f: I -> A) :=
    List.fold_right (fun i x => op (f i) x) id idx.

  Lemma bigop_ext_eq {I} (idx: list I) (f g: I -> A):
    (forall i, In i idx -> f i = g i) ->
    bigop idx f = bigop idx g.
  Proof.
    induction idx; [reflexivity|].
    intros Hi; simpl.
    rewrite (Hi a) by (left; reflexivity).
    rewrite IHidx; [reflexivity|].
    intros; apply Hi; right; auto.
  Qed.

  Lemma bigop_index_change {I I'} (idx: list I) (f: I' -> A) (phi: I -> I'):
    bigop (List.map phi idx) f = bigop idx (fun i => f (phi i)).
  Proof.
    induction idx; [reflexivity|].
    simpl. rewrite IHidx. reflexivity.
  Qed.

  Lemma bigop_index_change_inj {I I'} (idx: list I) (f: I -> A)
    (phi: I -> I') (psi: I' -> I)
    (Hinj: forall i, List.In i idx -> psi (phi i) = i :> I):
    bigop idx f = bigop (List.map phi idx) (fun i => f (psi i)).
  Proof.
    rewrite bigop_index_change. apply bigop_ext_eq.
    intros; rewrite Hinj by assumption; reflexivity.
  Qed.

  Lemma bigop_shift a b len f:
    bigop (seq a len) f = bigop (seq (a + b) len) (fun i => (f (i - b))).
  Proof.
    assert (seq (a + b) len = map (fun i => i + b) (seq a len) :> _) as ->.
    { induction b.
      - rewrite PeanoNat.Nat.add_0_r.
        rewrite (map_ext _ Datatypes.id); [|intros; rewrite PeanoNat.Nat.add_0_r; reflexivity].
        rewrite map_id. reflexivity.
      - assert (a + S b = S (a + b) :> _) as -> by Lia.lia.
        rewrite <- seq_shift, IHb, map_map.
        apply map_ext. intros; Lia.lia. }
    rewrite bigop_index_change.
    apply bigop_ext_eq; intros.
    assert (i + b - b = i :> _) as -> by Lia.lia. reflexivity.
  Qed.

  Lemma bigop_nil {I} (f: I -> A):
    bigop nil f = id.
  Proof. reflexivity. Qed.

  Lemma bigop_app {I} (f: I -> A) idx1 idx2:
    bigop (idx1 ++ idx2) f = op (bigop idx1 f) (bigop idx2 f).
  Proof.
    induction idx1; simpl.
    - symmetry; apply left_identity.
    - rewrite IHidx1. apply associative.
  Qed.

  Lemma bigop_cons {I} (f: I -> A) i idx:
    bigop (i::idx) f = op (f i) (bigop idx f).
  Proof. reflexivity. Qed.

  Lemma bigop_same_index {I} (f g: I -> A) idx:
    op (bigop idx f) (bigop idx g) = bigop idx (fun i => op (f i) (g i)).
  Proof.
    induction idx; simpl; [apply left_identity|].
    rewrite <- IHidx. repeat rewrite associative.
    rewrite <- (associative _ _ (g a)).
    rewrite (commutative _ (g a)).
    rewrite associative. reflexivity.
  Qed.

  Lemma bigop_permutation {I} (f: I -> A) idx1 idx2:
    Permutation idx1 idx2 ->
    bigop idx1 f = bigop idx2 f.
  Proof.
    intros. unfold bigop. apply fold_right_permutation; auto; try typeclasses eauto.
    - intros. intros a b Heq. rewrite Heq; reflexivity.
    - intros. rewrite (associative (f a1)), (commutative (f a1)), <- (associative (f a2)).
      reflexivity.
  Qed.

  Lemma bigop_rev {I} (f: I -> A) idx:
    bigop (rev idx) f = bigop idx f.
  Proof. symmetry; apply bigop_permutation, Permutation_rev. Qed.

  Lemma bigop_flatten {I I'} (idx: list I) (idx': I -> list I') (f: I -> I' -> A):
    bigop idx (fun i => bigop (idx' i) (fun j => f i j)) =
    bigop (flat_map (fun i => List.map (fun j => (i, j)) (idx' i)) idx) (fun '(i, j) => f i j).
  Proof.
    induction idx; [reflexivity|].
    simpl. rewrite bigop_app.
    rewrite IHidx.
    assert ((bigop (idx' a) (fun j : I' => f a j)) = (bigop (map (fun j : I' => (a, j)) (idx' a)) (fun '(i, j) => f i j))) as ->; [|reflexivity].
    clear IHidx. induction (idx' a); [reflexivity|].
    simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma bigop_flatten_index_char {I I'} (idx: list I) (idx': I -> list I'):
    forall i j, In (i, j) (flat_map (fun i => List.map (fun j => (i, j)) (idx' i)) idx) <-> (In i idx /\ In j (idx' i)).
  Proof.
    intros i j; split; [intros H|intros [HA HB]].
    - apply in_flat_map in H. destruct H as (x & Hin & Hinm).
      apply in_map_iff in Hinm. destruct Hinm as (? & Heq & ?).
      inversion Heq; subst; clear Heq; split; auto.
    - apply in_flat_map.
      exists i. split; auto. apply in_map; auto.
  Qed.

  Lemma bigop_inv {I} (idx: list I) f:
    inv (bigop idx f) = bigop idx (fun i => inv (f i)).
  Proof.
    induction idx; simpl;[apply Group.inv_id|].
    rewrite <- IHidx, Group.inv_op, commutative. reflexivity.
  Qed.

  Context {one:A}{sub mul:A->A->A}{ring:@ring A eq id one inv op sub mul}.

  Lemma bigop_const {I} (idx: list I) (a:A):
    bigop idx (fun _ => a) = mul (bigop idx (fun _ => one)) a.
  Proof.
    induction idx; simpl; [rewrite mul_0_l; reflexivity|].
    rewrite IHidx. rewrite right_distributive.
    rewrite left_identity. reflexivity.
  Qed.

  Lemma bigop_l_distr {I} (idx: list I) (a: A) (f: I->A):
    mul a (bigop idx f) = bigop idx (fun i => mul a (f i)).
  Proof.
    induction idx; simpl.
    - apply mul_0_r.
    - rewrite left_distributive, IHidx. reflexivity.
  Qed.

  Lemma bigop_r_distr {I} (idx: list I) (a: A) (f: I->A):
    mul (bigop idx f) a = bigop idx (fun i => mul (f i) a).
  Proof.
    induction idx; simpl.
    - apply mul_0_l.
    - rewrite right_distributive, IHidx. reflexivity.
  Qed.

  Lemma bigop_widen {I} (f: I -> A) idx1 idx2:
    (forall i, In i idx2 -> f i = id) ->
     bigop idx1 f = bigop (idx1 ++ idx2) f.
  Proof.
    intros Hi. rewrite bigop_app.
    rewrite (bigop_ext_eq idx2 _ (fun _ => id) Hi).
    rewrite bigop_const, mul_0_r, right_identity.
    reflexivity.
  Qed.
End Bigop.

Section Polynomial.
  (* We define univariate polynomials with coefficients defined over a commutative ring. *)
  Context {F:Type}{Feq:F->F->Prop}{Fzero Fone:F}{Fopp:F->F}{Fadd Fsub Fmul:F->F->F}
    {cring:@commutative_ring F Feq Fzero Fone Fopp Fadd Fsub Fmul}
    {Feq_dec:DecidableRel Feq}.

  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero. Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul.

  Class polynomial_ops {P: Type} :=
    {
      Pzero: P;
      Pone: P;
      coeff: P -> nat -> F;
      degree: P -> option nat;
      Popp: P -> P;
      Padd: P -> P -> P;
      Psub: P -> P -> P;
      Pmul: P -> P -> P;
      base: nat -> P;
      Pconst: F -> P
    }.

  Definition Peq {P} `{@polynomial_ops P} (p1 p2: P): Prop :=
    forall k, coeff p1 k = coeff p2 k.

  Definition mul_coeff (f1 f2: nat -> F) (n: nat): F :=
    @bigop _ Fadd Fzero _ (List.seq 0%nat (S n)) (fun i => f1 i * f2 (n - i)%nat).

  Context {P} {Poly_ops: @polynomial_ops P}.

  Class is_zero_definition :=
    { zero_definition : forall k, coeff Pzero k = 0 }.
  Class is_one_definition :=
    { one_definition : forall k, coeff Pone k = match k with O => 1 | _ => 0 end }.
  Class is_degree_definition :=
    { degree_definition : forall p, match degree p with
                               | None => forall k, coeff p k = 0
                               | Some n => coeff p n <> 0 /\ forall k, k > n -> coeff p k = 0
                               end }.
  Class is_opp_definition :=
    { opp_definition : forall p k, coeff (Popp p) k = Fopp (coeff p k) }.
  Class is_add_definition :=
    { add_definition : forall p1 p2 k, coeff (Padd p1 p2) k = coeff p1 k + coeff p2 k }.
  Class is_sub_definition :=
    { sub_definition : forall p1 p2 k, coeff (Psub p1 p2) k = coeff p1 k - coeff p2 k }.
  Class is_mul_definition :=
    { mul_definition : forall p1 p2 k, coeff (Pmul p1 p2) k = mul_coeff (coeff p1) (coeff p2) k }.
  Class is_base_definition :=
    { base_definition: forall n k, coeff (base n) k = if dec_eq_nat n k then 1 else 0 }.
  Class is_const_definition :=
    { const_definition: forall c k, coeff (Pconst c) k = match k with 0%nat => c | _ => 0 end }.

  Class polynomial_defs :=
    {
      polynomial_is_zero_definition: is_zero_definition;
      polynomial_is_one_definition: is_one_definition;
      polynomial_is_degree_definition : is_degree_definition;
      polynomial_is_opp_definition: is_opp_definition;
      polynomial_is_add_definition: is_add_definition;
      polynomial_is_sub_definition: is_sub_definition;
      polynomial_is_mul_definition: is_mul_definition;
      polynomial_is_base_definition: is_base_definition;
      polynomial_is_const_definition: is_const_definition;
    }.

  Global Existing Instance polynomial_is_zero_definition.
  Global Existing Instance polynomial_is_one_definition.
  Global Existing Instance polynomial_is_degree_definition.
  Global Existing Instance polynomial_is_opp_definition.
  Global Existing Instance polynomial_is_add_definition.
  Global Existing Instance polynomial_is_sub_definition.
  Global Existing Instance polynomial_is_mul_definition.
  Global Existing Instance polynomial_is_base_definition.
  Global Existing Instance polynomial_is_const_definition.

End Polynomial.

Section Theorems.
  Context {F:Type}{Feq:F->F->Prop}{Fzero Fone:F}{Fopp:F->F}{Fadd Fsub Fmul:F->F->F}
    {cring:@commutative_ring F Feq Fzero Fone Fopp Fadd Fsub Fmul}
    {Feq_dec:DecidableRel Feq}.

  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero. Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul.

  Context {P} {poly_ops: @polynomial_ops F P} {poly_defs: @polynomial_defs F Feq Fzero Fone Fopp Fadd Fsub Fmul P poly_ops}.

  Local Notation Peq := (@Peq F Feq P poly_ops).
  Local Notation mul_coeff := (@mul_coeff F Fzero Fadd Fmul).

  Definition lead_coeff p: F :=
    match degree p with
    | None => 0
    | Some n => coeff p n
    end.

  Definition is_monic p: Prop :=
    lead_coeff p = 1.

  Section Degree.
    Definition convert (x: option nat): nat := match x with None => 0%nat | Some n => S n end.
    Definition measure p := convert (degree p).
    Lemma measure_definition p k:
      (measure p <= k)%nat ->
      coeff p k = 0.
    Proof.
      generalize (degree_definition p); unfold measure, convert.
      destruct (degree p); [intros [A B] Hle|intros A Hle].
      - apply B; Lia.lia.
      - apply A.
    Qed.
    Definition degree_le (d1 d2: option nat): Prop := (convert d1 <= convert d2)%nat.
    Global Instance degree_le_dec: DecidableRel degree_le := fun x y => dec_le_nat (convert x) (convert y).
    Global Instance degree_le_preorder: PreOrder degree_le.
    Proof. constructor; intro; unfold degree_le; intros; [|etransitivity]; eauto. Qed.
    Definition degree_lt (d1 d2: option nat): Prop := (convert d1 < convert d2)%nat.
    Global Instance degree_lt_dec: DecidableRel degree_lt := fun x y => dec_lt_nat (convert x) (convert y).
    Global Instance degree_lt_strorder: StrictOrder degree_lt.
    Proof. constructor; intro; unfold degree_lt; intro; simpl; Lia.lia. Qed.
    Definition degree_max (d1 d2: option nat): option nat :=
      if degree_lt_dec d1 d2 then d2 else d1.
    Definition degree_add (d1 d2: option nat): option nat :=
      Option.map2 Nat.add d1 d2.
    Lemma degree_add_0_l d:
      degree_add (Some 0%nat) d = d :> _.
    Proof. destruct d; reflexivity. Qed.
    Lemma degree_add_0_r d:
      degree_add d (Some 0%nat) = d :> _.
    Proof. destruct d; simpl; [rewrite <- plus_n_O|]; reflexivity. Qed.
    Lemma degree_max_lub:
      forall x y z, degree_le x z -> degree_le y z -> degree_le (degree_max x y) z.
    Proof.
      unfold degree_le, degree_max, degree_lt_dec, convert.
      intros. destruct x, y, z; destruct (dec_lt_nat _ _); Lia.lia.
    Qed.
    Lemma degree_max_lub_lt:
      forall x y z, degree_lt x z -> degree_lt y z -> degree_lt (degree_max x y) z.
    Proof.
      unfold degree_lt, degree_max, degree_lt_dec, convert.
      intros. destruct x, y, z; simpl in *; try Lia.lia.
      destruct (dec_lt_nat _ _); Lia.lia.
    Qed.
    Lemma degree_le_lt_trans:
      forall x y z, degree_le x y -> degree_lt y z -> degree_lt x z.
    Proof. unfold degree_le, degree_lt, convert; intros; destruct x, y, z; Lia.lia. Qed.
    Lemma degree_lt_le_trans:
      forall x y z, degree_lt x y -> degree_le y z -> degree_lt x z.
    Proof. unfold degree_le, degree_lt, convert; intros; destruct x, y, z; Lia.lia. Qed.
    Lemma degree_lt_add_mono_l p q r (Hr: r <> None :> _):
      degree_lt p q ->
      degree_lt (degree_add r p) (degree_add r q).
    Proof. destruct p, q, r; unfold degree_lt; simpl; try Lia.lia; congruence. Qed.
    Lemma degree_char:
      forall p n,
        coeff p n <> 0 ->
        (forall k, k > n -> coeff p k = 0) ->
        degree p = Some n :> _.
    Proof.
      intros p n HA HB.
      generalize (degree_definition p); intro HC.
      destruct (degree p) as [np|] eqn:Hp; [|rewrite HC in HA; elim HA; reflexivity].
      destruct HC as (HC1 & HC2).
      assert (n = np :> _ \/ n < np \/ np < n) as [<- | [Hn | Hn]] by Lia.lia; auto.
      - rewrite HB in HC1 by Lia.lia. elim HC1; reflexivity.
      - rewrite HC2 in HA by Lia.lia. elim HA; reflexivity.
    Qed.
    Global Instance peq_proper_degree: Proper (Peq ==> eq) degree.
    Proof.
      intros p1 p2 Heq.
      generalize (degree_definition p1); intro Hp1.
      generalize (degree_definition p2); intro Hp2.
      destruct (degree p1) eqn:Heq1.
      - destruct Hp1 as (Hp1 & Hp1').
        symmetry; apply degree_char.
        + rewrite <- (Heq n). assumption.
        + intros k Hk. rewrite <- (Heq k). apply Hp1'; auto.
      - destruct (degree p2) eqn:Heq2.
        + destruct Hp2 as (Hp2 & Hp2').
          elim Hp2. rewrite <- (Heq n). apply Hp1.
        + reflexivity.
    Qed.
    Lemma degree_zero:
      degree Pzero = None :> _.
    Proof.
      generalize (degree_definition Pzero); destruct (degree Pzero) eqn:Hz; [|reflexivity].
      rewrite zero_definition. intros (A & B); elim A; reflexivity.
    Qed.
    Lemma zero_degree p:
      degree p = None :> _ -> Peq p Pzero.
    Proof.
      intro A; generalize (degree_definition p); rewrite A.
      intros B k; rewrite B, zero_definition; reflexivity.
    Qed.
    Lemma degree_max_id d:
      degree_max d d = d :> _.
    Proof.
      unfold degree_max. destruct (degree_lt_dec d d) as [H|H]; [|reflexivity].
      apply StrictOrder_Irreflexive in H. tauto.
    Qed.
    Lemma opp_degree:
      forall p, degree p = degree (Popp p) :> _.
    Proof.
      intros. generalize (degree_definition p); intro Hp.
      destruct (degree p) eqn:Heq.
      - destruct Hp as (Hp1 & Hp2).
        symmetry; apply degree_char.
        + rewrite opp_definition. intro Hx.
          apply Hp1. apply Group.inv_id_iff; auto.
        + intros k Hk. rewrite opp_definition.
          rewrite Hp2; auto.
          apply Group.inv_id.
      - generalize (degree_definition (Popp p)); intro Hp'.
        destruct (degree (Popp p)) eqn:Heq'; [|reflexivity].
        destruct Hp' as (Hp' & _).
        elim Hp'.
        rewrite opp_definition, Hp. apply Group.inv_id.
    Qed.
    Lemma add_degree:
      forall p1 p2, degree_le (degree (Padd p1 p2)) (degree_max (degree p1) (degree p2)).
    Proof.
      intros. generalize (degree_definition p1); intro Hp1.
      generalize (degree_definition p2); intro Hp2.
      generalize (degree_definition (Padd p1 p2)); intro Hadd.
      destruct (degree p1), (degree p2), (degree (Padd p1 p2)); simpl; unfold degree_max, degree_le, degree_lt_dec, convert; destruct (dec_lt_nat _ _); simpl; try Lia.lia; rewrite add_definition in Hadd; destruct Hadd as (Hadd1 & Hadd2).
      - destruct Hp1 as (Hp1 & Hp1').
        destruct Hp2 as (Hp2 & Hp2').
        destruct (dec_le_nat n1 n0); [Lia.lia|].
        assert (Hin1: coeff p1 n1 = 0) by (apply Hp1'; Lia.lia).
        assert (Hin2: coeff p2 n1 = 0) by (apply Hp2'; Lia.lia).
        rewrite Hin1, Hin2 in Hadd1.
        elim Hadd1. apply left_identity.
      - destruct Hp1 as (Hp1 & Hp1').
        destruct Hp2 as (Hp2 & Hp2').
        destruct (dec_le_nat n1 n); [Lia.lia|].
        assert (Hin1: coeff p1 n1 = 0) by (apply Hp1'; Lia.lia).
        assert (Hin2: coeff p2 n1 = 0) by (apply Hp2'; Lia.lia).
        rewrite Hin1, Hin2 in Hadd1.
        elim Hadd1. apply left_identity.
      - destruct Hp1 as (Hp1 & Hp1').
        rewrite Hp2, right_identity in Hadd1.
        destruct (dec_le_nat n0 n); [Lia.lia|].
        elim Hadd1. apply Hp1'. Lia.lia.
      - destruct Hp2 as (Hp2 & Hp2').
        rewrite Hp1, left_identity in Hadd1.
        destruct (dec_le_nat n0 n); [Lia.lia|].
        elim Hadd1. apply Hp2'. Lia.lia.
      - elim Hadd1. rewrite Hp1, Hp2. apply left_identity.
    Qed.
    Lemma sub_degree:
      forall p1 p2, degree_le (degree (Psub p1 p2)) (degree_max (degree p1) (degree p2)).
    Proof.
      intros; assert (Peq (Psub p1 p2) (Padd p1 (Popp p2))) as ->.
      - intro k. rewrite sub_definition, add_definition, opp_definition.
        apply cring.(commutative_ring_ring).(ring_sub_definition).
      - rewrite (opp_degree p2).
        apply add_degree.
    Qed.
    Lemma mul_coeff_hi p1 p2 n1 n2
      (Hp1: degree p1 = Some n1 :> _) (Hp2: degree p2 = Some n2 :> _):
      coeff (Pmul p1 p2) (n1 + n2)%nat = coeff p1 n1 * coeff p2 n2 /\
      (forall k : nat, k > (n1 + n2)%nat -> coeff (Pmul p1 p2) k = 0).
    Proof.
      generalize (degree_definition p1); rewrite Hp1; intros (Hd1 & Hd1').
      generalize (degree_definition p2); rewrite Hp2; intros (Hd2 & Hd2').
      split; intros; rewrite mul_definition; unfold mul_coeff.
      1: assert (S (n1 + n2) = S n1 + n2 :> nat)%nat as -> by Lia.lia.
      2: assert (S k = S n1 + (n2 + (k - (n1 + n2))) :> nat)%nat as -> by Lia.lia.
      all: rewrite seq_app, seq_S; repeat rewrite bigop_app.
      all: rewrite (bigop_ext_eq (seq 0 n1) _ (fun _ => 0)) by (intros i Hi; rewrite in_seq in Hi; rewrite Hd2' by Lia.lia; apply mul_0_r).
      all: rewrite bigop_const; rewrite mul_0_r, left_identity.
      all: rewrite (bigop_ext_eq (seq _ _) _ (fun _ => 0)) by (intros i Hi; rewrite in_seq in Hi; rewrite Hd1' by Lia.lia; apply mul_0_l).
      all: rewrite bigop_const; rewrite mul_0_r, right_identity.
      all: simpl; rewrite right_identity.
      1: assert (n1 + n2 - n1 = n2 :> nat)%nat as -> by Lia.lia.
      2: rewrite Hd2' by Lia.lia; rewrite mul_0_r.
      all: reflexivity.
    Qed.
    (* We only have equality when we are in an integral domain, as it is otherwise possible that lead_coeff p * lead_coeff q = 0 *)
    Lemma mul_degree_le:
      forall p1 p2, degree_le (degree (Pmul p1 p2)) (degree_add (degree p1) (degree p2)).
    Proof.
      intros. generalize (degree_definition p1); intro Hp1.
      generalize (degree_definition p2); intro Hp2.
      generalize (degree_definition (Pmul p1 p2)); intro Hmul.
      destruct (degree p1) eqn:H1.
      2:{ simpl. destruct (degree (Pmul p1 p2)); simpl; [|reflexivity].
          rewrite mul_definition in Hmul. destruct Hmul as (Hmul1 & Hmul2).
          elim Hmul1. unfold mul_coeff.
          rewrite (bigop_ext_eq _ _ (fun _ => 0)) by (intros; rewrite Hp1; apply mul_0_l).
          rewrite bigop_const. apply mul_0_r. }
      destruct (degree p2) eqn:H2.
      2:{ simpl. destruct (degree (Pmul p1 p2)); simpl; [|reflexivity].
          rewrite mul_definition in Hmul. destruct Hmul as (Hmul1 & Hmul2).
          elim Hmul1. unfold mul_coeff.
          rewrite (bigop_ext_eq _ _ (fun _ => 0)) by (intros; rewrite Hp2; apply mul_0_r).
          rewrite bigop_const. apply mul_0_r. }
      destruct (degree (Pmul p1 p2)) eqn:Hp; unfold degree_le, convert; simpl; [|Lia.lia].
      destruct Hmul as (Hmul1 & Hmul2).
      destruct (mul_coeff_hi p1 p2 _ _ H1 H2) as (_ & HA).
      destruct (dec_le_nat n1 (n + n0)%nat); try Lia.lia.
      elim Hmul1. apply HA; Lia.lia.
    Qed.
    Lemma mul_degree_eq `{HID: @Hierarchy.integral_domain F Feq Fzero Fone Fopp Fadd Fsub Fmul}:
      forall p1 p2, degree (Pmul p1 p2) = degree_add (degree p1) (degree p2) :> _.
    Proof.
      intros. generalize (mul_degree_le p1 p2). intro Hmul_le.
      destruct (degree p1) eqn:Hp1.
      2:{ destruct (degree (Pmul p1 p2)); simpl in *; [|reflexivity].
          unfold degree_le in *. simpl in *; Lia.lia. }
      destruct (degree p2) eqn:Hp2.
      2:{ destruct (degree (Pmul p1 p2)); simpl in *; [|reflexivity].
          unfold degree_le in *. simpl in *; Lia.lia. }
      simpl. generalize (mul_coeff_hi _ _ _ _ Hp1 Hp2). intros (Hmul1 & Hmul2).
      generalize (degree_definition p1); rewrite Hp1. intros (Hp1n & Heq1).
      generalize (degree_definition p2); rewrite Hp2. intros (Hp2n & Heq2).
      destruct (Feq_dec (coeff (Pmul p1 p2) (n + n0)) 0).
      { rewrite Hmul1 in f. apply zero_product_zero_factor in f.
        destruct f; tauto. }
      apply degree_char; auto.
    Qed.
    Lemma degree_one `{Hznone: @is_zero_neq_one F Feq Fzero Fone}:
      degree Pone = Some 0%nat :> _.
    Proof.
      apply degree_char.
      - rewrite one_definition. symmetry; apply zero_neq_one.
      - intros; rewrite one_definition. destruct k; [Lia.lia|reflexivity].
    Qed.
    Lemma is_monic_degree:
      forall p, is_monic p ->
           if (Feq_dec 0 1) then degree p = None :> _ else exists n, degree p = Some n :> _.
    Proof.
      intros p H. unfold is_monic, lead_coeff in H.
      generalize (degree_definition p); intros Hp.
      destruct (degree p).
      - rewrite H in Hp. destruct Hp as [Hznone Hp].
        destruct (Feq_dec 0 1); [elim Hznone; symmetry; auto| eauto].
      - destruct (Feq_dec 0 1); [reflexivity| contradiction].
    Qed.
  End Degree.

  Global Instance peq_proper_lead_coeff:
    Proper (Peq ==> Feq) lead_coeff.
  Proof.
    intros p p' Hp. unfold lead_coeff.
    rewrite Hp. destruct (degree p'); [|reflexivity].
    rewrite (Hp n). reflexivity.
  Qed.

  Global Instance peq_proper_is_monic:
    Proper (Peq ==> iff) is_monic.
  Proof.
    intros p1 p2 Hp; unfold is_monic.
    rewrite Hp. reflexivity.
  Qed.

  Global Instance Peq_dec: DecidableRel Peq.
  Proof.
    intros p q. generalize (degree_definition p); intros Hp.
    generalize (degree_definition q); intros Hq.
    destruct (degree p) as [np|] eqn:Heqp.
    - destruct (degree q) as [nq|] eqn:Heqq.
      + destruct (dec_eq_nat np nq).
        * subst np. destruct Hp as (Hp1 & Hp2).
          destruct Hq as (Hq1 & Hq2).
          set (check := fix loop n := match n with O => O | S n' => if Feq_dec (coeff p n') (coeff q n') then loop n' else n end).
          assert (Hcheck: forall n, match check n with
                               | O => forall k, (k < n)%nat -> coeff p k = coeff q k
                               | S n' => coeff p n' <> coeff q n' end).
          { clear. induction n.
            - simpl; intros. Lia.lia.
            - simpl. destruct (Feq_dec (coeff p n) (coeff q n)); auto.
              destruct (check n) eqn:Hn; auto.
              intros. destruct (dec_eq_nat k n); [subst k; auto|].
              apply IHn; Lia.lia. }
          specialize (Hcheck (S nq)); destruct (check (S nq)).
          { left. intro k. destruct (dec_lt_nat k (S nq)); [apply Hcheck; auto|].
            rewrite Hp2, Hq2 by Lia.lia. reflexivity. }
          { right. intro eq. apply Hcheck. apply eq. }
        * right. intro Heq. rewrite Heq in Heqp.
          rewrite Heqp in Heqq. apply n; congruence.
      + right. intro Heq. rewrite Heq in Heqp.
        rewrite Heqp in Heqq. congruence.
    - destruct (degree q) as [nq|] eqn:Heqq.
      + right. intro Heq. rewrite Heq in Heqp.
        rewrite Heqp in Heqq. congruence.
      + left. intro k; rewrite Hp, Hq. reflexivity.
  Qed.

  Section Pmul.
    Lemma mul_coeff_comm:
      forall f1 f2 n, mul_coeff f1 f2 n = mul_coeff f2 f1 n.
    Proof.
      intros. unfold mul_coeff.
      rewrite (bigop_index_change_inj _ _ (fun i => (n - i)%nat) (fun i => (n - i)%nat)).
      2: { intros i Hi. apply in_seq in Hi. Lia.lia. }
      rewrite (bigop_ext_eq _ _ (fun i : nat => f2 i * f1 (n - i)%nat)).
      2: { intros i Hi. apply in_map_iff in Hi.
           destruct Hi as (j & Hj & Hi).
           apply in_seq in Hi.
           assert (n - (n - i) = i :> nat)%nat as -> by Lia.lia.
           apply commutative_ring_is_commutative. }
      apply bigop_permutation.
      apply Permutation_nth with (d := (fun i : nat => (n - i)%nat) 0%nat).
      rewrite length_map, length_seq; split; [reflexivity|].
      exists (fun i => (n - i)%nat).
      split; [intro; Lia.lia|].
      split; [red; intros; Lia.lia|].
      intros. rewrite map_nth. do 2 rewrite seq_nth by Lia.lia.
      Lia.lia.
    Qed.

    Lemma mul_coeff_ext_eq_l:
      forall f1 f1' f2 n,
        (forall i, (i <= n)%nat -> f1 i = f1' i) ->
        mul_coeff f1 f2 n = mul_coeff f1' f2 n.
    Proof.
      intros. unfold mul_coeff.
      apply bigop_ext_eq. intros.
      apply in_seq in H0. rewrite (H i) by Lia.lia. reflexivity.
    Qed.

    Lemma mul_coeff_ext_eq_r:
      forall f1 f2 f2' n,
        (forall i, (i <= n)%nat -> f2 i = f2' i) ->
        mul_coeff f1 f2 n = mul_coeff f1 f2' n.
    Proof.
      intros. unfold mul_coeff.
      apply bigop_ext_eq. intros.
      apply in_seq in H0. rewrite (H (n - i)%nat) by Lia.lia. reflexivity.
    Qed.

    Lemma mul_coeff_left_identity f:
      forall n, mul_coeff (coeff Pone) f n = f n.
    Proof.
      unfold mul_coeff; simpl; intros.
      assert (n - 0 = n :> nat)%nat as -> by Lia.lia.
      rewrite one_definition, left_identity.
      rewrite bigop_ext_eq with (g := fun _ => 0).
      2:{ intros i Hi. apply in_seq in Hi.
          rewrite one_definition. destruct i; [Lia.lia|].
          apply mul_0_l. }
      assert (bigop (seq 1 n) (fun _ : nat => 0) = 0) as ->; [|apply right_identity].
      rewrite bigop_const, mul_0_r. reflexivity.
    Qed.

    Lemma mul_coeff_right_identity f:
      forall n, mul_coeff f (coeff Pone) n = f n.
    Proof.
      intros. rewrite mul_coeff_comm.
      apply mul_coeff_left_identity.
    Qed.

    Lemma mul_coeff_assoc:
      forall f1 f2 f3 n, mul_coeff f1 (mul_coeff f2 f3) n = mul_coeff (mul_coeff f1 f2) f3 n.
    Proof.
      intros. unfold mul_coeff.
      rewrite (bigop_ext_eq _ (fun i : nat => f1 i * bigop (seq 0 (S (n - i))) (fun i0 : nat => f2 i0 * f3 (n - i - i0)%nat)) (fun i : nat => @bigop _ Fadd Fzero _ (seq 0 (S (n - i))) (fun i0 : nat => f1 i * f2 i0 * f3 (n - i - i0)%nat))).
      2: { intros. rewrite bigop_l_distr; apply bigop_ext_eq.
           intros. apply associative. }
      rewrite (bigop_ext_eq _ (fun i : nat => bigop (seq 0 (S i)) (fun i0 : nat => f1 i0 * f2 (i - i0)%nat) * f3 (n - i)%nat) (fun i : nat => @bigop _ Fadd Fzero _ (seq 0 (S i)) (fun i0 : nat => f1 i0 * f2 (i - i0)%nat  * f3 (n - i)%nat))).
      2: { intros. rewrite bigop_r_distr; reflexivity. }
      do 2 rewrite bigop_flatten.
      assert (Hnd: forall f, NoDup (flat_map (fun i : nat => map (fun j : nat => (i, j)) (seq 0 (f i))) (seq 0 (S n)))).
      { intro f; induction n.
        - simpl. rewrite app_nil_r.
          apply NoDup_map; [|apply seq_NoDup].
          intros ? ? ? ? Heq; inversion Heq; subst; reflexivity.
        - rewrite seq_S, flat_map_app.
          apply NoDup_app. split; auto.
          split.
          + intros. destruct x as (i & j).
            apply bigop_flatten_index_char in H.
            destruct H as (Hi & Hj). apply in_seq in Hi, Hj.
            intro H. apply bigop_flatten_index_char in H.
            destruct H as (Hi' & _).
            apply in_inv in Hi'. destruct Hi' as [H|H]; [Lia.lia|eapply in_nil; eauto].
          + cbn [flat_map]. rewrite app_nil_r.
            apply NoDup_map; [|apply seq_NoDup].
            intros. inversion H1; subst; reflexivity. }
      generalize (bigop_flatten_index_char (seq 0%nat (S n)) (fun i => seq 0%nat (S i))). intro Hin1.
      generalize (bigop_flatten_index_char (seq 0%nat (S n)) (fun i => seq 0%nat (S (n - i)%nat))). intro Hin2.
      set (psi := (fun '(i, j) => (i + j, i)%nat)).
      set (phi := (fun '(i, j) => (j, i - j)%nat)).
      erewrite (bigop_index_change_inj _ (fun '(i, j) => f1 j * f2 (i - j)%nat * f3 (n - i)%nat) phi psi).
      2: { intros. destruct i as (i & j). simpl.
           f_equal. apply Hin1 in H.
           destruct H as [HA HB]. apply in_seq in HA, HB.
           Lia.lia. }
      rewrite (bigop_ext_eq _ (fun i : nat * nat => let '(i0, j) := psi i in f1 j * f2 (i0 - j)%nat * f3 (n - i0)%nat) (fun '(i, j) => f1 i * f2 j * f3 (n - i - j)%nat)).
      2: { intros; destruct i; simpl.
           apply in_map_iff in H. destruct H as (? & Hphi & Hi).
           destruct x; simpl in Hphi.
           inversion Hphi; subst; clear Hphi.
           apply Hin1 in Hi.
           destruct Hi as [Hi1 Hi2]. apply in_seq in Hi1, Hi2.
           assert ((n0 + (n2 - n0) - n0)%nat = (n2 - n0)%nat :> nat) as -> by Lia.lia.
           assert ((n - (n0 + (n2 - n0)))%nat = (n - n0 - (n2 - n0))%nat :> nat) as -> by Lia.lia.
           reflexivity. }
      generalize (in_map_iff phi (flat_map (fun i : nat => map (fun j : nat => (i, j)) (seq 0 (S i))) (seq 0 (S n)))). intro Hin1'.
      apply bigop_permutation. apply NoDup_Permutation.
      { apply Hnd. }
      { apply NoDup_map.
        - intros x y Hx Hy Heq.
          destruct x as (x1 & y1). destruct y as (x2 & y2).
          apply Hin1 in Hx, Hy.
          destruct Hx as (Hx1 & Hx2).
          destruct Hy as (Hy1 & Hy2).
          apply in_seq in Hx1, Hx2, Hy1, Hy2.
          inversion Heq; subst; clear Heq.
          f_equal. Lia.lia.
        - apply Hnd. }
      { intro x. destruct x as (i & j).
        split; intro H.
        - apply Hin2 in H.
          destruct H as [HA HB]. apply in_seq in HA, HB.
          apply Hin1'. exists (psi (i, j)).
          split; [simpl; f_equal; Lia.lia|].
          apply Hin1. split; apply in_seq; Lia.lia.
        - apply Hin1' in H. apply Hin2.
          destruct H as (x & Heq & H). destruct x as (i' & j').
          inversion Heq; subst; clear Heq.
          apply Hin1 in H. destruct H as [HA HB]; apply in_seq in HA, HB.
          split; apply in_seq; Lia.lia. }
    Qed.
    Lemma is_monic_mul `{Hznone: @is_zero_neq_one F Feq Fzero Fone}:
      forall p q, is_monic p -> is_monic q -> is_monic (Pmul p q).
    Proof.
      intros p q Hp Hq. unfold is_monic, lead_coeff.
      unfold is_monic, lead_coeff in Hp, Hq.
      destruct (degree p) as [np|] eqn:Hnp; [|apply zero_neq_one in Hp; elim Hp].
      destruct (degree q) as [nq|] eqn:Hnq; [|apply zero_neq_one in Hq; elim Hq].
      generalize (mul_coeff_hi _ _ _ _ Hnp Hnq).
      rewrite Hp, Hq, left_identity. intros [X Y].
      rewrite (degree_char (Pmul p q) (np + nq)%nat ltac:(rewrite X; symmetry; apply zero_neq_one) Y).
      apply X.
    Qed.
  End Pmul.

  Global Instance polynomial_group:
    @commutative_group P Peq Padd Pzero Popp.
  Proof.
    repeat constructor.
    - unfold Peq; intros; repeat rewrite add_definition.
      apply associative.
    - unfold Peq; intros; rewrite add_definition, zero_definition.
      apply left_identity.
    - unfold Peq; intros; rewrite add_definition, zero_definition.
      apply right_identity.
    - intros p1 p1' Heq1 p2 p2' Heq2.
      unfold Peq in *; intros; simpl.
      repeat rewrite add_definition.
      rewrite Heq1, Heq2. reflexivity.
    - intros p k. reflexivity.
    - intros p1 p2 Heq k. rewrite (Heq k). reflexivity.
    - intros p1 p2 p3 Heq1 Heq2 k.
      rewrite (Heq1 k). apply Heq2.
    - intros p k. rewrite add_definition, opp_definition, zero_definition.
      apply left_inverse.
    - intros p k. rewrite add_definition, opp_definition, zero_definition.
      apply right_inverse.
    - intros p1 p2 Heq k.
      repeat rewrite opp_definition. rewrite (Heq k). reflexivity.
    - intros p1 p2 k. repeat rewrite add_definition.
      apply commutative.
  Qed.

  Global Instance polynomial_ring:
    @commutative_ring P Peq Pzero Pone Popp Padd Psub Pmul.
  Proof.
    constructor.
    - constructor.
      + apply polynomial_group.
      + constructor; [..|apply (@monoid_Equivalence _ _ _ _ (@group_monoid _ _ _ _ _ (commutative_group_group polynomial_group)))]; repeat constructor.
        * unfold Peq; intros p1 p2 p3 k.
          repeat rewrite mul_definition.
          unfold mul_coeff.
          rewrite (bigop_ext_eq _ (fun i : nat => coeff p1 i * coeff (Pmul p2 p3) (k - i)) (fun i : nat => coeff p1 i * (mul_coeff (coeff p2) (coeff p3)) (k - i))) by (intros; rewrite mul_definition; reflexivity).
          rewrite (bigop_ext_eq _ (fun i : nat => coeff (Pmul p1 p2) i * coeff p3 (k - i)) (fun i : nat => mul_coeff (coeff p1) (coeff p2) i * coeff p3 (k - i))) by (intros; rewrite mul_definition; reflexivity).
          apply mul_coeff_assoc.
        * intros p k. rewrite mul_definition.
          apply mul_coeff_left_identity.
        * intros p k. rewrite mul_definition.
          apply mul_coeff_right_identity.
        * intros p1 p1' Heq1 p2 p2' Heq2 k.
          repeat rewrite mul_definition.
          apply bigop_ext_eq; intros. rewrite (Heq1 _), (Heq2 _); reflexivity.
      + constructor. intros p1 p2 p3 k.
        rewrite mul_definition. rewrite add_definition.
        repeat rewrite mul_definition.
        unfold mul_coeff. rewrite bigop_same_index. apply bigop_ext_eq.
        intros; rewrite add_definition.  apply left_distributive.
      + constructor. intros p1 p2 p3 k.
        rewrite mul_definition. rewrite add_definition.
        repeat rewrite mul_definition.
        unfold mul_coeff. rewrite bigop_same_index. apply bigop_ext_eq.
        intros; rewrite add_definition. apply right_distributive.
      + intros p1 p2 k. rewrite sub_definition, add_definition, opp_definition.
        apply ring_sub_definition.
      + intros p1 p1' Heq1 p2 p2' Heq2 k.
        repeat rewrite mul_definition.
        unfold mul_coeff. apply bigop_ext_eq; intros.
        rewrite (Heq1 _), (Heq2 _); reflexivity.
      + intros p1 p1' Heq1 p2 p2' Heq2 k.
        repeat rewrite sub_definition. rewrite (Heq1 k), (Heq2 k). reflexivity.
    - constructor. intros p1 p2 k.
      repeat rewrite mul_definition. apply mul_coeff_comm.
  Qed.
  Global Instance polynomial_integral_domain `{HID: @Hierarchy.integral_domain F Feq Fzero Fone Fopp Fadd Fsub Fmul}:
    @Hierarchy.integral_domain P Peq Pzero Pone Popp Padd Psub Pmul.
  Proof.
    econstructor.
    - apply polynomial_ring.
    - constructor; intros.
      generalize (mul_degree_eq x y); rewrite H, degree_zero.
      destruct (degree x) as [nx|] eqn:Hnx; [|apply zero_degree in Hnx; auto].
      destruct (degree y) as [ny|] eqn:Hny; [|apply zero_degree in Hny; auto].
      simpl; congruence.
    - constructor. intro H.
      generalize (H O); rewrite one_definition, zero_definition.
      intro X. apply zero_neq_one; auto.
  Qed.
  Section Base.
    Lemma mul_base_coeff:
      forall p n k, coeff (Pmul p (base n)) k = if dec_lt_nat k n then 0 else coeff p (k - n)%nat.
    Proof.
      intros. rewrite (@commutative _ _ _ (@commutative_ring_is_commutative _ _ _ _ _ _ _ _ (polynomial_ring)) _ _ k), mul_definition.
      unfold mul_coeff. destruct (dec_lt_nat k n).
      - rewrite (bigop_ext_eq _ _ (fun _ => 0)).
        + rewrite bigop_const. apply mul_0_r.
        + intros. rewrite base_definition.
          apply in_seq in H.
          destruct (dec_eq_nat n i); [Lia.lia|].
          apply mul_0_l.
      - assert (S k = S n + (k - n) :> nat)%nat as -> by Lia.lia.
        rewrite seq_app, bigop_app, seq_S, bigop_app.
        rewrite (bigop_ext_eq (seq 0 n) _ (fun _ => 0)).
        2: { intros i Hi; apply in_seq in Hi; rewrite base_definition.
             destruct (dec_eq_nat n i); [Lia.lia|].
             apply mul_0_l. }
        rewrite bigop_const, mul_0_r, left_identity.
        rewrite (bigop_ext_eq (seq _ _) _ (fun _ => 0)).
        2: { intros i Hi; apply in_seq in Hi; rewrite base_definition.
             destruct (dec_eq_nat n i); [Lia.lia|].
             apply mul_0_l. }
        rewrite bigop_const, mul_0_r, right_identity.
        simpl. rewrite base_definition, right_identity.
        destruct (dec_eq_nat n n); [|Lia.lia].
        apply left_identity.
    Qed.
    Lemma degree_base `{Hznone: @is_zero_neq_one F Feq Fzero Fone}:
      forall n, degree (base n) = Some n :> _.
    Proof.
      intros. apply degree_char.
      - rewrite base_definition.
        destruct (dec_eq_nat _ _); [|congruence].
        symmetry; apply zero_neq_one.
      - intros; rewrite base_definition.
        destruct (dec_eq_nat n k); [Lia.lia|reflexivity].
    Qed.
    Lemma is_monic_base n:
      is_monic (base n).
    Proof.
      unfold is_monic, lead_coeff.
      destruct (Feq_dec 1 0).
      - destruct (degree (base n)) eqn:Hn; [|rewrite f; reflexivity].
        rewrite base_definition. destruct (dec_eq_nat n n0); [reflexivity|].
        rewrite f; reflexivity.
      - rewrite (degree_char (base n) n); intros.
        all: rewrite base_definition.
        1-2: destruct (dec_eq_nat _ _); [|congruence].
        reflexivity. assumption.
        destruct (dec_eq_nat n k); [Lia.lia|reflexivity].
    Qed.
    Lemma base_0_one:
      Peq (base 0%nat) Pone.
    Proof.
      intros k. rewrite base_definition, one_definition.
      destruct k; [destruct (dec_eq_nat _ _); [|congruence]; reflexivity|].
      destruct (dec_eq_nat 0 (S k)); [Lia.lia|reflexivity].
    Qed.
    Lemma base_mul_base n1 n2:
      Peq (Pmul (base n1) (base n2)) (base (n1 + n2)%nat).
    Proof.
      intro k. rewrite base_definition, mul_base_coeff.
      destruct (dec_lt_nat k n2); [destruct (dec_eq_nat (n1 + n2)%nat k); [Lia.lia|reflexivity]|].
      rewrite base_definition.
      destruct (dec_eq_nat n1 (k - n2)%nat); destruct (dec_eq_nat (n1 + n2)%nat k); try Lia.lia; reflexivity.
    Qed.
    Lemma base_not_zero `{Hznone: @is_zero_neq_one F Feq Fzero Fone} n:
      not (Peq (base n) Pzero).
    Proof.
      intro Heq.
      generalize (Heq n). rewrite zero_definition, base_definition.
      destruct (dec_eq_nat _ _); [|congruence]. intro; apply zero_neq_one; symmetry; auto.
    Qed.
  End Base.
  Section Pconst.
    Global Instance eq_proper_const:
      Proper (Feq ==> Peq) Pconst.
    Proof.
      intros x y Heq k. do 2 rewrite const_definition.
      destruct k; auto; reflexivity.
    Qed.

    Lemma const_zero_definition:
      Peq (Pconst 0) Pzero.
    Proof.
      intros k; rewrite zero_definition, const_definition.
      destruct k; reflexivity.
    Qed.
    Lemma const_one_definition:
      Peq (Pconst 1) Pone.
    Proof.
      intros k; rewrite one_definition, const_definition.
      destruct k; reflexivity.
    Qed.
    Lemma mul_const_coeff_l c p:
      forall k,
        coeff (Pmul (Pconst c) p) k = c * (coeff p k).
    Proof.
      intros k; rewrite mul_definition.
      unfold mul_coeff. simpl.
      assert (k - 0 = k :> _)%nat as -> by Lia.lia.
      rewrite const_definition.
      rewrite (bigop_ext_eq _ _ (fun _ => 0)).
      - rewrite bigop_const. rewrite mul_0_r.
        apply right_identity.
      - intros i Hi. apply in_seq in Hi.
        rewrite const_definition; destruct i; [Lia.lia|].
        apply mul_0_l.
    Qed.
    Lemma mul_const_coeff_r c p:
      forall k,
        coeff (Pmul p (Pconst c)) k = c * (coeff p k).
    Proof.
      intros k; rewrite mul_definition.
      unfold mul_coeff. rewrite seq_S, bigop_app. simpl.
      assert (k - k = 0 :> _)%nat as -> by Lia.lia.
      rewrite const_definition, right_identity.
      rewrite (bigop_ext_eq _ _ (fun _ => 0)).
      - rewrite bigop_const. rewrite mul_0_r.
        rewrite left_identity, commutative. reflexivity.
      - intros i Hi. apply in_seq in Hi.
        destruct k; [Lia.lia|].
        rewrite const_definition; destruct i.
        + assert (S k - 0 = S k :> _)%nat as -> by Lia.lia.
          apply mul_0_r.
        + assert (S k - S i = S (k - S i) :> _)%nat as -> by Lia.lia.
          apply mul_0_r.
    Qed.
    Lemma mul_const_base_coeff:
      forall c n k,
        coeff (Pmul (Pconst c) (base n)) k = if dec_eq_nat n k then c else 0.
    Proof.
      intros c n k. rewrite mul_const_coeff_l.
      rewrite base_definition. destruct (dec_eq_nat n k).
      - apply right_identity.
      - apply mul_0_r.
    Qed.
    Lemma mul_const_base_degree:
      forall c n,
        degree (Pmul (Pconst c) (base n)) = (if Feq_dec c 0 then None else Some n) :> _.
    Proof.
      intros. destruct (Feq_dec c 0).
      - assert (Peq Pzero (Pmul _ _)) as <-; [|apply degree_zero].
        intro k. rewrite mul_const_base_coeff, zero_definition.
        destruct (dec_eq_nat n k); symmetry; [apply f|reflexivity].
      - apply degree_char; [|intros k Hk]; rewrite mul_const_base_coeff.
        + destruct (dec_eq_nat _ _); [|congruence]; auto.
        + destruct (dec_eq_nat n k); [Lia.lia|reflexivity].
    Qed.
    Lemma degree_const n:
      (degree (Pconst n) = (if Feq_dec n 0 then None else Some 0%nat) :> _).
    Proof.
      destruct (Feq_dec n 0) as [->|Hnez].
      - rewrite const_zero_definition; apply degree_zero.
      - apply degree_char; [rewrite const_definition; auto|].
        intros; rewrite const_definition; destruct k; [Lia.lia|reflexivity].
    Qed.
    Lemma degree_0_const p:
      (degree p = Some 0%nat :> _) ->
      Peq p (Pconst (coeff p 0%nat)).
    Proof.
      intros Hdegp. generalize (degree_definition p); rewrite Hdegp.
      intros [Hpne Heq] k.
      rewrite const_definition.
      destruct k; [reflexivity|].
      apply Heq; Lia.lia.
    Qed.
    Lemma const_add_const c1 c2:
      Peq (Padd (Pconst c1) (Pconst c2)) (Pconst (c1 + c2)).
    Proof.
      intro k. rewrite const_definition, add_definition, const_definition, const_definition.
      destruct k; [reflexivity|apply left_identity].
    Qed.
    Lemma opp_const c:
      Peq (Popp (Pconst c)) (Pconst (Fopp c)).
    Proof.
      intro k. rewrite opp_definition, const_definition, const_definition.
      destruct k; [reflexivity|apply Group.inv_id].
    Qed.
    Lemma const_sub_const c1 c2:
      Peq (Psub (Pconst c1) (Pconst c2)) (Pconst (c1 - c2)).
    Proof.
      rewrite ring_sub_definition, opp_const, const_add_const, <- ring_sub_definition.
      reflexivity.
    Qed.
    Lemma const_mul_const c1 c2:
      Peq (Pmul (Pconst c1) (Pconst c2)) (Pconst (c1 * c2)).
    Proof.
      intro k. rewrite const_definition, mul_const_coeff_l, const_definition.
      destruct k; [reflexivity|apply mul_0_r].
    Qed.
  End Pconst.
  Section DivMod.
    Context {Finv: F -> F}{Fdiv: F -> F -> F}
      {field: @field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}.
    (* Assume a field for simplicity in order to define euclidean division *)
    (* A pseudo euclidean division exists for rings https://math.stackexchange.com/questions/116029/why-polynomial-division-algorithm-works-for-x-a-or-any-monic-polynomial/116037#116037 *)
    Local Infix "/" := Fdiv.

    (* Invariant: measure p ≤ n *)
    Fixpoint Pdivmod_rec p q n :=
      match n with
      | O => (Pzero, Pzero)
      | S n' => match degree p with
               | None => (Pzero, Pzero)
               | Some np => match degree q with
                          | None => (Pzero, p)
                          | Some nq => if dec_lt_nat np nq then (Pzero, p)
                                     else
                                       let a := lead_coeff p in
                                       let b := lead_coeff q in
                                       let '(d, r) := Pdivmod_rec (Psub p (Pmul (Pmul (Pconst (a/b)) (base (np - nq)%nat)) q)) q n' in
                                       (Padd (Pmul (Pconst (a/b)) (base (np - nq)%nat)) d, r)
                          end
               end
      end.

    Definition Pdivmod p q :=
      Pdivmod_rec p q (measure p).

    Definition Pdiv p q :=
      fst (Pdivmod p q).

    Definition Pmod p q :=
      snd (Pdivmod p q).

    Definition Pdivides p q :=
      Peq (Pmod q p) Pzero.

    Global Instance peq_divmod_rec_proper n: Proper (Peq ==> Peq ==> (fun a b => Peq (fst a) (fst b) /\ Peq (snd a) (snd b))) (fun a b => Pdivmod_rec a b n).
    Proof.
      induction n; intros p1 p1' Hp1 p2 p2' Hp2.
      - simpl; split; reflexivity.
      - cbn [Pdivmod_rec]. rewrite Hp1.
        destruct (degree p1') eqn:Hp1'; [|split; reflexivity].
        rewrite Hp2; destruct (degree p2') eqn:Hp2'; [|split; simpl; auto; reflexivity].
        destruct (dec_lt_nat n0 n1); [simpl; split; auto; reflexivity|].
        rewrite (surjective_pairing (Pdivmod_rec (Psub p1 _) _ n)).
        rewrite (surjective_pairing (Pdivmod_rec (Psub p1' _) _ n)). simpl.
        assert (Heq: Peq (Psub p1 (Pmul (Pmul (Pconst (lead_coeff p1 / lead_coeff p2)) (base (n0 - n1))) p2)) (Psub p1' (Pmul (Pmul (Pconst (lead_coeff p1' / lead_coeff p2')) (base (n0 - n1))) p2'))) by (rewrite Hp1, Hp2; reflexivity).
        generalize (IHn _ _ Heq _ _ Hp2). intros [U V].
        simpl; split.
        + rewrite U, Hp1, Hp2. reflexivity.
        + rewrite V. reflexivity.
    Qed.

    Global Instance peq_divmod_proper: Proper (Peq ==> Peq ==> (fun a b => Peq (fst a) (fst b) /\ Peq (snd a) (snd b))) Pdivmod.
    Proof.
      intros p1 p1' Hp1 p2 p2' Hp2.
      unfold Pdivmod. assert (measure p1 = measure p1' :> _) as -> by (unfold measure; rewrite Hp1; reflexivity).
      apply peq_divmod_rec_proper; auto.
    Qed.

    Global Instance peq_div_proper: Proper (Peq ==> Peq ==> Peq) Pdiv.
    Proof.
      intros p1 p1' Hp1 p2 p2' Hp2.
      unfold Pdiv. apply peq_divmod_proper; auto.
    Qed.

    Global Instance peq_mod_proper: Proper (Peq ==> Peq ==> Peq) Pmod.
    Proof.
      intros p1 p1' Hp1 p2 p2' Hp2.
      unfold Pdiv. apply peq_divmod_proper; auto.
    Qed.

    Global Instance peq_divides_proper: Proper (Peq ==> Peq ==> iff) Pdivides.
    Proof.
      intros p1 p1' Hp1 p2 p2' Hp2.
      unfold Pdivides. rewrite Hp1, Hp2. reflexivity.
    Qed.

    Lemma Pdivmod_eq p q:
      Pdivmod p q = (Pdiv p q, Pmod p q) :> _.
    Proof. apply surjective_pairing. Qed.

    Lemma Pdivmod_rec_spec q:
      not (Peq q Pzero) ->
      forall n p,
        (measure p <= n)%nat ->
        let '(d, r) := Pdivmod_rec p q n in
        Peq p (Padd (Pmul d q) r) /\ degree_lt (degree r) (degree q).
    Proof.
      intro H. assert (Hlt: degree_lt (None) (degree q)) by (destruct (degree q) as [nq|] eqn:Y; cbv; try Lia.lia; apply zero_degree in Y; contradiction).
      induction n; intros.
      - unfold Pdivmod_rec.
        rewrite mul_0_l, left_identity, degree_zero.
        split; auto. apply zero_degree.
        unfold measure, convert in H0; destruct (degree p); [Lia.lia|reflexivity].
      - generalize (degree_definition p).
        destruct (degree p) as [np|] eqn:Hp; [intros (Hp1 & Hp2)|intros Hp1].
        2: { simpl. rewrite Hp, mul_0_l, left_identity, degree_zero.
             split; auto. apply zero_degree; auto. }
        cbn [Pdivmod_rec]; rewrite Hp.
        generalize (degree_definition q).
        destruct (degree q) as [nq|] eqn:Hqeq; [intros (Hq1 & Hq2)|apply StrictOrder_Irreflexive in Hlt; tauto].
        unfold measure, convert in H0; rewrite Hp in H0.
        destruct (dec_lt_nat np nq).
        + rewrite mul_0_l, left_identity, Hp; simpl; split; [reflexivity|]; cbv; Lia.lia.
        + rewrite (surjective_pairing (Pdivmod_rec _ q n)).
          assert (Hle: (measure (Psub p (Pmul (Pmul (Pconst (lead_coeff p / lead_coeff q)) (base (np - nq))) q)) <= n)%nat).
          { unfold measure. destruct (degree (Psub _ _)) as [ns|] eqn:Hs; [|cbv; Lia.lia].
            generalize (sub_degree p (Pmul (Pmul (Pconst (lead_coeff p / lead_coeff q)) (base (np - nq))) q)).
            rewrite Hs, Hp. intro X.
            generalize (mul_degree_eq (Pmul (Pconst (lead_coeff p / lead_coeff q)) (base (np - nq))) q).
            rewrite Hqeq, mul_const_base_degree.
            destruct (Feq_dec (lead_coeff p / lead_coeff q) 0) as [He|Hn].
            { rewrite field_div_definition in He.
              apply is_mul_nonzero_nonzero in He.
              unfold lead_coeff in He; rewrite Hp, Hqeq in He.
              destruct He as [He|He]; [contradiction|].
              generalize (right_multiplicative_inverse (coeff q nq) Hq1).
              rewrite He, mul_0_r. intro Hx. elim (zero_neq_one Hx). }
            simpl. assert (np - nq + nq = np :> _)%nat as -> by Lia.lia.
            intro Y. rewrite Y in X. simpl in X. rewrite degree_max_id in X.
            cbv in X.
            assert (ns < np \/ ns = np :> _)%nat as [Hns| ->] by Lia.lia; [Lia.lia|].
            generalize (degree_definition (Psub p (Pmul (Pmul (Pconst (lead_coeff p / lead_coeff q)) (base (np - nq))) q))); rewrite Hs; intros (U&V).
            elim U.
            rewrite sub_definition, mul_definition.
            unfold mul_coeff.
            rewrite (bigop_ext_eq _ _ (fun i => (if dec_eq_nat (np - nq)%nat i then (coeff p np) / (coeff q nq) else 0) * coeff q (np - i)%nat)).
            2:{ intros i Hi. rewrite mul_const_base_coeff.
                unfold lead_coeff; rewrite Hp, Hqeq. reflexivity. }
            assert (S np = S (np - nq) + nq :> _)%nat as -> by Lia.lia.
            rewrite seq_add, seq_S, bigop_app, bigop_app.
            rewrite (bigop_ext_eq (seq 0 _) _ (fun _ => 0)).
            2:{ intros i Hi. apply in_seq in Hi.
                destruct (dec_eq_nat (np - nq)%nat i); [Lia.lia|].
                apply mul_0_l. }
            rewrite bigop_const, mul_0_r, left_identity.
            rewrite (bigop_ext_eq (seq _ _) _ (fun _ => 0)).
            2:{ intros i Hi. apply in_seq in Hi.
                destruct (dec_eq_nat (np - nq)%nat i); [Lia.lia|].
                apply mul_0_l. }
            rewrite bigop_const, mul_0_r, right_identity.
            simpl. rewrite right_identity.
            destruct (dec_eq_nat _ _); [|congruence].
            assert (np - _ = nq :> nat)%nat as -> by Lia.lia.
            rewrite field_div_definition, <-associative, left_multiplicative_inverse, right_identity, ring_sub_definition, right_inverse; auto.
            reflexivity. }
          generalize (IHn _ Hle).
          rewrite (surjective_pairing (Pdivmod_rec _ q n)); cbn [fst snd].
          intros (X & Y). split; [|exact Y].
          rewrite (right_distributive), <- associative, <- X.
          rewrite ring_sub_definition, commutative, <- associative, left_inverse, right_identity.
          reflexivity.
    Qed.

    Lemma Pdiv_0_l q:
      Peq (Pdiv Pzero q) Pzero.
    Proof. unfold Pdiv, Pdivmod, Pdivmod_rec, measure. rewrite degree_zero. reflexivity. Qed.

    Lemma Pdiv_0_r p:
      Peq (Pdiv p Pzero) Pzero.
    Proof.
      unfold Pdiv, Pdivmod, Pdivmod_rec, measure, convert.
      destruct (degree p) as [n|] eqn:Hp; [|reflexivity].
      rewrite Hp, degree_zero. reflexivity.
    Qed.

    Lemma Pmod_0_l q:
      Peq (Pmod Pzero q) Pzero.
    Proof. unfold Pmod, Pdivmod, Pdivmod_rec, measure, convert; rewrite degree_zero. reflexivity. Qed.

    Lemma Pmod_0_r p:
      Peq (Pmod p Pzero) p.
    Proof.
      unfold Pmod, Pdivmod, Pdivmod_rec, measure, convert.
      destruct (degree p) as [n|] eqn:Hp.
      - rewrite Hp, degree_zero. reflexivity.
      - symmetry. apply zero_degree. auto.
    Qed.

    Lemma Pdivmod_eq_spec p q:
      Peq p (Padd (Pmul (Pdiv p q) q) (Pmod p q)).
    Proof.
      destruct (Peq_dec q Pzero) as [->|Hn].
      - rewrite Pmod_0_r, Pdiv_0_r, mul_0_l, left_identity. reflexivity.
      - generalize (Pdivmod_rec_spec q Hn (measure p) p ltac:(reflexivity)).
        rewrite (surjective_pairing (Pdivmod_rec p q _)); intros [X Y].
        unfold Pdiv, Pmod, Pdivmod. auto.
    Qed.

    Lemma Pdivmod_spec p q (Hn: not (Peq q Pzero)):
      Peq p (Padd (Pmul (Pdiv p q) q) (Pmod p q))
      /\ degree_lt (degree (Pmod p q)) (degree q).
    Proof.
      generalize (Pdivmod_rec_spec q Hn (measure p) p ltac:(reflexivity)).
      rewrite (surjective_pairing (Pdivmod_rec p q _)); intros [X Y].
      unfold Pdiv, Pmod, Pdivmod. auto.
    Qed.

    Lemma Pmod_degree_lt p q (Hn: not (Peq q Pzero)):
      degree_lt (degree (Pmod p q)) (degree q).
    Proof. apply Pdivmod_spec; auto. Qed.

    Lemma Pmod_1_r p:
      Peq (Pmod p Pone) Pzero.
    Proof.
      assert (Hn: not (Peq Pone Pzero)) by (intro X; generalize (degree_one); rewrite X, degree_zero; inversion 1).
      generalize (Pmod_degree_lt p Pone Hn). rewrite degree_one.
      destruct (degree (Pmod p Pone)) as [n|] eqn:Hdeg; cbv; [Lia.lia|].
      intro; apply zero_degree; auto.
    Qed.

    Lemma Pdiv_1_r p:
      Peq (Pdiv p Pone) p.
    Proof.
      generalize (Pdivmod_eq_spec p Pone).
      rewrite Pmod_1_r. rewrite right_identity, right_identity.
      symmetry; auto.
    Qed.

    Lemma Pdivides_0_r p:
      Pdivides p Pzero.
    Proof. apply Pmod_0_l. Qed.

    Lemma Pdivides_1_l p:
      Pdivides Pone p.
    Proof. apply Pmod_1_r. Qed.

    Lemma Pdivmod_eq_iff p q (Hn: not (Peq q Pzero)):
      forall d r, Peq p (Padd (Pmul d q) r) ->
             degree_lt (degree r) (degree q) ->
             Peq d (Pdiv p q) /\ Peq r (Pmod p q).
    Proof.
      intros. generalize (Pdivmod_spec p q Hn); intros (X & Y).
      assert (Z: Peq (Pmul (Psub d (Pdiv p q)) q) (Psub (Pmod p q) r)).
      { assert (Peq r (Psub p (Pmul d q))) as -> by (rewrite H, ring_sub_definition, commutative, associative, left_inverse, left_identity; reflexivity).
        assert (Peq (Pmod p q) (Psub p (Pmul (Pdiv p q) q))) as -> by (rewrite X at 2; rewrite ring_sub_definition, commutative, associative, left_inverse, left_identity; reflexivity).
        repeat rewrite ring_sub_definition.
        rewrite Group.inv_op, Group.inv_inv, <- mul_opp_l.
        rewrite <- (commutative (Popp p)), (commutative p).
        rewrite <- associative, (associative p), right_inverse, left_identity, <- right_distributive, (commutative d).
        reflexivity. }
      assert (W: degree_lt (degree (Psub (Pmod p q) r)) (degree q)).
      { eapply degree_le_lt_trans; [apply (sub_degree (Pmod p q) r)|].
        apply degree_max_lub_lt; auto. }
      rewrite <- Z in W.
      generalize (mul_degree_eq (Psub d (Pdiv p q)) q). intro U.
      rewrite U in W.
      destruct (degree q) as [nq|] eqn:Hq; [|apply zero_degree in Hq; contradiction].
      destruct (degree (Psub d (Pdiv p q))) as [n|] eqn:Hx; [cbv -[Nat.add] in W; Lia.lia|apply zero_degree in Hx; rewrite Hx, mul_0_l in Z].
      split.
      - rewrite <- (right_identity (Pdiv _ _)), <- Hx, ring_sub_definition, (commutative d), associative, right_inverse, left_identity. reflexivity.
      - rewrite <- (right_identity r), Z, ring_sub_definition, (commutative (Pmod _ _)), associative, right_inverse, left_identity. reflexivity.
    Qed.

    Lemma Pmod_opp p q:
      Peq (Pmod (Popp p) q) (Popp (Pmod p q)).
    Proof.
      destruct (Peq_dec q Pzero) as [->|Hqnz]; [rewrite Pmod_0_r, Pmod_0_r; reflexivity|].
      symmetry. assert (HA: Peq (Popp p) (Padd (Pmul (Popp (Pdiv p q)) q) (Popp (Pmod p q)))).
      { rewrite (Pdivmod_eq_spec p q) at 1.
        rewrite Group.inv_op, commutative.
        rewrite <- mul_opp_l. reflexivity. }
      apply (proj2 (Pdivmod_eq_iff (Popp p) q Hqnz _ _ HA ltac:(rewrite <- opp_degree; apply Pmod_degree_lt; auto))).
    Qed.

    Lemma Pdiv_same p (Hn: not (Peq p Pzero)):
      Peq (Pdiv p p) Pone.
    Proof.
      assert (Hlt: degree_lt (degree Pzero) (degree p)) by (destruct (degree p) as [np|] eqn:Hp; [rewrite degree_zero; cbv; auto; Lia.lia|apply zero_degree in Hp; contradiction]).
      generalize (Pdivmod_eq_iff p p Hn Pone Pzero ltac:(rewrite left_identity, right_identity; reflexivity) Hlt).
      intros [A B]; symmetry; assumption.
    Qed.

    Lemma Pmod_same p:
      Peq (Pmod p p) Pzero.
    Proof.
      destruct (Peq_dec p Pzero) as [->|Hn]; [apply Pmod_0_l|].
      assert (Hlt: degree_lt (degree Pzero) (degree p)) by (destruct (degree p) as [np|] eqn:Hp; [rewrite degree_zero; cbv; Lia.lia|apply zero_degree in Hp; contradiction]).
      generalize (Pdivmod_eq_iff p p Hn Pone Pzero ltac:(rewrite left_identity, right_identity; reflexivity) Hlt).
      intros [A B]; symmetry; assumption.
    Qed.

    Lemma Pdiv_mul_r p q (Hn: not (Peq q Pzero)):
      Peq (Pdiv (Pmul p q) q) p.
    Proof.
      assert (Hlt: degree_lt (degree Pzero) (degree q)) by (destruct (degree q) as [np|] eqn:Hp; [rewrite degree_zero; cbv; Lia.lia|apply zero_degree in Hp; contradiction]).
      generalize (Pdivmod_eq_iff (Pmul p q) q Hn p Pzero ltac:(rewrite right_identity; reflexivity) Hlt).
      intros [A B]; symmetry; assumption.
    Qed.

    Lemma Pdiv_mul_l q p (Hn: not (Peq q Pzero)):
      Peq (Pdiv (Pmul q p) q) p.
    Proof. rewrite commutative. apply Pdiv_mul_r. auto. Qed.

    Lemma Pdivmod_distr p q d:
      Peq (Pdiv (Padd p q) d) (Padd (Pdiv p d) (Pdiv q d)) /\
      Peq (Pmod (Padd p q) d) (Padd (Pmod p d) (Pmod q d)).
    Proof.
      destruct (Peq_dec d Pzero) as [->|Hdnz].
      - repeat rewrite Pdiv_0_r, Pmod_0_r.
        rewrite left_identity; split; reflexivity.
      - edestruct (Pdivmod_eq_iff (Padd p q) d Hdnz) as [<- <-]; [| |split; reflexivity].
        + rewrite (Pdivmod_eq_spec p d) at 1.
          rewrite (Pdivmod_eq_spec q d) at 1.
          rewrite <- (associative (Pmul _ _) (Pmod _ _) (Padd _ _)).
          rewrite (associative (Pmod _ _)).
          rewrite (commutative (Pmod _ _)).
          rewrite <- associative, associative, right_distributive.
          reflexivity.
        + generalize (add_degree (Pmod p d) (Pmod q d)).
          generalize (Pmod_degree_lt p d Hdnz).
          generalize (Pmod_degree_lt q d Hdnz). intros.
          destruct (degree d) as [nd|] eqn:Hd; [|elim Hdnz; apply zero_degree; auto].
          destruct (degree (Pmod p d)); destruct (degree (Pmod q d)); destruct ((degree (Padd (Pmod p d) (Pmod q d)))); cbv -[degree_lt_dec] in *; destruct (degree_lt_dec _ _); Lia.lia.
    Qed.

    Lemma Pdiv_distr p q d:
      Peq (Pdiv (Padd p q) d) (Padd (Pdiv p d) (Pdiv q d)).
    Proof. apply Pdivmod_distr. Qed.

    Lemma Pmod_distr p q d:
      Peq (Pmod (Padd p q) d) (Padd (Pmod p d) (Pmod q d)).
    Proof. apply Pdivmod_distr. Qed.

    Lemma Pmod_mul p q:
      Peq (Pmod (Pmul p q) q) Pzero.
    Proof.
      destruct (Peq_dec q Pzero) as [->|Hn]; [rewrite mul_0_r; apply Pmod_0_l|].
      assert (Hlt: degree_lt (degree Pzero) (degree q)) by (destruct (degree q) as [np|] eqn:Hp; [rewrite degree_zero; cbv; Lia.lia|apply zero_degree in Hp; contradiction]).
      generalize (Pdivmod_eq_iff (Pmul p q) q Hn p Pzero ltac:(rewrite right_identity; reflexivity) Hlt).
      intros [A B]; symmetry; assumption.
    Qed.

    Lemma Pmod_mod_eq p q:
      Peq (Pmod (Pmod p q) q) (Pmod p q).
    Proof.
      destruct (Peq_dec q Pzero) as [->|Hn]; [repeat rewrite Pmod_0_r; reflexivity|].
      generalize (Pdivmod_eq_iff (Pmod p q) q Hn Pzero (Pmod p q) ltac:(rewrite mul_0_l, left_identity; reflexivity) ltac:(apply Pmod_degree_lt; auto)).
      intros [A B]; symmetry; assumption.
    Qed.

    Lemma Pmod_small p q:
      degree_lt (degree p) (degree q) ->
      Peq (Pmod p q) p.
    Proof.
      intro Hlt. destruct (Peq_dec q Pzero) as [->|Hn]; [rewrite Pmod_0_r; reflexivity|].
      generalize (Pdivmod_eq_iff p q Hn Pzero p ltac:(rewrite mul_0_l, left_identity; reflexivity) Hlt).
      intros [A B]; symmetry; assumption.
    Qed.

    Lemma Pmul_mod_idemp_l p1 p2 q:
      Peq (Pmod (Pmul (Pmod p1 q) p2) q) (Pmod (Pmul p1 p2) q).
    Proof.
      destruct (Peq_dec q Pzero) as [->|Hn]; [repeat rewrite Pmod_0_r; reflexivity|].
      generalize (Pdivmod_spec p1 q Hn); intros [A1 B1].
      generalize (Pdivmod_spec (Pmul p1 p2) q Hn); intros [A B].
      set (d1 := Pdiv p1 q). set (d := Pdiv (Pmul p1 p2) q).
      fold d1 in A1; fold d in A.
      assert (A1': Peq (Psub p1 (Pmul d1 q)) (Pmod p1 q)) by (rewrite A1 at 1; rewrite ring_sub_definition, (commutative (Pmul _ _)), <- associative, right_inverse, right_identity; reflexivity).
      assert (A': Peq (Psub (Pmul p1 p2) (Pmul d q)) (Pmod (Pmul p1 p2) q)) by (rewrite A at 1; rewrite ring_sub_definition, (commutative (Pmul _ _)), <- associative, right_inverse, right_identity; reflexivity).
      assert (X: Peq (Pmul (Pmod p1 q) p2) (Padd (Pmul (Psub d (Pmul d1 p2)) q) (Pmod (Pmul p1 p2) q))).
      { rewrite <- A1', <- A', (right_distributive q).
        repeat rewrite ring_sub_definition.
        rewrite (commutative (Pmul d q)), <- (commutative (Popp (Pmul d q))).
        rewrite associative, <- (associative (Popp (Pmul (Pmul d1 p2) q))).
        rewrite right_inverse, right_identity.
        rewrite <- (associative d1), (commutative p2), associative, <- (mul_opp_l (Pmul d1 q)).
        rewrite <- right_distributive, (commutative p1). reflexivity. }
      generalize (Pdivmod_eq_iff (Pmul (Pmod p1 q) p2) q Hn (Psub d (Pmul d1 p2)) (Pmod (Pmul p1 p2) q) X B).
      intros [U V]; symmetry; assumption.
    Qed.

    Lemma Pmul_mod_idemp_r p1 p2 q:
      Peq (Pmod (Pmul p1 (Pmod p2 q)) q) (Pmod (Pmul p1 p2) q).
    Proof.
      rewrite (commutative p1 p2), <- (Pmul_mod_idemp_l p2 p1 q).
      rewrite (commutative p1). reflexivity.
    Qed.

    Lemma Pmul_mod_idemp p1 p2 q:
      Peq (Pmod (Pmul (Pmod p1 q) (Pmod p2 q)) q) (Pmod (Pmul p1 p2) q).
    Proof. rewrite Pmul_mod_idemp_l, Pmul_mod_idemp_r. reflexivity. Qed.

    Lemma Pmul_mod_distr_l p1 p2 q:
      Peq (Pmod (Pmul q p1) (Pmul q p2)) (Pmul q (Pmod p1 p2)).
    Proof.
      destruct (Peq_dec p2 Pzero) as [->|Hnp2].
      - rewrite mul_0_r, Pmod_0_r, Pmod_0_r. reflexivity.
      - generalize (Pdivmod_spec p1 p2 Hnp2). intros [A B].
        destruct (Peq_dec q Pzero) as [->|Hnq].
        + rewrite mul_0_l, mul_0_l, Pmod_0_l, mul_0_l. reflexivity.
        + symmetry. eapply (proj2 (Pdivmod_eq_iff (Pmul q p1) (Pmul q p2) _ (Pdiv p1 p2) _ _ _)). Unshelve.
          * intro X. apply zero_product_zero_factor in X.
            destruct X; contradiction.
          * rewrite A at 1. rewrite left_distributive.
            rewrite (associative q), (commutative q), <-associative.
            reflexivity.
          * repeat rewrite mul_degree_eq.
            apply degree_lt_add_mono_l; auto.
            intro X; apply zero_degree in X; congruence.
    Qed.

    Lemma Pmul_mod_distr_r p1 p2 q:
      Peq (Pmod (Pmul p1 q) (Pmul p2 q)) (Pmul (Pmod p1 p2) q).
    Proof.
      repeat rewrite <- (commutative q).
      apply Pmul_mod_distr_l.
    Qed.

    Lemma Pmod_add_l p q r:
      Peq (Pmod (Padd (Pmul p q) r) q) (Pmod r q).
    Proof.
      destruct (Peq_dec q Pzero) as [->|Hn]; [rewrite mul_0_r, left_identity; reflexivity|].
      symmetry.
      eapply (proj2 (Pdivmod_eq_iff (Padd (Pmul p q) r) q Hn (Padd p (Pdiv r q)) (Pmod r q) _ _)).
      Unshelve.
      - generalize (Pdivmod_spec r q Hn); intros [A B].
        rewrite A at 1. rewrite associative, <- right_distributive.
        reflexivity.
      - apply Pmod_degree_lt; auto.
    Qed.

    Lemma Pmod_add_r p q r:
      Peq (Pmod (Padd r (Pmul p q)) q) (Pmod r q).
    Proof. rewrite (commutative r). apply Pmod_add_l. Qed.

    Lemma Padd_mod_idemp_l p1 p2 q:
      Peq (Pmod (Padd (Pmod p1 q) p2) q) (Pmod (Padd p1 p2) q).
    Proof.
      destruct (Peq_dec q Pzero) as [->|Hn]; [repeat rewrite Pmod_0_r; reflexivity|].
      generalize (Pdivmod_spec p1 q Hn); intros [A B].
      assert (Peq (Pmod p1 q) (Psub p1 (Pmul (Pdiv p1 q) q))) as ->.
      { rewrite A at 2. rewrite ring_sub_definition, (commutative (Pmul _ _)), <- associative, right_inverse, right_identity. reflexivity. }
      rewrite ring_sub_definition, <- mul_opp_l, (commutative p1), <- associative.
      apply Pmod_add_l.
    Qed.

    Lemma Padd_mod_idemp_r p1 p2 q:
      Peq (Pmod (Padd p1 (Pmod p2 q)) q) (Pmod (Padd p1 p2) q).
    Proof.
      rewrite (commutative p1 p2), <- (Padd_mod_idemp_l p2 p1).
      rewrite (commutative p1). reflexivity.
    Qed.

    Lemma Padd_mod_idemp p1 p2 q:
      Peq (Pmod (Padd (Pmod p1 q) (Pmod p2 q)) q) (Pmod (Padd p1 p2) q).
    Proof. rewrite Padd_mod_idemp_l, Padd_mod_idemp_r. reflexivity. Qed.

    Lemma Pmod_mul_mod_l x p1 p2:
      Peq (Pmod (Pmod x (Pmul p1 p2)) p1) (Pmod x p1).
    Proof.
      assert (HA: Peq (Pmod x (Pmul p1 p2)) (Psub x (Pmul (Pdiv x (Pmul p1 p2)) (Pmul p1 p2)))); [|rewrite HA at 1].
      { rewrite (Pdivmod_eq_spec x (Pmul p1 p2)) at 2.
        rewrite ring_sub_definition, (commutative _ (Pmod _ _)), <- associative, right_inverse, right_identity. reflexivity. }
      rewrite ring_sub_definition, <- mul_opp_l, (commutative p1 p2), Pmod_distr, (associative _ p2 p1), Pmod_mul, right_identity. reflexivity.
    Qed.

    Lemma Pmod_mul_mod_r x p1 p2:
      Peq (Pmod (Pmod x (Pmul p1 p2)) p2) (Pmod x p2).
    Proof. rewrite (commutative p1 p2). apply Pmod_mul_mod_l. Qed.

    Lemma Pdivides_iff a b:
      Pdivides a b <-> exists c, Peq b (Pmul c a).
    Proof.
      split; [intro Hdiv|intros [c Heq]].
      - exists (Pdiv b a). rewrite <- (right_identity (Pmul _ _)).
        unfold Pdivides in Hdiv. rewrite <- Hdiv.
        apply Pdivmod_eq_spec.
      - rewrite <- (right_identity (Pmul _ _)) in Heq.
        destruct (Peq_dec a Pzero) as [He|Hn]; [rewrite Heq, He, mul_0_r, right_identity; apply Pdivides_0_r|].
        apply Pdivmod_eq_iff in Heq; auto.
        + unfold Pdivides; symmetry. apply Heq.
        + rewrite degree_zero. destruct (degree a) as [|] eqn:Ha; [cbv; Lia.lia|elim Hn; apply zero_degree; auto].
    Qed.

    Lemma Pmul_div_l a b c (Hc: Pdivides c a):
      Peq (Pmul (Pdiv a c) b) (Pdiv (Pmul a b) c).
    Proof.
      destruct (Peq_dec c Pzero) as [->|Hcnz]; [rewrite Pdiv_0_r, Pdiv_0_r, mul_0_l; reflexivity|].
      apply Pdivides_iff in Hc. destruct Hc as [k Hc].
      rewrite Hc. rewrite Pdiv_mul_r; auto.
      rewrite <- associative, (commutative c), associative.
      rewrite Pdiv_mul_r; auto. reflexivity.
    Qed.

    Lemma Pmul_div_r a b c (Hc: Pdivides c b):
      Peq (Pmul a (Pdiv b c)) (Pdiv (Pmul a b) c).
    Proof.
      destruct (Peq_dec c Pzero) as [->|Hcnz]; [rewrite Pdiv_0_r, Pdiv_0_r, mul_0_r; reflexivity|].
      apply Pdivides_iff in Hc. destruct Hc as [k Hc].
      rewrite Hc. rewrite Pdiv_mul_r; auto.
      rewrite associative, Pdiv_mul_r; auto. reflexivity.
    Qed.

    Lemma Pdivides_trans a b c:
      Pdivides a b -> Pdivides b c -> Pdivides a c.
    Proof.
      repeat rewrite Pdivides_iff.
      intros [c1 A] [c2 B]. rewrite A, associative in B.
      eauto.
    Qed.

    Lemma Pdivides_opp a b:
      Pdivides a b -> Pdivides a (Popp b).
    Proof.
      repeat rewrite Pdivides_iff.
      intros (c & Heq). exists (Popp c). rewrite Heq, mul_opp_l.
      reflexivity.
    Qed.

    Lemma Pdivides_add x a b:
      Pdivides x a -> Pdivides x b -> Pdivides x (Padd a b).
    Proof.
      repeat rewrite Pdivides_iff. intros (ca & Ha) (cb & Hb).
      exists (Padd ca cb). rewrite Ha, Hb, right_distributive. reflexivity.
    Qed.

    Lemma Pdivides_sub x a b:
      Pdivides x a -> Pdivides x b -> Pdivides x (Psub a b).
    Proof.
      rewrite ring_sub_definition; intros.
      apply Pdivides_add; auto. apply Pdivides_opp; auto.
    Qed.

    Lemma Pdivides_mul_l x a b:
      Pdivides x a -> Pdivides x (Pmul a b).
    Proof.
      repeat rewrite Pdivides_iff; intros (c & Ha).
      exists (Pmul c b). rewrite Ha. rewrite <- associative, (commutative x b), associative.
      reflexivity.
    Qed.

    Lemma Pdivides_mul_r x a b:
      Pdivides x b -> Pdivides x (Pmul a b).
    Proof. rewrite commutative. apply Pdivides_mul_l. Qed.

    Lemma Pdivides_mod x a b:
      Pdivides x a -> Pdivides x b -> Pdivides x (Pmod a b).
    Proof.
      intros Ha Hb. generalize (Pdivmod_eq_spec a b); intro Heq.
      assert (Peq (Pmod a b) (Psub a (Pmul (Pdiv a b) b))) as ->; [|apply Pdivides_sub; auto; apply Pdivides_mul_r; auto].
      rewrite Heq at 2. rewrite ring_sub_definition.
      rewrite <- associative, (commutative (Pmod _ _)), associative, right_inverse, left_identity.
      reflexivity.
    Qed.

    (* Extended euclidean algorithm for Bezout's coefficients *)
    Definition Pegcd p q :=
      let fix egcd_rec n p' q' :=
        match n with
        | O => (Pone, Pzero)
        | S n' => if Peq_dec q' Pzero then (Pone, Pzero) else
                   let '(u, v) := egcd_rec n' q' (Pmod p' q') in
                   (v, Psub u (Pmul v (Pdiv p' q')))
        end
      in egcd_rec (measure q) p q.

    Definition Pgcd p q :=
      (* Invariant measure q' <= n *)
      let fix gcd_rec n p' q' :=
        match n with
        | O => p'
        | S n' => if Peq_dec q' Pzero then p' else gcd_rec n' q' (Pmod p' q')
        end
      in gcd_rec (measure q) p q.

    Global Instance peq_egcd_proper: Proper (Peq ==> Peq ==> (fun x y => Peq (fst x) (fst y) /\ Peq (snd x) (snd y))) Pegcd.
    Proof.
      pose (egcd_rec := (fix egcd_rec n p' q' :=
        match n with
        | O => (Pone, Pzero)
        | S n' => if Peq_dec q' Pzero then (Pone, Pzero) else
                   let '(u, v) := egcd_rec n' q' (Pmod p' q') in
                   (v, Psub u (Pmul v (Pdiv p' q')))
        end)).
      assert (IH: forall n, Proper (Peq ==> Peq ==> (fun x y => Peq (fst x) (fst y) /\ Peq (snd x) (snd y))) (egcd_rec n)).
      { induction n; intros p1 p1' Hp1 p2 p2' Hp2; simpl; [split; reflexivity|].
        destruct (Peq_dec p2 Pzero); destruct (Peq_dec p2' Pzero); try rewrite Hp1 in *; try rewrite Hp2 in *; simpl; try (split; reflexivity); try contradiction.
        rewrite (surjective_pairing (egcd_rec n p2 _)).
        rewrite (surjective_pairing (egcd_rec n p2' _)).
        simpl. generalize (IHn p2 p2' Hp2 (Pmod p1 p2) (Pmod p1' p2') ltac:(rewrite Hp1, Hp2; reflexivity)); intros [A B].
        rewrite A, B, Hp1, Hp2. split; reflexivity. }
      intros p1 p1' Hp1 p2 p2' Hp2.
      unfold Pegcd. unfold measure. assert (degree p2 = degree p2' :> _) as -> by (rewrite Hp2; reflexivity).
      apply IH; auto.
    Qed.

    Global Instance peq_egcd_proper1: Proper (Peq ==> Peq ==> (fun x y => Peq (fst x) (fst y))) Pegcd.
    Proof. intros p1 p1' Hp1 p2 p2' Hp2. apply (proj1 (peq_egcd_proper _ _ Hp1 _ _ Hp2)). Qed.

    Global Instance peq_egcd_proper2: Proper (Peq ==> Peq ==> (fun x y => Peq (snd x) (snd y))) Pegcd.
    Proof. intros p1 p1' Hp1 p2 p2' Hp2. apply (proj2 (peq_egcd_proper _ _ Hp1 _ _ Hp2)). Qed.

    Global Instance peq_gcd_proper: Proper (Peq ==> Peq ==> Peq) Pgcd.
    Proof.
      pose (gcd_rec := (fix gcd_rec (n : nat) (p' q' : P) {struct n} : P :=
        match n with
        | 0%nat => p'
        | S n' => if Peq_dec q' Pzero then p' else gcd_rec n' q' (Pmod p' q')
        end)).
      assert (IHn: forall n, Proper (Peq ==> Peq ==> Peq) (gcd_rec n)).
      { induction n; intros p1 p1' Hp1 p2 p2' Hp2; simpl; auto.
        destruct (Peq_dec p2 Pzero); destruct (Peq_dec p2' Pzero); try rewrite Hp1 in *; try rewrite Hp2 in *; try reflexivity; try contradiction. }
      intros p1 p1' Hp1 p2 p2' Hp2.
      unfold Pgcd. unfold measure. rewrite Hp2 at 1.
      apply IHn; auto.
    Qed.

    Lemma Pegcd_0_r p:
      Peq (fst (Pegcd p Pzero)) Pone /\ Peq (snd (Pegcd p Pzero)) Pzero.
    Proof.
      unfold Pegcd; unfold measure; rewrite degree_zero; simpl.
      split; reflexivity.
    Qed.

    Lemma Pegcd_0_l p:
      Peq (fst (Pegcd Pzero p)) (if Peq_dec p Pzero then Pone else Pzero) /\ Peq (snd (Pegcd Pzero p)) (if Peq_dec p Pzero then Pzero else Pone).
    Proof.
      unfold Pegcd. unfold measure; destruct (degree p) as [np|] eqn:Hp.
      - simpl. destruct (Peq_dec p Pzero) as [He|Hne]; [rewrite He, degree_zero in Hp; congruence|].
        destruct np; simpl; [rewrite mul_0_l, ring_sub_definition, Group.inv_id, right_identity; split; reflexivity|].
        destruct (Peq_dec (Pmod Pzero p) Pzero) as [He|Hn]; simpl; [rewrite mul_0_l, ring_sub_definition, Group.inv_id, right_identity; split; reflexivity|].
        rewrite Pmod_0_l in Hn; elim Hn; reflexivity.
      - simpl. apply zero_degree in Hp.
        destruct (Peq_dec p Pzero); [|contradiction].
        split; reflexivity.
    Qed.

    Lemma Pgcd_0_r p:
      Peq (Pgcd p Pzero) p.
    Proof. unfold Pgcd. unfold measure; rewrite degree_zero. reflexivity. Qed.

    Lemma Pgcd_0_l p:
      Peq (Pgcd Pzero p) p.
    Proof.
      unfold Pgcd. unfold measure; destruct (degree p) as [np|] eqn:Hp.
      - simpl; destruct (Peq_dec p Pzero) as [He|Hne]; [rewrite He, degree_zero in Hp; congruence|].
        destruct np; simpl; [reflexivity|].
        destruct (Peq_dec (Pmod Pzero p) Pzero) as [He|Hn]; [reflexivity|].
        destruct np; [rewrite Pmod_0_l in Hn; elim Hn; reflexivity|].
        destruct (Peq_dec (Pmod p (Pmod Pzero p)) Pzero) as [He|_]; [rewrite Pmod_0_l, Pmod_0_r in He; contradiction|].
        destruct np; [rewrite Pmod_0_l, Pmod_0_r; reflexivity|].
        destruct (Peq_dec (Pmod (Pmod Pzero p) (Pmod p (Pmod Pzero p))) Pzero) as [|HX]; [|elim HX]; rewrite Pmod_0_l, Pmod_0_r; [| rewrite Pmod_0_l]; reflexivity.
      - symmetry; apply zero_degree; auto.
    Qed.

    Lemma Pgcd_mod p q:
      Peq (Pgcd p q) (Pgcd q (Pmod p q)).
    Proof.
      pose (gcd_rec := (fix gcd_rec (n : nat) (p' q' : P) {struct n} : P :=
        match n with
        | 0%nat => p'
        | S n' => if Peq_dec q' Pzero then p' else gcd_rec n' q' (Pmod p' q')
        end)).
      assert (IH: forall n1 n2 p q, (measure q <= n1 <= n2)%nat -> Peq (gcd_rec n1 p q) (gcd_rec n2 p q)).
      { clear p q. induction n1; simpl; intros n2 p q (Hle1 & Hle2).
        - unfold measure, convert in Hle1; destruct (degree q) as [nq|] eqn:Hq; [Lia.lia|].
          apply zero_degree in Hq.
          destruct n2; [reflexivity|].
          simpl. destruct (Peq_dec q Pzero); [reflexivity|contradiction].
        - destruct n2; [Lia.lia|]; simpl.
          destruct (Peq_dec q Pzero) as [|Hn]; [reflexivity|].
          generalize (Pmod_degree_lt p q Hn); intro Hlt.
          apply IHn1; try Lia.lia. unfold measure, convert in *.
          destruct (degree (Pmod p q)) as [|] eqn:Hm; [|Lia.lia].
          destruct (degree q) as [nq|] eqn:Hq; cbv in Hlt; Lia.lia. }
      destruct (Peq_dec q Pzero) as [->|Hqnz]; [rewrite Pgcd_0_l, Pgcd_0_r, Pmod_0_r; reflexivity|].
      unfold Pgcd. destruct (measure q) eqn:Hq.
      - unfold measure in Hq; destruct (degree q) as [|] eqn:Hqq; [inversion Hq|apply zero_degree in Hqq; contradiction].
      - destruct (Peq_dec q Pzero) as [|_]; [contradiction|].
        generalize (Pmod_degree_lt p q Hqnz). intro Hlt.
        unfold measure in Hq; destruct (degree q) as [|] eqn:Hqq; [|apply zero_degree in Hqq; contradiction].
        inversion Hq; subst n0; clear Hq.
        assert (Hle: (measure (Pmod p q) <= n)%nat) by (unfold measure, convert; destruct (degree (Pmod p q)) as [npq|] eqn:Hpq; cbv in Hlt; Lia.lia).
        fold gcd_rec.
        rewrite (IH (measure (Pmod p q)) n q (Pmod p q) ltac:(Lia.lia)).
        reflexivity.
    Qed.

    Lemma Pgcd_same p:
      Peq (Pgcd p p) p.
    Proof. rewrite Pgcd_mod, Pmod_same, Pgcd_0_r. reflexivity. Qed.

    Lemma Pgcd_divides_lr:
      forall p q, Pdivides (Pgcd p q) p /\ Pdivides (Pgcd p q) q.
    Proof.
      assert (IH: forall n p q, measure p <= n -> measure q <= n -> Pdivides (Pgcd p q) p /\ Pdivides (Pgcd p q) q).
      { induction n; intros p q Hp Hq.
        - unfold measure in Hp, Hq.
          destruct (degree p) as [|] eqn:Hpz; [inversion Hp|].
          destruct (degree q) as [|] eqn:Hqz; [inversion Hq|].
          apply zero_degree in Hpz, Hqz.
          rewrite Hpz, Hqz; unfold Pdivides.
          rewrite Pmod_0_l; split; reflexivity.
        - assert ((measure p <= n /\ measure q <= n) \/ (measure p = S n :> _ \/ measure q = S n :> _))%nat as [[Hlep Hleq] | Hnle] by Lia.lia.
          + apply IHn; auto.
          + destruct (Peq_dec p Pzero) as [->|Hnpz]; [unfold Pdivides; rewrite Pmod_0_l, Pgcd_0_l, Pmod_same; split; reflexivity|].
            destruct (Peq_dec q Pzero) as [->|Hnqz]; [unfold Pdivides; rewrite Pmod_0_l, Pgcd_0_r, Pmod_same; split; reflexivity|].
            assert (Hmod1: (measure (Pmod p q) <= n)%nat).
            { generalize (Pmod_degree_lt p q Hnqz); intros Hmod1.
              unfold measure, convert; destruct (degree (Pmod p q)) as [nm|]; [|Lia.lia].
              unfold measure, convert in Hq; destruct (degree q) as [nq|] eqn:Hqq; [|elim Hnqz; apply zero_degree; auto].
              cbv in Hmod1; Lia.lia. }
            rewrite Pgcd_mod.
            destruct (Peq_dec (Pmod p q) Pzero) as [He|Hmodnz].
            * unfold Pdivides. rewrite He, Pgcd_0_r, Pmod_same.
              split; [auto|reflexivity].
            * rewrite Pgcd_mod.
              assert (Hmod2: (measure (Pmod q (Pmod p q)) <= n)%nat).
              { generalize (Pmod_degree_lt q (Pmod p q) Hmodnz). intros Hmod2.
                unfold measure, convert; destruct (degree (Pmod q (Pmod p q))) as [nm|]; [|Lia.lia].
                unfold measure, convert in Hmod1; destruct (degree (Pmod p q)) as [nq|] eqn:Hqq; [|elim Hmodnz; apply zero_degree; auto].
                cbv in Hmod2; Lia.lia. }
              generalize (IHn _ _ Hmod1 Hmod2).
              rewrite <- Pgcd_mod, <- Pgcd_mod.
              intros [A B].
              apply Pdivides_iff in A, B.
              destruct A as [c1 A]; destruct B as [c2 B].
              assert (exists cq, Peq q (Pmul cq (Pgcd p q))) as [cq C].
              { eexists. rewrite (Pdivmod_eq_spec q (Pmod p q)) at 1; rewrite B.
                rewrite A at 2. rewrite associative, <- right_distributive.
                reflexivity. }
              split; apply Pdivides_iff; eauto.
              { eexists. rewrite (Pdivmod_eq_spec p q) at 1.
                rewrite A. rewrite C at 2.
                rewrite associative, <- right_distributive.
                reflexivity. } }
      intros p q. apply (IH (measure p + measure q)%nat p q); Lia.lia.
    Qed.

    Lemma Pgcd_divides_l p q:
      Pdivides (Pgcd p q) p.
    Proof. apply Pgcd_divides_lr. Qed.

    Lemma Pgcd_divides_r p q:
      Pdivides (Pgcd p q) q.
    Proof. apply Pgcd_divides_lr. Qed.

    Lemma Pgcd_eq_0_l p q:
      Peq (Pgcd p q) Pzero -> Peq p Pzero.
    Proof.
      intros A; generalize (Pgcd_divides_l p q); rewrite Pdivides_iff.
      intros [c B]. rewrite A, mul_0_r in B. auto.
    Qed.

    Lemma Pgcd_eq_0_r p q:
      Peq (Pgcd p q) Pzero -> Peq q Pzero.
    Proof.
      intros A; generalize (Pgcd_divides_r p q); rewrite Pdivides_iff.
      intros [c B]. rewrite A, mul_0_r in B. auto.
    Qed.

    Lemma Pgcd_greatest:
      forall p q s,
        Pdivides s p ->
        Pdivides s q ->
        Pdivides s (Pgcd p q).
    Proof.
      assert (IH: forall n p q s, (measure p + measure q <= n)%nat -> Pdivides s p -> Pdivides s q -> Pdivides s (Pgcd p q)).
      { induction n; intros p q s Hpq Hdivp Hdivq.
        - assert (measure p <= 0 /\ measure q <= 0) as [Hpn Hqn] by Lia.lia.
          unfold measure, convert in Hpn, Hqn.
          destruct (degree p) as [|] eqn:Hpz; [inversion Hpn|].
          destruct (degree q) as [|] eqn:Hqz; [inversion Hqn|].
          apply zero_degree in Hpz, Hqz.
          rewrite Hpz, Hqz, Pgcd_0_l. apply Pdivides_0_r.
        - destruct (Peq_dec p Pzero) as [->|Hpnz]; [rewrite Pgcd_0_l; auto|].
          destruct (Peq_dec q Pzero) as [->|Hqnz]; [rewrite Pgcd_0_r; auto|].
          destruct (degree p) as [np|] eqn:Hp; [|elim Hpnz; apply zero_degree; auto].
          destruct (degree q) as [nq|] eqn:Hq; [|elim Hqnz; apply zero_degree; auto].
          destruct (degree_lt_dec (degree p) (degree q)) as [Hlt|Hnlt].
          + assert (Peq (Pgcd p q) (Pgcd q p)) as -> by (rewrite (Pgcd_mod p q), Pmod_small; auto; reflexivity).
            rewrite Pgcd_mod. generalize (Pdivides_mod s q p Hdivq Hdivp); intro Hdivm.
            apply IHn; auto.
            generalize (Pmod_degree_lt q p Hpnz); intro X.
            unfold measure, convert in *.
            rewrite Hp in *; rewrite Hq in *; simpl in *.
            destruct (degree (Pmod q p)) as [nm|] eqn:Hmm; cbv in X, Hlt; Lia.lia.
          + rewrite Pgcd_mod. generalize (Pdivides_mod s p q Hdivp Hdivq); intro Hdivm.
            apply IHn; auto.
            generalize (Pmod_degree_lt p q Hqnz); intro X.
            unfold measure, convert in *.
            rewrite Hp in *; rewrite Hq in *; simpl in *.
            destruct (degree (Pmod p q)) as [nm|] eqn:Hmm; cbv in X, Hnlt; Lia.lia. }
      intros; apply (IH (measure p + measure q)%nat); auto; Lia.lia.
    Qed.

    Lemma Pegcd_mod:
      forall p q, not (Peq q Pzero) ->
             Peq (fst (Pegcd p q)) (snd (Pegcd q (Pmod p q))) /\
             Peq (snd (Pegcd p q)) (Psub (fst (Pegcd q (Pmod p q))) (Pmul (snd (Pegcd q (Pmod p q))) (Pdiv p q))).
    Proof.
      pose (egcd_rec := (fix egcd_rec n p' q' :=
        match n with
        | O => (Pone, Pzero)
        | S n' => if Peq_dec q' Pzero then (Pone, Pzero) else
                   let '(u, v) := egcd_rec n' q' (Pmod p' q') in
                   (v, Psub u (Pmul v (Pdiv p' q')))
        end)).
      assert (IH: forall n n' p q, (measure q <= n)%nat -> (measure q <= n')%nat -> Peq (fst (Pegcd p q)) (fst (egcd_rec n' p q)) /\ Peq (snd (Pegcd p q)) (snd (egcd_rec n' p q))).
      { induction n; intros n' p q Hle Hle'.
        - unfold measure, convert in Hle.
          destruct (degree q) as [|] eqn:Hqz; [Lia.lia|].
          apply zero_degree in Hqz.
          destruct (peq_egcd_proper _ p ltac:(reflexivity) _ _ Hqz) as [-> ->].
          destruct (Pegcd_0_r p) as [-> ->].
          destruct n'; simpl; [split; reflexivity|].
          destruct (Peq_dec q Pzero) as [_|]; [|contradiction].
          simpl. split; reflexivity.
        - destruct (Peq_dec q Pzero) as [Hqz|Hqnz].
          + destruct (peq_egcd_proper _ p ltac:(reflexivity) _ _ Hqz) as [-> ->].
            destruct (Pegcd_0_r p) as [-> ->].
            simpl; destruct (Peq_dec q Pzero) as [_|]; [|contradiction].
            destruct n'; simpl; [split; reflexivity|].
            destruct (Peq_dec q Pzero) as [_|]; [|contradiction].
            simpl; split; reflexivity.
          + generalize (Pmod_degree_lt p q Hqnz). intro Hlt.
            destruct (degree q) as [nq|] eqn:Hq; [|elim Hqnz; apply zero_degree; auto].
            destruct n'; [unfold measure, convert in Hle'; rewrite Hq in Hle'; Lia.lia|].
            unfold Pegcd; fold egcd_rec.
            unfold measure; rewrite Hq. simpl.
            destruct (Peq_dec q Pzero) as [|_]; [contradiction|].
            rewrite (surjective_pairing (egcd_rec n' _ _)).
            rewrite (surjective_pairing (egcd_rec nq _ _)).
            assert (Hn: (measure (Pmod p q) <= n)%nat) by (unfold measure, convert in *; rewrite Hq in *; destruct (degree (Pmod p q)); cbv in *; Lia.lia).
            assert (Hn': (measure (Pmod p q) <= n')%nat) by (unfold measure, convert in *; rewrite Hq in *; destruct (degree (Pmod p q)); cbv in *; Lia.lia).
            assert (Hnq: (measure (Pmod p q) <= nq)%nat) by (unfold measure, convert in *; rewrite Hq in *; destruct (degree (Pmod p q)); cbv in *; Lia.lia).
            simpl. destruct (IHn n' q _ Hn Hn') as [<- <-].
            simpl. destruct (IHn nq q _ Hn Hnq) as [<- <-].
            split; reflexivity. }
      intros p q Hqnz. unfold Pegcd; fold egcd_rec.
      destruct (IH _ _ q (Pmod p q) ltac:(reflexivity) ltac:(reflexivity)) as [<- <-].
      destruct (degree q) as [nq|] eqn:Hq; [|elim Hqnz; apply zero_degree; auto].
      unfold measure; rewrite Hq; simpl.
      destruct (Peq_dec q Pzero) as [|_]; [contradiction|].
      rewrite (surjective_pairing (egcd_rec _ _ _)). simpl.
      generalize (Pmod_degree_lt p q Hqnz). intro Hlt.
      assert (Hle: (measure (Pmod p q) <= nq)%nat) by (unfold measure, convert in *; rewrite Hq in *; destruct (degree (Pmod p q)); cbv in *; Lia.lia).
      destruct (IH _ _ q _ ltac:(reflexivity) Hle) as [<- <-].
      split; reflexivity.
    Qed.

    (* We do not generally have equality here as we do not enforce the GCD
       to be monic *)
    Lemma Pgcd_comm p q:
      Pdivides (Pgcd p q) (Pgcd q p) /\ Pdivides (Pgcd q p) (Pgcd p q).
    Proof. split; apply Pgcd_greatest; apply Pgcd_divides_lr. Qed.

    Lemma Pegcd_bezout:
      forall p q, Peq (Padd (Pmul (fst (Pegcd p q)) p) (Pmul (snd (Pegcd p q)) q)) (Pgcd p q).
    Proof.
      assert (IH: forall n p q, (measure q <= n)%nat -> Peq (Padd (Pmul (fst (Pegcd p q)) p) (Pmul (snd (Pegcd p q)) q)) (Pgcd p q)).
      { induction n; intros p q Hle.
        - unfold measure in *.
          destruct (degree q) eqn:Hqz; [inversion Hle|].
          apply zero_degree in Hqz.
          destruct (peq_egcd_proper p _ ltac:(reflexivity) _ _ Hqz) as [-> ->].
          destruct (Pegcd_0_r p) as [-> ->].
          rewrite mul_0_l, left_identity, right_identity.
          rewrite Hqz, Pgcd_0_r. reflexivity.
        - destruct (Peq_dec q Pzero) as [Hqz|Hqnz].
          { destruct (peq_egcd_proper p _ ltac:(reflexivity) _ _ Hqz) as [-> ->].
            destruct (Pegcd_0_r p) as [-> ->].
            rewrite Hqz, Pgcd_0_r, mul_0_l, left_identity, right_identity; reflexivity. }
          destruct (degree q) as [nq|] eqn:Hq; [|elim Hqnz; apply zero_degree; auto].
          generalize (Pmod_degree_lt p q Hqnz). intro Hlt.
          assert (Hn: (measure (Pmod p q) <= n)%nat) by (unfold measure, convert in *; rewrite Hq in *; destruct (degree (Pmod p q)); cbv in *; Lia.lia).
          rewrite Pgcd_mod.
          rewrite <- (IHn q _ Hn).
          destruct (Pegcd_mod p q Hqnz) as [-> ->].
          assert (Heq: Peq (Pmod p q) (Psub p (Pmul (Pdiv p q) q))) by (rewrite (Pdivmod_eq_spec p q) at 2; rewrite ring_sub_definition, <- associative, (commutative (Pmod _ _)), associative, right_inverse, left_identity; reflexivity).
          rewrite Heq at 6.
          clear Heq.
          rewrite ring_sub_definition, ring_sub_definition, right_distributive, left_distributive.
          rewrite associative, associative.
          rewrite (commutative (Pmul (snd _) _)).
          rewrite mul_opp_l, mul_opp_r.
          rewrite associative. reflexivity. }
      intros p q; apply (IH _ p q ltac:(reflexivity)).
    Qed.

    Lemma Pgcd_bezout:
      forall p q, exists u v, Peq (Padd (Pmul u p) (Pmul v q)) (Pgcd p q).
    Proof.
      intros p q. eexists; eexists. apply (Pegcd_bezout p q).
    Qed.

    Lemma Pdivides_degree_zero p q:
      degree p = Some 0%nat :> _ -> Pdivides p q.
    Proof.
      intro Hd0. generalize (degree_0_const _ Hd0).
      intro Heq. rewrite Heq. apply Pdivides_iff.
      generalize (degree_definition p); rewrite Hd0.
      intros [Hnz Hs].
      exists (Pmul q (Pconst (Finv (coeff p 0)))).
      intro k. rewrite mul_const_coeff_r, mul_const_coeff_r.
      rewrite associative, right_multiplicative_inverse; auto.
      rewrite left_identity. reflexivity.
    Qed.

    Lemma Pgcd_same_degree p q:
      degree (Pgcd p q) = degree (Pgcd q p) :> _.
    Proof.
      generalize (Pgcd_comm p q); intros [A B].
      apply Pdivides_iff in A, B.
      destruct A as [c1 A]. destruct B as [c2 B].
      generalize (mul_degree_eq c1 (Pgcd p q)); rewrite <- A at 1.
      generalize (mul_degree_eq c2 (Pgcd q p)); rewrite <- B at 1.
      intros BB AA. rewrite AA.
      destruct (degree (Pgcd p q)) as [np|] eqn:Hpq; [|destruct (degree c1); simpl; reflexivity].
      destruct (degree (Pgcd q p)) as [nq|] eqn:Hqp; [|destruct (degree c2); simpl in BB; congruence].
      destruct (degree c1) as [nc1|] eqn:Hc1; [|simpl in AA; congruence].
      destruct (degree c2) as [nc2|] eqn:Hc2; [|simpl in BB; congruence].
      rewrite BB in AA; simpl in AA. inversion AA.
      assert (nc1 = 0%nat :> _ /\ nc2 = 0%nat :> _) as [-> ->] by Lia.lia.
      simpl. reflexivity.
    Qed.

    Lemma Pdivides_gcd p q:
      Pdivides q p -> Peq (Pgcd p q) q.
    Proof.
      unfold Pdivides; intro A.
      rewrite Pgcd_mod, A, Pgcd_0_r.
      reflexivity.
    Qed.

    Definition coprime p q :=
      degree (Pgcd p q) = Some 0%nat :> _.

    Global Instance peq_proper_coprime: Proper (Peq ==> Peq ==> iff) coprime.
    Proof.
      intros p1 p1' Heq1 p2 p2' Heq2.
      unfold coprime. rewrite Heq1, Heq2. reflexivity.
    Qed.

    Lemma coprime_comm p q:
      coprime p q <-> coprime q p.
    Proof. unfold coprime; rewrite Pgcd_same_degree. reflexivity. Qed.

    Lemma Pegcd_bezout_coprime p q:
      coprime p q -> Peq (Padd (Pmul (Pdiv (fst (Pegcd p q)) (Pgcd p q)) p) (Pmul (Pdiv (snd (Pegcd p q)) (Pgcd p q)) q)) Pone.
    Proof.
      intro Hcoprime. generalize (Pegcd_bezout p q). intro Heq.
      pose (u := (fst (Pegcd p q))). pose (v := (snd (Pegcd p q))).
      generalize (Pdivides_degree_zero (Pgcd p q) u Hcoprime). intro Hu.
      generalize (Pdivides_degree_zero (Pgcd p q) v Hcoprime). intro Hv.
      assert (Hnz: not (Peq (Pgcd p q) Pzero)) by (intro He; unfold coprime in Hcoprime; rewrite He, degree_zero in Hcoprime; congruence).
      rewrite <- (Pdiv_same (Pgcd p q) Hnz).
      rewrite Pmul_div_l, Pmul_div_l by assumption.
      rewrite <- Pdiv_distr. rewrite Heq. reflexivity.
    Qed.

    Lemma Bezout_coprime p q:
      coprime p q -> exists u v, Peq (Padd (Pmul u p) (Pmul v q)) Pone.
    Proof.
      intro Hcoprime. eexists; eexists.
      apply Pegcd_bezout_coprime; auto.
    Qed.

    Lemma gauss_divides_r d p q:
      coprime d p -> Pdivides d (Pmul p q) -> Pdivides d q.
    Proof.
      intros Hcoprime Hdiv.
      destruct (Bezout_coprime d p Hcoprime) as (u & v & Heq).
      apply Pdivides_iff. apply Pdivides_iff in Hdiv.
      destruct Hdiv as (kpq & Hdiv).
      exists (Padd (Pmul q u) (Pmul v kpq)).
      transitivity (Pmul q Pone); [symmetry; apply right_identity|].
      rewrite <- Heq. rewrite left_distributive.
      rewrite (associative q v), (commutative q v), <- (associative v q), (commutative q p), Hdiv.
      rewrite right_distributive, associative, associative.
      reflexivity.
    Qed.

    Lemma gauss_divides_l d p q:
      coprime d p -> Pdivides d (Pmul q p) -> Pdivides d q.
    Proof. rewrite commutative. apply gauss_divides_r. Qed.

    Lemma coprime_divides p1 p2 q:
      coprime p1 p2 -> Pdivides p1 q -> Pdivides p2 q -> Pdivides (Pmul p1 p2) q.
    Proof.
      intros Hco Hdiv1 Hdiv2.
      apply Pdivides_iff in Hdiv2.
      destruct Hdiv2 as (c2 & Hdiv2).
      rewrite Hdiv2 in Hdiv1.
      generalize (gauss_divides_l _ _ _ Hco Hdiv1). intros Hdiv.
      apply Pdivides_iff in Hdiv. destruct Hdiv as (c & Hdiv).
      rewrite Hdiv in Hdiv2. rewrite Hdiv2.
      apply Pdivides_iff.
      exists c. rewrite associative. reflexivity.
    Qed.

    Lemma coprime_mul_r p q1 q2:
      coprime p q1 -> coprime p q2 -> coprime p (Pmul q1 q2).
    Proof.
      unfold coprime; intros A B.
      generalize (Pgcd_divides_lr p (Pmul q1 q2)); intros [C1 C2].
      assert (D: coprime (Pgcd p (Pmul q1 q2)) q1).
      { unfold coprime. generalize (Pgcd_divides_lr (Pgcd p (Pmul q1 q2)) q1); intros [D1 D2].
        generalize (Pdivides_trans _ _ _ D1 C1). intro E.
        generalize (Pgcd_greatest _ _ _ E D2). intro G.
        apply Pdivides_iff in G. destruct G as [c G].
        rewrite G, mul_degree_eq in A.
        destruct (degree c) as [nc|]; [|simpl in A; congruence].
        destruct (degree (Pgcd (Pgcd p (Pmul q1 q2)) q1)) as [n|]; simpl in A; [|congruence].
        inversion A; f_equal. Lia.lia. }
      generalize (gauss_divides_r _ q1 q2 D C2).
      intro E. generalize (Pgcd_greatest _ _ _ C1 E). intro G.
      apply Pdivides_iff in G. destruct G as [c G].
      rewrite G, mul_degree_eq in B.
      destruct (degree c) as [nc|]; [|simpl in B; congruence].
      destruct (degree (Pgcd p (Pmul q1 q2))) as [n|]; simpl in B; [|congruence].
      inversion B; f_equal; Lia.lia.
    Qed.

    Lemma coprime_mul_l q1 q2 p:
      coprime q1 p -> coprime q2 p -> coprime (Pmul q1 q2) p.
    Proof.
      intros A B. apply coprime_comm. apply coprime_mul_r; apply coprime_comm; auto.
    Qed.
  End DivMod.
  Section Decomposition.
    Context {Finv: F -> F}{Fdiv: F -> F -> F}
      {field: @field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}.

    Local Notation Pdivmod := (@Pdivmod Fdiv).
    Local Notation Pdiv := (@Pdiv Fdiv).
    Local Notation Pmod := (@Pmod Fdiv).

    (* Show that base is actually a base system for polynomials *)
    (* p = Σ p_i X^i *)
    Definition Pdecompose (p: P): P :=
      @bigop _ Padd Pzero _ (seq 0 (measure p)) (fun k => Pmul (Pconst (coeff p k)) (base k)).

    Lemma coeff_bigop n c:
      forall i, coeff (@bigop _ Padd Pzero _ (seq 0 n) (fun k => Pmul (Pconst (c k)) (base k))) i = @bigop F Fadd Fzero _ (seq 0 n) (fun k => coeff (Pmul (Pconst (c k )) (base k)) i).
    Proof.
      induction n; intros; [simpl; apply zero_definition|].
      rewrite seq_S, (@bigop_app F) by typeclasses eauto.
      rewrite <- IHn; simpl.
      etransitivity; [generalize ((bigop_app (fun k : nat => Pmul (Pconst (c k)) (base k)) (seq 0 n) (n::nil)) i); eauto|].
      rewrite add_definition; simpl.
      rewrite add_definition, zero_definition; reflexivity.
    Qed.

    Global Instance peq_proper_decompose: Proper (Peq ==> Peq) Pdecompose.
    Proof.
      intros p1 p2 Heq. unfold Pdecompose.
      assert (measure p1 = measure p2 :> _) as -> by (unfold measure; rewrite Heq; reflexivity).
      apply bigop_ext_eq; intros i Hi.
      rewrite (Heq i). reflexivity.
    Qed.

    Lemma Pdecompose_add p1 p2:
      Peq (Pdecompose (Padd p1 p2)) (Padd (Pdecompose p1) (Pdecompose p2)).
    Proof.
      pose (n := max (measure p1) (measure p2)).
      assert (exists n1, n = measure p1 + n1 :> _)%nat as [n1 Hn1] by (exists (n - measure p1)%nat; Lia.lia).
      assert (exists n2, n = measure p2 + n2 :> _)%nat as [n2 Hn2] by (exists (n - measure p2)%nat; Lia.lia).
      assert (Hn: measure (Padd p1 p2) <= n).
      { generalize (add_degree p1 p2). unfold measure, convert in *.
        destruct (degree (Padd p1 p2)); destruct (degree p1); destruct (degree p2); cbv -[degree_lt_dec Nat.max] in *; destruct (degree_lt_dec _ _); try Lia.lia. }
      assert (exists nn, n = measure (Padd p1 p2) + nn :> _)%nat as [nn Hnn] by (exists (n - (measure (Padd p1 p2)))%nat; Lia.lia).
      assert (Hlt: forall p k, (measure p <= k)%nat -> coeff p k = 0).
      { intros p k Hk. unfold measure, convert in Hk.
        generalize (degree_definition p). destruct (degree p); auto.
        intros [X Y]; apply Y; Lia.lia. }
      unfold Pdecompose.
      rewrite (bigop_widen _ (seq 0 (measure p1)) (seq (measure p1) n1)) by (intros i Hi k; apply in_seq in Hi; rewrite mul_const_base_coeff, zero_definition; destruct (dec_eq_nat i k); [apply Hlt; Lia.lia|reflexivity]).
      rewrite <- seq_add, <- Hn1.
      rewrite (bigop_widen _ (seq 0 (measure p2)) (seq (measure p2) n2)) by (intros i Hi k; apply in_seq in Hi; rewrite mul_const_base_coeff, zero_definition; destruct (dec_eq_nat i k); [apply Hlt; Lia.lia|reflexivity]).
      rewrite <- seq_add, <- Hn2.
      rewrite (bigop_widen _ (seq 0 (measure (Padd p1 p2))) (seq (measure (Padd p1 p2)) nn)) by (intros i Hi k; apply in_seq in Hi; rewrite mul_const_base_coeff, zero_definition; destruct (dec_eq_nat i k); [apply Hlt; Lia.lia|reflexivity]).
      rewrite <- seq_add, <- Hnn.
      rewrite bigop_same_index. apply bigop_ext_eq.
      intros i Hi. rewrite <- right_distributive, const_add_const, add_definition.
      reflexivity.
    Qed.

    Lemma Pdecompose_eq:
      forall p, Peq p (Pdecompose p).
    Proof.
      assert (IH: forall n p, (measure p <= n)%nat -> Peq p (Pdecompose p)).
      { induction n; intros p Hm.
        - unfold Pdecompose. assert (measure p = 0 :> _)%nat as -> by Lia.lia.
          simpl. unfold measure, convert in Hm.
          destruct (degree p) as [np|] eqn:Hnp; [Lia.lia|apply zero_degree; auto].
        - assert (measure p <= n \/ measure p = S n :> _)%nat as [A|A] by Lia.lia.
          + apply IHn; auto.
          + unfold measure, convert in A. destruct (degree p) as [np|] eqn:Hnp; [|congruence].
            inversion A; subst np; clear A.
            generalize (Pmod_degree_lt p (base n) (base_not_zero n)); intro Hlt.
            rewrite degree_base in Hlt.
            assert (Hm': (measure (Pmod p (base n)) <= n)%nat).
            { unfold measure, convert.
              destruct (degree (Pmod p (base n))); cbv in Hlt; Lia.lia. }
            assert (Heq': Peq p (Padd (Pmul (Pconst (coeff p n)) (base n)) (Pmod p (base n)))).
            { intro k. rewrite add_definition, mul_const_base_coeff.
              assert (k < n \/ k >= n)%nat as [Hk_lt|Hk_ge] by Lia.lia.
              - destruct (dec_eq_nat n k); [Lia.lia|].
                rewrite left_identity, (Pdivmod_eq_spec p (base n) k), add_definition, mul_definition.
                assert (mul_coeff (coeff (Pdiv p (base n))) (coeff (base n)) k = 0) as ->; [|rewrite left_identity; reflexivity].
                unfold mul_coeff. rewrite (bigop_ext_eq _ _ (fun _ => 0)); [rewrite bigop_const; rewrite mul_0_r; reflexivity|].
                intros i Hin; apply in_seq in Hin.
                rewrite base_definition.
                destruct (dec_eq_nat n (k - i)); [Lia.lia|].
                apply mul_0_r.
              - assert (coeff (Pmod p (base n)) k = 0) as ->.
                { generalize (degree_definition (Pmod p (base n))).
                  destruct (degree (Pmod p (base n))); cbv in Hlt; auto.
                  intros [X Y]; apply Y; Lia.lia. }
                rewrite right_identity.
                destruct (dec_eq_nat n k); [subst k; reflexivity|].
                generalize (degree_definition p); rewrite Hnp; intros [X Y].
                apply Y; Lia.lia. }
            rewrite Heq', Pdecompose_add, <- (IHn _ Hm').
            assert (Peq (Pdecompose _) (Pmul (Pconst (coeff p n)) (base n))) as ->; [|reflexivity].
            unfold Pdecompose.
            assert (measure _ = S n :> _) as ->.
            { unfold measure. rewrite mul_degree_eq, degree_base, degree_const.
              destruct (Feq_dec (coeff p n) 0); simpl; [|Lia.lia].
              generalize (degree_definition p); rewrite Hnp.
              intros [X Y]; contradiction. }
            rewrite seq_S, bigop_app; simpl.
            rewrite (bigop_ext_eq _ _ (fun _ => Pzero)).
            2: { intros i Hi. apply in_seq in Hi. intro k.
                 rewrite zero_definition, mul_definition.
                 unfold mul_coeff.
                 rewrite (bigop_ext_eq _ _ (fun _ => 0)); [rewrite bigop_const, mul_0_r; reflexivity|].
                 intros j Hj. rewrite base_definition, const_definition.
                 destruct j; [|apply mul_0_l].
                 rewrite mul_const_base_coeff.
                 destruct (dec_eq_nat n i); [|apply mul_0_l].
                 destruct (dec_eq_nat i (k - 0)%nat); Lia.lia. }
            rewrite bigop_const, mul_0_r, left_identity, right_identity.
            intro k. rewrite mul_const_base_coeff.
            rewrite (mul_const_base_coeff (coeff p n) n k).
            destruct (dec_eq_nat n k); [|reflexivity].
            rewrite mul_const_base_coeff.
            destruct (dec_eq_nat _ _); [|congruence]. reflexivity. }
      intros; eapply IH. reflexivity.
    Qed.

    Lemma Pdecompose_coeff n c:
      forall i, coeff (@bigop _ Padd Pzero _ (seq 0 n) (fun k => Pmul (Pconst (c k)) (base k))) i = if dec_lt_nat i n then c i else 0.
    Proof.
      intro i.
      transitivity (@bigop _ Fadd Fzero _ (seq 0 n) (fun k => coeff (Pmul (Pconst (c k)) (base k)) i)); [apply coeff_bigop|].
      destruct (dec_lt_nat i n).
      - assert (n = i + (n - i) :> _)%nat as -> by Lia.lia.
        rewrite seq_add, bigop_app; simpl.
        rewrite (bigop_ext_eq (seq 0 _) _ (fun _ => 0)) by (intros j Hj; apply in_seq in Hj; rewrite mul_const_base_coeff; destruct (dec_eq_nat _ _); [Lia.lia|reflexivity]).
        rewrite bigop_const, mul_0_r, left_identity.
        assert (n - i = S (pred (n - i)) :> _)%nat as -> by Lia.lia.
        simpl. rewrite (bigop_ext_eq _ _ (fun _ => 0)) by (intros j Hj; apply in_seq in Hj; rewrite mul_const_base_coeff; destruct (dec_eq_nat _ _); [Lia.lia|reflexivity]).
        rewrite bigop_const, mul_0_r, right_identity.
        rewrite mul_const_base_coeff.
        destruct (dec_eq_nat _ _); [|congruence]. reflexivity.
      - rewrite (bigop_ext_eq _ _ (fun _ => 0)) by (intros j Hj; apply in_seq in Hj; rewrite mul_const_base_coeff; destruct (dec_eq_nat _ _); [Lia.lia|reflexivity]).
        rewrite bigop_const, mul_0_r. reflexivity.
    Qed.

    (* First n coefficients of P *)
    Definition to_list (n: nat) (p: P): list F :=
      List.map (coeff p) (seq 0%nat n).

    Definition of_list (l: list F): P :=
      @bigop _ Padd Pzero _ (seq 0%nat (length l)) (fun k => Pmul (Pconst (nth_default 0 l k)) (base k)).

    Lemma to_list_length (p: P) (n: nat):
      length (to_list n p) = n :> _.
    Proof. unfold to_list. rewrite length_map, length_seq. reflexivity. Qed.

    Lemma to_list_nth_default_inbounds (p: P) (n: nat) d:
      forall k,
        (k < n)%nat ->
        nth_default d (to_list n p) k = coeff p k.
    Proof.
      intros. unfold to_list.
      erewrite map_nth_default by (rewrite length_seq; auto).
      instantiate (1 := 0%nat).
      rewrite nth_default_seq_inbounds; auto.
      reflexivity.
    Qed.

    Lemma of_list_to_list (p: P) (n: nat) (Hlt: degree_lt (degree p) (Some n)):
      Peq (of_list (to_list n p)) p.
    Proof.
      intro k. unfold of_list. rewrite Pdecompose_coeff, to_list_length.
      generalize (degree_definition p). intro Hp.
      destruct (degree p) as [np|] eqn:Hpdeg; [destruct Hp as [Hp1 Hp2]|].
      - cbv in Hlt. destruct (dec_lt_nat k n).
        + unfold to_list. assert (coeff p (S np) = 0) as <- by (apply Hp2; Lia.lia).
          rewrite map_nth_default_always, nth_default_seq_inbounds; auto.
          reflexivity.
        + symmetry; apply Hp2; Lia.lia.
      - destruct (dec_lt_nat k n); [|symmetry; apply Hp].
        unfold to_list. rewrite <- (Hp k), map_nth_default_always, nth_default_seq_inbounds; auto.
        reflexivity.
    Qed.

    Lemma to_list_of_list (l: list F):
      Forall2 Feq (to_list (length l) (of_list l)) l.
    Proof.
      erewrite Forall2_forall_iff; rewrite to_list_length; [|reflexivity].
      intros i Hlt. instantiate (1:=0). instantiate (1:=0).
      rewrite to_list_nth_default_inbounds by assumption.
      unfold of_list. rewrite Pdecompose_coeff.
      destruct (dec_lt_nat i (length l)); [|Lia.lia].
      reflexivity.
    Qed.

    Lemma to_list_scale (n: nat) (a: F) (p: P):
      Forall2 Feq (List.map (Fmul a) (to_list n p)) (to_list n (Pmul (Pconst a) p)).
    Proof.
      rewrite (Forall2_forall_iff _ _ _ 0 0) by (rewrite length_map, to_list_length, to_list_length; reflexivity).
      intros i Hi. rewrite length_map in Hi.
      rewrite (map_nth_default _ _ _ _ 0); auto.
      rewrite to_list_length in Hi. rewrite to_list_nth_default_inbounds, to_list_nth_default_inbounds; auto.
      rewrite mul_const_coeff_l. reflexivity.
    Qed.

    Lemma of_list_degree_lt (l: list F):
      degree_lt (degree (of_list l)) (Some (length l)).
    Proof.
      destruct (degree (of_list l)) eqn:Hdegree; [|cbv; Lia.lia].
      unfold degree_lt; simpl.
      destruct (dec_lt_nat n (length l)); [Lia.lia|].
      pose proof (degree_definition (of_list l)) as Hl.
      rewrite Hdegree in Hl. destruct Hl as [Ha Hb].
      elim Ha. unfold of_list; rewrite Pdecompose_coeff.
      destruct (dec_lt_nat n (length l)); [Lia.lia|]. reflexivity.
    Qed.
  End Decomposition.
  Section Pquot.
    Context {Finv: F -> F}{Fdiv: F -> F -> F}
      {field: @field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
      {char_ge_3: @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "/" := Fdiv.

    Local Notation Pdivmod := (@Pdivmod Fdiv).
    Local Notation Pdiv := (@Pdiv Fdiv).
    Local Notation Pmod := (@Pmod Fdiv).
    Local Notation Pgcd := (@Pgcd Fdiv).
    Local Notation Pegcd := (@Pegcd Fdiv).
    Local Notation Pdivides := (@Pdivides Fdiv).
    Local Notation coprime := (@coprime Fdiv).

    Definition Pquot (q: P): Type := { p: P | Peq p (Pmod p q) }.

    Section PquotOperations.
      Definition to_P {q} (p: Pquot q) := proj1_sig p.
      Context {q: P}.
      Program Definition of_P (p: P): Pquot q := Pmod p q.
      Next Obligation. symmetry. apply Pmod_mod_eq. Qed.

      Definition eq1 {q'} (p1: Pquot q) (p2: Pquot q'): Prop :=
        Peq (to_P p1) (to_P p2).
      Definition zero: Pquot q := of_P Pzero.
      Definition one: Pquot q := of_P Pone.

      Definition add (p1 p2: Pquot q): Pquot q :=
        of_P (Padd (to_P p1) (to_P p2)).
      Definition mul (p1 p2: Pquot q): Pquot q :=
        of_P (Pmul (to_P p1) (to_P p2)).
      Definition opp (p: Pquot q): Pquot q :=
        of_P (Popp (to_P p)).
      Definition sub (p1 p2: Pquot q): Pquot q :=
        add p1 (opp p2).

      Global Instance peq_proper_of_P: Proper (Peq ==> eq1) of_P.
      Proof. intros x y Heq. unfold eq1; simpl. rewrite Heq. reflexivity. Qed.
    End PquotOperations.
    Section PquotRing.
      Context {q: P}.

      Ltac unwrap_Pquot :=
        match goal with
        | |- Proper _ _ => unfold Proper, respectful
        | |- Reflexive _ => unfold Reflexive
        | |- Symmetric _ => unfold Symmetric
        | |- Transitive _ => unfold Transitive
        | |- _ => idtac end;
        intros;
        repeat match goal with | [ x : Pquot _ |- _ ] => destruct x end;
        lazy iota beta delta [eq1 zero one add mul opp sub of_P to_P proj1_sig] in *.
      Global Instance PquotRing:
        @commutative_ring (Pquot q) eq1 zero one opp add sub mul.
      Proof.
        repeat constructor; unwrap_Pquot.
        - rewrite Padd_mod_idemp_l, Padd_mod_idemp_r, associative.
          reflexivity.
        - rewrite Pmod_0_l, left_identity.
          symmetry; assumption.
        - rewrite Pmod_0_l, right_identity.
          symmetry; assumption.
        - rewrite H, H0. reflexivity.
        - reflexivity.
        - symmetry; assumption.
        - etransitivity; eauto.
        - rewrite Padd_mod_idemp_l, left_inverse. reflexivity.
        - rewrite Padd_mod_idemp_r, right_inverse. reflexivity.
        - rewrite H; reflexivity.
        - rewrite commutative; reflexivity.
        - rewrite Pmul_mod_idemp_l, Pmul_mod_idemp_r, associative.
          reflexivity.
        - rewrite Pmul_mod_idemp_l, left_identity. symmetry; assumption.
        - rewrite Pmul_mod_idemp_r, right_identity. symmetry; assumption.
        - rewrite H, H0. reflexivity.
        - reflexivity.
        - symmetry; assumption.
        - etransitivity; eauto.
        - rewrite Padd_mod_idemp_l, Padd_mod_idemp_r, Pmul_mod_idemp_r, <- left_distributive.
          reflexivity.
        - rewrite Padd_mod_idemp_l, Padd_mod_idemp_r, Pmul_mod_idemp_l, <- right_distributive.
          reflexivity.
        - reflexivity.
        - rewrite H, H0. reflexivity.
        - rewrite H, H0. reflexivity.
        - rewrite commutative. reflexivity.
      Qed.
    End PquotRing.
    Section PquotConvertRingIsomorphism.
      Program Definition Pquot_convert {q1 q2} (Heq: Peq q1 q2) (p: Pquot q1): Pquot q2 := proj1_sig p.
      Next Obligation.
        rewrite (proj2_sig p). apply peq_mod_proper; auto. apply (proj2_sig p).
      Qed.

      Lemma Pquot_convert_isomorphism {q1 q2} (Heq1: Peq q1 q2) (Heq2: Peq q2 q1):
        @Ring.is_isomorphism
          (Pquot q1) eq1 one add mul
          (Pquot q2) eq1 one add mul
          (Pquot_convert Heq1)
          (Pquot_convert Heq2).
      Proof.
        constructor.
        - repeat constructor.
          + intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
            unfold eq1; cbn. apply peq_mod_proper; [reflexivity|assumption].
          + intros a b H. destruct a as (a & Ha). destruct b as (b & Hb).
            unfold eq1 in *; cbn in *. assumption.
          + intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
            unfold eq1; cbn. apply peq_mod_proper; [reflexivity|assumption].
          + unfold eq1; cbn. apply peq_mod_proper; [reflexivity|assumption].
        - intro a. destruct a as (a & Ha); unfold eq1; simpl. reflexivity.
        - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
          unfold eq1; simpl. auto.
      Qed.
    End PquotConvertRingIsomorphism.
    Section PquotRingListIsomorphism.
      Definition Pquot' (q: P): Type :=
        { l : list F | length l = (measure q - 1)%nat :> _ }.

      Context {q: P} {Hqnz: not (Peq q Pzero)}.
      Program Definition to_list' (p: Pquot q): Pquot' q :=
        to_list (measure q - 1)%nat (proj1_sig p).
      Next Obligation. apply to_list_length. Qed.

      Program Definition of_list' (p: Pquot' q): Pquot q :=
        of_list (proj1_sig p).
      Next Obligation.
        symmetry. apply Pmod_small.
        assert (degree q = Some (length (proj1_sig p)) :> _) as ->.
        { rewrite (proj2_sig p). unfold measure.
          unfold convert. pose proof (degree_definition q) as H.
          pose proof (zero_degree q).
          destruct (degree q); [f_equal; Lia.lia|elim Hqnz; tauto]. }
        apply of_list_degree_lt.
      Qed.

      Definition eq' (p1 p2: Pquot' q): Prop := List.Forall2 Feq (proj1_sig p1) (proj1_sig p2).

      Program Definition zero': Pquot' q := List.repeat Fzero (measure q - 1)%nat.
      Next Obligation. apply repeat_length. Qed.

      Definition one': Pquot' q := to_list' one.

      Program Definition opp' (p: Pquot' q): Pquot' q :=
        List.map Fopp (proj1_sig p).
      Next Obligation. rewrite length_map, (proj2_sig p). reflexivity. Qed.

      Program Definition add' (p1 p2: Pquot' q): Pquot' q :=
        List.map2 Fadd (proj1_sig p1) (proj1_sig p2).
      Next Obligation. rewrite map2_length, (proj2_sig p1), (proj2_sig p2), PeanoNat.Nat.min_id; reflexivity. Qed.

      Program Definition sub' (p1 p2: Pquot' q): Pquot' q :=
        List.map2 Fsub (proj1_sig p1) (proj1_sig p2).
      Next Obligation. rewrite map2_length, (proj2_sig p1), (proj2_sig p2), PeanoNat.Nat.min_id; reflexivity. Qed.

      Definition mul' (p1 p2: Pquot' q): Pquot' q :=
        to_list' (mul (of_list' p1) (of_list' p2)).

      Global Instance PquotRing':
        @commutative_ring (Pquot' q) eq' zero' one' opp' add' sub' mul'.
      Proof.
        repeat match goal with
               | [ H : eq' _ _  |- _ ] => unfold eq' in H; rewrite (Forall2_forall_iff _ _ _ Fzero Fzero) in H
               | [ |- eq' _ _ ] => apply (Forall2_forall_iff _ _ _ Fzero Fzero); repeat rewrite (proj2_sig (_: Pquot' q)); [reflexivity|]
               | |- context [nth_default _ (map2 _ _ _) _] => rewrite (nth_default_map2 _ _ _ _ _ Fzero Fzero)
               | |- context [nth_default _ (map _ _) _] => rewrite (map_nth_default _ _ _ _ Fzero) by (rewrite (proj2_sig (_: Pquot' q)); assumption)
               | |- context [nth_default _ (map _ _) _] => rewrite (map_nth_default _ _ _ _ 0%nat) by (rewrite length_seq; assumption)
               | |- context [nth_default _ (repeat _ _) _] => rewrite (nth_default_repeat _ _ _ Fzero)
               | |- context [nth_default _ (seq 0%nat _) _] => rewrite nth_default_seq_inbounds, PeanoNat.Nat.add_0_l by assumption
               | |- context [length (map _ _)] => rewrite length_map
               | |- context [length (map2 _ _ _)] => rewrite map2_length
               | H :context [length (proj1_sig _)] |- _ => rewrite (proj2_sig (_: Pquot' q)) in H
               | |- context [length (proj1_sig _)] => rewrite (proj2_sig (_: Pquot' q))
               | |- context [length (seq _ _)] => rewrite length_seq
               | |- context [length (repeat _ _)] => rewrite repeat_length
               | |- context [Nat.min _ _] => rewrite PeanoNat.Nat.min_id
               | |- context [dec (_ < measure q - 1)%nat] => destruct (dec (_ < measure q - 1)%nat); [|Lia.lia]
               | |- context [Compare_dec.lt_dec _ (measure q - 1)%nat] => destruct (Compare_dec.lt_dec _ (measure q - 1)%nat); [|Lia.lia]
               | _ => intro
               | _ => split
               | _ => unfold add', sub', opp', mul', zero'; cbn [proj1_sig]
               end.
        - apply associative.
        - apply left_identity.
        - apply right_identity.
        - rewrite H, H0 by assumption; reflexivity.
        - reflexivity.
        - rewrite H by assumption; reflexivity.
        - rewrite H, H0 by assumption; reflexivity.
        - apply left_inverse.
        - apply right_inverse.
        - rewrite H by assumption; reflexivity.
        - apply commutative.
        - unfold to_list'; simpl.
          repeat rewrite to_list_nth_default_inbounds by Lia.lia.
          match goal with
          | |- coeff ?x1 _ = coeff ?x2 _ => assert (Peq x1 x2) as Hx; [|apply Hx]
          end.
          repeat rewrite of_list_to_list.
          2-3: assert (Some _ = degree q :> _) as ->; [|apply Pmod_degree_lt; auto].
          2-3: unfold measure, convert; pose proof (zero_degree q) as Hq; destruct (degree q); try tauto; simpl; f_equal; Lia.lia.
          rewrite Pmul_mod_idemp_l, Pmul_mod_idemp_r, associative. reflexivity.
        - unfold to_list'; simpl.
          repeat rewrite to_list_nth_default_inbounds by Lia.lia.
          match goal with
          | |- coeff ?px _ = _ => assert (Peq px (of_list (proj1_sig x))) as Hx
          end.
          2: rewrite (Hx i); unfold of_list; rewrite Pdecompose_coeff, (proj2_sig x); destruct (dec_lt_nat _ _); [reflexivity|Lia.lia].
          rewrite of_list_to_list.
          2: assert (Some _ = degree q :> _) as ->; [|apply Pmod_degree_lt; auto].
          2: unfold measure, convert; pose proof (zero_degree q) as Hq; destruct (degree q); try tauto; simpl; f_equal; Lia.lia.
          rewrite (Pmod_small Pone), left_identity. apply Pmod_small.
          2: rewrite degree_one.
          1-2: assert (Some (measure q - 1)%nat = degree q :> _) as <-.
          1,3: unfold measure, convert; pose proof (zero_degree q) as Hq; destruct (degree q); try tauto; simpl; f_equal; Lia.lia.
          rewrite <- (proj2_sig x) at 1. apply of_list_degree_lt.
          cbv. cbv in H. Lia.lia.
        - unfold to_list'; simpl.
          repeat rewrite to_list_nth_default_inbounds by Lia.lia.
          match goal with
          | |- coeff ?px _ = _ => assert (Peq px (of_list (proj1_sig x))) as Hx
          end.
          2: rewrite (Hx i); unfold of_list; rewrite Pdecompose_coeff, (proj2_sig x); destruct (dec_lt_nat _ _); [reflexivity|Lia.lia].
          rewrite of_list_to_list.
          2: assert (Some _ = degree q :> _) as ->; [|apply Pmod_degree_lt; auto].
          2: unfold measure, convert; pose proof (zero_degree q) as Hq; destruct (degree q); try tauto; simpl; f_equal; Lia.lia.
          rewrite (Pmod_small Pone), right_identity. apply Pmod_small.
          2: rewrite degree_one.
          1-2: assert (Some (measure q - 1)%nat = degree q :> _) as <-.
          1,3: unfold measure, convert; pose proof (zero_degree q) as Hq; destruct (degree q); try tauto; simpl; f_equal; Lia.lia.
          rewrite <- (proj2_sig x) at 1. apply of_list_degree_lt.
          cbv. cbv in H. Lia.lia.
        - unfold to_list'; simpl.
          repeat rewrite to_list_nth_default_inbounds by Lia.lia.
          match goal with
          | |- coeff ?p1 _ = coeff ?p2 _ => assert (Peq p1 p2) as Hx; [|apply Hx]
          end.
          assert (Peq (of_list (proj1_sig x)) (of_list (proj1_sig y))) as ->.
          { intro. unfold of_list; repeat rewrite Pdecompose_coeff.
            repeat rewrite (proj2_sig (_: Pquot' q)).
            destruct (dec_lt_nat k _); [apply H; auto|reflexivity]. }
          assert (Peq (of_list (proj1_sig x0)) (of_list (proj1_sig y0))) as ->.
          { intro. unfold of_list; repeat rewrite Pdecompose_coeff.
            repeat rewrite (proj2_sig (_: Pquot' q)).
            destruct (dec_lt_nat k _); [apply H0; auto|reflexivity]. }
          reflexivity.
        - reflexivity.
        - symmetry; apply H; assumption.
        - rewrite H by Lia.lia. apply H0; Lia.lia.
        - simpl. repeat rewrite to_list_nth_default_inbounds by assumption.
          rewrite <- add_definition.
          match goal with
          | |- coeff ?p1 _ = coeff ?p2 _ => assert (Peq p1 p2) as Hx; [|apply Hx]
          end.
          assert (Peq (of_list (map2 _ _ _)) (Padd (of_list (proj1_sig b)) (of_list (proj1_sig c)))) as ->.
          + intro. rewrite add_definition. unfold of_list.
            repeat rewrite Pdecompose_coeff. rewrite map2_length.
            erewrite nth_default_map2.
            repeat (rewrite (proj2_sig (_: Pquot' q))).
            rewrite PeanoNat.Nat.min_id.
            destruct (dec_lt_nat _ _); [|rewrite left_identity; reflexivity].
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
            reflexivity.
          + rewrite left_distributive.
            rewrite <- (Pmod_small (Padd (Pmod _ _) (Pmod _ _)) q).
            rewrite Padd_mod_idemp_l, Padd_mod_idemp_r. reflexivity.
            eapply degree_le_lt_trans; [apply add_degree|].
            apply degree_max_lub_lt; apply Pmod_degree_lt; auto.
        - simpl. repeat rewrite to_list_nth_default_inbounds by assumption.
          rewrite <- add_definition.
          match goal with
          | |- coeff ?p1 _ = coeff ?p2 _ => assert (Peq p1 p2) as Hx; [|apply Hx]
          end.
          assert (Peq (of_list (map2 _ _ _)) (Padd (of_list (proj1_sig b)) (of_list (proj1_sig c)))) as ->.
          + intro. rewrite add_definition. unfold of_list.
            repeat rewrite Pdecompose_coeff. rewrite map2_length.
            erewrite nth_default_map2.
            repeat (rewrite (proj2_sig (_: Pquot' q))).
            rewrite PeanoNat.Nat.min_id.
            destruct (dec_lt_nat _ _); [|rewrite left_identity; reflexivity].
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
            reflexivity.
          + rewrite right_distributive.
            rewrite <- (Pmod_small (Padd (Pmod _ _) (Pmod _ _)) q).
            rewrite Padd_mod_idemp_l, Padd_mod_idemp_r. reflexivity.
            eapply degree_le_lt_trans; [apply add_degree|].
            apply degree_max_lub_lt; apply Pmod_degree_lt; auto.
        - rewrite ring_sub_definition. reflexivity.
        - unfold to_list'; simpl. repeat rewrite to_list_nth_default_inbounds by assumption.
          match goal with
          | |- coeff ?p1 _ = coeff ?p2 _ => assert (Peq p1 p2) as Hx; [|apply Hx]
          end.
          assert (Peq (of_list (proj1_sig x)) (of_list (proj1_sig y))) as ->.
          { intro. unfold of_list; repeat rewrite Pdecompose_coeff.
            repeat rewrite (proj2_sig (_: Pquot' q)).
            destruct (dec_lt_nat k _); [apply H; auto|reflexivity]. }
          assert (Peq (of_list (proj1_sig x0)) (of_list (proj1_sig y0))) as ->.
          { intro. unfold of_list; repeat rewrite Pdecompose_coeff.
            repeat rewrite (proj2_sig (_: Pquot' q)).
            destruct (dec_lt_nat k _); [apply H0; auto|reflexivity]. }
          reflexivity.
        - rewrite H, H0 by Lia.lia. reflexivity.
        - unfold to_list'; simpl. repeat rewrite to_list_nth_default_inbounds by assumption.
          match goal with
          | |- coeff ?p1 _ = coeff ?p2 _ => assert (Peq p1 p2) as Hx; [|apply Hx]
          end.
          rewrite commutative. reflexivity.
      Qed.

      Lemma PquotRingIsomorphism:
        @Ring.is_isomorphism (Pquot q) eq1 one add mul (Pquot' q) eq' one' add' mul' to_list' of_list'.
      Proof.
        constructor.
        - repeat split.
          + intros. unfold eq'. apply (Forall2_forall_iff _ _ _ Fzero Fzero); repeat rewrite (proj2_sig (_: Pquot' q)); [reflexivity|].
            intros. unfold to_list'; simpl.
            rewrite (nth_default_map2 _ _ _ _ _ Fzero Fzero).
            repeat rewrite to_list_length. rewrite PeanoNat.Nat.min_id.
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
            repeat rewrite to_list_nth_default_inbounds by assumption.
            assert (degree_lt (degree (Padd (to_P a) (to_P b))) (degree q)) as Hadd.
            { eapply degree_le_lt_trans; [apply add_degree|].
              apply degree_max_lub_lt.
              - pose proof (Pmod_degree_lt (to_P a) _ Hqnz) as Ha.
                rewrite <- (proj2_sig a) in Ha. apply Ha.
              - pose proof (Pmod_degree_lt (to_P b) _ Hqnz) as Hb.
                rewrite <- (proj2_sig b) in Hb. apply Hb. }
            rewrite (Pmod_small (Padd _ _) q Hadd i).
            rewrite add_definition. reflexivity.
          + intros x y Heq. unfold eq'.
            apply (Forall2_forall_iff _ _ _ Fzero Fzero); repeat rewrite (proj2_sig (_: Pquot' q)); [reflexivity|].
            intros. simpl.
            repeat rewrite to_list_nth_default_inbounds by assumption.
            apply Heq.
          + intros. unfold eq', to_list'; simpl.
            apply (Forall2_forall_iff _ _ _ Fzero Fzero).
            * repeat rewrite to_list_length. reflexivity.
            * rewrite to_list_length. intros.
              repeat rewrite to_list_nth_default_inbounds by assumption.
              match goal with
              | |- coeff ?p1 _ = coeff ?p2 _ => assert (Peq p1 p2) as Hx; [|apply Hx]
              end.
              repeat rewrite of_list_to_list. reflexivity.
              rewrite (proj2_sig y).
              2: rewrite (proj2_sig x).
              1-2: assert (Some (measure q - 1)%nat = degree q :> _) as ->.
              2,4: apply Pmod_degree_lt; auto.
              1-2: unfold measure, convert; pose proof (zero_degree q) as Hq; destruct (degree q); try tauto; simpl; f_equal; Lia.lia.
          + unfold eq', to_list', one'. simpl.
            apply (Forall2_forall_iff _ _ _ Fzero Fzero); repeat rewrite (proj2_sig (_: Pquot' q)); reflexivity.
        - intros. apply (Forall2_forall_iff _ _ _ Fzero Fzero); repeat rewrite (proj2_sig (_: Pquot' q)); [reflexivity|].
          intros. simpl. rewrite to_list_nth_default_inbounds by assumption.
          unfold of_list. rewrite Pdecompose_coeff. rewrite (proj2_sig (_: Pquot' q)).
          destruct (dec_lt_nat _ _); [|Lia.lia]. reflexivity.
        - intros. destruct a as (a & Ha). destruct b as (b & Hb).
          unfold eq', to_list' in H; simpl in H.
          unfold eq1; simpl. intro.
          pose proof (Pmod_degree_lt a q Hqnz) as Ha'.
          pose proof (Pmod_degree_lt b q Hqnz) as Hb'.
          rewrite <- Ha in Ha'. rewrite <- Hb in Hb'.
          rewrite (Forall2_forall_iff _ _ _ Fzero Fzero) in H by (repeat rewrite to_list_length; reflexivity).
          pose proof (zero_degree q) as Hq'.
          rewrite to_list_length in H. unfold measure, convert in H.
          destruct (degree q) eqn:Hdq; [|elim Hqnz; auto].
          simpl in H. rewrite PeanoNat.Nat.sub_0_r in H.
          pose proof (degree_definition a) as Haa.
          pose proof (degree_definition b) as Hbb.
          destruct (Compare_dec.lt_dec k n); [repeat rewrite <- (to_list_nth_default_inbounds _ n Fzero k) by assumption; apply H; auto|].
          destruct (degree a); [destruct Haa as [Haa1 Haa2]|rewrite Haa].
          + cbv in Ha'. rewrite Haa2 by Lia.lia.
            destruct (degree b); [destruct Hbb as [Hbb1 Hbb2]|rewrite Hbb; reflexivity].
            cbv in Hb'. rewrite Hbb2 by Lia.lia; reflexivity.
          + destruct (degree b); [destruct Hbb as [Hbb1 Hbb2]|rewrite Hbb; reflexivity].
            cbv in Hb'. rewrite Hbb2 by Lia.lia; reflexivity.
      Qed.
    End PquotRingListIsomorphism.
  End Pquot.
  Section Pquotl.
    Context {Finv: F -> F}{Fdiv: F -> F -> F}
      {field: @field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
      {char_ge_3: @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "/" := Fdiv.

    Local Notation Pdivmod := (@Pdivmod Fdiv).
    Local Notation Pdiv := (@Pdiv Fdiv).
    Local Notation Pmod := (@Pmod Fdiv).
    Local Notation Pgcd := (@Pgcd Fdiv).
    Local Notation Pegcd := (@Pegcd Fdiv).
    Local Notation Pdivides := (@Pdivides Fdiv).
    Local Notation coprime := (@coprime Fdiv).

    Definition Pquotl (ql: list P): Type := { pl: list P | List.Forall2 (fun p q => Peq p (Pmod p q)) pl ql }.

    Section PquotlOperations.
      Definition to_pl {ql} (pl: Pquotl ql) := proj1_sig pl.

      Context {ql: list P}.
      Lemma to_pl_length (pl: Pquotl ql): length (to_pl pl) = length ql :> _.
      Proof. destruct pl as [pl Hpl]; simpl. eapply Forall2_length; eauto. Qed.

      Program Definition of_pl (pl: list P) (Hpl: length pl = length ql :> _): Pquotl ql :=
        map2 (fun p q => Pmod p q) pl ql.
      Next Obligation.
        revert pl Hpl. induction ql; intros pl Hpl; [destruct pl; simpl in Hpl; try constructor; congruence|].
        destruct pl; [simpl in Hpl; congruence|].
        eapply Forall2_cons; [rewrite Pmod_mod_eq; reflexivity|].
        apply IHl. simpl in Hpl; congruence.
      Qed.

      Definition eql {ql'} (pl1: Pquotl ql) (pl2: Pquotl ql'): Prop :=
        List.Forall2 Peq (to_pl pl1) (to_pl pl2).

      Program Definition zerol: Pquotl ql := repeat Pzero (length ql).
      Next Obligation. induction ql; simpl; constructor; auto. rewrite Pmod_0_l. reflexivity. Qed.

      Lemma nth_error_zerol:
        forall k, (k < length ql) -> (nth_error (to_pl zerol) k = Some Pzero :> _).
      Proof. intros. simpl. apply List.nth_error_repeat; auto. Qed.

      Definition onel: Pquotl ql := of_pl (repeat Pone (length ql)) ltac:(apply repeat_length).

      Program Definition addl (p1 p2: Pquotl ql): Pquotl ql :=
        map2 Padd (to_pl p1) (to_pl p2).
      Next Obligation.
        destruct p1 as [p1 Hp1]. destruct p2 as [p2 Hp2].
        simpl. revert p2 Hp2. induction Hp1.
        - intros. inversion Hp2. constructor.
        - intros. destruct p2 as [|z]; inversion Hp2.
          simpl. constructor; auto.
          subst. rewrite Pmod_distr, <- H, <- H3. reflexivity.
      Qed.

      Program Definition mull (p1 p2: Pquotl ql): Pquotl ql :=
        of_pl (map2 Pmul (to_pl p1) (to_pl p2)) _.
      Next Obligation. rewrite map2_length, to_pl_length, to_pl_length, PeanoNat.Nat.min_id. reflexivity. Qed.

      Program Definition oppl (pl: Pquotl ql): Pquotl ql :=
        List.map Popp (to_pl pl).
      Next Obligation.
        destruct pl as [pl Hpl]. simpl. induction Hpl; simpl; constructor; auto.
        rewrite Pmod_opp, <- H. reflexivity.
      Qed.

      Program Definition subl (p1 p2: Pquotl ql): Pquotl ql :=
        map2 Psub (to_pl p1) (to_pl p2).
      Next Obligation.
        destruct p1 as [p1 Hp1]. destruct p2 as [p2 Hp2].
        simpl. revert p2 Hp2. induction Hp1.
        - intros. inversion Hp2. constructor.
        - intros. destruct p2 as [|z]; inversion Hp2.
          simpl. constructor; auto.
          subst. rewrite ring_sub_definition, Pmod_distr, Pmod_opp, <- H, <- H3. reflexivity.
      Qed.
    End PquotlOperations.
    Section PquotlRing.
      Context {ql: list P}.

      Global Instance PquotlRing:
        @commutative_ring (Pquotl ql) eql zerol onel oppl addl subl mull.
      Proof.
        split; repeat constructor; intros;
          match goal with
          | |- Proper _ _ => unfold Proper, respectful
          | |- Reflexive _ => unfold Reflexive
          | |- Symmetric _ => unfold Symmetric
          | |- Transitive _ => unfold Transitive
          | |- _ => idtac end;
          intros; repeat match goal with
                    | [ x : Pquotl ql  |- _ ] => destruct x as [?a ?A]
                    | [ H : Forall2 _ ?a ql |- _ ] => revert a H
                    end;
          lazy iota beta delta [eql zerol onel addl mull oppl subl] in *; simpl in *.
        - induction ql; intros.
          + inversion A; inversion A0; inversion A1; subst; simpl; constructor.
          + inversion A; inversion A0; inversion A1; subst; simpl; constructor; auto.
            apply associative.
        - induction ql; intros.
          + inversion A; subst; simpl; constructor.
          + inversion A; subst; simpl; constructor; auto.
            rewrite left_identity; reflexivity.
        - induction ql; intros.
          + inversion A; subst; simpl; constructor.
          + inversion A; subst; simpl; constructor; auto.
            rewrite right_identity; reflexivity.
        - revert H H0; repeat match goal with | [ H : Forall2 _ ?a ql |- _ ] => revert a H end.
          induction ql; intros.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; constructor.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; simpl; constructor; auto; inversion H; inversion H0; subst; auto.
            rewrite H6, H16; reflexivity.
        - induction ql; intros.
          + inversion A; subst; constructor.
          + inversion A; subst; constructor; auto. reflexivity.
        - apply Forall2_flip. eapply Forall2_impl; eauto.
          intros; symmetry; auto.
        - revert H H0; repeat match goal with | [ H : Forall2 _ ?a ql |- _ ] => revert a H end.
          induction ql; intros.
          + inversion A; inversion A0; inversion A1; subst; constructor.
          + inversion A; inversion A0; inversion A1; subst; simpl; constructor; auto; inversion H; inversion H0; subst; auto.
            * rewrite H6, H16; reflexivity.
            * eapply IHl; eauto.
              clear -field. induction l2; constructor; auto. intro; reflexivity.
        - induction ql; intros.
          + inversion A; subst; constructor.
          + inversion A; subst; simpl; constructor; auto.
            rewrite left_inverse; reflexivity.
        - induction ql; intros.
          + inversion A; subst; constructor.
          + inversion A; subst; simpl; constructor; auto.
            rewrite right_inverse; reflexivity.
        - revert H. revert a A a0 A0. induction ql; intros.
          + inversion A; inversion A0; subst; constructor.
          + inversion A; inversion A0; subst; inversion H; subst; constructor; auto.
            rewrite H5; reflexivity.
        - induction ql; intros.
          + inversion A; inversion A0; subst; constructor.
          + inversion A; inversion A0; subst; simpl; constructor; auto.
            apply commutative.
        - induction ql; intros.
          + inversion A; inversion A0; inversion A1; subst; constructor.
          + inversion A; inversion A0; inversion A1; subst; simpl; constructor; auto.
            rewrite Pmul_mod_idemp_l, Pmul_mod_idemp_r, associative.
            reflexivity.
        - induction ql; intros.
          + inversion A; subst; constructor.
          + inversion A; subst; simpl; constructor; auto.
            rewrite Pmul_mod_idemp_l, left_identity. symmetry; assumption.
        - induction ql; intros.
          + inversion A; subst; constructor.
          + inversion A; subst; simpl; constructor; auto.
            rewrite Pmul_mod_idemp_r, right_identity. symmetry; assumption.
        - revert H H0; repeat match goal with | [ H : Forall2 _ ?a ql |- _ ] => revert a H end.
          induction ql; intros.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; constructor.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; simpl; constructor; auto; inversion H; inversion H0; subst; auto.
            rewrite H6, H16; reflexivity.
        - intros a _. induction a; constructor; auto. reflexivity.
        - apply Forall2_flip. eapply Forall2_impl; eauto. intros; symmetry; auto.
        - clear A A0 A1. revert H H0. revert a1 a0 a. induction a1; intros; auto.
          + inversion H; inversion H0; subst; try congruence; constructor.
          + inversion H; subst.
            inversion H0; subst; constructor; auto.
            * rewrite H3; auto.
            * eapply IHa1; eauto.
        - induction ql; intros.
          + inversion A; inversion A0; inversion A1; subst; constructor.
          + inversion A; inversion A0; inversion A1; subst; simpl; constructor; auto.
            rewrite <- Pmod_distr, <- left_distributive. reflexivity.
        - induction ql; intros.
          + inversion A; inversion A0; inversion A1; subst; constructor.
          + inversion A; inversion A0; inversion A1; subst; simpl; constructor; auto.
            rewrite <- Pmod_distr, <- right_distributive. reflexivity.
        - induction ql; intros.
          + inversion A; inversion A0; subst; constructor.
          + inversion A; inversion A0; subst; simpl; constructor; auto.
            rewrite ring_sub_definition; reflexivity.
        - revert H H0; repeat match goal with | [ H : Forall2 _ ?a ql |- _ ] => revert a H end.
          induction ql; intros.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; constructor.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; simpl; constructor; auto; inversion H; inversion H0; subst; auto.
            rewrite H6, H16; reflexivity.
        - revert H H0; repeat match goal with | [ H : Forall2 _ ?a ql |- _ ] => revert a H end.
          induction ql; intros.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; constructor.
          + inversion A; inversion A0; inversion A1; inversion A2; subst; simpl; constructor; auto; inversion H; inversion H0; subst; auto.
            rewrite H6, H16; reflexivity.
        - induction ql; intros.
          + inversion A; inversion A0; subst; constructor.
          + inversion A; inversion A0; subst; simpl; constructor; auto.
            rewrite commutative. reflexivity.
      Qed.
    End PquotlRing.
    Section Pquotl1.
      Context {q: P}. Local Notation Pquot := (@Pquot Fdiv).
      Program Definition to_pquotl1 (p: Pquot q): Pquotl (q::nil) :=
        (proj1_sig p)::nil.
      Next Obligation. repeat constructor. apply (proj2_sig p). Qed.

      Program Definition from_pquotl1 (p: Pquotl (q::nil)): Pquot q :=
        List.hd Pzero (proj1_sig p).
      Next Obligation.
        destruct p as (p & Hp).
        simpl; inversion Hp; subst; clear Hp.
        inversion H3. simpl. auto.
      Qed.

      Lemma PquotlRingIsomorphism1:
        @Ring.is_isomorphism
          (Pquot q) eq1 one add mul
          (Pquotl (q::nil)) eql onel addl mull
          to_pquotl1
          from_pquotl1.
      Proof.
        repeat constructor.
        - destruct a as (a & Ha); destruct b as (b & Hb); simpl.
          rewrite Pmod_distr, <- Ha, <- Hb. reflexivity.
        - apply H.
        - destruct x as (x & Hx); destruct y as (y & Hy); simpl.
          reflexivity.
        - simpl. reflexivity.
        - intros (a & Ha). unfold eql; simpl.
          inversion Ha; subst; clear Ha. inversion H3. reflexivity.
        - intros (a & Ha) (b & Hb). unfold eql, eq1; simpl.
          inversion 1; subst; auto.
      Qed.
    End Pquotl1.
    Section PquotlAppRingIsomorphism.
      Context {ql1 ql2: list P}.

      Program Definition Pquotl_app (pl: Pquotl ql1 * Pquotl ql2): Pquotl (ql1 ++ ql2) :=
       (proj1_sig (fst pl)) ++ (proj1_sig (snd pl)).
      Next Obligation. apply Forall2_app; [apply (proj2_sig p)|apply (proj2_sig p0)]. Qed.

      Program Definition Pquotl_split (pl: Pquotl (ql1 ++ ql2)): (Pquotl ql1 * Pquotl ql2) :=
        (firstn (length ql1) (proj1_sig pl), skipn (length ql1) (proj1_sig pl)).
      Next Obligation.
        destruct pl as (pl & Hpl); simpl.
        pose proof (Forall2_length Hpl) as Hlen.
        rewrite length_app in Hlen.
        rewrite <- (firstn_skipn (length ql1) pl) in Hpl.
        assert (length (firstn (length ql1) pl) = length ql1 :> _) as Hql1 by (rewrite length_firstn, Hlen, PeanoNat.Nat.min_l by Lia.lia; reflexivity).
        apply (Forall2_app_inv _ _ _ _ _ Hql1 Hpl).
      Qed.
      Next Obligation.
        destruct pl as (pl & Hpl); simpl.
        pose proof (Forall2_length Hpl) as Hlen.
        rewrite length_app in Hlen.
        rewrite <- (firstn_skipn (length ql1) pl) in Hpl.
        assert (length (firstn (length ql1) pl) = length ql1 :> _) as Hql1 by (rewrite length_firstn, Hlen, PeanoNat.Nat.min_l by Lia.lia; reflexivity).
        apply (Forall2_app_inv _ _ _ _ _ Hql1 Hpl).
      Qed.

      Lemma PquotlAppRingIsomorphism:
        @Ring.is_isomorphism (Pquotl ql1 * Pquotl ql2) (fun x y => eql (fst x) (fst y) /\ eql (snd x) (snd y)) (onel, onel) (apply_binop_pair addl addl) (apply_binop_pair mull mull) (Pquotl (ql1 ++ ql2)) eql onel addl mull Pquotl_app Pquotl_split.
      Proof.
        constructor.
        - constructor.
          + constructor.
            * intros pl1 pl2. destruct pl1 as (pl1 & pl1'). destruct pl2 as (pl2 & pl2').
              destruct pl1 as (pl1 & Hpl1). destruct pl2 as (pl2 & Hpl2).
              destruct pl1' as (pl1' & Hpl1'). destruct pl2' as (pl2' & Hpl2').
              unfold eql; simpl. rewrite <- map2_app by (rewrite (Forall2_length Hpl1), (Forall2_length Hpl2); reflexivity).
              reflexivity.
            * intros pl1 pl2. destruct pl1 as (pl1 & pl1'). destruct pl2 as (pl2 & pl2').
              destruct pl1 as (pl1 & Hpl1). destruct pl2 as (pl2 & Hpl2).
              destruct pl1' as (pl1' & Hpl1'). destruct pl2' as (pl2' & Hpl2').
              unfold eql; simpl. intros (Heql & Heql').
              apply Forall2_app; auto.
          + intros pl1 pl2. destruct pl1 as (pl1 & pl1'). destruct pl2 as (pl2 & pl2').
            destruct pl1 as (pl1 & Hpl1). destruct pl2 as (pl2 & Hpl2).
            destruct pl1' as (pl1' & Hpl1'). destruct pl2' as (pl2' & Hpl2').
            unfold eql; simpl. rewrite <- map2_app by (rewrite map2_length, (Forall2_length Hpl1), (Forall2_length Hpl2), PeanoNat.Nat.min_id; reflexivity).
            rewrite <- map2_app by (rewrite (Forall2_length Hpl1), (Forall2_length Hpl2); reflexivity).
            reflexivity.
          + unfold eql; simpl. rewrite length_app, repeat_app, map2_app; [reflexivity|].
            apply repeat_length.
        - intro pl; destruct pl as (pl & Hpl).
          unfold eql; simpl. rewrite firstn_skipn.
          reflexivity.
        - intros pl1 pl2. destruct pl1 as (pl1 & pl1'). destruct pl2 as (pl2 & pl2').
          destruct pl1 as (pl1 & Hpl1). destruct pl2 as (pl2 & Hpl2).
          destruct pl1' as (pl1' & Hpl1'). destruct pl2' as (pl2' & Hpl2').
          unfold eql; simpl; intros Heql.
          apply Forall2_app_inv; auto.
          apply Forall2_length in Hpl1, Hpl2. congruence.
      Qed.
    End PquotlAppRingIsomorphism.
    Section PquotlConvertRingIsomorphism.
      Program Definition Pquotl_convert {ql1 ql2} (Heql: Forall2 Peq ql1 ql2) (pl: Pquotl ql1): Pquotl ql2 :=
        proj1_sig pl.
      Next Obligation.
        pose proof (Hlen1 := Forall2_length Heql).
        pose proof (Hlen2 := Forall2_length (proj2_sig pl)).
        pose proof (X := proj2_sig pl). simpl in X.
        rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) by congruence.
        rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) in Heql by congruence.
        rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) in X by congruence.
        intros. rewrite (X i H). apply peq_mod_proper.
        - apply (X i H).
        - apply (Heql i ltac:(congruence)).
      Qed.

      Lemma Pquotl_convert_isomorphism {ql1 ql2} (Heql1: Forall2 Peq ql1 ql2) (Heql2: Forall2 Peq ql2 ql1):
        @Ring.is_isomorphism
          (Pquotl ql1) eql onel addl mull
          (Pquotl ql2) eql onel addl mull
          (Pquotl_convert Heql1)
          (Pquotl_convert Heql2).
      Proof.
        constructor.
        - repeat constructor.
          + intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
            unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero); reflexivity.
          + intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
            unfold eql; cbn. auto.
          + intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
            unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
            * repeat rewrite ListUtil.map2_length. rewrite (Forall2_length Ha), (Forall2_length Hb).
              repeat rewrite min_l by Lia.lia. intros.
              repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
              repeat rewrite ListUtil.map2_length. rewrite (Forall2_length Ha), (Forall2_length Hb), <- (Forall2_length Heql1).
              repeat rewrite min_l by Lia.lia. intros.
              destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
              apply peq_mod_proper; [reflexivity|].
              apply (proj1 (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero (Forall2_length Heql1)) Heql1); auto.
            * repeat rewrite ListUtil.map2_length. rewrite (Forall2_length Heql1).
              reflexivity.
          + unfold eql; cbn. rewrite (Forall2_length Heql1).
            rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) by (do 2 rewrite ListUtil.map2_length; rewrite (Forall2_length Heql1); reflexivity).
            rewrite ListUtil.map2_length. rewrite (Forall2_length Heql1), repeat_length, min_l by Lia.lia.
            intros. repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
            rewrite repeat_length, (Forall2_length Heql1), min_l by Lia.lia.
            rewrite ListUtil.nth_default_repeat.
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
            destruct (Decidable.dec _); [|Lia.lia].
            apply peq_mod_proper; [reflexivity|].
            apply (proj1 (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero (Forall2_length Heql1)) Heql1).
            rewrite (Forall2_length Heql1); auto.
        - intro a; destruct a as (a & Ha). unfold eql; simpl.
          reflexivity.
        - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
          unfold eql; cbn. auto.
      Qed.
    End PquotlConvertRingIsomorphism.
    Section PquotlRingListIsomorphism.
      Definition Pquotl' (ql: list P): Type :=
        { l : list F | length l = list_sum (List.map (fun q => measure q - 1)%nat ql) :> _ }.

      Context {ql: list P} {Hqlnz: Forall (fun q => not (Peq q Pzero)) ql}.
      Program Definition to_listl' (pl: Pquotl ql): Pquotl' ql :=
        List.concat (List.map (fun '(p, q) => to_list (measure q - 1)%nat p) (combine (proj1_sig pl) ql)).
      Next Obligation.
        rewrite length_concat. f_equal.
        rewrite map_map.
        rewrite (map_ext _ (fun '(p, q) => (measure q - 1)%nat)) at 1 by (intros [p q]; simpl; apply to_list_length).
        clear. destruct pl as (pl & Hpl); simpl.
        induction Hpl; simpl; [reflexivity|].
        rewrite IHHpl; reflexivity.
      Qed.

      Program Definition of_listl' (pl: Pquotl' ql): Pquotl ql :=
        let fix aux xs ys :=
          match ys with
          | nil => nil
          | y::ys => (of_list (firstn (measure y - 1)%nat xs)) :: (aux (skipn (measure y - 1)%nat xs) ys)
          end
        in aux (proj1_sig pl) ql.
      Next Obligation.
        destruct pl as (pl & Hpl). simpl.
        revert pl Hpl. induction Hqlnz; intros; [constructor|].
        simpl in *. assert (Hpl2: length (skipn (measure x - 1)%nat pl) = list_sum (map (fun q : P => (measure q - 1)%nat) l) :> _).
        { rewrite skipn_length, Hpl. Lia.lia. }
        constructor.
        - symmetry. apply Pmod_small.
          assert (degree x = Some (length (firstn (measure x - 1)%nat pl)) :> _) as ->.
          { rewrite length_firstn, Hpl.
            rewrite PeanoNat.Nat.min_l by Lia.lia.
            unfold measure. unfold convert. pose proof (degree_definition x) as Hx.
            pose proof (zero_degree x).
            destruct (degree x); [f_equal; Lia.lia|elim f; tauto]. }
          apply of_list_degree_lt.
        - apply IHf; auto.
      Qed.

      Definition eql' (p1 p2: Pquotl' ql): Prop := List.Forall2 Feq (proj1_sig p1) (proj1_sig p2).

      Global Instance Peq_proper_to_list n:
        Proper (Peq ==> Forall2 Feq) (to_list n).
      Proof.
        intros x y He. eapply (Forall2_forall_iff _ _ _ Fzero Fzero).
        - repeat rewrite to_list_length. reflexivity.
        - rewrite to_list_length. intros.
          repeat rewrite to_list_nth_default_inbounds; auto.
      Qed.

      Global Instance eql_proper_to_listl':
        Proper (eql ==> eql') to_listl'.
      Proof.
        intros x y. destruct x as (x & Hx). destruct y as (y & Hy).
        unfold eql, eql'; simpl. intro Heq.
        clear Hx Hy. clear Hqlnz. revert x y Heq.
        induction ql; intros; simpl; [repeat rewrite combine_nil_r; constructor|].
        inversion Heq; subst; clear Heq; simpl.
        - constructor.
        - apply Forall2_app.
          + apply Peq_proper_to_list; auto.
          + apply IHl. auto.
      Qed.

      Program Definition zerol': Pquotl' ql := List.repeat Fzero (list_sum (List.map (fun q => measure q - 1)%nat ql)).
      Next Obligation. apply repeat_length. Qed.

      Definition onel': Pquotl' ql := to_listl' onel.

      Program Definition oppl' (p: Pquotl' ql): Pquotl' ql :=
        List.map Fopp (proj1_sig p).
      Next Obligation. rewrite length_map, (proj2_sig p). reflexivity. Qed.

      Program Definition addl' (p1 p2: Pquotl' ql): Pquotl' ql :=
        List.map2 Fadd (proj1_sig p1) (proj1_sig p2).
      Next Obligation. rewrite map2_length, (proj2_sig p1), (proj2_sig p2), PeanoNat.Nat.min_id; reflexivity. Qed.

      Program Definition subl' (p1 p2: Pquotl' ql): Pquotl' ql :=
        List.map2 Fsub (proj1_sig p1) (proj1_sig p2).
      Next Obligation. rewrite map2_length, (proj2_sig p1), (proj2_sig p2), PeanoNat.Nat.min_id; reflexivity. Qed.

      Definition mull' (p1 p2: Pquotl' ql): Pquotl' ql :=
        to_listl' (mull (of_listl' p1) (of_listl' p2)).

      Lemma PquotlRing_by_isomorphism:
        @ring (Pquotl' ql) eql' zerol' onel' oppl' addl' subl' mull'
        /\ @is_homomorphism _ eql onel addl mull _ eql' onel' addl' mull' to_listl'
        /\ @is_homomorphism _ eql' onel' addl' mull' _ eql onel addl mull of_listl'.
      Proof.
        assert (forall A : Pquotl ql, eql (of_listl' (to_listl' A)) A) as Heql.
        { intros pl. destruct pl as (pl & Hpl).
          unfold eql; simpl. induction Hpl; [constructor|].
          simpl. constructor.
          - rewrite firstn_app_sharp by apply to_list_length.
            apply of_list_to_list. rewrite H.
            assert (Some _ = degree y :> _) as ->.
            { inversion Hqlnz; subst. pose proof (degree_definition y).
              unfold measure, convert. destruct (degree y); [f_equal; Lia.lia|elim H2].
              intro; rewrite zero_definition; auto. }
            apply Pmod_degree_lt. inversion Hqlnz; auto.
          - rewrite skipn_app_sharp by apply to_list_length.
            apply IHHpl. inversion Hqlnz; auto. }
        apply (ring_by_isomorphism (ringF:=(@PquotlRing ql).(commutative_ring_ring)) (phi:=to_listl') (phi':=of_listl')); auto.
        + clear Heql. intros; destruct a as (a & Ha). destruct b as (b & Hb).
          unfold eql, eql'; simpl.
          revert a b Ha Hb. induction Hqlnz.
          * simpl; intros. apply length0_nil in Ha. apply length0_nil in Hb.
            subst. split; auto.
          * simpl; intros. split; intros.
            { rewrite <- (firstn_skipn (measure x - 1)%nat a).
              rewrite <- (firstn_skipn (measure x - 1)%nat b).
              inversion H0; subst.
              apply Forall2_app. rewrite (Forall2_forall_iff _ _ _ Fzero Fzero).
              - rewrite length_firstn, Ha, PeanoNat.Nat.min_l by Lia.lia.
                intros. pose proof (H4 i) as HX.
                unfold of_list in HX.
                do 2 rewrite Pdecompose_coeff in HX.
                rewrite length_firstn, Ha, PeanoNat.Nat.min_l in HX by Lia.lia.
                rewrite length_firstn, Hb, PeanoNat.Nat.min_l in HX by Lia.lia.
                destruct (dec_lt_nat i (measure x - 1)%nat); [|Lia.lia]; auto.
              - rewrite length_firstn, Ha, PeanoNat.Nat.min_l by Lia.lia.
                rewrite length_firstn, Hb, PeanoNat.Nat.min_l by Lia.lia.
                reflexivity.
              - apply IHf; auto.
                + rewrite skipn_length, Ha; Lia.lia.
                + rewrite skipn_length, Hb; Lia.lia. }
            { constructor.
              - intros i. unfold of_list. do 2 rewrite Pdecompose_coeff.
                rewrite length_firstn, Ha, PeanoNat.Nat.min_l by Lia.lia.
                rewrite length_firstn, Hb, PeanoNat.Nat.min_l by Lia.lia.
                destruct (dec_lt_nat _ _); [|reflexivity].
                do 2 rewrite nth_default_firstn. rewrite Ha, Hb.
                destruct (Compare_dec.le_dec _ _); [|Lia.lia].
                destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
                rewrite Forall2_forall_iff in H0 by congruence.
                apply H0. rewrite Ha; Lia.lia.
              - apply IHf; auto.
                + rewrite skipn_length, Ha; Lia.lia.
                + rewrite skipn_length, Hb; Lia.lia.
                + rewrite (Forall2_forall_iff _ _ _ Fzero Fzero) by (do 2 rewrite skipn_length; rewrite Ha, Hb; reflexivity).
                  rewrite skipn_length, Ha.
                  intros; do 2 rewrite nth_default_skipn.
                  rewrite (Forall2_forall_iff _ _ _ Fzero Fzero) in H0 by congruence.
                  apply H0. rewrite Ha. Lia.lia. }
        + unfold eql; simpl. clear Heql; induction Hqlnz; simpl; constructor.
          * rewrite firstn_repeat, PeanoNat.Nat.min_l by Lia.lia.
            intro i. rewrite zero_definition.
            unfold of_list; rewrite Pdecompose_coeff.
            rewrite repeat_length, nth_default_repeat.
            destruct (dec_lt_nat _ _); [|reflexivity].
            destruct (dec _); reflexivity.
          * rewrite skipn_repeat. assert (_ - 1 + _ - _ = list_sum (map (fun q : P => (measure q - 1)%nat) l) :> _)%nat as -> by Lia.lia.
            apply IHf; auto.
        + unfold eql; simpl. clear Heql; induction Hqlnz; simpl; constructor.
          * rewrite firstn_app_sharp by apply to_list_length.
            rewrite of_list_to_list; [reflexivity|].
            assert (Some _ = degree x :> _) as ->; [|apply Pmod_degree_lt]; auto.
            unfold measure, convert. pose proof (degree_definition x).
            destruct (degree x); [f_equal; Lia.lia|].
            elim H. intro; rewrite zero_definition; auto.
          * rewrite skipn_app_sharp by apply to_list_length.
            apply IHf; auto.
        + intros a. destruct a as (a & Ha); unfold eql; simpl.
          revert a Ha. clear Heql; induction Hqlnz; simpl; intros; constructor.
          * intro k. rewrite opp_definition.
            unfold of_list. do 2 rewrite Pdecompose_coeff.
            do 2 rewrite length_firstn. rewrite length_map.
            destruct (dec_lt_nat _ _); [|rewrite Group.inv_id; reflexivity].
            rewrite firstn_map, (map_nth_default _ _ _ _ Fzero); [reflexivity|].
            rewrite length_firstn. assumption.
          * rewrite skipn_map. apply IHf; auto.
            rewrite length_skipn, Ha. Lia.lia.
        + intros a b; destruct a as (a & Ha); destruct b as (b & Hb).
          unfold eql; simpl. revert a Ha b Hb. clear Heql; induction Hqlnz; simpl; intros; constructor.
          * intro k. unfold of_list. rewrite add_definition.
            repeat rewrite Pdecompose_coeff.
            repeat rewrite length_firstn. rewrite map2_length.
            rewrite Ha, Hb, PeanoNat.Nat.min_id.
            repeat rewrite PeanoNat.Nat.min_l by Lia.lia.
            destruct (dec_lt_nat _ _); [|rewrite right_identity; reflexivity].
            repeat rewrite nth_default_firstn.
            rewrite (nth_default_map2 _ _ _ _ _ Fzero Fzero).
            repeat rewrite map2_length, Ha, Hb, PeanoNat.Nat.min_id.
            destruct (Compare_dec.le_dec _ _); [|Lia.lia].
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia]. reflexivity.
          * etransitivity; [|apply IHf; auto; rewrite skipn_length; [rewrite Ha|rewrite Hb]; Lia.lia].
            match goal with
            | |- Forall2 Peq (?f _ l) (?g _ _) =>
                assert (Proper (Forall2 Feq ==> Forall2 Peq) (fun x => f x l)) as Hp
            end.
            { intros u v Huv. clear -Huv field cring poly_defs.
              revert u v Huv; induction l; intros; simpl; constructor.
              - intro k. unfold of_list. repeat rewrite Pdecompose_coeff.
                repeat rewrite length_firstn. rewrite <- (Forall2_length Huv).
                destruct (dec_lt_nat _ _); [|reflexivity].
                do 2 rewrite nth_default_firstn. rewrite <- (Forall2_length Huv).
                rewrite (Forall2_forall_iff _ _ _ Fzero Fzero (Forall2_length Huv)) in Huv.
                destruct (Compare_dec.le_dec _ _); [|apply Huv; Lia.lia].
                destruct (Compare_dec.lt_dec _ _); [apply Huv; Lia.lia|reflexivity].
              - apply IHl. rewrite (Forall2_forall_iff _ _ _ Fzero Fzero).
                + intros. repeat rewrite nth_default_skipn.
                  rewrite (Forall2_forall_iff _ _ _ Fzero Fzero (Forall2_length Huv)) in Huv.
                  apply Huv. rewrite skipn_length in H. Lia.lia.
                + repeat rewrite skipn_length. rewrite (Forall2_length Huv). reflexivity. }
            apply Hp. rewrite (Forall2_forall_iff _ _ _ Fzero Fzero).
            { intros. rewrite nth_default_skipn, (nth_default_map2 _ _ _ _ _ Fzero Fzero), (nth_default_map2 _ _ _ _ _ Fzero Fzero).
              do 2 rewrite nth_default_skipn.
              rewrite Ha, Hb, PeanoNat.Nat.min_id.
              rewrite length_skipn, length_skipn, Ha, Hb, PeanoNat.Nat.min_id.
              destruct (Compare_dec.lt_dec _ _); destruct (Compare_dec.lt_dec _ _); try Lia.lia; reflexivity. }
            { rewrite length_skipn, map2_length, map2_length, length_skipn, length_skipn.
              rewrite Ha, Hb. Lia.lia. }
        + intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
          unfold eql; simpl. revert a Ha b Hb. clear Heql; induction Hqlnz; simpl; intros; constructor.
          * intro k. unfold of_list. rewrite sub_definition.
            repeat rewrite Pdecompose_coeff.
            repeat rewrite length_firstn. rewrite map2_length.
            rewrite Ha, Hb, PeanoNat.Nat.min_id.
            repeat rewrite PeanoNat.Nat.min_l by Lia.lia.
            destruct (dec_lt_nat _ _); [|rewrite ring_sub_definition, Group.inv_id, right_identity; reflexivity].
            repeat rewrite nth_default_firstn.
            rewrite (nth_default_map2 _ _ _ _ _ Fzero Fzero).
            repeat rewrite map2_length, Ha, Hb, PeanoNat.Nat.min_id.
            destruct (Compare_dec.le_dec _ _); [|Lia.lia].
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
            destruct (Compare_dec.lt_dec _ _); [|Lia.lia]. reflexivity.
          * etransitivity; [|apply IHf; auto; rewrite skipn_length; [rewrite Ha|rewrite Hb]; Lia.lia].
            match goal with
            | |- Forall2 Peq (?f _ l) (?g _ _) =>
                assert (Proper (Forall2 Feq ==> Forall2 Peq) (fun x => f x l)) as Hp
            end.
            { intros u v Huv. clear -Huv field cring poly_defs.
              revert u v Huv; induction l; intros; simpl; constructor.
              - intro k. unfold of_list. repeat rewrite Pdecompose_coeff.
                repeat rewrite length_firstn. rewrite <- (Forall2_length Huv).
                destruct (dec_lt_nat _ _); [|reflexivity].
                do 2 rewrite nth_default_firstn. rewrite <- (Forall2_length Huv).
                rewrite (Forall2_forall_iff _ _ _ Fzero Fzero (Forall2_length Huv)) in Huv.
                destruct (Compare_dec.le_dec _ _); [|apply Huv; Lia.lia].
                destruct (Compare_dec.lt_dec _ _); [apply Huv; Lia.lia|reflexivity].
              - apply IHl. rewrite (Forall2_forall_iff _ _ _ Fzero Fzero).
                + intros. repeat rewrite nth_default_skipn.
                  rewrite (Forall2_forall_iff _ _ _ Fzero Fzero (Forall2_length Huv)) in Huv.
                  apply Huv. rewrite skipn_length in H. Lia.lia.
                + repeat rewrite skipn_length. rewrite (Forall2_length Huv). reflexivity. }
            apply Hp. rewrite (Forall2_forall_iff _ _ _ Fzero Fzero).
            { intros. rewrite nth_default_skipn, (nth_default_map2 _ _ _ _ _ Fzero Fzero), (nth_default_map2 _ _ _ _ _ Fzero Fzero).
              do 2 rewrite nth_default_skipn.
              rewrite Ha, Hb, PeanoNat.Nat.min_id.
              rewrite length_skipn, length_skipn, Ha, Hb, PeanoNat.Nat.min_id.
              destruct (Compare_dec.lt_dec _ _); destruct (Compare_dec.lt_dec _ _); try Lia.lia; reflexivity. }
            { rewrite length_skipn, map2_length, map2_length, length_skipn, length_skipn.
              rewrite Ha, Hb. Lia.lia. }
        + intros a b. unfold mull'. apply Heql.
      Qed.

      Global Instance PquotlRing':
        @commutative_ring (Pquotl' ql) eql' zerol' onel' oppl' addl' subl' mull'.
      Proof.
        constructor.
        - apply PquotlRing_by_isomorphism.
        - constructor. intros x y.
          unfold eql', mull'.
          apply eql_proper_to_listl'. apply commutative.
      Qed.

      Lemma PquotlRingIsomorphism:
        @Ring.is_isomorphism (Pquotl ql) eql onel addl mull (Pquotl' ql) eql' onel' addl' mull' to_listl' of_listl'.
      Proof.
        constructor.
        - apply PquotlRing_by_isomorphism.
        - intro a. destruct a as (a & Ha).
          unfold eql'; simpl. revert a Ha.
          induction Hqlnz; simpl; intros.
          + simpl in Ha. apply length0_nil in Ha. subst a.
            constructor.
          + rewrite <- (firstn_skipn (measure x - 1)%nat a) at 3.
            apply Forall2_app.
            * rewrite <- (to_list_of_list (firstn (measure x - 1)%nat a)) at 2.
              rewrite length_firstn, Ha, PeanoNat.Nat.min_l by Lia.lia.
              reflexivity.
            * apply IHf; auto.
              rewrite length_skipn, Ha; Lia.lia.
        - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
          unfold eql, eql'; simpl. revert a Ha b Hb. induction Hqlnz; simpl; intros a Ha b Hb Hab.
          + inversion Ha; inversion Hb; constructor.
          + inversion Ha; subst; clear Ha.
            inversion Hb; subst; clear Hb.
            simpl in Hab. apply Forall2_app_inv in Hab; [|do 2 rewrite to_list_length; reflexivity].
            destruct Hab as (Hab1 & Hab2).
            constructor; [|apply IHf; auto].
            rewrite (Forall2_forall_iff _ _ _ Fzero Fzero) in Hab1 by (do 2 rewrite to_list_length; reflexivity).
            unfold to_list in Hab1. rewrite length_map, length_seq in Hab1.
            assert (forall k, (k >= measure x - 1)%nat -> coeff x0 k = Fzero) as Hx0.
            { assert (degree_lt (degree x0) (Some (measure x - 1)%nat)) as Hx.
              { assert (Some _ = degree x :> _) as ->.
                - unfold measure, convert.
                  pose proof (degree_definition x) as Hx.
                  destruct (degree x); [f_equal; Lia.lia|].
                  elim H. intro. rewrite zero_definition. apply Hx.
                - rewrite H3. apply Pmod_degree_lt; auto. }
              pose proof (degree_definition x0) as Hx0.
              destruct (degree x0); intros; apply Hx0.
              unfold degree_lt in Hx. simpl in Hx. Lia.lia. }
            assert (forall k, (k >= measure x - 1)%nat -> coeff x1 k = Fzero) as Hx1.
            { assert (degree_lt (degree x1) (Some (measure x - 1)%nat)) as Hx.
              { assert (Some _ = degree x :> _) as ->.
                - unfold measure, convert.
                  pose proof (degree_definition x) as Hx.
                  destruct (degree x); [f_equal; Lia.lia|].
                  elim H. intro. rewrite zero_definition. apply Hx.
                - rewrite H5. apply Pmod_degree_lt; auto. }
              pose proof (degree_definition x1) as Hx1.
              destruct (degree x1); intros; apply Hx1.
              unfold degree_lt in Hx. simpl in Hx. Lia.lia. }
            intro k. destruct (dec_lt_nat k (measure x - 1)%nat).
            * generalize (Hab1 k l2).
              do 2 rewrite (map_nth_default _ _ _ _ 0%nat) by (rewrite length_seq; auto).
              rewrite nth_default_seq_inbounds by assumption.
              simpl. auto.
            * rewrite Hx0, Hx1 by Lia.lia. reflexivity.
      Qed.
    End PquotlRingListIsomorphism.
    Section PquotlRingListMoreIsomorphisms.
      Program Definition Pquotl_convert' {ql1 ql2} (Heql: ql1 = ql2 :> _) (pl: Pquotl' ql1): Pquotl' ql2 :=
        proj1_sig pl.
      Next Obligation. exact (proj2_sig pl). Qed.

      Lemma Pquotl_convert_isomorphism'
        {ql1 ql2 : list P}
        (Hqlnz1: Forall (fun q => ~ Peq q Pzero) ql1)
        (Hqlnz2: Forall (fun q => ~ Peq q Pzero) ql2)
        (Heql1 : ql1 = ql2 :> _) (Heql2: ql2 = ql1 :> _):
        @Ring.is_isomorphism
          (Pquotl' ql1) eql' onel' addl' (mull' (Hqlnz:=Hqlnz1))
          (Pquotl' ql2) eql' onel' addl' (mull' (Hqlnz:=Hqlnz2))
          (Pquotl_convert' Heql1)
          (Pquotl_convert' Heql2).
      Proof.
        repeat match goal with
               | x: Pquotl' _ |- _ => destruct x
               | H: eql' _ _ |- _ => unfold eql' in H
               | |- eql' _ _ => unfold eql'
               | |- _ => constructor
               | |- _ => intro
               end; cbn -[mull' onel'] in *; auto; try reflexivity.
        - cbn. rewrite Heql1. reflexivity.
        - rewrite Heql1. reflexivity.
      Qed.

      Program Definition Pquotl_app' {ql1 ql2} (pl: Pquotl' ql1 * Pquotl' ql2): Pquotl' (ql1 ++ ql2) :=
        (proj1_sig (fst pl)) ++ (proj1_sig (snd pl)).
      Next Obligation.
        rewrite length_app, map_app, list_sum_app, (proj2_sig p), (proj2_sig p0). reflexivity.
      Qed.

      Program Definition Pquotl_split' {ql1 ql2} (pl: Pquotl' (ql1 ++ ql2)): (Pquotl' ql1 * Pquotl' ql2) :=
        (firstn (list_sum (map (fun q : P => (measure q - 1)%nat) ql1)) (proj1_sig pl), skipn (list_sum (map (fun q : P => (measure q - 1)%nat) ql1)) (proj1_sig pl)).
      Next Obligation.
        rewrite length_firstn, (proj2_sig pl), map_app, list_sum_app, PeanoNat.Nat.min_l by Lia.lia.
        reflexivity.
      Qed.
      Next Obligation.
        rewrite length_skipn, (proj2_sig pl), map_app, list_sum_app. Lia.lia.
      Qed.

      Lemma PquotlAppRingIsomorphism'
        {ql1 ql2}
        (Hqlnz: Forall (fun q => ~ Peq q Pzero) (ql1 ++ ql2))
        (Hqlnz1: Forall (fun q => ~ Peq q Pzero) ql1)
        (Hqlnz2: Forall (fun q => ~ Peq q Pzero) ql2):
        @Ring.is_isomorphism
          (Pquotl' ql1 * Pquotl' ql2)
          (fun x y => eql' (fst x) (fst y) /\ eql' (snd x) (snd y)) (onel', onel')
          (apply_binop_pair addl' addl') (apply_binop_pair (mull' (Hqlnz:=Hqlnz1)) (mull' (Hqlnz:=Hqlnz2)))
          (Pquotl' (ql1 ++ ql2))
          eql' onel' addl' (mull' (Hqlnz:=Hqlnz))
          Pquotl_app'
          Pquotl_split'.
      Proof.
        repeat match goal with
               | x: Pquotl' _ |- _ => destruct x
               | H: eql' _ _ |- _ => unfold eql' in H
               | H: _ /\ _ |- _ => destruct H
               | |- eql' _ _ => unfold eql'
               | |- _ => constructor
               | |- _ => intro
               end; cbn -[mull' onel'] in *.
        - rewrite <- map2_app; [reflexivity|].
          rewrite (proj2_sig (fst a)), (proj2_sig (fst b)). reflexivity.
        - apply Forall2_app; auto.
        - cbn -[of_listl'].
          rewrite <- concat_app, <- map_app, <- combine_app_samelength by (rewrite map2_length, map2_length, to_pl_length, to_pl_length, PeanoNat.Nat.min_id, PeanoNat.Nat.min_id; reflexivity).
          rewrite <- map2_app by (rewrite map2_length, to_pl_length, to_pl_length; apply PeanoNat.Nat.min_id).
          rewrite <- map2_app by (rewrite to_pl_length, to_pl_length; reflexivity).
          assert (forall (x: Pquotl' ql1 * Pquotl' ql2), to_pl (of_listl' (Hqlnz:=Hqlnz) (Pquotl_app' x)) = to_pl (of_listl' (Hqlnz:=Hqlnz1) (fst x)) ++ to_pl (of_listl' (Hqlnz:=Hqlnz2) (snd x)) :> _) as HX; [|do 2 rewrite HX; reflexivity].
          { cbn. intros z; match goal with |- context [?x (_ ++ _) _] => set (f := x) end.
            assert (forall b1 b2 a1 a2, (length a1 = list_sum (map (fun q : P => (measure q - 1)%nat) b1) :> _) -> f (a1 ++ a2) (b1 ++ b2) = f a1 b1 ++ f a2 b2 :> _) as X; [|apply X; apply (proj2_sig (fst z))].
            induction b1; intros.
            - simpl in H. apply length0_nil in H. subst a1.
              reflexivity.
            - simpl in H. rewrite <- (firstn_skipn (measure a - 1)%nat a1).
              simpl. rewrite firstn_app_inleft by (rewrite length_app, length_firstn, H, PeanoNat.Nat.min_l; Lia.lia).
              f_equal. rewrite <- IHb1.
              + f_equal. rewrite skipn_app_inleft; [reflexivity|].
                rewrite length_app, length_firstn, H, PeanoNat.Nat.min_l; Lia.lia.
              + rewrite length_skipn, length_app, length_firstn, length_skipn, H.
                rewrite PeanoNat.Nat.min_l by Lia.lia. Lia.lia. }
        - cbn. rewrite <- concat_app, <- map_app, <- combine_app_samelength by (rewrite map2_length, repeat_length; apply PeanoNat.Nat.min_id).
          rewrite <- map2_app by apply repeat_length.
          rewrite <- repeat_app, length_app. reflexivity.
        - rewrite firstn_skipn. reflexivity.
        - apply Forall2_app_inv in H; [destruct H; auto|].
          rewrite (proj2_sig (fst a)), (proj2_sig (fst b)). reflexivity.
        - apply Forall2_app_inv in H; [destruct H; auto|].
          rewrite (proj2_sig (fst a)), (proj2_sig (fst b)). reflexivity.
      Qed.

      Program Definition to_pquotl1' {q} (p: Pquot' q): Pquotl' (q::nil) :=
        (proj1_sig p).
      Next Obligation. rewrite (proj2_sig p). Lia.lia. Qed.

      Program Definition from_pquotl1' {q} (p: Pquotl' (q::nil)): Pquot' q :=
        (proj1_sig p).
      Next Obligation. destruct p as (p & Hp); simpl; rewrite Hp; simpl; Lia.lia. Qed.

      Lemma PquotlRingIsomorphism1' {q} (Hqnz: ~ Peq q Pzero) (Hqlnz: Forall (fun q => ~ Peq q Pzero) (q::nil)):
        @Ring.is_isomorphism
          (Pquot' q) eq' one' add' (mul' (Hqnz:=Hqnz))
          (Pquotl' (q::nil)) eql' onel' addl' (mull' (Hqlnz:=Hqlnz))
          to_pquotl1'
          from_pquotl1'.
      Proof.
        repeat match goal with
               | x: Pquotl' _ |- _ => destruct x
               | x: Pquot' _ |- _ => destruct x
               | H: eql' _ _ |- _ => unfold eql' in H
               | H: eq' _ _ |- _ => unfold eq' in H
               | H: _ /\ _ |- _ => destruct H
               | |- eql' _ _ => unfold eql'
               | |- eq' _ _ => unfold eq'
               | |- _ => constructor
               | |- _ => intro
               end; cbn -[of_list]; auto; try reflexivity.
        - rewrite app_nil_r. apply Peq_proper_to_list.
          apply peq_mod_proper; [|reflexivity].
          do 2 (rewrite firstn_all; auto). reflexivity.
        - rewrite app_nil_r. reflexivity.
      Qed.
    End PquotlRingListMoreIsomorphisms.
  End Pquotl.
End Theorems.
