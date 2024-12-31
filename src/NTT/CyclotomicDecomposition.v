Require Import Coq.PArith.BinPosDef. Local Open Scope positive_scope.
Require Import Coq.NArith.BinNat.
From Coq.Classes Require Import Morphisms.
Require Import Spec.ModularArithmetic.
Require Import Arithmetic.ModularArithmeticTheorems.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations.
Require Import NTT.Polynomial.
Require PrimeFieldTheorems.

Require Import coqutil.Datatypes.List.

Section Utils.
  (* These should be moved to ListUtil ? Maybe ? *)
  Lemma nth_error_cons {A: Type} (x: A) xs n:
    nth_error (x :: xs) n = match n with
                           | O => Some x
                           | S n => nth_error xs n
                           end.
  Proof. destruct n; reflexivity. Qed.

  Lemma fold_right_eq_ext {A B: Type} {eq: A->A->Prop}
    `{RelationClasses.Equivalence A eq}
    (f g: B -> A -> A) (v: A) (xs: list B):
    (forall x y1 y2, In x xs -> eq y1 y2 -> eq (f x y1) (g x y2)) ->
    eq (fold_right f v xs) (fold_right g v xs).
  Proof.
    induction xs; intros X; [reflexivity|].
    simpl. etransitivity; [eapply X; [apply in_eq|]|reflexivity].
    apply IHxs; intros; apply X; auto. apply in_cons; auto.
  Qed.

  Lemma flat_map_constant_nth_error {A B: Type} (c: nat) (f: A -> list B) (l: list A):
    (forall x : A, In x l -> length (f x) = c) ->
    forall k x, nth_error (flat_map f l) k = Some x ->
           exists y, nth_error l (PeanoNat.Nat.div k c) = Some y /\
                nth_error (f y) (PeanoNat.Nat.modulo k c) = Some x.
  Proof.
    destruct (NatUtil.nat_eq_dec c 0%nat) as [->|Hcnz].
    { intros Hl k x Hx. apply nth_error_In in Hx.
      apply in_flat_map in Hx. destruct Hx as [z [Hz Hzz]].
      apply Hl in Hz. apply ListUtil.length0_nil in Hz.
      rewrite Hz in Hzz. elim (in_nil Hzz). }
    induction l; intros Hl k x Hx; simpl in Hx.
    - rewrite ListUtil.nth_error_nil_error in Hx; inversion Hx.
    - rewrite ListUtil.nth_error_app, Hl in Hx; [|apply in_eq].
      destruct (Compare_dec.lt_dec k c).
      + rewrite PeanoNat.Nat.div_small, PeanoNat.Nat.mod_small by Lia.lia.
        simpl. eexists; split; eauto.
      + apply IHl in Hx; [|intros; apply Hl; apply in_cons; auto].
        assert (k = (k - c) + c)%nat as -> by Lia.lia.
        rewrite NatUtil.div_minus by Lia.lia.
        assert (k - c + c = (k - c) + 1 * c)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.Div0.mod_add.
        assert (_ + 1 = S (PeanoNat.Nat.div (k - c) c))%nat as -> by Lia.lia.
        simpl. exact Hx.
  Qed.

  Lemma Forall2_flat_map {X A B: Type} (R: A -> B -> Prop) (f: X -> list A) (g: X -> list B)
    (l: list X):
    (forall x, In x l -> length (f x) = length (g x)) ->
    (forall x, In x l -> Forall2 R (f x) (g x)) ->
    Forall2 R (flat_map f l) (flat_map g l).
  Proof.
    induction l; intros Hl Hf; [constructor|].
    simpl. apply Forall2_app; [apply Hf; left; reflexivity|].
    apply IHl; intros; [apply Hl|apply Hf]; right; auto.
  Qed.

  Lemma map2_map_combine {A B C: Type} (f: A -> B -> C):
    forall (l: list A) (l': list B),
      ListUtil.List.map2 f l l' = map (fun x => f (fst x) (snd x)) (combine l l').
  Proof.
    induction l; intros; [reflexivity|].
    destruct l'; [reflexivity|]. simpl.
    rewrite IHl. reflexivity.
  Qed.

  Lemma nth_error_map2 {A B C: Type} (f: A -> B -> C):
    forall (l: list A) (l': list B) (k: nat) (a: A) (b: B),
      nth_error l k = Some a ->
      nth_error l' k = Some b ->
      nth_error (ListUtil.List.map2 f l l') k = Some (f a b).
  Proof.
    intros l l' k a b Ha Hb.
    rewrite map2_map_combine, nth_error_map, ListUtil.nth_error_combine.
    rewrite Ha, Hb; reflexivity.
  Qed.

  Lemma flat_map_map2 {X A B C: Type} (f: A -> B -> C) (g: X -> list A) (h: X -> list B)
    (l: list X):
    (forall x, In x l -> length (g x) = length (h x)) ->
    ListUtil.List.map2 f (flat_map g l) (flat_map h l) = flat_map (fun x => ListUtil.List.map2 f (g x) (h x)) l.
  Proof.
    intros Hx. induction l; [reflexivity|].
    simpl. rewrite ListUtil.map2_app by (apply Hx; left; reflexivity).
    rewrite IHl; [reflexivity|]. intros; apply Hx; right; auto.
  Qed.

  Lemma Forall2_app_inv {A B} (R: A -> B -> Prop) (l1 l1': list A) (l2 l2': list B):
    length l1 = length l2 ->
    Forall2 R (l1 ++ l1') (l2 ++ l2') ->
    Forall2 R l1 l2 /\ Forall2 R l1' l2'.
  Proof.
    revert l1' l2 l2'. induction l1; intros l1' l2 l2' Hlength HF.
    - destruct l2; [|simpl in Hlength; Lia.lia].
      simpl in HF. split; auto; constructor.
    - destruct l2; simpl in Hlength; [congruence|].
      do 2 rewrite <- app_comm_cons in HF.
      inversion HF; subst. apply IHl1 in H4; [|Lia.lia].
      destruct H4. split; auto.
  Qed.

  Lemma Forall2_nth_error_iff {A B} (R: A -> B -> Prop) (l1: list A) (l2: list B):
    Forall2 R l1 l2 <-> (length l1 = length l2 /\ forall k v1 v2, nth_error l1 k = Some v1 -> nth_error l2 k = Some v2 -> R v1 v2).
  Proof.
    split.
    - intros; split; [eapply Forall2_length; eauto|].
      induction H; intros.
      + rewrite ListUtil.nth_error_nil_error in H; congruence.
      + destruct k; simpl in *.
        * inversion H1; inversion H2; subst x; subst y; auto.
        * eapply IHForall2; eauto.
    - revert l2; induction l1; intros l2 [HA HB].
      + destruct l2; [constructor|simpl in HA; congruence].
      + destruct l2; [simpl in HA; congruence|].
        simpl in HA. constructor.
        * apply (HB O); reflexivity.
        * apply IHl1. split; [Lia.lia|].
          intros. apply (HB (S k)); auto.
  Qed.

  Section Fold_right_monoid.
    Context {A}{eq}{op}{id}{monoid: @Hierarchy.monoid A eq op id}.

    Lemma fold_right_monoid_op:
      forall a l, eq (fold_right op a l) (op (fold_right op id l) a).
    Proof.
      induction l; simpl.
      - rewrite Hierarchy.left_identity. reflexivity.
      - rewrite IHl. rewrite Hierarchy.associative. reflexivity.
    Qed.

    Lemma fold_right_monoid_app:
      forall l1 l2, eq (fold_right op id (l1 ++ l2)) (op (fold_right op id l1) (fold_right op id l2)).
    Proof. intros. rewrite fold_right_app, fold_right_monoid_op. reflexivity. Qed.

    Lemma fold_right_monoid_concat:
      forall l, eq (fold_right op id (concat l)) (fold_right op id (map (fold_right op id) l)).
    Proof. induction l; [reflexivity|]. simpl; rewrite fold_right_monoid_app, IHl. reflexivity. Qed.

    Lemma fold_right_monoid_singleton:
      forall a, eq (fold_right op id (a::nil)) a.
    Proof. intros; simpl. rewrite Hierarchy.right_identity. reflexivity. Qed.
  End Fold_right_monoid.

  (* TODO: I did not notice there was a chunk function in coqutil, replace below with it *)
  Fixpoint chunks2 {A} (l: list A): list (list A) :=
    match l with
    | nil => nil
    | a::nil => [[a]]
    | a1::a2::l' => [a1; a2]::(chunks2 l')
    end.

  Lemma chunks2_eq {A} (l: list A):
    chunks2 l = match l with
                | nil => nil
                | _ => (firstn 2 l)::(chunks2 (skipn 2 l))
                end.
  Proof.
    destruct l; [reflexivity|].
    destruct l; reflexivity.
  Qed.

  Lemma chunks2_cons {A} (l: list A):
    l <> nil ->
    chunks2 l = (firstn 2 l)::(chunks2 (skipn 2 l)).
  Proof. intro X. rewrite chunks2_eq at 1. destruct l; congruence. Qed.

  Lemma chunks2_length {A} (l: list A):
    length (chunks2 l) = ((PeanoNat.Nat.div (length l) 2) + (PeanoNat.Nat.modulo (length l) 2))%nat.
  Proof.
    assert (forall n (xs: list A), (length xs <= n) -> length (chunks2 xs) = (PeanoNat.Nat.div (length xs) 2) + (PeanoNat.Nat.modulo (length xs) 2))%nat as IH.
    { induction n; intros xs Hxs.
      - destruct xs; [|simpl in Hxs; Lia.lia]. reflexivity.
      - destruct (@Decidable.dec_eq_list_nil_r _ xs) as [->|Hnn]; [reflexivity|].
        rewrite chunks2_cons; auto. cbn [length].
        rewrite IHn by (rewrite skipn_length; simpl in *; Lia.lia).
        rewrite skipn_length. assert (length xs = 1 \/ 2 <= length xs)%nat as [->|Hle] by (destruct xs; simpl in *; [congruence|]; Lia.lia); [reflexivity|].
        set (m := (length xs - 2)%nat). assert (length xs = m + 2)%nat as -> by Lia.lia.
        rewrite NatUtil.div_minus by Lia.lia.
        assert (m + 2 = m + 1 * 2)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.Div0.mod_add. Lia.lia. }
    apply (IH _ _ ltac:(reflexivity)).
  Qed.

  Lemma chunks2_elem_length_exact {A} (l: list A):
    PeanoNat.Nat.Even (length l) ->
    Forall (fun x => length x = 2%nat) (chunks2 l).
  Proof.
    assert (IH: forall n (xs: list A), (length xs <= n) -> PeanoNat.Nat.Even (length xs) -> Forall (fun x => length x = 2%nat) (chunks2 xs)).
    { induction n; intros xs Hxs Heven.
      - destruct xs; [|simpl in Hxs; Lia.lia]. constructor.
      - destruct (@Decidable.dec_eq_list_nil_r _ xs) as [->|Hnn]; [constructor|].
        rewrite chunks2_cons; auto.
        assert (2 <= length xs)%nat as Hle.
        { destruct xs; [congruence|]; destruct xs; simpl in *; try Lia.lia.
          apply PeanoNat.Nat.Even_succ in Heven. eelim PeanoNat.Nat.Even_Odd_False; eauto.
          exists O. Lia.lia. }
        constructor; [rewrite firstn_length; Lia.lia|].
        apply IHn; rewrite skipn_length; [Lia.lia|].
        apply (proj1 (PeanoNat.Nat.Even_succ_succ _)).
        assert (S (S _) = length xs) as -> by Lia.lia. auto. }
    apply (IH _ _ ltac:(reflexivity)).
  Qed.

  Lemma chunks2_concat {A} (l: list A):
    l = concat (chunks2 l).
  Proof.
    assert (IH: forall n (xs: list A), (length xs <= n) -> xs = concat (chunks2 xs)).
    { induction n; intros xs Hxs.
      - destruct xs; [|simpl in Hxs; Lia.lia].
        reflexivity.
      - rewrite chunks2_eq. destruct xs; [reflexivity|].
        cbn [concat]. rewrite <- IHn by (rewrite skipn_length; simpl in *; Lia.lia).
        rewrite firstn_skipn; reflexivity. }
    apply (IH _ _ ltac:(reflexivity)).
  Qed.

  Lemma chunks2_nth_error {A} (l: list A):
    forall k, nth_error l k = Option.bind (nth_error (chunks2 l) (PeanoNat.Nat.div k 2)) (fun chunk => nth_error chunk (PeanoNat.Nat.modulo k 2)).
  Proof.
    assert (IH: forall n (xs: list A), (length xs <= n) -> forall k : nat, nth_error xs k = Option.bind (nth_error (chunks2 xs) (PeanoNat.Nat.div k 2)) (fun chunk : list A => nth_error chunk (PeanoNat.Nat.modulo k 2))).
    { induction n; intros xs Hxs k.
      - destruct xs; simpl in Hxs; [|Lia.lia].
        simpl. repeat rewrite ListUtil.nth_error_nil_error. reflexivity.
      - rewrite (PeanoNat.Nat.Div0.div_mod k 2) at 1.
        destruct (@Decidable.dec_eq_list_nil_r _ xs) as [->|Hnn]; [simpl; repeat rewrite ListUtil.nth_error_nil_error; reflexivity|].
        rewrite chunks2_cons; auto. rewrite nth_error_cons.
        assert (length xs = 1 \/ 2 <= length xs)%nat as [He|Hle] by (destruct xs; simpl in *; [congruence|]; Lia.lia).
        + rewrite skipn_all2 by Lia.lia. cbn [chunks2].
          destruct xs; [congruence|]. destruct xs; [|simpl in He; Lia.lia].
          destruct k; [reflexivity|].
          destruct k; [reflexivity|].
          assert (S (S k) = k + 2)%nat as -> by Lia.lia.
          rewrite NatUtil.div_minus by Lia.lia.
          rewrite (ListUtil.nth_error_length_error _ (2 * _ + _)%nat [a]) by (simpl; Lia.lia).
          rewrite PeanoNat.Nat.add_1_r, ListUtil.nth_error_nil_error. reflexivity.
        + destruct k; [simpl; destruct xs; reflexivity|].
          destruct k; [simpl; destruct xs; [reflexivity|destruct xs; reflexivity]|].
          assert (S (S k) = k + 2)%nat as -> by Lia.lia.
          rewrite NatUtil.div_minus by Lia.lia.
          rewrite PeanoNat.Nat.add_1_r.
          assert (k + 2 = k + 1 * 2)%nat as -> by Lia.lia.
          rewrite PeanoNat.Nat.Div0.mod_add.
          rewrite <- IHn by (rewrite skipn_length; Lia.lia).
          rewrite <- (firstn_skipn 2 xs) at 1.
          rewrite nth_error_app2; rewrite firstn_length_le; try Lia.lia.
          rewrite (PeanoNat.Nat.Div0.div_mod k 2) at 3. f_equal. Lia.lia. }
    apply (IH _ _ ltac:(reflexivity)).
  Qed.

  Lemma chunks2_Forall2 {A B} (R: A -> B -> Prop) (l1: list A) (l2: list B):
    Forall2 R l1 l2 ->
    Forall2 (Forall2 R) (chunks2 l1) (chunks2 l2).
  Proof.
    assert (IH: forall n (xs1: list A) (xs2: list B), (length xs1 <= n) -> Forall2 R xs1 xs2 -> Forall2 (Forall2 R) (chunks2 xs1) (chunks2 xs2)).
    { induction n; intros xs1 xs2 Hxs1 HR.
      - destruct xs1; simpl in Hxs1; [|Lia.lia].
        inversion HR; subst xs2. constructor.
      - destruct (@Decidable.dec_eq_list_nil_r _ xs1) as [->|Hnn1]; [inversion HR; subst xs2; constructor|].
        generalize (Forall2_length HR); intro Hlength.
        destruct (@Decidable.dec_eq_list_nil_r _ xs2) as [->|Hnn2]; [destruct xs1; simpl in Hlength; try congruence; Lia.lia|].
        rewrite (chunks2_cons xs1), (chunks2_cons xs2); auto.
        rewrite <- (firstn_skipn 2 xs1), <- (firstn_skipn 2 xs2) in HR.
        apply Forall2_app_inv in HR; [|repeat rewrite firstn_length; Lia.lia].
        destruct HR. constructor; auto.
        apply IHn; auto. rewrite skipn_length. Lia.lia. }
    apply (IH _ _ _ ltac:(reflexivity)).
  Qed.

  Lemma chunks2_map {A B} (f: A -> B) (l: list A):
    chunks2 (map f l) = map (map f) (chunks2 l).
  Proof.
    assert (IH: forall n (xs: list A), length xs <= n -> chunks2 (map f xs) = map (map f) (chunks2 xs)).
    { induction n; intros xs Hxs.
      - destruct xs; simpl in Hxs; [|Lia.lia]. reflexivity.
      - destruct xs; [reflexivity|].
        destruct xs; [reflexivity|].
        simpl in *. rewrite IHn by Lia.lia. reflexivity. }
    apply (IH _ _ ltac:(reflexivity)).
  Qed.

  Lemma chunks2_app2 {A} (l1 l2: list A):
    length l1 = 2%nat ->
    chunks2 (l1 ++ l2) = l1::(chunks2 l2).
  Proof.
    intro X. destruct l1; [|destruct l1; [|destruct l1]]; simpl in X; try congruence.
    reflexivity.
  Qed.

  Lemma chunks2_flat_map_constant2 {A B} (f: A -> list B) (l: list A):
    (forall x : A, In x l -> length (f x) = 2%nat) ->
    chunks2 (flat_map f l) = map f l.
  Proof.
    induction l; intros X; [reflexivity|].
    simpl. rewrite chunks2_app2; [|apply X; left; auto].
    rewrite IHl; [reflexivity|]. intros; apply X; right; auto.
  Qed.

  Lemma chunk_concat {A} (l: list (list A)) (sz: nat) (szn0: (sz <> 0)%nat)
    (Hl: Forall (fun l => length l = sz) l):
    chunk sz (concat l) = l.
  Proof.
    induction Hl; [reflexivity|].
    simpl. rewrite chunk_app_chunk; auto.
    rewrite IHHl. reflexivity.
  Qed.

  Lemma skipn_flat_map_constant_length {A B: Type} (c: nat) (f: A -> list B)
    (l: list A):
    (forall x, In x l -> length (f x) = c) ->
    forall k, skipn (k * c) (flat_map f l) = flat_map f (skipn k l).
  Proof.
    assert (HS: forall l, (forall x, In x l -> length (f x) = c) -> skipn c (flat_map f l) = flat_map f (skipn 1 l)).
    { clear l; induction l; intro Hlen.
      - simpl. apply skipn_nil.
      - simpl. rewrite skipn_app_r; auto.
        rewrite Hlen; auto. left; reflexivity. }
    induction k; [reflexivity|].
    assert (S k * c = c + k * c)%nat as -> by Lia.lia.
    rewrite <- skipn_skipn, IHk.
    rewrite HS; [|intros; apply H; eapply ListUtil.In_skipn; eauto].
    rewrite skipn_skipn. f_equal.
  Qed.

  Global Instance Forall2_Equivalence {A: Type} {R: A -> A -> Prop} `{Equivalence _ R}:
    Equivalence (Forall2 R).
  Proof.
    constructor.
    - intro. apply Forall2_nth_error_iff. split; [reflexivity|].
      intros k v1 v2 Hv1 Hv2. rewrite Hv2 in Hv1; inversion Hv1; subst v1; reflexivity.
    - intros x y Hxy. apply Forall2_nth_error_iff in Hxy.
      apply Forall2_nth_error_iff. destruct Hxy as [Heq Hxy].
      split; auto. intros k v1 v2 Hv1 Hv2.
      symmetry. eapply Hxy; eauto.
    - intros x y z Hxy Hyz. apply Forall2_nth_error_iff in Hxy, Hyz.
      destruct Hxy as [Heq1 Hxy]. destruct Hyz as [Heq2 Hyz].
      apply Forall2_nth_error_iff. split; [congruence|].
      intros k v1 v2 Hv1 Hv2.
      generalize (ListUtil.nth_error_value_length _ _ _ _ Hv1). intro Hlt.
      rewrite Heq1 in Hlt.
      apply ListUtil.nth_error_length_exists_value in Hlt.
      destruct Hlt as [v3 Hv3]. etransitivity; eauto.
  Qed.

  Lemma Forall2_map {A B: Type} {R: A -> A -> Prop} {R': B -> B -> Prop}
    `{Equivalence _ R} `{Equivalence _ R'}:
    forall f l1 l2,
      Forall2 R l1 l2 ->
      Proper (R ==> R') f ->
      Forall2 R' (map f l1) (map f l2).
  Proof.
    intros f l1 l2 HA HB. apply Forall2_nth_error_iff.
    split; [repeat rewrite map_length; eapply Forall2_length; eauto|].
    intros k v1 v2 Hv1 Hv2.
    rewrite nth_error_map in Hv1, Hv2.
    destruct (nth_error l1 k) as [a1|] eqn:Ha1; simpl in Hv1; [|congruence].
    destruct (nth_error l2 k) as [a2|] eqn:Ha2; simpl in Hv2; [|congruence].
    inversion Hv1; inversion Hv2; subst v1; subst v2. apply HB.
    apply Forall2_nth_error_iff in HA. eapply (proj2 HA); eauto.
  Qed.

  Lemma Forall2_map_in {X A B: Type} {R: A -> B -> Prop}:
    forall (l: list X) f g,
      (forall x, In x l -> R (f x) (g x)) ->
      Forall2 R (map f l) (map g l).
  Proof.
    induction l; intros f g HR; [constructor|].
    simpl. constructor; auto.
    - apply HR. left. reflexivity.
    - apply IHl. intros; apply HR; right; auto.
  Qed.

  Lemma Forall_chunk_length_eq {A: Type} (k c: nat):
    forall (l: list A),
      (length l = k * c)%nat ->
      Forall (fun ck => length ck = k) (chunk k l).
  Proof.
    induction c; intros l Hl.
    - rewrite PeanoNat.Nat.mul_0_r in Hl.
      apply ListUtil.length0_nil in Hl. subst l.
      rewrite chunk_nil. constructor.
    - destruct (NatUtil.nat_eq_dec k 0%nat) as [->|Hknz].
      + rewrite PeanoNat.Nat.mul_0_l in Hl.
        apply ListUtil.length0_nil in Hl. subst l.
        rewrite chunk_nil. constructor.
      + rewrite <- (firstn_skipn k l).
        rewrite chunk_app_chunk; auto.
        2: apply firstn_length_le; Lia.lia.
        constructor; [apply firstn_length_le; Lia.lia|].
        apply IHc. rewrite skipn_length. Lia.lia.
  Qed.

  Lemma skipn_concat_same_length {A: Type} (k c : nat) (l: list (list A)):
    Forall (fun x => length x = c) l ->
    skipn (k * c) (concat l) = concat (skipn k l).
  Proof.
    revert l. induction k; intros l HF.
    - rewrite PeanoNat.Nat.mul_0_l; reflexivity.
    - destruct l as [|x].
      + rewrite skipn_nil, concat_nil. reflexivity.
      + rewrite skipn_cons, <- IHk; [|inversion HF; auto].
        simpl. rewrite <- ListUtil.skipn_skipn.
        rewrite skipn_app_r; auto.
        inversion HF; auto.
  Qed.

  Lemma chunk_map {A B: Type} (f: A -> B) (n: nat):
    forall l,
      (n <> 0)%nat ->
      chunk n (map f l) = map (map f) (chunk n l).
  Proof.
    intros l Hn. apply nth_error_ext.
    intro i. rewrite nth_error_map.
    destruct (Compare_dec.lt_dec i (length (chunk n l))) as [Hlt|Hnlt]; rewrite length_chunk in * by assumption.
    - rewrite nth_error_chunk; auto.
      2: rewrite map_length; auto.
      rewrite nth_error_chunk; auto.
      simpl. rewrite skipn_map, firstn_map. reflexivity.
    - rewrite ListUtil.nth_error_length_error.
      2: rewrite length_chunk, map_length; auto; Lia.lia.
      rewrite ListUtil.nth_error_length_error.
      2: rewrite length_chunk; auto; Lia.lia.
      reflexivity.
  Qed.

End Utils.

Section CyclotomicDecomposition.
  Context {q: positive} {prime_q: prime q}.
  Local Notation F := (F q). (* This is to have F.pow available, there is no Fpow defined for a general field *)
  Local Open Scope F_scope.
  Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
    {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.
  Context {P}{poly_ops: @Polynomial.polynomial_ops F P}.
  Context {poly_defs: @Polynomial.polynomial_defs F eq F.zero F.one F.opp F.add F.sub F.mul P _}.
  Context {zeta: F} {km1: N} {Hkm1: zeta ^ (N.pow 2 km1) = F.opp 1}.

  Local Notation Peq := (@Polynomial.Peq F eq P _).
  Local Notation Pmod := (@Polynomial.Pmod F F.zero P _ F.div).
  Local Notation Pmul := (@Polynomial.Pmul _ _ poly_ops).
  Local Notation Pconst := (@Polynomial.Pconst _ _ poly_ops).
  Local Notation negacyclic := (@Polynomial.negacyclic F P _).
  Local Notation posicyclic := (@Polynomial.posicyclic F P _).
  Local Notation coprime := (Polynomial.coprime (poly_defs:=poly_defs) (Fdiv:=F.div)).
  Local Notation Pquotl := (@Polynomial.Pquotl F eq F.zero P _ F.div).
  Local Notation of_pl := (Polynomial.of_pl (poly_defs:=poly_defs) (Finv:=F.inv) (Fdiv:=F.div) (field:=field)).

  Lemma zeta_pow_nz:
    forall k, zeta ^ k <> 0.
  Proof.
    apply N.peano_ind.
    - rewrite F.pow_0_r. symmetry; apply Hierarchy.zero_neq_one.
    - intros n IH. rewrite F.pow_succ_r.
      intro X. apply Hierarchy.zero_product_zero_factor in X.
      destruct X as [X|X]; [|elim IH; auto].
      rewrite X in Hkm1. rewrite F.pow_0_l in Hkm1 by Lia.lia.
      symmetry in Hkm1. apply Group.inv_id_iff in Hkm1.
      rewrite Group.inv_inv in Hkm1.
      symmetry in Hkm1. apply Hierarchy.zero_neq_one in Hkm1; auto.
  Qed.

  Lemma zeta_pow_succ_km1:
    zeta ^ (N.pow 2 (N.succ km1)) = 1.
  Proof.
    rewrite N.pow_succ_r', N.mul_comm, <- F.pow_pow_l, Hkm1.
    rewrite F.pow_2_r, (@Ring.mul_opp_l F eq _ _ _ _ _ _ _ 1 _), (@Ring.mul_opp_r F eq _ _ _ _ _ _ _ _ 1).
    rewrite (@Group.inv_inv F _ _ _ _ _).
    apply Hierarchy.left_identity.
  Qed.

  Lemma zeta_pow_mod:
    forall k, zeta ^ k = zeta ^ (k mod (N.pow 2 (N.succ km1))).
  Proof.
    intros k; rewrite (N.Div0.div_mod k (N.pow 2 (N.succ km1))) at 1.
    rewrite F.pow_add_r, <- F.pow_pow_l.
    rewrite zeta_pow_succ_km1, F.pow_1_l.
    apply Hierarchy.left_identity.
  Qed.

  Lemma neg_zeta_power_eq:
    forall k,
      F.opp (zeta ^ k) = zeta ^ (N.add (N.pow 2 km1) k).
  Proof.
    intros k. rewrite F.pow_add_r, Hkm1.
    rewrite Ring.mul_opp_l, (@Hierarchy.left_identity F eq F.mul _ _ _).
    reflexivity.
  Qed.

  Fixpoint cyclotomic_decompose (i: nat) :=
    match i with
    | O => [2 ^ km1]%N
    | S i => flat_map (fun n => [N.div n 2%N; N.add (2 ^ km1) (N.div n 2)])%N (cyclotomic_decompose i)
    end.

  Definition cyclotomic_decomposition (n: nat) (i: nat) :=
    List.map (fun j => posicyclic (Nat.pow 2 (n - i)%nat) (zeta ^ j)) (cyclotomic_decompose i).

  (* We only keep one half of the coefficients since the other half can be recovered from it *)
  Fixpoint zeta_powers (i: nat) :=
    match i with
    | O => cyclotomic_decompose O
    | S i => (zeta_powers i) ++ (List.map (fun k => nth_default 0%N (cyclotomic_decompose (S i)) (2 * k)%nat) (seq 0%nat (Nat.pow 2 i)))
    end.

  Lemma zeta_powers_length (i: nat):
    length (zeta_powers i) = Nat.pow 2 i.
  Proof.
    induction i; [reflexivity|].
    simpl; rewrite app_length, map_length, seq_length, IHi.
    Lia.lia.
  Qed.

  Lemma cyclotomic_decompose_length i:
    length (cyclotomic_decompose i) = Nat.pow 2 i.
  Proof.
    induction i; [reflexivity|].
    rewrite PeanoNat.Nat.pow_succ_r'. simpl.
    erewrite flat_map_constant_length; [|simpl; reflexivity].
    rewrite IHi; Lia.lia.
  Qed.

  Lemma cyclotomic_decomposition_length n i:
    length (cyclotomic_decomposition n i) = Nat.pow 2 i.
  Proof. unfold cyclotomic_decomposition; rewrite map_length, cyclotomic_decompose_length. reflexivity. Qed.

  Context {n: nat} {Hnkm1: (n >= N.to_nat km1)%nat}.

  Lemma cyclotomic_decompose_mod:
    forall i, (i <= N.to_nat km1)%nat ->
         (forall p, In p (cyclotomic_decompose i) -> (p mod (2 ^ (km1 - N.of_nat i)) = 0)%N /\ (p < N.pow 2 (N.succ km1))%N).
  Proof.
    induction i; intros Hi p Hin.
    - simpl. simpl in Hin. destruct Hin as [<-|Hin]; [|elim Hin].
      rewrite N.sub_0_r, N.Div0.mod_same, N.pow_succ_r'.
      split; Lia.lia.
    - specialize (IHi ltac:(Lia.lia)).
      apply In_nth_error in Hin. destruct Hin as [k Hin].
      simpl in Hin. eapply flat_map_constant_nth_error in Hin; [|simpl; reflexivity].
      destruct Hin as (n1 & (Hn1 & Hn2)).
      destruct (IHi n1 ltac:(eapply nth_error_In; eauto)) as [A B].
      assert (km1 - N.of_nat i = N.succ (km1 - N.of_nat (S i)) :> _)%N as C by Lia.lia.
      rewrite C, N.pow_succ_r' in A.
      apply N.Div0.div_exact in A.
      assert (n1/2 = 2 ^ (km1 - N.of_nat (S i)) * (n1 / (2 * 2 ^ (km1 - N.of_nat (S i)))) :> _)%N as D.
      { rewrite A at 1. assert (2 * 2 ^ (km1 - N.of_nat (S i)) * (n1 / (2 * 2 ^ (km1 - N.of_nat (S i)))) = (2 ^ (km1 - N.of_nat (S i)) * (n1 / (2 * 2 ^ (km1 - N.of_nat (S i))))) * 2 :> _)%N as -> by Lia.lia.
        rewrite N.div_mul by Lia.lia. reflexivity. }
      assert (PeanoNat.Nat.modulo k 2 = 0%nat :> _ \/ PeanoNat.Nat.modulo k 2 = 1%nat :> _)%nat as E by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
      destruct E as [E|E]; rewrite E in Hn2; simpl in Hn2; inversion Hn2; subst p.
      + split.
        * rewrite D, N.mul_comm. apply N.Div0.mod_mul.
        * rewrite N.pow_succ_r' in B.
          apply N.Div0.div_lt_upper_bound in B.
          rewrite N.pow_succ_r'; Lia.lia.
      + split.
        * rewrite D.
          assert (2 ^ km1 = 2 ^ ((km1 - N.of_nat (S i)) + N.of_nat (S i)))%N as -> by (f_equal; Lia.lia).
          rewrite N.pow_add_r, <- N.mul_add_distr_l, N.mul_comm. apply N.Div0.mod_mul.
        * rewrite N.pow_succ_r' in B.
          apply N.Div0.div_lt_upper_bound in B.
          rewrite N.pow_succ_r'; Lia.lia.
  Qed.

  Lemma cyclotomic_decompose_S_nth_error:
    forall i, (S i <= N.to_nat km1)%nat ->
         forall k v,
           nth_error (cyclotomic_decompose i) k = Some v ->
           nth_error (cyclotomic_decompose (S i)) (2 * k) = Some (v / 2)%N /\
           nth_error (cyclotomic_decompose (S i)) (2 * k + 1) = Some (2 ^ km1 + v / 2)%N /\
           (v = 2 * (v / 2))%N.
  Proof.
    intros i Hi k v Hv.
    cbn [cyclotomic_decompose].
    generalize (ListUtil.nth_error_value_length _ _ _ _ Hv).
    rewrite cyclotomic_decompose_length. intro Hk.
    assert (Hlt: (2 * k + 1 < PeanoNat.Nat.pow 2 (S i))%nat) by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
    destruct (ListUtil.nth_error_length_exists_value (2 * k) (cyclotomic_decompose (S i)) ltac:(rewrite cyclotomic_decompose_length; Lia.lia)) as [v1 Hv1].
    destruct (ListUtil.nth_error_length_exists_value (2 * k + 1) (cyclotomic_decompose (S i)) ltac:(rewrite cyclotomic_decompose_length; Lia.lia)) as [v2 Hv2].
    cbn [cyclotomic_decompose] in Hv1, Hv2.
    destruct (flat_map_constant_nth_error 2%nat (fun n0 : N => [(n0 / 2)%N; (2 ^ km1 + n0 / 2)%N]) _ ltac:(reflexivity) _ _ Hv1) as [y [Hy1 Hy1']].
    destruct (flat_map_constant_nth_error 2%nat (fun n0 : N => [(n0 / 2)%N; (2 ^ km1 + n0 / 2)%N]) _ ltac:(reflexivity) _ _ Hv2) as [y2 [Hy2 Hy2']].
    assert (PeanoNat.Nat.div (2 * k) 2 = k) as HA by (symmetry; apply (PeanoNat.Nat.div_unique _ 2 k 0 ltac:(Lia.lia)); Lia.lia).
    rewrite HA in Hy1. clear HA.
    assert (PeanoNat.Nat.div (2 * k + 1) 2 = k) as HA by (symmetry; apply (PeanoNat.Nat.div_unique _ 2 k 1 ltac:(Lia.lia)); Lia.lia).
    rewrite HA in Hy2. clear HA.
    assert (y = y2) by congruence; subst y2.
    assert (v = y) by congruence; subst y.
    assert (PeanoNat.Nat.modulo (2 * k) 2 = 0)%nat as HA by (symmetry; apply (PeanoNat.Nat.mod_unique _ 2 k 0 ltac:(Lia.lia)); Lia.lia).
    rewrite HA in Hy1'; clear HA.
    assert (PeanoNat.Nat.modulo (2 * k + 1) 2 = 1)%nat as HA by (symmetry; apply (PeanoNat.Nat.mod_unique _ 2 k 1 ltac:(Lia.lia)); Lia.lia).
    rewrite HA in Hy2'; clear HA.
    simpl in Hy1', Hy2'.
    split; [congruence|]. split; [congruence|].
    apply ListUtil.List.nth_error_In in Hv.
    destruct (cyclotomic_decompose_mod i ltac:(Lia.lia) _ Hv) as [HA HB].
    apply N.Div0.div_exact.
    apply N.Div0.mod_divides. apply N.Div0.mod_divides in HA.
    destruct HA as [a HA]. rewrite HA.
    assert (km1 - N.of_nat i = N.succ (km1 - N.of_nat (S i)))%N as -> by Lia.lia.
    rewrite N.pow_succ_r'. exists (2 ^ (km1 - N.of_nat (S i)) * a)%N. Lia.lia.
  Qed.

  Lemma zeta_powers_In:
    forall i, (i <= N.to_nat km1)%nat ->
         forall x, In x (zeta_powers i) ->
              (x <= N.pow 2 km1)%N.
  Proof.
    induction i; intros Hi x Hx.
    - cbn in Hx. destruct Hx as [<- | Hx]; [reflexivity|elim Hx].
    - cbn [zeta_powers] in Hx. apply in_app_or in Hx.
      destruct Hx as [Hx|Hx].
      + apply IHi; auto. Lia.lia.
      + apply in_map_iff in Hx. destruct Hx as [y [Hy Hy']].
        apply in_seq in Hy'. rewrite PeanoNat.Nat.add_0_l in Hy'.
        destruct (ListUtil.nth_error_length_exists_value y (cyclotomic_decompose i) ltac:(rewrite cyclotomic_decompose_length; Lia.lia)) as [v Hv].
        generalize (nth_error_In _ _ Hv). intro Hin.
        apply cyclotomic_decompose_mod in Hin; [|Lia.lia].
        destruct Hin as [Hv1 Hv2].
        apply cyclotomic_decompose_S_nth_error in Hv; [|Lia.lia].
        destruct Hv as [Hv1' [Hv2' Hv_eq]].
        rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hv1') in Hy.
        subst x. assert (N.pow 2 km1 = N.div (N.pow 2 (N.succ km1)) 2) as -> by (rewrite N.pow_succ_r, N.mul_comm, N.div_mul by Lia.lia; reflexivity).
        apply N.Div0.div_le_mono. Lia.lia.
  Qed.

  Lemma cyclotomic_decomposition_0:
    Peq (negacyclic (Nat.pow 2 n) F.one) (List.fold_right Pmul Pone (cyclotomic_decomposition n 0%nat)).
  Proof.
    simpl. rewrite (@Hierarchy.right_identity P Peq Pmul _ _), Hkm1, Polynomial.posicyclic_opp.
    rewrite PeanoNat.Nat.sub_0_r. reflexivity.
  Qed.

  Lemma cyclotomic_decompose_zeta_powers_nth:
    forall i j k, (S i <= j)%nat ->
             (k < Nat.pow 2 i)%nat ->
             exists v, nth_error (zeta_powers j) (Nat.pow 2 i + k) = Some v /\
                  nth_error (cyclotomic_decompose (S i)) (2 * k)%nat = Some v.
  Proof.
    assert (IH: forall j i, (S i <= j)%nat -> exists tl, zeta_powers j = zeta_powers i ++ (map (fun k : nat => nth_default 0%N (cyclotomic_decompose (S i)) (2 * k)) (seq 0 (Nat.pow 2 i))) ++ tl).
    { induction j; intros i Hi; [Lia.lia|].
      assert (S i <= j \/ i = j) as [Hlt|<-] by Lia.lia.
      - simpl. destruct (IHj _ Hlt) as [tl Heq].
        rewrite Heq. repeat rewrite <- List.app_assoc.
        eexists; f_equal.
      - exists nil. rewrite List.app_nil_r. reflexivity. }
    intros i j k Hj Hk.
    generalize (zeta_powers_length j); intros Hlenj.
    generalize (PeanoNat.Nat.pow_le_mono_r 2%nat _ _ ltac:(Lia.lia) Hj).
    rewrite PeanoNat.Nat.pow_succ_r'; intro Hle.
    destruct (ListUtil.nth_error_length_exists_value (Nat.pow 2 i + k) (zeta_powers j) ltac:(Lia.lia)) as [x Hx].
    eexists; split; eauto.
    destruct (IH _ _ Hj) as [tl Heq].
    rewrite Heq, nth_error_app2 in Hx by (rewrite zeta_powers_length; Lia.lia).
    rewrite zeta_powers_length in Hx.
    rewrite nth_error_app1 in Hx by (rewrite map_length, seq_length; Lia.lia).
    rewrite nth_error_map in Hx.
    replace (Nat.pow 2 i + k - _)%nat with k in Hx by Lia.lia.
    rewrite ListUtil.nth_error_seq in Hx.
    destruct (Compare_dec.lt_dec k (Nat.pow 2 i)) as [_|]; [|Lia.lia].
    rewrite PeanoNat.Nat.add_0_l in Hx. cbn [option_map] in Hx.
    erewrite ListUtil.nth_error_Some_nth_default; eauto.
    rewrite cyclotomic_decompose_length, PeanoNat.Nat.pow_succ_r'. Lia.lia.
  Qed.

  Lemma cyclotomic_decomposition_S_chunks2:
    forall i,
      (S i <= N.to_nat km1)%nat ->
      Forall2 (fun p pp =>
                 exists p1 p2, pp = [p1; p2] /\ coprime p1 p2 /\ Peq p (Pmul p1 p2)
                          /\ exists k, Peq p (posicyclic (2 * (Nat.pow 2 (n - S i))) (F.mul (zeta^k) (zeta^k)))
                                 /\ Peq p1 (posicyclic (Nat.pow 2 (n - S i)) (zeta^k))
                                 /\ Peq p2 (negacyclic (Nat.pow 2 (n - S i)) (zeta^k)))
        (cyclotomic_decomposition n i)
        (chunks2 (cyclotomic_decomposition n (S i))).
  Proof.
    intros i Hi.
    unfold cyclotomic_decomposition. rewrite chunks2_map.
    cbn [cyclotomic_decompose]. rewrite chunks2_flat_map_constant2 by reflexivity.
    apply Forall2_nth_error_iff.
    repeat rewrite map_length. split; [reflexivity|].
    intros k v1 v2 Hv1 Hv2. rewrite ListUtil.nth_error_map in Hv1.
    do 2 rewrite ListUtil.nth_error_map in Hv2.
    destruct (nth_error (cyclotomic_decompose i) k) as [v|] eqn:Hv; simpl in Hv1, Hv2; [|congruence].
    inversion Hv1; inversion Hv2; subst v1; subst v2; clear Hv1; clear Hv2.
    eexists; eexists; split; [reflexivity|].
    apply nth_error_In in Hv. apply cyclotomic_decompose_mod in Hv; [|Lia.lia].
    destruct Hv as [Hv1 Hv2].
    rewrite <- neg_zeta_power_eq, Polynomial.posicyclic_opp.
    split; [apply Polynomial.posicyclic_decomposition_coprime; [generalize (NatUtil.pow_nonzero 2 (n - S i)%nat); Lia.lia|apply zeta_pow_nz]|].
    rewrite <- Polynomial.posicyclic_decomposition.
    assert (Nat.pow 2 (n - i) = 2 * Nat.pow 2 (n - (S i)))%nat as -> by (rewrite <- PeanoNat.Nat.pow_succ_r'; f_equal; Lia.lia).
    assert (zeta ^ v = zeta ^ (v / 2) * zeta ^ (v / 2)) as ->; [|split; [reflexivity|exists (v/2)%N; split; [reflexivity|split; [reflexivity|apply Polynomial.posicyclic_opp]]]].
    rewrite <- F.pow_2_r, F.pow_pow_l.
    assert (v / 2 * 2 = v :> _)%N as ->; [|reflexivity].
    rewrite (N.Div0.div_mod v 2) at 2.
    assert (v mod 2 = 0 :> _)%N as ->; [|Lia.lia].
    apply N.Div0.mod_divides. apply N.Div0.mod_divides in Hv1.
    destruct Hv1 as [c Hc]. rewrite Hc.
    assert (km1 - N.of_nat i = N.succ (km1 - N.of_nat (S i)) :> _)%N as -> by Lia.lia.
    rewrite N.pow_succ_r'. exists (2 ^ (km1 - N.of_nat (S i)) * c)%N; Lia.lia.
  Qed.

  Lemma cyclotomic_decomposition_S:
    forall i,
      (S i <= N.to_nat km1)%nat ->
      forall k p1 p2, nth_error (cyclotomic_decomposition n (S i)) (2 * k)%nat = Some p1 ->
                 nth_error (cyclotomic_decomposition n (S i)) (2 * k + 1)%nat = Some p2 ->
                 coprime p1 p2 /\
                 exists p, nth_error (cyclotomic_decomposition n i) k = Some p /\
                      Peq p (Pmul p1 p2).
  Proof.
    intros i Hi k p1 p2 Hp1 Hp2.
    unfold cyclotomic_decomposition in *.
    rewrite nth_error_map in *.
    destruct (nth_error (cyclotomic_decompose (S i)) (2 * k)) as [n1|] eqn:Hn1; [|inversion Hp1].
    destruct (nth_error (cyclotomic_decompose (S i)) (2 * k + 1)) as [n2|] eqn:Hn2; [|inversion Hp2].
    simpl in Hp1, Hp2. unfold cyclotomic_decompose in Hn1, Hn2.
    fold cyclotomic_decompose in Hn1, Hn2.
    eapply flat_map_constant_nth_error in Hn1; [|simpl; reflexivity].
    eapply flat_map_constant_nth_error in Hn2; [|simpl; reflexivity].
    rewrite (PeanoNat.Nat.mul_comm 2%nat k), PeanoNat.Nat.div_mul, PeanoNat.Nat.Div0.mod_mul in Hn1 by Lia.lia.
    rewrite <- (PeanoNat.Nat.div_unique (2 * k + 1)%nat 2 k 1 ltac:(Lia.lia) ltac:(reflexivity)) in Hn2.
    rewrite <- (PeanoNat.Nat.mod_unique (2 * k + 1)%nat 2 k 1 ltac:(Lia.lia) ltac:(reflexivity)) in Hn2.
    simpl in Hn1, Hn2. destruct Hn1 as (n0 & (Hn0 & Hn1)). rewrite Hn0 in Hn2.
    destruct Hn2 as (n0' & (Hn0' & Hn2)). inversion Hn0'; subst n0'; clear Hn0'.
    rewrite Hn0; simpl. inversion Hn1; subst n1; clear Hn1.
    inversion Hn2; subst n2; clear Hn2.
    inversion Hp1; subst p1; clear Hp1.
    inversion Hp2; subst p2; clear Hp2.
    rewrite F.pow_add_r, Hkm1, (@Ring.mul_opp_l F eq F.zero F.one F.opp _ _ _ _).
    rewrite (@Hierarchy.left_identity F eq _ _ _).
    rewrite Polynomial.posicyclic_opp.
    split; [apply Polynomial.posicyclic_decomposition_coprime; [generalize (NatUtil.pow_nonzero 2 (n - S i)%nat); Lia.lia|apply zeta_pow_nz]|].
    eexists; split; [reflexivity|].
    rewrite Polynomial.posicyclic_opp, <- Polynomial.posicyclic_decomposition.
    rewrite <- PeanoNat.Nat.pow_succ_r'.
    assert (S (n - S i) = n - i :> _)%nat as -> by Lia.lia.
    rewrite <- F.pow_2_r, F.pow_pow_l.
    assert (n0 / 2 * 2 = n0 :> _)%N as ->; [|reflexivity].
    rewrite (N.Div0.div_mod n0 2) at 2.
    assert (n0 mod 2 = 0 :> _)%N as ->; [|Lia.lia].
    apply nth_error_In in Hn0.
    apply cyclotomic_decompose_mod in Hn0; [|Lia.lia].
    destruct Hn0 as [X _].
    apply N.Div0.mod_divides. apply N.Div0.mod_divides in X.
    destruct X as [c Hc]. rewrite Hc.
    assert (km1 - N.of_nat i = N.succ (km1 - N.of_nat (S i)) :> _)%N as -> by Lia.lia.
    rewrite N.pow_succ_r'. exists (2 ^ (km1 - N.of_nat (S i)) * c)%N; Lia.lia.
  Qed.

  Lemma cyclotomic_decomposition_product_S:
    forall i,
      (S i <= N.to_nat km1)%nat ->
      Peq (List.fold_right Pmul Pone (cyclotomic_decomposition n i)) (List.fold_right Pmul Pone (cyclotomic_decomposition n (S i))).
  Proof.
    intros i Hi.
    assert (IH: forall k, Peq (fold_right Pmul Pone (firstn k (cyclotomic_decomposition n i))) (fold_right Pmul Pone (firstn (2*k) (cyclotomic_decomposition n (S i))))).
    { induction k; [reflexivity|].
      destruct (Decidable.dec_le_nat (length (cyclotomic_decomposition n i)) k) as [Hle|Hgt].
      - assert (Hle': length (cyclotomic_decomposition n (S i)) <= 2 * k).
        { rewrite cyclotomic_decomposition_length in *.
          rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia. }
        do 2 rewrite firstn_all2 in IHk by assumption.
        do 2 rewrite firstn_all2 by Lia.lia. assumption.
      - rewrite (ListUtil.firstn_succ Pzero) by Lia.lia.
        assert (2 * S k = S (S (2 * k)) :> _)%nat as -> by Lia.lia.
        assert (Hgt': S (2 * k) < length (cyclotomic_decomposition n (S i))).
        { rewrite cyclotomic_decomposition_length in *.
          rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia. }
        do 2 rewrite (ListUtil.firstn_succ Pzero) by Lia.lia.
        repeat rewrite (@fold_right_monoid_app P Peq Pmul _ _).
        rewrite <- IHk. repeat rewrite (@fold_right_monoid_singleton P Peq Pmul _ _).
        rewrite <- (@Hierarchy.associative P Peq Pmul _).
        generalize (ListUtil.nth_error_Some_nth_default (2 * k) Pzero (cyclotomic_decomposition n (S i)) ltac:(Lia.lia)). intro H2k.
        assert (S (2 * k) = 2 * k + 1 :> _)%nat as -> by Lia.lia.
        generalize (ListUtil.nth_error_Some_nth_default (2 * k + 1) Pzero (cyclotomic_decomposition n (S i)) ltac:(Lia.lia)). intro H2kp1.
        generalize (ListUtil.nth_error_Some_nth_default k Pzero (cyclotomic_decomposition n i) ltac:(Lia.lia)). intro Hk.
        generalize (cyclotomic_decomposition_S i Hi k _ _ H2k H2kp1).
        intros [_ [x [He Hmul]]].
        rewrite Hk in He. inversion He; subst x; clear He.
        rewrite <- Hmul. reflexivity. }
    rewrite <- (ListUtil.List.firstn_all (cyclotomic_decomposition n i)).
    rewrite <- (ListUtil.List.firstn_all (cyclotomic_decomposition n (S i))).
    do 2 rewrite cyclotomic_decomposition_length.
    rewrite PeanoNat.Nat.pow_succ_r'. apply IH.
  Qed.

  Lemma cyclotomic_decompose_product:
    forall i,
      (i <= N.to_nat km1)%nat ->
      Peq (negacyclic (Nat.pow 2 n) 1) (List.fold_right Pmul Pone (cyclotomic_decomposition n i)).
  Proof.
    induction i; intro Hi.
    - unfold cyclotomic_decomposition; simpl. rewrite PeanoNat.Nat.sub_0_r, Hkm1, Polynomial.posicyclic_opp.
      rewrite (@Hierarchy.right_identity P Peq Pmul _ _). reflexivity.
    - rewrite IHi by Lia.lia. apply cyclotomic_decomposition_product_S; auto.
  Qed.

  Lemma cyclotomic_decompose_inv:
    forall i, (i <= N.to_nat km1)%nat ->
         forall k, (k < Nat.pow 2 i)%nat ->
              forall a b,
                nth_error (cyclotomic_decompose i) k = Some a ->
                nth_error (cyclotomic_decompose i) (Nat.pow 2 i - 1 - k)%nat = Some b ->
                (a + b = N.pow 2 (N.succ km1))%N /\ (F.mul (F.pow zeta a) (F.pow zeta b) = 1)%F.
  Proof.
    induction i; intros Hi k Hk a b Ha Hb.
    - simpl in Hk. assert (k = 0)%nat as -> by Lia.lia.
      simpl in Ha, Hb. inversion Ha; subst a; clear Ha.
      inversion Hb; subst b; clear Hb.
      rewrite N.pow_succ_r', <- F.pow_2_r, F.pow_pow_l.
      split; [Lia.lia|].
      rewrite N.mul_comm, <- N.pow_succ_r', zeta_pow_succ_km1. reflexivity.
    - simpl in Ha, Hb. rewrite PeanoNat.Nat.add_0_r in Hb.
      eapply flat_map_constant_nth_error in Ha, Hb; try (simpl; reflexivity).
      destruct Ha as [a' [Ha1 Ha2]]. destruct Hb as [b' [Hb1 Hb2]].
      assert (Nat.pow 2 i + Nat.pow 2 i = 2 * Nat.pow 2 i)%nat as He by Lia.lia.
      rewrite He, <- PeanoNat.Nat.pow_succ_r' in Hb1, Hb2. clear He.
      rewrite PeanoNat.Nat.pow_succ_r' in Hk.
      apply PeanoNat.Nat.Div0.div_lt_upper_bound in Hk.
      assert (Nat.modulo k 2 = 0 \/ Nat.modulo k 2 = 1)%nat as Hkmod by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
      assert (PeanoNat.Nat.div (PeanoNat.Nat.pow 2 (S i) - 1 - k) 2 = Nat.pow 2 i - 1 - Nat.div k 2)%nat as He.
      { rewrite (PeanoNat.Nat.div_mod_eq k 2) at 1.
        rewrite PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.sub_add_distr.
        assert (2 * PeanoNat.Nat.pow 2 i - 1 - 2 * PeanoNat.Nat.div k 2 - PeanoNat.Nat.modulo k 2 = 2 * (PeanoNat.Nat.pow 2 i - PeanoNat.Nat.div k 2 - 1) + (1 - PeanoNat.Nat.modulo k 2))%nat as -> by Lia.lia.
        rewrite NatUtil.div_add_l' by Lia.lia.
        rewrite (PeanoNat.Nat.div_small (1 - _)) by Lia.lia.
        Lia.lia. }
      rewrite He in Hb1.
      assert (PeanoNat.Nat.modulo (PeanoNat.Nat.pow 2 (S i) - 1 - k) 2 = 1 - Nat.modulo k 2)%nat as He2.
      { rewrite PeanoNat.Nat.pow_succ_r', (PeanoNat.Nat.div_mod_eq k 2) at 1.
        assert (2 * PeanoNat.Nat.pow 2 i - 1 - _ = 2 * (PeanoNat.Nat.pow 2 i - 1 - Nat.div k 2) + (1 - Nat.modulo k 2))%nat as -> by Lia.lia.
        rewrite NatUtil.mod_add_l' by Lia.lia.
        apply PeanoNat.Nat.mod_small. Lia.lia. }
      rewrite He2 in Hb2. clear He He2.
      generalize (IHi ltac:(Lia.lia) _ Hk a' b' Ha1 Hb1).
      generalize (cyclotomic_decompose_mod i ltac:(Lia.lia)). intros X.
      apply nth_error_In in Ha1, Hb1. apply X in Ha1, Hb1.
      destruct Ha1 as [Ha1 _]. destruct Hb1 as [Hb1 _].
      apply (proj1 (N.Div0.mod_divides _ _)) in Ha1, Hb1.
      destruct Ha1 as [ac Ha1]. destruct Hb1 as [bc Hb1].
      assert (km1 - N.of_nat i = N.succ (km1 - N.of_nat (S i)))%N as He by Lia.lia.
      rewrite He, N.pow_succ_r' in Ha1, Hb1. intros [Y Z].
      rewrite N.pow_succ_r', Ha1, Hb1, <- N.mul_add_distr_l in Y.
      rewrite <- N.mul_assoc in Y. apply N.mul_cancel_l in Y; [|Lia.lia].
      rewrite <- N.mul_assoc, N.mul_comm in Ha1, Hb1.
      rewrite <- F.pow_add_r.
      assert ((a + b)%N = (2 ^ N.succ km1)%N) as ->; [|split; [reflexivity|apply zeta_pow_succ_km1]].
      destruct Hkmod as [-> | ->] in Ha2, Hb2.
      + simpl in Ha2, Hb2. inversion Ha2; subst a; clear Ha2.
        inversion Hb2; subst b; clear Hb2.
        rewrite Ha1, Hb1, N.div_mul, N.div_mul by Lia.lia.
        transitivity (2 * 2 ^ km1)%N; [Lia.lia|].
        rewrite N.pow_succ_r'. reflexivity.
      + simpl in Ha2, Hb2. inversion Ha2; subst a; clear Ha2.
        inversion Hb2; subst b; clear Hb2.
        rewrite Ha1, Hb1, N.div_mul, N.div_mul by Lia.lia.
        transitivity (2 * 2 ^ km1)%N; [Lia.lia|].
        rewrite N.pow_succ_r'. reflexivity.
  Qed.

  Lemma cyclotomic_decomposition_degree (i: nat) (Hle: i <= N.to_nat km1):
    forall k p, nth_error (cyclotomic_decomposition n i) k = Some p ->
           degree p = Some (Nat.pow 2 (n - i)).
  Proof.
    intros k p Hp.
    unfold cyclotomic_decomposition in Hp.
    rewrite nth_error_map in Hp; destruct (nth_error (cyclotomic_decompose i) k); simpl in Hp; try congruence.
    inversion Hp; subst p; clear Hp.
    apply Polynomial.posicyclic_degree.
    generalize (NatUtil.pow_nonzero 2 (n - i)%nat ltac:(Lia.lia)). Lia.lia.
  Qed.

  Section NTT.
    Local Notation Pmod_cyclotomic_list := (@Pmod_cyclotomic_list F F.zero F.add F.sub F.mul).
    Local Notation of_list := (@of_list F F.zero P poly_ops).

    Lemma Pmod_cyclotomic_decomposition_list (i: nat) (p: P):
      (S i <= N.to_nat km1) ->
      (measure p <= Nat.pow 2 (n - i))%nat ->
      forall k, (k < Nat.pow 2 i)%nat ->
           Peq (Pmod p (List.nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k)))
               (of_list (firstn (Nat.pow 2 (n - S i)) (Pmod_cyclotomic_list (to_list (Nat.pow 2 (n - i)) p) (Nat.pow 2 (n - S i)) (List.nth_default F.zero (List.map (fun x => F.pow zeta x) (cyclotomic_decompose (S i))) (2 * k))))) /\
           Peq (Pmod p (List.nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k + 1)))
               (of_list (skipn (Nat.pow 2 (n - S i)) (Pmod_cyclotomic_list (to_list (Nat.pow 2 (n - i)) p) (Nat.pow 2 (n - S i)) (List.nth_default F.zero (List.map (fun x => F.pow zeta x) (cyclotomic_decompose (S i))) (2 * k))))).
    Proof.
      intros Hi Hp k Hk.
      generalize (ListUtil.nth_error_length_exists_value (2 * k) (cyclotomic_decompose (S i)) ltac:(rewrite cyclotomic_decompose_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)).
      intros [x0 Hx0].
      generalize (cyclotomic_decomposition_S_chunks2 i Hi). intro HF.
      apply Forall2_nth_error_iff in HF. destruct HF as [HF1 HF2].
      generalize (ListUtil.nth_error_length_exists_value k (cyclotomic_decomposition n i) ltac:(rewrite cyclotomic_decomposition_length; Lia.lia)).
      intros [p1 Hp1].
      generalize (ListUtil.nth_error_length_exists_value k (chunks2 (cyclotomic_decomposition n (S i))) ltac:(rewrite <- HF1, cyclotomic_decomposition_length; Lia.lia)).
      intros [v Hv].
      destruct (HF2 k p1 v Hp1 Hv) as [p2 [p3 [-> [Hcoprime [HEQ X]]]]].
      destruct X as [kp [Hpeq1 [Hpeq2 Hpeq3]]].
      generalize (chunks2_nth_error (cyclotomic_decomposition n (S i)) (2 * k)). intro HX.
      rewrite PeanoNat.Nat.mul_comm, PeanoNat.Nat.div_mul, Hv, PeanoNat.Nat.Div0.mod_mul in HX by Lia.lia.
      simpl in HX. rewrite PeanoNat.Nat.mul_comm in HX.
      rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ HX).
      unfold cyclotomic_decomposition in HX.
      rewrite nth_error_map, Hx0 in HX.
      simpl in HX. inversion HX; subst p2; clear HX.
      generalize (chunks2_nth_error (cyclotomic_decomposition n (S i)) (2 * k + 1)). intro HX.
      rewrite <- (PeanoNat.Nat.div_unique (2 * k + 1) 2 k 1 ltac:(Lia.lia) ltac:(reflexivity)) in HX.
      rewrite <- (PeanoNat.Nat.mod_unique (2 * k + 1) 2 k 1 ltac:(Lia.lia) ltac:(reflexivity)) in HX.
      rewrite Hv in HX. cbn [Option.bind nth_error] in HX.
      rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ HX).
      rewrite (Polynomial.peq_mod_proper (poly_ops:=poly_ops) p p ltac:(reflexivity) _ _ Hpeq3).
      assert (Heq: zeta ^ kp = zeta ^ x0).
      { generalize (Hpeq2 0%nat).
        unfold posicyclic. rewrite sub_definition, sub_definition, const_definition, base_definition, const_definition.
        generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)).
        destruct (Decidable.dec_eq_nat (Nat.pow 2 (n - S i)) 0); [Lia.lia|].
        rewrite Hierarchy.ring_sub_definition, Hierarchy.ring_sub_definition, Hierarchy.left_identity, Hierarchy.left_identity.
        intros _ Z. apply Group.inv_bijective. auto. }
      repeat rewrite (ListUtil.map_nth_default _ _ _ _ 0%N) by (rewrite cyclotomic_decompose_length, PeanoNat.Nat.pow_succ_r'; Lia.lia).
      rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hx0).
      rewrite Heq. assert (Hp': (measure p <= 2 * Nat.pow 2 (n - S i))).
      { rewrite <- PeanoNat.Nat.pow_succ_r'.
        assert (S (n - S i) = n - i)%nat as -> by Lia.lia. assumption. }
      unfold posicyclic, negacyclic.
      assert (Nat.pow 2 (n - i) = 2 * Nat.pow 2 (n - S i))%nat as ->.
      { rewrite <- PeanoNat.Nat.pow_succ_r'. f_equal. Lia.lia. }
      apply (Pmod_cyclotomic_list_correct (poly_ops:=poly_ops) (poly_defs:=poly_defs) p (Nat.pow 2 (n - S i)) (zeta ^ x0) ltac:(generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); Lia.lia) Hp').
    Qed.

    Definition NTT_phi_layer_aux (i: nat) (pl: list P): list P :=
      List.fold_left
        (fun l k =>
           List.app l [(Pmod (List.nth_default Pzero pl k) (List.nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k))); (Pmod (List.nth_default Pzero pl k) (List.nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k + 1)))])
        (seq 0 (Nat.pow 2 i))
        nil.

    Definition fold_left_chunked {A} {B}
      (sz: nat) (f: nat -> A -> list B -> A) (l: list B) (a: A) :=
      List.fold_left (fun acc '(i, chunk) => f i acc chunk) (enumerate 0%nat (chunk sz l)) a.

    Definition NTT_phi_layer_list (i: nat) (l: list F): list F :=
      (fold_left_chunked (Nat.pow 2 (n - i)%nat) (fun k l chunk => List.app l (Pmod_cyclotomic_list chunk (Nat.pow 2 (n - S i)%nat) (List.nth_default F.zero (List.map (fun x => F.pow zeta x) (cyclotomic_decompose (S i))) (2 * k)))) l nil).

    Lemma NTT_phi_layer_list_spec (i: nat) (pl: list P):
      (S i <= N.to_nat km1)%nat ->
      Forall2 (fun p q => Peq p (Pmod p q)) pl (cyclotomic_decomposition n i) ->
      Forall2 Peq (NTT_phi_layer_aux i pl) (List.map of_list (chunk (Nat.pow 2 (n - S i)) (NTT_phi_layer_list i (concat (List.map (fun p => to_list (Nat.pow 2 (n - i)) p) pl))))).
    Proof.
      intros Hi HF. unfold NTT_phi_layer_list, fold_left_chunked.
      assert (Hnz: forall k, Nat.pow 2 k <> 0%nat) by (intros; apply NatUtil.pow_nonzero; Lia.lia).
      assert (HF': Forall (fun l : list F => length l = Nat.pow 2 (n - i)) (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) pl)).
      { apply Forall_map. apply Forall_forall.
        intros. apply to_list_length. }
      rewrite (chunk_concat _ _ ltac:(apply Hnz) HF').
      rewrite (@ListUtil.fold_left_ext _ _ _ (fun acc ic => acc ++ (Pmod_cyclotomic_list (snd ic) (Nat.pow 2 (n - S i)) (nth_default 0 (map (fun x => zeta ^ x) (cyclotomic_decompose (S i))) (2 * (fst ic)))))).
      2: intros x y; destruct y; simpl; reflexivity.
      rewrite <- ListUtil.eq_flat_map_fold_left.
      unfold NTT_phi_layer_aux. rewrite <- ListUtil.eq_flat_map_fold_left.
      unfold enumerate. rewrite map_length, (Forall2_length HF), cyclotomic_decomposition_length.
      apply Forall2_nth_error_iff. split.
      - rewrite map_length, length_chunk by apply Hnz.
        erewrite flat_map_const_length by (simpl; reflexivity).
        erewrite flat_map_constant_length.
        2:{ intros x Hx; unfold Pmod_cyclotomic_list.
            destruct x as [k l]. apply in_combine_r in Hx.
            apply in_map_iff in Hx. destruct Hx as [x [Hx Hx2]].
            simpl. instantiate (1 := Nat.pow 2 (n - i)).
            apply ListUtil.fold_left_invariant.
            - subst l; rewrite to_list_length. reflexivity.
            - intros. repeat rewrite ListUtil.length_set_nth. auto. }
        rewrite combine_length, seq_length, map_length.
        rewrite (Forall2_length HF), cyclotomic_decomposition_length.
        rewrite PeanoNat.Nat.min_id, <- PeanoNat.Nat.pow_add_r.
        assert (i + (n - i) = S i + (n - S i))%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.pow_add_r, Nat.div_up_exact by apply Hnz.
        rewrite PeanoNat.Nat.pow_succ_r'. reflexivity.
      - intros k v1 v2 Hv1 Hv2.
        eapply flat_map_constant_nth_error in Hv1; [|simpl; reflexivity].
        apply nth_error_map_Some in Hv2.
        destruct Hv1 as [k1 [Hk1 Hv1]].
        rewrite ListUtil.nth_error_seq in Hk1.
        rewrite PeanoNat.Nat.add_0_l in Hk1.
        destruct (Compare_dec.lt_dec (PeanoNat.Nat.div k 2) (Nat.pow 2 i)) as [Hklt1|]; [|congruence].
        destruct Hv2 as [chk [Hchk Hv2]].
        set (f := (fun y : nat * list F => Pmod_cyclotomic_list (snd y) (Nat.pow 2 (n - S i)) (nth_default 0 (map (fun x : N => zeta ^ x) (cyclotomic_decompose (S i))) (2 * fst y)))).
        fold f in Hchk.
        assert (Hklt: (k < Nat.div_up (length (flat_map f (combine (seq 0 (Nat.pow 2 i)) (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) pl)))) (Nat.pow 2 (n - S i)))).
        { erewrite flat_map_constant_length.
          2:{ unfold f, Pmod_cyclotomic_list.
              instantiate (1 := Nat.pow 2 (n - i)). intros x Hx.
              apply ListUtil.fold_left_invariant.
              - destruct x. apply in_combine_r in Hx.
                apply in_map_iff in Hx. destruct Hx as [x [Hx _]].
                subst l. simpl. rewrite to_list_length. reflexivity.
              - intros. repeat rewrite ListUtil.length_set_nth. auto. }
          rewrite combine_length, seq_length, map_length, (Forall2_length HF), cyclotomic_decomposition_length.
          rewrite PeanoNat.Nat.min_id, <- PeanoNat.Nat.pow_add_r.
          assert (i + (n - i) = S i + (n - S i))%nat as -> by Lia.lia.
          rewrite PeanoNat.Nat.pow_add_r, Nat.div_up_exact by apply Hnz.
          rewrite PeanoNat.Nat.pow_succ_r'.
          rewrite (PeanoNat.Nat.Div0.div_mod k 2%nat).
          generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)). Lia.lia. }
        generalize (nth_error_chunk (Nat.pow 2 (n - S i)) ltac:(apply Hnz) (flat_map f (combine (seq 0 (Nat.pow 2 i )) (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) pl))) k Hklt).
        rewrite Hchk. intro X; inversion X; subst chk; clear X.
        rewrite <- Hv2.
        assert (v1 = Pmod (nth_default Pzero pl k1) (nth_default Pzero (cyclotomic_decomposition n (S i)) k)) as ->.
        { assert (PeanoNat.Nat.modulo k 2 = 0 \/ PeanoNat.Nat.modulo k 2 = 1)%nat as Hkmodeq by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
          destruct Hkmodeq as [Hkmodeq|Hkmodeq]; rewrite Hkmodeq in Hv1; cbn [nth_error] in Hv1; inversion Hv1; subst v1; repeat f_equal; rewrite (PeanoNat.Nat.Div0.div_mod k 2%nat); rewrite Hkmodeq; assert (k1 = PeanoNat.Nat.div k 2) as -> by congruence; Lia.lia. }
        assert (Hm1: (measure (nth_default Pzero pl k1) <= Nat.pow 2 (n - i))%nat).
        { assert (k1 = PeanoNat.Nat.div k 2) by congruence. subst k1.
          generalize (ListUtil.nth_error_length_exists_value (PeanoNat.Nat.div k 2) pl ltac:(rewrite (Forall2_length HF), cyclotomic_decomposition_length; Lia.lia)).
          intros [p1 Hp1].
          rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hp1).
          generalize (ListUtil.nth_error_length_exists_value (PeanoNat.Nat.div k 2) (cyclotomic_decomposition n i) ltac:(rewrite cyclotomic_decomposition_length; Lia.lia)).
          intros [q1 Hq1].
          apply Forall2_nth_error_iff in HF.
          destruct HF as [_ HF]. unfold measure.
          rewrite (Polynomial.peq_proper_degree (poly_defs:=poly_defs) _ _ (HF _ _ _ Hp1 Hq1)).
          assert (Hqnz: not (Peq q1 Pzero)).
          { intro Heq. apply cyclotomic_decomposition_degree in Hq1; try Lia.lia.
            rewrite (Polynomial.peq_proper_degree (poly_defs:=poly_defs) _ _ Heq) in Hq1.
            rewrite Polynomial.degree_zero in Hq1. congruence. }
          generalize (Polynomial.Pmod_degree_lt (poly_defs:=poly_defs) p1 q1 Hqnz).
          rewrite (cyclotomic_decomposition_degree i ltac:(Lia.lia) _ _ Hq1).
          unfold degree_lt. simpl. Lia.lia. }
        generalize (Pmod_cyclotomic_decomposition_list i (nth_default Pzero pl k1) Hi Hm1 k1 ltac:(assert (k1 = PeanoNat.Nat.div k 2) as -> by congruence; Lia.lia)).
        intros [HA HB].
        assert (Hkeq: (k = 2 * k1 + PeanoNat.Nat.modulo k 2)%nat).
        { rewrite (PeanoNat.Nat.Div0.div_mod k 2) at 1.
          assert (k1 = PeanoNat.Nat.div k 2) as <- by congruence. reflexivity. }
        assert (k * Nat.pow 2 (n - S i) = k1 * Nat.pow 2 (n - i) + PeanoNat.Nat.modulo k 2 * Nat.pow 2 (n - S i))%nat as ->.
        { rewrite Hkeq at 1. assert (n - i = S (n - S i))%nat as -> by Lia.lia.
          rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia. }
        rewrite <- ListUtil.skipn_skipn.
        rewrite skipn_flat_map_constant_length.
        2:{ unfold f. intros x Hx. destruct x as [n1 l1].
            apply in_combine_r in Hx. apply in_map_iff in Hx.
            destruct Hx as [x [Hl1 Hx]]. subst l1.
            unfold Pmod_cyclotomic_list; simpl.
            apply ListUtil.fold_left_invariant.
            - rewrite to_list_length; reflexivity.
            - intros. repeat (rewrite ListUtil.length_set_nth); auto. }
        rewrite ListUtil.skipn_combine, ListUtil.skipn_seq, skipn_map.
        rewrite PeanoNat.Nat.add_0_r.
        rewrite ListUtil.firstn_skipn_add.
        assert (PeanoNat.Nat.modulo k 2 = 0 \/ PeanoNat.Nat.modulo k 2 = 1)%nat as Hkmodeq by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
        rewrite <- (ListUtil.firstn_firstn (Nat.pow 2 (n - i))).
        2:{ assert (n - i = S (n - S i))%nat as -> by Lia.lia.
            rewrite PeanoNat.Nat.pow_succ_r'.
            destruct Hkmodeq as [-> | ->]; Lia.lia. }
        rewrite <- (ListUtil.map_nth_default_seq Pzero (Nat.pow 2 i) pl ltac:(rewrite (Forall2_length HF), cyclotomic_decomposition_length; Lia.lia)) at 2.
        rewrite skipn_map, ListUtil.skipn_seq, PeanoNat.Nat.add_0_r.
        rewrite map_map, ListUtil.combine_map_r.
        assert (Nat.pow 2 i - k1 = S (Nat.pred (Nat.pow 2 i - k1)))%nat as ->.
        { assert (k1 = PeanoNat.Nat.div k 2)%nat as -> by congruence. Lia.lia. }
        cbn [seq combine map flat_map].
        rewrite firstn_app_l.
        2:{ unfold f; simpl. unfold Pmod_cyclotomic_list; simpl.
            apply ListUtil.fold_left_invariant.
            - rewrite to_list_length. reflexivity.
            - intros. repeat (rewrite ListUtil.length_set_nth). auto. }
        unfold f. cbn [fst snd]. rewrite Hkeq at 1.
        destruct Hkmodeq as [-> | ->].
        { rewrite PeanoNat.Nat.add_0_r, HA, PeanoNat.Nat.mul_0_l, PeanoNat.Nat.add_0_l.
          reflexivity. }
        { rewrite HB, PeanoNat.Nat.mul_1_l.
          rewrite firstn_all2; [reflexivity|].
          assert (_ + _ = 2 * Nat.pow 2 (n - S i))%nat as -> by Lia.lia.
          rewrite <- PeanoNat.Nat.pow_succ_r'.
          assert (S (n - S i) = n - i)%nat as -> by Lia.lia.
          apply PeanoNat.Nat.eq_le_incl.
          unfold Pmod_cyclotomic_list. apply ListUtil.fold_left_invariant.
          - apply to_list_length.
          - intros; repeat (rewrite ListUtil.length_set_nth). auto. }
    Qed.

    Program Definition NTT_phi_layer (i: nat) (pl: Pquotl (cyclotomic_decomposition n i)): Pquotl (cyclotomic_decomposition n (S i)) :=
      NTT_phi_layer_aux i (proj1_sig pl).
    Next Obligation.
      unfold NTT_phi_layer_aux.
      rewrite <- ListUtil.eq_flat_map_fold_left.
      apply Forall2_nth_error_iff.
      erewrite flat_map_constant_length; [|simpl; reflexivity].
      rewrite cyclotomic_decomposition_length, seq_length; split; [simpl; Lia.lia|].
      intros. eapply flat_map_constant_nth_error in H; [|simpl; reflexivity].
      destruct H as [y [HA HB]].
      rewrite ListUtil.nth_error_seq in HA. destruct (Compare_dec.lt_dec (PeanoNat.Nat.div k 2) (Nat.pow 2 i)); try congruence.
      set (k' := PeanoNat.Nat.div k 2). fold k' in HA.
      rewrite PeanoNat.Nat.add_0_l in HA. inversion HA; subst y; clear HA.
      set (r := PeanoNat.Nat.modulo k 2). fold r in HB.
      assert (r = 0 \/ r = 1)%nat as HEQ by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); unfold r; Lia.lia).
      assert (k = 2 * k' + r)%nat as Hk by (apply PeanoNat.Nat.div_mod_eq).
      rewrite Hk in H1. eapply (ListUtil.nth_error_value_eq_nth_default) in H1.
      instantiate (1:=Pzero) in H1.
      rewrite <- H1. simpl in HB.
      assert ((k' + (k' + 0) + 1) = 2 * k' + 1)%nat as Hx by Lia.lia; rewrite Hx in HB; clear Hx.
      assert (k' + (k' + 0) = 2 * k' + 0)%nat as Hx by Lia.lia; rewrite Hx in HB; clear Hx.
      destruct HEQ as [-> | ->]; simpl in HB; inversion HB; subst v1; clear HB; rewrite Polynomial.Pmod_mod_eq; reflexivity.
    Qed.

    Lemma NTT_phi_layer_list_length:
      forall i l, length (NTT_phi_layer_list i l) = length l.
    Proof.
      intros i l. unfold NTT_phi_layer_list.
      unfold fold_left_chunked.
      set (f := (fun (acc : list F) '(i0, chunk) => acc ++ Pmod_cyclotomic_list chunk (Nat.pow 2 (n - S i)) (nth_default 0 (map (fun x : N => zeta ^ x) (cyclotomic_decompose (S i))) (2 * i0)))).
      assert (forall x acc, length (fold_left f x acc) = length acc + list_sum (map (fun y => length (snd y)) x))%nat as IH.
      { induction x; [simpl; Lia.lia|].
        simpl. intros. rewrite IHx. destruct a; simpl.
        rewrite app_length. assert (length (Pmod_cyclotomic_list _ _ _) = length l0) as ->; [|Lia.lia].
        unfold Pmod_cyclotomic_list. apply ListUtil.fold_left_invariant; [reflexivity|].
        intros. repeat (rewrite ListUtil.length_set_nth). auto. }
      rewrite IH. unfold enumerate.
      rewrite <- (map_map snd), ListUtil.map_snd_combine.
      rewrite seq_length, firstn_all, <- concat_length, concat_chunk.
      simpl; Lia.lia.
    Qed.

    Program Fixpoint NTT_phi (i: nat) (pl: Pquotl (cyclotomic_decomposition n 0%nat)): Pquotl (cyclotomic_decomposition n i) :=
      match i with
      | O => pl
      | S i => NTT_phi_layer i (NTT_phi i pl)
      end.

    Lemma NTT_phi_proj1_sig (i: nat) (pl: Pquotl (cyclotomic_decomposition n 0%nat)):
      proj1_sig (NTT_phi i pl) =
        nat_rect (fun _ => list P) (proj1_sig pl) NTT_phi_layer_aux i.
    Proof.
      induction i; [reflexivity|].
      simpl. rewrite IHi. reflexivity.
    Qed.

    Definition NTT_phi_list (i: nat) (l: list F) :=
      nat_rect (fun _ => list F) l NTT_phi_layer_list i.

    Lemma NTT_phi_list_length:
      forall i l, length (NTT_phi_list i l) = length l.
    Proof.
      unfold NTT_phi_list. induction i; [reflexivity|].
      intros. simpl. rewrite NTT_phi_layer_list_length, IHi.
      reflexivity.
    Qed.

    Global Instance peq_proper_to_list {m:nat}: Proper (Peq ==> Logic.eq) (to_list m).
    Proof.
      intros x y Heq.
      unfold to_list. apply nth_error_ext.
      intro k. rewrite nth_error_map, nth_error_map, ListUtil.nth_error_seq, PeanoNat.Nat.add_0_l.
      destruct (Compare_dec.lt_dec k m); [simpl|reflexivity].
      rewrite Heq. reflexivity.
    Qed.

    Lemma to_list_of_list (m: nat) (l: list F) (Hm: length l = m :> nat):
      to_list m (of_list l) = l :> _.
    Proof.
      apply nth_error_ext; intros k.
      unfold to_list, of_list. rewrite nth_error_map.
      rewrite ListUtil.nth_error_seq, PeanoNat.Nat.add_0_l.
      destruct (Compare_dec.lt_dec k m) as [Hlt|Hnlt].
      - rewrite <- Hm in Hlt.
        destruct (ListUtil.nth_error_length_exists_value _ _ Hlt) as [x Hx].
        rewrite Hx. simpl. f_equal. rewrite Pdecompose_coeff.
        destruct (Decidable.dec_lt_nat k (length l)); [|Lia.lia].
        apply ListUtil.nth_error_value_eq_nth_default; auto.
      - rewrite <- Hm in Hnlt.
        rewrite ListUtil.nth_error_length_error by Lia.lia. reflexivity.
    Qed.

    Lemma NTT_phi_list_spec (i: nat) (pl: Pquotl (cyclotomic_decomposition n 0%nat)):
      (i <= N.to_nat km1) ->
      Forall2 Peq
        (proj1_sig (NTT_phi i pl))
        (map of_list (chunk (Nat.pow 2 (n - i)) (NTT_phi_list i (concat (map (fun p : P => to_list (Nat.pow 2 n) p) (proj1_sig pl)))))).
    Proof.
      induction i; intro Hi.
      - rewrite PeanoNat.Nat.sub_0_r.
        destruct pl as [pl Hpl].
        generalize (Forall2_length Hpl); rewrite cyclotomic_decomposition_length.
        rewrite PeanoNat.Nat.pow_0_r. intro Hlen.
        destruct pl; [simpl in Hlen; congruence|].
        destruct pl; [|simpl in Hlen; congruence].
        simpl. rewrite app_nil_r.
        rewrite chunk_small.
        2: rewrite to_list_length; generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)); Lia.lia.
        simpl. repeat constructor.
        symmetry. apply Polynomial.of_list_to_list.
        unfold cyclotomic_decomposition in Hpl.
        simpl in Hpl. inversion Hpl.
        rewrite (Polynomial.peq_proper_degree (poly_defs:=poly_defs) _ _ H2).
        rewrite PeanoNat.Nat.sub_0_r.
        assert (Hnz: not (Peq (posicyclic (Nat.pow 2 n) (zeta ^ 2 ^km1)) Pzero)).
        { intro Heq. generalize (Heq (Nat.pow 2 n)).
          rewrite zero_definition. unfold posicyclic.
          rewrite sub_definition, base_definition, const_definition.
          destruct (Decidable.dec_eq_nat _ _); [|congruence].
          generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)).
          intro. destruct (Nat.pow 2 n); [congruence|].
          rewrite Hierarchy.ring_sub_definition, Group.inv_id, Hierarchy.right_identity.
          apply Hierarchy.one_neq_zero. }
        generalize (Polynomial.Pmod_degree_lt (poly_defs:=poly_defs) p (posicyclic (Nat.pow 2 n) (zeta ^ 2 ^km1)) Hnz).
        rewrite (Polynomial.posicyclic_degree (poly_defs:=poly_defs)) by (generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)); Lia.lia).
        auto.
      - specialize (IHi ltac:(Lia.lia)).
        rewrite NTT_phi_proj1_sig. simpl. rewrite <- NTT_phi_proj1_sig.
        unfold NTT_phi_list. simpl.
        assert (nat_rect _ _ _ i = NTT_phi_list i (concat (map (fun p : P => to_list (Nat.pow 2 n) p) (proj1_sig pl)))) as -> by reflexivity.
        generalize (NTT_phi_layer_list_spec i (proj1_sig (NTT_phi i pl)) Hi (proj2_sig (NTT_phi i pl))).
        intro X. etransitivity; eauto.
        assert (concat (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) (proj1_sig (NTT_phi i pl))) = NTT_phi_list i (concat (map (fun p : P => to_list (Nat.pow 2 n) p) (proj1_sig pl)))) as ->; [|reflexivity].
        assert (map _ (proj1_sig (NTT_phi i pl)) = map (fun p : P => to_list (Nat.pow 2 (n - i)) p) (map of_list (chunk (Nat.pow 2 (n - i)) (NTT_phi_list i (concat (map (fun p : P => to_list (Nat.pow 2 n) p) (proj1_sig pl))))))) as ->.
        { apply nth_error_ext; intros j.
          rewrite nth_error_map, nth_error_map.
          apply Forall2_nth_error_iff in IHi.
          destruct IHi as [Hl Hv].
          destruct (Compare_dec.lt_dec j (length (proj1_sig (NTT_phi i pl)))) as [Hlt|Hnlt].
          - destruct (ListUtil.nth_error_length_exists_value _ _ Hlt) as [vv Hvv].
            rewrite Hl in Hlt. destruct (ListUtil.nth_error_length_exists_value _ _ Hlt) as [vv2 Hvv2].
            rewrite Hvv, Hvv2. simpl.
            f_equal. generalize (Hv _ _ _ Hvv Hvv2). intro D.
            rewrite D. reflexivity.
          - rewrite ListUtil.nth_error_length_error by Lia.lia.
            rewrite Hl in Hnlt.
            rewrite ListUtil.nth_error_length_error by Lia.lia.
            reflexivity. }
        rewrite map_map, map_ext_id, concat_chunk; [reflexivity|].
        intros x Hx. apply to_list_of_list.
        eapply (@Forall_In _ (fun z => length z = Nat.pow 2 (n - i)) _ _ x Hx).
        Unshelve.
        eapply Forall_chunk_length_eq. instantiate (1 := Nat.pow 2 i).
        rewrite <- PeanoNat.Nat.pow_add_r.
        assert (n - i + i = n)%nat as -> by Lia.lia.
        rewrite NTT_phi_list_length.
        rewrite (length_concat_same_length (Nat.pow 2 n)).
        { rewrite map_length. destruct pl as [pl Hpl]. simpl.
          rewrite (Forall2_length Hpl), cyclotomic_decomposition_length.
          rewrite PeanoNat.Nat.pow_0_r. Lia.lia. }
        { apply Forall_forall. intros o Ho.
          apply in_map_iff in Ho. destruct Ho as [b [Hb1 Hb2]].
          subst o. rewrite to_list_length. reflexivity. }
    Qed.

    Lemma NTT_phi_0 pl:
      NTT_phi 0%nat pl = pl.
    Proof. reflexivity. Qed.

    Lemma NTT_phi_S i pl:
      NTT_phi (S i) pl = NTT_phi_layer i (NTT_phi i pl).
    Proof. reflexivity. Qed.

    Local Notation NTT_psi2 := (@Polynomial.NTT_base_psi_unpacked F F.one F.add P _ F.inv).

    Local Notation NTT_psi2_list := (@Polynomial.NTT_base_psi_unpacked_list F F.zero F.add F.sub F.mul).

    Definition NTT_psi_layer_aux (i: nat) (pl: list P): list P :=
      List.fold_left
        (fun l k => List.app l [NTT_psi2 (Nat.pow 2 (n - S i)) (F.pow zeta (List.nth_default 0%N (cyclotomic_decompose (S i)) (2 * k))) (List.nth_default Pzero pl (2 * k)%nat) (List.nth_default Pzero pl (2 * k + 1)%nat)])
        (seq 0 (Nat.pow 2 i))
        nil.

    Local Instance NTT_psi_layer_aux_proper_peq {i:nat}:
      Proper (Forall2 Peq ==> Forall2 Peq) (NTT_psi_layer_aux i).
    Proof.
      intros pl1 pl2 Heq. unfold NTT_psi_layer_aux.
      repeat rewrite <- ListUtil.eq_flat_map_fold_left.
      repeat rewrite ListUtil.flat_map_singleton.
      apply Forall2_nth_error_iff.
      split; [repeat rewrite map_length; reflexivity|].
      intros k v1 v2 Hv1 Hv2.
      rewrite nth_error_map in Hv1, Hv2.
      rewrite ListUtil.nth_error_seq, PeanoNat.Nat.add_0_l in Hv1, Hv2.
      destruct (Compare_dec.lt_dec k (Nat.pow 2 i)); cbn [option_map] in Hv1, Hv2; [|congruence].
      set (a := zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * k)).
      fold a in Hv1, Hv2.
      assert (v1 = NTT_psi2 (Nat.pow 2 (n - S i)) a (nth_default Pzero pl1 (2 * k)) (nth_default Pzero pl1 (2 * k + 1))) as -> by congruence.
      assert (v2 = NTT_psi2 (Nat.pow 2 (n - S i)) a (nth_default Pzero pl2 (2 * k)) (nth_default Pzero pl2 (2 * k + 1))) as -> by congruence.
      clear Hv1 Hv2.
      apply peq_NTT_base_psi_unpacked_proper.
      - destruct (Compare_dec.lt_dec (2 * k) (length pl1)) as [Hlt|Hnlt].
        + apply ListUtil.Forall2_forall_iff; auto.
          apply (Forall2_length Heq).
        + repeat rewrite ListUtil.nth_default_out_of_bounds; try Lia.lia; try reflexivity.
          rewrite <- (Forall2_length Heq); Lia.lia.
      - destruct (Compare_dec.lt_dec (2 * k + 1) (length pl1)) as [Hlt|Hnlt].
        + apply ListUtil.Forall2_forall_iff; auto.
          apply (Forall2_length Heq).
        + repeat rewrite ListUtil.nth_default_out_of_bounds; try Lia.lia; try reflexivity.
          rewrite <- (Forall2_length Heq); Lia.lia.
    Qed.

    Lemma NTT_psi_layer_aux_const_mul (i: nat) (c:F) (pl: list P):
      Forall2 Peq
        (NTT_psi_layer_aux i (map (fun p => Pmul (Pconst c) p) pl))
        (map (fun p => Pmul (Pconst c) p) (NTT_psi_layer_aux i pl)).
    Proof.
      unfold NTT_psi_layer_aux. do 2 rewrite <- ListUtil.eq_flat_map_fold_left.
      do 2 rewrite ListUtil.flat_map_singleton.
      rewrite map_map. apply Forall2_nth_error_iff.
      split; [repeat rewrite map_length; reflexivity|].
      intros k v1 v2 Hv1 Hv2.
      rewrite nth_error_map in Hv1, Hv2.
      destruct (nth_error (seq 0 (Nat.pow 2 i))) as [m|] eqn:Hm; [|simpl in Hv1; congruence].
      cbn [option_map] in Hv1, Hv2.
      inversion Hv1; inversion Hv2; subst v1; subst v2; clear Hv1; clear Hv2.
      set (a := zeta ^ _).
      destruct (Compare_dec.lt_dec (m + (m + 0) + 1) (length pl)) as [Hlt|Hnlt].
      - assert (m + (m + 0) < length pl) as Hlt' by Lia.lia.
        rewrite (@ListUtil.map_nth_default _ _ _ _ Pzero _ _ Hlt).
        rewrite (@ListUtil.map_nth_default _ _ _ _ Pzero _ _ Hlt').
        unfold NTT_psi2. repeat rewrite <- (Hierarchy.left_distributive (Pconst c)).
        repeat rewrite (Hierarchy.associative _ (Pconst c)).
        do 2 rewrite (Hierarchy.commutative _ (Pconst c)).
        do 2 rewrite <- (Hierarchy.associative (Pconst c)).
        rewrite <- (Hierarchy.left_distributive (Pconst c)).
        reflexivity.
      - rewrite (ListUtil.nth_default_out_of_bounds (m + (m + 0) + 1) (map _ _)) by (rewrite map_length; Lia.lia).
        rewrite (ListUtil.nth_default_out_of_bounds (m + (m + 0) + 1) pl) by (Lia.lia).
        destruct (Compare_dec.lt_dec (m + (m + 0)) (length pl)) as [Hlt|Hnlt'].
        + rewrite (@ListUtil.map_nth_default _ _ _ _ Pzero _ _ Hlt).
          unfold NTT_psi2. do 2 rewrite Hierarchy.ring_sub_definition.
          rewrite Group.inv_id.
          repeat rewrite Hierarchy.right_identity.
          repeat rewrite (Hierarchy.associative _ (Pconst c)).
          do 2 rewrite (Hierarchy.commutative _ (Pconst c)).
          do 2 rewrite <- (Hierarchy.associative (Pconst c)).
          rewrite <- (Hierarchy.left_distributive (Pconst c)).
          reflexivity.
        + rewrite (ListUtil.nth_default_out_of_bounds (m + (m + 0)) (map _ _)) by (rewrite map_length; Lia.lia).
          rewrite (ListUtil.nth_default_out_of_bounds (m + (m + 0)) pl) by (Lia.lia).
          unfold NTT_psi2. rewrite Hierarchy.left_identity.
          rewrite Ring.mul_0_r. rewrite Hierarchy.ring_sub_definition.
          rewrite Group.inv_id. rewrite Hierarchy.left_identity.
          rewrite Hierarchy.left_identity, Ring.mul_0_r.
          rewrite Ring.mul_0_r. reflexivity.
    Qed.

    Definition NTT_psi_layer_list (i: nat) (l: list F): list F :=
      fold_left_chunked (Nat.pow 2 (n - i))
        (fun k l chunk =>
           l ++ NTT_psi2_list chunk (Nat.pow 2 (n - S i)) (F.inv (F.pow zeta (List.nth_default 0%N (cyclotomic_decompose (S i)) (2 * k)))))
        l [].

    Lemma NTT_psi_layer_list_length:
      forall i l, length (NTT_psi_layer_list i l) = length l.
    Proof.
      intros i l. unfold NTT_psi_layer_list.
      unfold fold_left_chunked.
      set (f := (fun (acc : list F) '(i0, chunk) => acc ++ _)).
      assert (forall x acc, length (fold_left f x acc) = length acc + list_sum (map (fun y => length (snd y)) x))%nat as IH.
      { induction x; [simpl; Lia.lia|].
        simpl. intros. rewrite IHx. destruct a; unfold f; cbn [fst snd].
        rewrite app_length. assert (length (NTT_psi2_list _ _ _) = length l0) as ->; [|Lia.lia].
        unfold NTT_psi2_list. apply ListUtil.fold_left_invariant; [reflexivity|].
        intros. repeat (rewrite ListUtil.length_set_nth). auto. }
      rewrite IH. unfold enumerate.
      rewrite <- (map_map snd), ListUtil.map_snd_combine.
      rewrite seq_length, firstn_all, <- concat_length, concat_chunk.
      simpl; Lia.lia.
    Qed.

    Lemma NTT_psi_layer_list_map_mul c i l:
      NTT_psi_layer_list i (map (F.mul c) l) = map (F.mul c) (NTT_psi_layer_list i l).
    Proof.
      unfold NTT_psi_layer_list, fold_left_chunked.
      rewrite chunk_map by (apply NatUtil.pow_nonzero; Lia.lia).
      unfold enumerate. rewrite ListUtil.combine_map_r.
      rewrite ListUtil.fold_left_map.
      repeat rewrite map_length.
      rewrite <- ListUtil.eq_flat_map_fold_left.
      rewrite (ListUtil.fold_left_ext _ _ _ (fun (acc : list F) z => acc ++ NTT_psi2_list (snd z) (Nat.pow 2 (n - S i)) (F.inv (zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * (fst z)))))) by (intros x y; destruct y; reflexivity).
      rewrite <- ListUtil.eq_flat_map_fold_left.
      rewrite ListUtil.map_flat_map.
      apply flat_map_ext. destruct a as [k chunk]. cbn [fst snd].
      unfold NTT_psi2_list.
      set (f := fun (l0 : list F) (i0 : nat) => _).
      revert chunk. induction (seq 0 (Nat.pow 2 (n - S i))).
      - reflexivity.
      - cbn [fold_left]. intros.
        rewrite <- IHl0. f_equal.
        unfold f.
        apply nth_error_ext. intro j.
        rewrite nth_error_map.
        repeat rewrite ListUtil.nth_set_nth.
        repeat rewrite ListUtil.set_nth_nth_default_full.
        repeat rewrite ListUtil.length_set_nth.
        repeat rewrite map_length.
        destruct (PeanoNat.Nat.eq_dec j (a + Nat.pow 2 (n - S i))).
        { destruct (Compare_dec.lt_dec j (length chunk)); [|reflexivity].
          cbn [option_map]. destruct (Compare_dec.lt_dec (a + Nat.pow 2 (n - S i)) (length chunk)); [|repeat rewrite Ring.mul_0_r; reflexivity].
          rewrite NatUtil.eq_nat_dec_refl.
          rewrite Hierarchy.associative, (Hierarchy.commutative c (F.inv _)).
          rewrite <- Hierarchy.associative.
          rewrite (Hierarchy.left_distributive c).
          repeat rewrite <- (ListUtil.map_nth_default_always (F.mul c)).
          rewrite Ring.mul_0_r. reflexivity. }
        destruct (PeanoNat.Nat.eq_dec j a).
        { destruct (Compare_dec.lt_dec j (length chunk)); [|reflexivity].
          cbn [option_map].
          rewrite (Hierarchy.left_distributive c).
          repeat rewrite <- (ListUtil.map_nth_default_always (F.mul c)).
          rewrite Ring.mul_0_r. reflexivity. }
        apply nth_error_map.
    Qed.

    Lemma NTT_psi_layer_list_spec (i: nat) (pl: list P):
      (S i <= N.to_nat km1)%nat ->
      Forall2 (fun p q => Peq p (Pmod p q)) pl (cyclotomic_decomposition n (S i)) ->
      Forall2 Peq (List.map (fun x => Pmul (Pconst (F.of_Z _ 2)) x) (NTT_psi_layer_aux i pl)) (List.map of_list (chunk (Nat.pow 2 (n - i)) (NTT_psi_layer_list i (concat (List.map (fun p => to_list (Nat.pow 2 (n - S i)) p) pl))))).
    Proof.
      intros Hi HF.
      assert (Hnz: forall k, Nat.pow 2 k <> 0%nat) by (intros; apply NatUtil.pow_nonzero; Lia.lia).
      assert (HF': Forall (fun l : list F => length l = Nat.pow 2 (n - S i)) (map (fun p : P => to_list (Nat.pow 2 (n - S i)) p) pl)).
      { apply Forall_map. apply Forall_forall.
        intros. apply to_list_length. }
      unfold NTT_psi_layer_aux. rewrite <- ListUtil.eq_flat_map_fold_left.
      apply Forall2_nth_error_iff. split.
      - rewrite map_length.
        erewrite flat_map_const_length; [|simpl; reflexivity].
        rewrite seq_length, PeanoNat.Nat.mul_1_l.
        rewrite map_length, length_chunk; [|apply Hnz].
        rewrite NTT_psi_layer_list_length.
        erewrite length_concat_same_length; eauto.
        rewrite map_length.
        rewrite (Forall2_length HF), cyclotomic_decomposition_length.
        rewrite <- PeanoNat.Nat.pow_add_r.
        assert (S i + (n - S i) = i + (n - i))%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.pow_add_r, Nat.div_up_exact; [reflexivity|].
        apply Hnz.
      - intros k v1 v2 Hv1 Hv2.
        rewrite nth_error_map in Hv1.
        destruct (nth_error (flat_map (fun y : nat => [NTT_psi2 (Nat.pow 2 (n - S i)) (zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * y)) (nth_default Pzero pl (2 * y)) (nth_default Pzero pl (2 * y + 1))]) (seq 0 (Nat.pow 2 i))) k) as [v1'|] eqn:Hv1'; [|simpl in Hv1; congruence].
        apply (flat_map_constant_nth_error 1%nat) in Hv1'; [|reflexivity].
        rewrite PeanoNat.Nat.div_1_r in Hv1'.
        destruct Hv1' as [k1 [Hk1 Hv1']].
        rewrite ListUtil.nth_error_seq, PeanoNat.Nat.add_0_l in Hk1.
        destruct (Compare_dec.lt_dec k (Nat.pow 2 i)) as [Hklt|]; [|congruence].
        inversion Hk1; subst k1; clear Hk1.
        rewrite PeanoNat.Nat.mod_1_r in Hv1'. cbn [nth_error] in Hv1'.
        assert (v1 = Pmul (Pconst (F.of_Z q (Zpos 2))) (NTT_psi2 (Nat.pow 2 (n - S i)) (zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * k)) (nth_default Pzero pl (2 * k)) (nth_default Pzero pl (2 * k + 1)))) by (rewrite <- Hv1' in Hv1; cbn [option_map] in Hv1; congruence); subst v1; clear Hv1 Hv1'.
        rewrite nth_error_map in Hv2.
        rewrite nth_error_chunk in Hv2.
        2: apply Hnz.
        2:{ rewrite NTT_psi_layer_list_length, (length_concat_same_length (Nat.pow 2 (n - S i))), map_length.
            2: apply Forall_map, Forall_forall; intros; rewrite to_list_length; reflexivity.
            rewrite (Forall2_length HF), cyclotomic_decomposition_length.
            rewrite <- PeanoNat.Nat.pow_add_r.
            assert (S i + (n - S i) = i + (n - i))%nat as -> by Lia.lia.
            rewrite PeanoNat.Nat.pow_add_r, Nat.div_up_exact; auto. }
        simpl in Hv2. unfold NTT_psi_layer_list in Hv2.
        unfold fold_left_chunked in Hv2.
        assert (Hlen: length (concat (map (fun p : P => to_list (Nat.pow 2 (n - S i)) p) pl)) = (Nat.pow 2 (n - i) * Nat.pow 2 i)%nat).
        { rewrite (length_concat_same_length (Nat.pow 2 (n - S i))).
          - rewrite map_length, (Forall2_length HF), cyclotomic_decomposition_length.
            do 2 rewrite <- PeanoNat.Nat.pow_add_r.
            f_equal; Lia.lia.
          - apply Forall_map, Forall_forall.
            intros; rewrite to_list_length; reflexivity. }
        rewrite (ListUtil.fold_left_ext _ _ _ (fun acc ic => acc ++ NTT_psi2_list (snd ic) (Nat.pow 2 (n - S i)) (F.inv (zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * fst ic))))) in Hv2.
        2: intros x y; destruct y; reflexivity.
        rewrite <- ListUtil.eq_flat_map_fold_left in Hv2.
        rewrite skipn_flat_map_constant_length in Hv2.
        2:{ intros x Hx. destruct x as [kx lx].
            unfold enumerate in Hx. apply in_combine_r in Hx.
            generalize (Forall_chunk_length_eq (Nat.pow 2 (n - i)) _ (concat (map (fun p : P => to_list (Nat.pow 2 (n - S i)) p) pl)) Hlen).
            intro HFF.
            apply (Forall_In HFF) in Hx.
            rewrite <- Hx. cbn [fst snd].
            unfold NTT_psi2_list. apply ListUtil.fold_left_invariant; auto.
            intros. repeat rewrite ListUtil.length_set_nth; auto. }
        unfold enumerate in Hv2. rewrite ListUtil.skipn_combine, skipn_seq_step in Hv2.
        rewrite PeanoNat.Nat.add_0_l in Hv2.
        rewrite length_chunk, Hlen in Hv2; auto.
        rewrite (PeanoNat.Nat.mul_comm (Nat.pow 2 (n - i)) (Nat.pow 2 i)) in Hv2.
        rewrite Nat.div_up_exact in Hv2; auto.
        rewrite skipn_chunk in Hv2; auto.
        replace (n - i)%nat with (S (n - S i))%nat in Hv2 at 3 by Lia.lia.
        rewrite PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.mul_assoc, (PeanoNat.Nat.mul_comm k 2) in Hv2.
        rewrite skipn_concat_same_length in Hv2; [|apply Forall_map, Forall_forall; intros; apply to_list_length].
        rewrite skipn_map in Hv2.
        assert (XX: exists p1 p2 pl', skipn (2 * k) pl = p1::p2::pl').
        { generalize (skipn_length (2 * k) pl).
          rewrite (Forall2_length HF), cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'. intro X.
          assert (length (skipn (2 * k) pl) >= 2)%nat as Y by Lia.lia.
          destruct (skipn (2 * k) pl); [simpl in Y; Lia.lia|].
          destruct l; [simpl in Y; Lia.lia|].
          do 3 eexists; reflexivity. }
        destruct XX as [p1 [p2 [pl' XX]]].
        rewrite XX in Hv2. cbn [map concat] in Hv2.
        rewrite app_assoc, chunk_app_chunk in Hv2; auto.
        2: rewrite app_length, to_list_length, to_list_length.
        2: assert (n - i = S (n - S i))%nat as -> by Lia.lia; rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia.
        replace (Nat.pow 2 i - k)%nat with (S (Nat.pred (Nat.pow 2 i - k)))%nat in Hv2 by Lia.lia.
        rewrite <- cons_seq in Hv2. cbn [combine flat_map] in Hv2.
        rewrite firstn_app_l in Hv2.
        2:{ unfold NTT_psi2_list; simpl; apply ListUtil.fold_left_invariant.
            - rewrite app_length, to_list_length, to_list_length.
              assert (n - i = S (n - S i))%nat as -> by Lia.lia; rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia.
            - intros. repeat rewrite ListUtil.length_set_nth. auto. }
        cbn [fst snd] in Hv2.
        assert (v2 = of_list (NTT_psi2_list (to_list (Nat.pow 2 (n - S i)) p1 ++ to_list (Nat.pow 2 (n - S i)) p2) (Nat.pow 2 (n - S i)) (F.inv (zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * k))))) by congruence; subst v2; clear Hv2.
        assert (F.of_Z _ (Zpos 2) = F.one + F.one) as ->.
        { unfold F.one. rewrite <- F.of_Z_add. apply F.eq_of_Z_iff. f_equal. }
        assert (nth_default Pzero pl (2 * k) = p1 /\ nth_default Pzero pl (2 * k + 1) = p2) as [<- <-].
        { replace (2 * k)%nat with (2 * k + 0)%nat at 1 by Lia.lia.
          do 2 rewrite <- ListUtil.nth_default_skipn.
          rewrite XX. split; reflexivity. }
        apply (NTT_base_psi_unpacked_list_spec (poly_ops:=poly_ops)).
        + generalize (Hnz (n - S i)%nat); Lia.lia.
        + apply zeta_pow_nz.
        + unfold measure.
          rewrite (Polynomial.peq_proper_degree (poly_defs:=poly_defs) _ _ (proj1 (ListUtil.Forall2_forall_iff (fun p q0 : P => Peq p (Pmod p q0)) _ _ Pzero Pzero ltac:(apply (Forall2_length HF))) HF (2 * k)%nat ltac:(rewrite (Forall2_length HF), cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia))).
          assert (ZZ: forall x, In x (cyclotomic_decomposition n (S i)) -> degree x = Some (Nat.pow 2 (n - S i))%nat).
          { intros x Hx. unfold cyclotomic_decomposition in Hx.
            apply in_map_iff in Hx. destruct Hx as [y [Hy Hyz]]. subst x.
            apply Polynomial.posicyclic_degree.
            generalize (Hnz (n - S i)%nat); Lia.lia. }
          generalize (ListUtil.nth_default_preserves_properties_length_dep (fun x => degree x = Some (Nat.pow 2 (n - S i)))%nat (cyclotomic_decomposition n (S i)) (2 * k)%nat Pzero ltac:(intros; apply ZZ; auto) ltac:(rewrite cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)).
          intro Q. assert (QQ: not (Peq (nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k)) Pzero)).
          { intro EE. rewrite (Polynomial.peq_proper_degree _ _ EE), degree_zero in Q; congruence. }
          generalize (Pmod_degree_lt (poly_ops:=poly_ops) (nth_default Pzero pl (2 * k)) (nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k)) QQ).
          unfold degree_lt. rewrite Q. cbn [convert]. Lia.lia.
        + unfold measure.
          rewrite (Polynomial.peq_proper_degree (poly_defs:=poly_defs) _ _ (proj1 (ListUtil.Forall2_forall_iff (fun p q0 : P => Peq p (Pmod p q0)) _ _ Pzero Pzero ltac:(apply (Forall2_length HF))) HF (2 * k + 1)%nat ltac:(rewrite (Forall2_length HF), cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia))).
          assert (ZZ: forall x, In x (cyclotomic_decomposition n (S i)) -> degree x = Some (Nat.pow 2 (n - S i))%nat).
          { intros x Hx. unfold cyclotomic_decomposition in Hx.
            apply in_map_iff in Hx. destruct Hx as [y [Hy Hyz]]. subst x.
            apply Polynomial.posicyclic_degree.
            generalize (Hnz (n - S i)%nat); Lia.lia. }
          generalize (ListUtil.nth_default_preserves_properties_length_dep (fun x => degree x = Some (Nat.pow 2 (n - S i)))%nat (cyclotomic_decomposition n (S i)) (2 * k + 1)%nat Pzero ltac:(intros; apply ZZ; auto) ltac:(rewrite cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)).
          intro Q. assert (QQ: not (Peq (nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k + 1)) Pzero)).
          { intro EE. rewrite (Polynomial.peq_proper_degree _ _ EE), degree_zero in Q; congruence. }
          generalize (Pmod_degree_lt (poly_ops:=poly_ops) (nth_default Pzero pl (2 * k + 1)) (nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * k + 1)) QQ).
          unfold degree_lt. rewrite Q. cbn [convert]. Lia.lia.
    Qed.

    Program Definition NTT_psi_layer (i: nat) (Hle: S i <= N.to_nat km1) (pl: Pquotl (cyclotomic_decomposition n (S i))): Pquotl (cyclotomic_decomposition n i) :=
      NTT_psi_layer_aux i (proj1_sig pl).
    Next Obligation.
      (* Coq ate the hypothesis :( *)
      assert (Hkm1: zeta ^ (N.pow 2 km1) = F.opp 1).
      { unfold F.pow, F.opp, F.of_Z. apply ModularArithmeticPre.exist_reduced_eq.
        exact H0. }
      unfold NTT_psi_layer_aux.
      clear H0. rewrite <- ListUtil.eq_flat_map_fold_left.
      apply Forall2_nth_error_iff.
      erewrite flat_map_constant_length; [|simpl; reflexivity].
      rewrite PeanoNat.Nat.mul_1_r, seq_length, cyclotomic_decomposition_length.
      split; [reflexivity|].
      intros. eapply flat_map_constant_nth_error in H; [|simpl; reflexivity].
      rewrite PeanoNat.Nat.mod_1_r in H. cbn [nth_error] in H.
      destruct H as [y [HA HB]]. inversion HB; subst v1; clear HB.
      rewrite PeanoNat.Nat.div_1_r in HA.
      rewrite ListUtil.nth_error_seq in HA. destruct (Compare_dec.lt_dec k (Nat.pow 2 i)) as [Hlt|]; try congruence.
      rewrite PeanoNat.Nat.add_0_l in HA; inversion HA; subst y; clear HA.
      assert (2 * k + 1 < Nat.pow 2 (S i))%nat as Hlt' by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
      generalize (@ListUtil.nth_error_value_eq_nth_default _ _ _ _ H0 Pzero). intro Hx; subst v2.
      set (m := nth_default 0%N (cyclotomic_decompose i) k).
      assert (Hm': exists m', nth_error (cyclotomic_decompose i) k = Some m') by (apply ListUtil.nth_error_length_exists_value; rewrite cyclotomic_decompose_length; Lia.lia).
      destruct Hm' as [m' Hm].
      assert (m = m') by (apply ListUtil.nth_error_value_eq_nth_default; auto). subst m'.
      generalize (cyclotomic_decompose_S_nth_error _ Hle _ _ Hm). intros [HA [HB HC]].
      unfold cyclotomic_decomposition. erewrite ListUtil.map_nth_default by (rewrite cyclotomic_decompose_length; Lia.lia).
      instantiate (1 := 0%N). rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hm).
      generalize (ListUtil.nth_error_value_eq_nth_default _ _ _ HA 0%N).
      intro X; cbn in X; rewrite X. clear X.
      assert (Hp1: nth_error (cyclotomic_decomposition n (S i)) (2 * k) = Some (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (m / 2)%N))).
      { unfold cyclotomic_decomposition. rewrite nth_error_map, HA. reflexivity. }
      assert (Hp2: nth_error (cyclotomic_decomposition n (S i)) (2 * k + 1) = Some (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (2 ^ km1 + m / 2)%N))).
      { unfold cyclotomic_decomposition. rewrite nth_error_map, HB. reflexivity. }
      generalize (cyclotomic_decomposition_S _ Hle k _ _ Hp1 Hp2). intros [Hcoprime [p [Hp Hmul]]].
      rewrite <- neg_zeta_power_eq in Hmul.
      rewrite Polynomial.posicyclic_opp in Hmul.
      rewrite <- Polynomial.posicyclic_decomposition in Hmul.
      assert (Hxy: Peq (nth_default Pzero (proj1_sig pl) (k + (k + 0))) (Pmod (nth_default Pzero (proj1_sig pl) (k + (k + 0))) (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (m / 2)))) /\ Peq (nth_default Pzero (proj1_sig pl) (k + (k + 0) + 1)) (Pmod (nth_default Pzero (proj1_sig pl) (k + (k + 0) + 1)) (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (2 ^ km1 + m / 2))))).
      { destruct pl as [pl Hpl]; simpl.
        apply Forall2_nth_error_iff in Hpl.
        destruct Hpl as [Hpl1 Hpl2]. rewrite cyclotomic_decomposition_length in Hpl1.
        split; eapply Hpl2; try (apply ListUtil.nth_error_Some_nth_default; Lia.lia); [exact Hp1|exact Hp2]. }
      destruct Hxy as [Hx Hy].
      rewrite <- neg_zeta_power_eq in Hy.
      set (x := exist (fun p => Peq p (Pmod p _)) (nth_default Pzero (proj1_sig pl) (k + (k + 0))) Hx).
      assert (X:Peq (Pmod (nth_default Pzero (proj1_sig pl) (k + (k + 0) + 1)) (posicyclic (Nat.pow 2 (n - S i)) (F.opp (zeta ^ (m / 2))))) (Pmod (nth_default Pzero (proj1_sig pl) (k + (k + 0) + 1)) (negacyclic (Nat.pow 2 (n - S i)) ((zeta ^ (m / 2)))))) by (apply Polynomial.peq_mod_proper; [reflexivity|apply Polynomial.posicyclic_opp]).
      rewrite X in Hy. clear X.
      set (y := exist (fun p => Peq p (Pmod p _)) (nth_default Pzero (proj1_sig pl) (k + (k + 0) + 1)) Hy).
      generalize (Polynomial.NTT_base_psi_obligation_1 (poly_defs:=poly_defs) (Nat.pow 2 (n - S i)) (zeta ^ (m / 2)%N) _ _ _ ltac:(generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); Lia.lia) ltac:(apply zeta_pow_nz) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) (x, y)).
      unfold x, y; simpl. intro X. etransitivity; eauto.
      apply Polynomial.peq_mod_proper; [reflexivity|].
      rewrite <- F.pow_add_r.
      assert (Nat.pow 2 (n - S i) + (Nat.pow 2 (n - S i) + 0) = Nat.pow 2 (n - i))%nat as -> by (assert (n - i = S (n - S i))%nat as -> by Lia.lia; rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
      assert (m / 2 + m / 2 = m)%N as -> by Lia.lia. reflexivity.
    Qed.

    (* This does not compute well *)
    (* Program Fixpoint NTT_psi (i: nat) (Hle: i <= N.to_nat km1) (pl: Pquotl (cyclotomic_decomposition n i)): Pquotl (cyclotomic_decomposition n 0%nat) := *)
    (*   match i with *)
    (*   | O => pl *)
    (*   | S i => (NTT_psi i ltac:(Lia.lia) (NTT_psi_layer i Hle pl)) *)
    (*   end. *)
    (* Next Obligation. destruct pl as [pl Hpl]. simpl. exact Hpl. Qed. *)
    (* Next Obligation. destruct pl as [pl Hpl]. simpl. exact Hpl. Qed. *)

    (* Goal forall (Hle: (0 <= N.to_nat km1)%nat)pl, NTT_psi 0%nat Hle pl = pl. intros. Fail reflexivity. *)

    Fixpoint NTT_psi_aux (i: nat) (pl: list P): list P :=
      match i with
      | O => pl
      | S i => NTT_psi_aux i (NTT_psi_layer_aux i pl)
      end.

    Local Instance NTT_psi_aux_proper_peq {i:nat}:
      Proper (Forall2 Peq ==> Forall2 Peq) (NTT_psi_aux i).
    Proof.
      induction i; intros pl1 pl2 Heq; simpl; [assumption|].
      apply IHi. apply NTT_psi_layer_aux_proper_peq. assumption.
    Qed.

    Lemma NTT_psi_aux_const_mul (i: nat) (c:F) (pl: list P):
      Forall2 Peq
        (NTT_psi_aux i (map (fun p => Pmul (Pconst c) p) pl))
        (map (fun p => Pmul (Pconst c) p) (NTT_psi_aux i pl)).
    Proof.
      revert pl. induction i; [reflexivity|].
      intros pl; simpl. rewrite <- IHi.
      apply NTT_psi_aux_proper_peq.
      apply NTT_psi_layer_aux_const_mul.
    Qed.

    Lemma mul_const_of_list (c: F) (l: list F):
      Peq (Pmul (Pconst c) (of_list l)) (of_list (List.map (F.mul c) l)).
    Proof.
      intro i. unfold of_list.
      rewrite mul_const_coeff_l, coeff_bigop, coeff_bigop.
      rewrite map_length. rewrite bigop_l_distr.
      apply bigop_ext_eq. intros k Hk.
      do 2 rewrite mul_const_coeff_l.
      apply in_seq in Hk.
      erewrite ListUtil.map_nth_default by Lia.lia.
      rewrite Hierarchy.associative. reflexivity.
    Qed.

    Lemma of_list_inj (l1 l2: list F) (Heq: length l1 = length l2):
      Peq (of_list l1) (of_list l2) -> l1 = l2.
    Proof.
      unfold of_list; intro.
      apply nth_error_ext_samelength; auto.
      intros i Hi. generalize (H i).
      do 2 rewrite Polynomial.Pdecompose_coeff.
      rewrite <- Heq. destruct (Decidable.dec_lt_nat i (length l1)) as [_|]; [|Lia.lia].
      rewrite (ListUtil.nth_error_Some_nth_default i 0 l1 Hi).
      rewrite (ListUtil.nth_error_Some_nth_default i 0 l2 ltac:(rewrite <- Heq; apply Hi)).
      congruence.
    Qed.

    Fixpoint NTT_psi_list_no_div (i: nat) (l: list F): list F :=
      match i with
      | O => l
      | S i => NTT_psi_list_no_div i (NTT_psi_layer_list i l)
      end.

    Lemma NTT_psi_list_no_div_length (i: nat) (l: list F):
      length (NTT_psi_list_no_div i l) = length l.
    Proof.
      revert l; induction i; [reflexivity|]; intros.
      simpl. rewrite IHi, NTT_psi_layer_list_length. reflexivity.
    Qed.

    Lemma NTT_psi_list_no_div_map_mul c i l:
      NTT_psi_list_no_div i (map (F.mul c) l) = map (F.mul c) (NTT_psi_list_no_div i l).
    Proof.
      revert l; induction i; [reflexivity|].
      simpl. intro. rewrite NTT_psi_layer_list_map_mul.
      rewrite IHi. reflexivity.
    Qed.

    Lemma NTT_psi_list_no_div_spec:
      forall (i: nat) (pl: list P),
        (i <= N.to_nat km1)%nat ->
        Forall2 (fun p q : P => Peq p (Pmod p q)) pl (cyclotomic_decomposition n i) ->
        Forall2 Peq
          (map (fun x : P => Pmul (Pconst (F.of_Z q (Zpower.two_power_nat i))) x) (NTT_psi_aux i pl))
          (map of_list
             (chunk (Nat.pow 2 n)
                (NTT_psi_list_no_div i
                   (concat (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) pl))))).
    Proof.
      induction i; intros pl Hi HF.
      - cbn [NTT_psi_aux NTT_psi_list_no_div].
        rewrite PeanoNat.Nat.sub_0_r.
        assert (Zpower.two_power_nat 0%nat = BinInt.Z.one) as -> by reflexivity.
        assert (Forall2 Peq (map _ pl) pl) as ->.
        { apply Forall2_nth_error_iff.
          split; [apply map_length|].
          intros k v1 v2 Hv1 Hv2.
          rewrite nth_error_map, Hv2 in Hv1.
          simpl in Hv1. inversion Hv1; subst v1; clear Hv1.
          rewrite const_one_definition. apply Hierarchy.left_identity. }
        rewrite chunk_concat, map_map.
        2: apply NatUtil.pow_nonzero; Lia.lia.
        2: apply Forall_forall; intros x Hx; apply in_map_iff in Hx.
        2: destruct Hx as [y [<- Hx]]; apply to_list_length.
        apply Forall2_nth_error_iff.
        split; [rewrite map_length; reflexivity|].
        intros k v1 v2 Hv1 Hv2.
        rewrite nth_error_map, Hv1 in Hv2. cbn in Hv2.
        inversion Hv2; subst v2.
        symmetry. apply Polynomial.of_list_to_list.
        cbv [cyclotomic_decomposition cyclotomic_decompose map] in HF.
        rewrite PeanoNat.Nat.sub_0_r, Hkm1 in HF.
        generalize (Forall2_length HF); cbn [length]. intro Hpl1.
        destruct pl; [cbn in Hpl1; congruence|].
        destruct pl; [|cbn in Hpl1; congruence].
        rewrite nth_error_cons in Hv1.
        destruct k; [|rewrite ListUtil.nth_error_nil_error in Hv1; congruence].
        assert (v1 = p) as -> by congruence.
        apply Forall2_cons_iff in HF. destruct HF as [Heq HF].
        rewrite (Polynomial.peq_proper_degree _ _ Heq).
        erewrite <- (Polynomial.posicyclic_degree (poly_ops:=poly_ops)) by (generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)); Lia.lia).
        apply Polynomial.Pmod_degree_lt.
        intro T.
        generalize (Polynomial.posicyclic_degree (poly_ops:=poly_ops) (Nat.pow 2 n) (F.opp 1) ltac:(generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)); Lia.lia)).
        rewrite (Polynomial.peq_proper_degree _ _ T), degree_zero.
        congruence.
      - simpl.
        destruct (NTT_psi_layer i Hi (exist _ pl HF)) as [pl' HF'] eqn:Heq.
        simpl in Heq. apply EqdepFacts.eq_sig_fst in Heq.
        cbn [proj1_sig] in Heq. subst pl'.
        generalize (IHi _ ltac:(Lia.lia) HF'). intro IH.
        rewrite Zpower.two_power_nat_S, F.of_Z_mul.
        assert (Forall2 Peq (map (fun x => Pmul (Pconst (F.of_Z q (Zpos 2))) x) (map (fun x => Pmul (Pconst (F.of_Z q (Zpower.two_power_nat i))) x) (NTT_psi_aux i (NTT_psi_layer_aux i pl)))) (map (fun x : P => Pmul (Pconst (F.of_Z q (Zpos 2) * F.of_Z q (Zpower.two_power_nat i))) x) (NTT_psi_aux i (NTT_psi_layer_aux i pl)))) as <-.
        { rewrite map_map. apply Forall2_nth_error_iff.
          split; [repeat rewrite map_length; reflexivity|].
          intros k v1 v2 Hv1 Hv2.
          rewrite nth_error_map in Hv1, Hv2.
          destruct (nth_error (NTT_psi_aux i (NTT_psi_layer_aux i pl)) k); [|simpl in Hv1; congruence].
          simpl in Hv1, Hv2. inversion Hv1; inversion Hv2; subst v1; subst v2.
          rewrite <- Polynomial.const_mul_const.
          rewrite Hierarchy.associative. reflexivity. }
        generalize (NTT_psi_layer_list_spec i pl Hi HF). intro IH2.
        etransitivity; [apply (Forall2_map _ _ _ IH); [intros x1 x2 Hx; rewrite Hx; reflexivity]|].
        transitivity (map of_list (map (map (F.mul (F.of_Z q (Zpos 2)))) (chunk (Nat.pow 2 n) (NTT_psi_list_no_div i (concat (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) (NTT_psi_layer_aux i pl))))))).
        { rewrite map_map. etransitivity; [eapply Forall2_map_in; intros; apply mul_const_of_list|].
          rewrite <- map_map. reflexivity. }
        rewrite <- chunk_map by (apply NatUtil.pow_nonzero; Lia.lia).
        rewrite <- NTT_psi_list_no_div_map_mul.
        rewrite concat_map.
        assert (concat (map _ _) = NTT_psi_layer_list i (concat (map (fun p : P => to_list (Nat.pow 2 (n - S i)) p) pl))) as ->; [|reflexivity].
        generalize (Forall2_map (to_list (Nat.pow 2 (n - i))) _ _ IH2 peq_proper_to_list).
        assert (map (to_list (Nat.pow 2 (n - i))) (map of_list _) = chunk (Nat.pow 2 (n - i)) (NTT_psi_layer_list i (concat (map (fun p : P => to_list (Nat.pow 2 (n - S i)) p) pl)))) as ->.
        { rewrite map_map. eapply map_ext_id.
          intros x Hx. apply to_list_of_list.
          eapply (Forall_In (P := fun x => length x = Nat.pow 2 (n - i))); [|apply Hx].
          apply (Forall_chunk_length_eq (Nat.pow 2 (n - i)) (Nat.pow 2 i)%nat (NTT_psi_layer_list i (concat (map (fun p : P => to_list (Nat.pow 2 (n - S i)) p) pl)))).
          rewrite NTT_psi_layer_list_length, (length_concat_same_length (Nat.pow 2 (n - S i))), map_length, (Forall2_length HF), cyclotomic_decomposition_length.
          2: apply Forall_map, Forall_forall; intros; apply to_list_length.
          do 2 rewrite <- PeanoNat.Nat.pow_add_r. f_equal. Lia.lia. }
        intro X. rewrite <- (concat_chunk (Nat.pow 2 (n - i)) (NTT_psi_layer_list i _)).
        f_equal.
        assert (chunk _ _ = (map (to_list (Nat.pow 2 (n - i))) (map (fun x : P => Pmul (Pconst (F.of_Z q (Zpos 2))) x) (NTT_psi_layer_aux i pl)))) as ->.
        { apply Forall2_nth_error_iff in X. destruct X as [X1 X2].
          apply nth_error_ext_samelength; auto.
          intros j Hj. destruct (ListUtil.nth_error_length_exists_value _ _ Hj) as [? Y1].
          rewrite Y1. rewrite <- X1 in Hj.
          destruct (ListUtil.nth_error_length_exists_value _ _ Hj) as [? Y2].
          rewrite Y2. f_equal. symmetry. eapply X2; eauto. }
        do 2 rewrite map_map. apply map_ext_in. intros p Hp.
        apply of_list_inj.
        { rewrite map_length, to_list_length, to_list_length. reflexivity. }
        rewrite <- mul_const_of_list.
        assert (degree_lt (degree p) (Some (Nat.pow 2 (n - i)))).
        { destruct (In_nth_error _ _ Hp) as [j Hj].
          apply Forall2_nth_error_iff in HF'. destruct HF' as [HF1 HF2].
          generalize (nth_error_Some_bound_index _ _ _ Hj). intro Hjj.
          rewrite HF1 in Hjj. destruct (ListUtil.nth_error_length_exists_value _ _ Hjj) as [qq Hqq].
          generalize (HF2 _ _ _ Hj Hqq). intro Hpmod.
          rewrite (Polynomial.peq_proper_degree _ _ Hpmod).
          assert (Some (Nat.pow 2 (n - i)) = degree qq) as DD.
          { unfold cyclotomic_decomposition in Hqq. rewrite nth_error_map in Hqq.
            destruct (nth_error (cyclotomic_decompose i) j) as [nn|] eqn:Hnn; simpl in Hqq; [|congruence].
            inversion Hqq. symmetry. apply posicyclic_degree.
            generalize (NatUtil.pow_nonzero 2 (n - i) ltac:(Lia.lia)); Lia.lia. }
          rewrite DD. apply Polynomial.Pmod_degree_lt.
          intro T. rewrite (Polynomial.peq_proper_degree _ _ T), degree_zero in DD.
          congruence. }
        rewrite of_list_to_list; auto.
        rewrite of_list_to_list; [reflexivity|].
        rewrite mul_degree_eq, degree_const.
        destruct (F.eq_dec (F.of_Z q (Zpos 2)) 0) as [He|Hne]; [|rewrite degree_add_0_l; auto].
        generalize (char_ge_3 2%positive ltac:(simpl; Lia.lia)); simpl.
        unfold F.zero, F.one. repeat rewrite <- F.of_Z_add.
        assert (Z0 + Zpos 1 + Zpos 1 = Zpos 2)%Z as -> by Lia.lia.
        intro Hne. elim Hne. apply He.
    Qed.

    Definition NTT_psi_list (i: nat) (l: list F): list F :=
      map (fun c => F.div c (F.of_Z _ (Zpower.two_power_nat i))) (NTT_psi_list_no_div i l).

    Lemma NTT_psi_list_spec:
      forall (i: nat) (pl: list P),
        (i <= N.to_nat km1)%nat ->
        Forall2 (fun p q : P => Peq p (Pmod p q)) pl (cyclotomic_decomposition n i) ->
        Forall2 Peq
          (NTT_psi_aux i pl)
          (map of_list
             (chunk (Nat.pow 2 n)
                (NTT_psi_list i
                   (concat (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) pl))))).
    Proof.
      intros i pl Hi HF.
      generalize (NTT_psi_list_no_div_spec i pl Hi HF). intro HF2.
      unfold NTT_psi_list.
      rewrite chunk_map; [|generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)); Lia.lia].
      rewrite map_map.
      assert (Forall2 Peq (map _ _) (map (fun p => (Pmul (Pconst (1 / F.of_Z q (Zpower.two_power_nat i))) p)) (map (fun l => of_list l) (chunk (Nat.pow 2 n) (NTT_psi_list_no_div i (concat (map (fun p : P => to_list (Nat.pow 2 (n - i)) p) pl))))))) as ->.
      { rewrite map_map. eapply Forall2_map_in. intros x Hx.
        symmetry. rewrite mul_const_of_list.
        erewrite map_ext; [reflexivity|]. intros; simpl.
        do 2 rewrite Hierarchy.field_div_definition.
        rewrite Hierarchy.commutative, Hierarchy.associative, Hierarchy.right_identity.
        reflexivity. }
      eapply (@Forall2_map _ _ Peq Peq _ _ (fun p : P => Pmul (Pconst (1 / F.of_Z q (Zpower.two_power_nat i))) p)) in HF2.
      2: intros p1 p2 Hpeq; rewrite Hpeq; reflexivity.
      rewrite map_map in HF2.
      etransitivity; eauto.
      apply Forall2_nth_error_iff. rewrite map_length. split; [reflexivity|].
      intros k v1 v2 Hv1 Hv2.
      rewrite nth_error_map, Hv1 in Hv2. simpl in Hv2. inversion Hv2; clear Hv2.
      rewrite Hierarchy.associative, const_mul_const, Hierarchy.field_div_definition, Hierarchy.left_identity.
      rewrite Hierarchy.left_multiplicative_inverse, const_one_definition, Hierarchy.left_identity; [reflexivity|].
      intro X. unfold F.zero in X. apply F.eq_of_Z_iff in X.
      rewrite Zdiv.Zmod_0_l, Zpower.two_power_nat_equiv in X.
      apply Zmod_divide in X; [|congruence].
      clear -X prime_q char_ge_3. (* Prove that q does not divide 2^i *)
      induction i.
      { simpl in X. apply BinInt.Z.divide_1_r_nonneg in X; [|Lia.lia].
        inversion X; subst q. apply not_prime_1. auto. }
      { rewrite Znat.Nat2Z.inj_succ in X.
        rewrite BinInt.Z.pow_succ_r in X by Lia.lia.
        apply (prime_mult _ prime_q) in X. destruct X as [X|X]; auto.
        apply (prime_div_prime _ _ prime_q prime_2) in X.
        inversion X; subst q.
        generalize (char_ge_3 2%positive ltac:(simpl; Lia.lia)); simpl.
        unfold F.zero, F.one. repeat rewrite <- F.of_Z_add.
        assert (Z0 + Zpos 1 + Zpos 1 = Zpos 2)%Z as -> by Lia.lia.
        intro Y. apply Y. apply F.eq_of_Z_iff.
        rewrite Zdiv.Zmod_0_l, Zdiv.Z_mod_same by Lia.lia.
        reflexivity. }
    Qed.

    Program Definition NTT_psi (i: nat) (Hle: i <= N.to_nat km1) (pl: Pquotl (cyclotomic_decomposition n i)): Pquotl (cyclotomic_decomposition n 0%nat) :=
      NTT_psi_aux i (proj1_sig pl).
    Next Obligation.
      assert (Hkm1: zeta ^ (N.pow 2 km1) = F.opp 1).
      { unfold F.pow, F.opp, F.of_Z. apply ModularArithmeticPre.exist_reduced_eq.
        exact H0. }
      induction i.
      - destruct pl as [pl Hpl]. simpl. assumption.
      - simpl. specialize (IHi ltac:(Lia.lia)).
        assert (NTT_psi_layer_aux i (proj1_sig pl) = proj1_sig (NTT_psi_layer i Hle pl)) as -> by reflexivity.
        apply IHi.
    Qed.

    Lemma NTT_psi_0 (Hle: 0%nat <= N.to_nat km1) pl:
      Polynomial.eql (NTT_psi 0%nat Hle pl) pl.
    Proof.
      destruct pl as [pl Hpl]; unfold Polynomial.eql; simpl.
      apply Forall2_nth_error_iff. split; [reflexivity|].
      intros k v1 v2 Hv1 Hv2. rewrite Hv2 in Hv1; inversion Hv1; subst v2; reflexivity.
    Qed.

    Lemma NTT_psi_S (i: nat) (Hle: S i <= N.to_nat km1) pl:
      forall (Hle': i <= N.to_nat km1),
        Polynomial.eql (NTT_psi (S i) Hle pl) (NTT_psi i Hle' (NTT_psi_layer i Hle pl)).
    Proof.
      intros; destruct pl as [pl Hpl].
      unfold Polynomial.eql; simpl.
      apply Forall2_nth_error_iff. split; [reflexivity|].
      intros k v1 v2 Hv1 Hv2. rewrite Hv2 in Hv1; inversion Hv1; subst v2; reflexivity.
    Qed.

    Local Instance eql_NTT_psi_layer_proper: forall i Hle, Proper (Polynomial.eql ==> Polynomial.eql) (NTT_psi_layer i Hle).
    Proof.
      intros; intros p1 p2 Heq.
      unfold Polynomial.eql in *.
      destruct p1 as [p1 Hp1]. destruct p2 as [p2 Hp2]; simpl in *.
      unfold NTT_psi_layer_aux. repeat rewrite <- ListUtil.eq_flat_map_fold_left.
      apply Forall2_nth_error_iff.
      repeat rewrite (flat_map_constant_length (c:=1%nat)) by reflexivity.
      split; [reflexivity|].
      intros k v1 v2 Hv1 Hv2.
      apply (@flat_map_constant_nth_error _ _ 1%nat) in Hv1; [|reflexivity].
      apply (@flat_map_constant_nth_error _ _ 1%nat) in Hv2; [|reflexivity].
      rewrite PeanoNat.Nat.div_1_r in Hv1, Hv2.
      rewrite PeanoNat.Nat.mod_1_r in Hv1, Hv2. simpl in Hv1, Hv2.
      destruct Hv1 as [kk [Hkk Hv1]]. rewrite Hkk in Hv2.
      destruct Hv2 as [kk' [Hkk' Hv2]]. inversion Hkk'; subst kk'; clear Hkk'.
      inversion Hv1; subst v1; clear Hv1.
      inversion Hv2; subst v2; clear Hv2.
      unfold NTT_psi2. assert (kk + (kk + 0) = 2 * kk :> _)%nat as -> by Lia.lia.
      assert (Hlp1: (length p1 = Nat.pow 2 (S i) :> _)%nat) by (rewrite <- (cyclotomic_decomposition_length n); eapply Forall2_length; eauto).
      assert (Hkklt: (kk < Nat.pow 2 i)%nat) by (rewrite ListUtil.nth_error_seq in Hkk; destruct (Compare_dec.lt_dec k (Nat.pow 2 i)); [|congruence]; inversion Hkk; subst kk; Lia.lia).
      assert (Hkk2: (2 * kk < length p1)%nat) by (rewrite Hlp1, PeanoNat.Nat.pow_succ_r'; Lia.lia).
      assert (Hkk2': (2 * kk + 1 < length p1)%nat) by (rewrite Hlp1, PeanoNat.Nat.pow_succ_r'; Lia.lia).
      rewrite (proj1 (ListUtil.Forall2_forall_iff Peq p1 p2 Pzero Pzero ltac:(eapply Forall2_length; eauto)) Heq _ Hkk2).
      rewrite (proj1 (ListUtil.Forall2_forall_iff Peq p1 p2 Pzero Pzero ltac:(eapply Forall2_length; eauto)) Heq _ Hkk2').
      reflexivity.
    Qed.

    Local Instance eql_NTT_psi_proper: forall i Hle, Proper (Polynomial.eql ==> Polynomial.eql) (NTT_psi i Hle).
    Proof.
      induction i; intros; intros p1 p2 Heq.
      - repeat rewrite NTT_psi_0. auto.
      - repeat rewrite NTT_psi_S. apply (IHi ltac:(Lia.lia)).
        rewrite Heq. reflexivity.
    Qed.

    Local Instance eql_NTT_phi_layer_proper: forall i, Proper (Polynomial.eql ==> Polynomial.eql) (NTT_phi_layer i).
    Proof.
      intros; intros p1 p2 Heq.
      unfold Polynomial.eql in *.
      destruct p1 as [p1 Hp1]. destruct p2 as [p2 Hp2]; simpl in *.
      unfold NTT_phi_layer_aux.
      repeat rewrite <- ListUtil.eq_flat_map_fold_left.
      apply Forall2_nth_error_iff.
      repeat rewrite (flat_map_constant_length (c:=2%nat)) by reflexivity.
      split; [reflexivity|].
      intros k v1 v2 Hv1 Hv2.
      apply (@flat_map_constant_nth_error _ _ 2%nat) in Hv1; [|reflexivity].
      apply (@flat_map_constant_nth_error _ _ 2%nat) in Hv2; [|reflexivity].
      destruct Hv1 as [kk [Hkk Hv1]]. rewrite Hkk in Hv2.
      destruct Hv2 as [kk' [Hkk' Hv2]]. inversion Hkk'; subst kk'; clear Hkk'.
      rewrite ListUtil.nth_error_seq in Hkk.
      rewrite PeanoNat.Nat.add_0_l in Hkk.
      destruct (Compare_dec.lt_dec (PeanoNat.Nat.div k 2) (Nat.pow 2 i)) as [Hdivklt|]; [|congruence].
      assert (Hkkeq: kk = PeanoNat.Nat.div k 2) by congruence. clear Hkk.
      assert (HPP: Peq (nth_default Pzero p1 kk) (nth_default Pzero p2 kk)).
      { apply Forall2_nth_error_iff in Heq. destruct Heq as [Hl Heq].
        apply (Heq kk); apply ListUtil.nth_error_Some_nth_default; [rewrite (Forall2_length Hp1)|rewrite (Forall2_length Hp2)]; rewrite cyclotomic_decomposition_length; Lia.lia. }
      assert (Hr: (PeanoNat.Nat.modulo k 2 = 0 \/ PeanoNat.Nat.modulo k 2 = 1)%nat).
      { generalize (PeanoNat.Nat.mod_upper_bound k 2 ltac:(Lia.lia)). Lia.lia. }
      destruct Hr as [Hr|Hr]; rewrite Hr in *; cbn [nth_error] in *;
      inversion Hv1; subst v1; inversion Hv2; subst v2; apply (Polynomial.peq_mod_proper _ _ HPP); reflexivity.
    Qed.

    Local Instance eql_NTT_phi_proper: forall i, Proper (Polynomial.eql ==> Polynomial.eql) (NTT_phi i).
    Proof.
      induction i; intros; intros p1 p2 Heq.
      - repeat rewrite NTT_phi_0. auto.
      - repeat rewrite NTT_phi_S. apply eql_NTT_phi_layer_proper.
        apply IHi. apply Heq.
    Qed.

    Lemma NTT_psi_phi_layer (i: nat) (Hle: S i <= N.to_nat km1) pl:
      Polynomial.eql (NTT_psi_layer i Hle (NTT_phi_layer i pl)) pl.
    Proof.
      unfold Polynomial.eql, Polynomial.to_pl.
      destruct pl as [pl Hpl]. simpl. unfold NTT_phi_layer_aux.
      rewrite <- ListUtil.eq_flat_map_fold_left.
      unfold NTT_psi_layer_aux. rewrite <- ListUtil.eq_flat_map_fold_left.
      apply Forall2_nth_error_iff. split.
      - rewrite (flat_map_constant_length (c:=1%nat)); [|reflexivity].
        rewrite seq_length, PeanoNat.Nat.mul_1_r.
        apply Forall2_length in Hpl. rewrite Hpl.
        symmetry; apply cyclotomic_decomposition_length.
      - intros k p1 p Hp1 Hp.
        apply (flat_map_constant_nth_error 1%nat) in Hp1; [|reflexivity].
        destruct Hp1 as [y [Hy Hp1]].
        rewrite PeanoNat.Nat.div_1_r in Hy.
        rewrite ListUtil.nth_error_seq in Hy.
        destruct (Compare_dec.lt_dec k (Nat.pow 2 i)) as [Hlt|_]; [|congruence].
        destruct (ListUtil.nth_error_length_exists_value k (cyclotomic_decomposition n i) ltac:(rewrite cyclotomic_decomposition_length; Lia.lia)) as [p' Hp'].
        assert (Hpp: Peq p (Pmod p p')).
        { apply Forall2_nth_error_iff in Hpl. destruct Hpl as [_ Hpl]. eapply Hpl; eauto. }
        rewrite PeanoNat.Nat.add_0_l in Hy. inversion Hy; subst y; clear Hy.
        rewrite PeanoNat.Nat.mod_1_r in Hp1; simpl in Hp1.
        inversion Hp1; subst p1; clear Hp1.
        set (m := flat_map _ (seq _ _)).
        assert (Hmlength: (length m = 2 * Nat.pow 2 i)%nat).
        { unfold m; rewrite (flat_map_constant_length (c:=2%nat)); [|reflexivity].
          rewrite seq_length. Lia.lia. }
        set (p1 := nth_default Pzero m (k + (k + 0))).
        set (p2 := nth_default Pzero m (k + (k + 0) + 1)).
        assert (Hp1: nth_error m (k + (k + 0)) = Some p1).
        { apply ListUtil.nth_error_Some_nth_default.
          rewrite Hmlength; Lia.lia. }
        assert (Hp2: nth_error m (k + (k + 0) + 1) = Some p2).
        { apply ListUtil.nth_error_Some_nth_default.
          rewrite Hmlength; Lia.lia. }
        apply (flat_map_constant_nth_error 2%nat) in Hp1; [|reflexivity].
        apply (flat_map_constant_nth_error 2%nat) in Hp2; [|reflexivity].
        assert (k + (k + 0) + 1 = 2 * k + 1)%nat as H2k1 by Lia.lia.
        rewrite H2k1 in *. clear H2k1.
        assert (k + (k + 0) = 2 * k + 0)%nat as H2k by Lia.lia.
        rewrite H2k in *. clear H2k.
        assert (PeanoNat.Nat.div (2 * k + 0) 2 = k) as Hdiv2 by (symmetry; eapply PeanoNat.Nat.div_unique; [|reflexivity]; Lia.lia).
        rewrite Hdiv2 in *. clear Hdiv2.
        assert (PeanoNat.Nat.div (2 * k + 1) 2 = k) as Hdiv2 by (symmetry; eapply PeanoNat.Nat.div_unique; [|reflexivity]; Lia.lia).
        rewrite Hdiv2 in *. clear Hdiv2.
        assert (PeanoNat.Nat.modulo (2 * k + 0) 2 = 0)%nat as Hmod2 by (symmetry; eapply PeanoNat.Nat.mod_unique; [|reflexivity]; Lia.lia).
        rewrite Hmod2 in *. clear Hmod2.
        assert (PeanoNat.Nat.modulo (2 * k + 1) 2 = 1)%nat as Hmod2 by (symmetry; eapply PeanoNat.Nat.mod_unique; [|reflexivity]; Lia.lia).
        rewrite Hmod2 in *. clear Hmod2.
        cbn [nth_error] in Hp1, Hp2.
        destruct Hp1 as [k1 [Hk1 Hp1]].
        destruct Hp2 as [k2 [Hk2 Hp2]].
        rewrite ListUtil.nth_error_seq in Hk1, Hk2.
        rewrite PeanoNat.Nat.add_0_l in Hk1, Hk2.
        destruct (Compare_dec.lt_dec k (Nat.pow 2 i)) as [_|_]; [|congruence].
        inversion Hk1; subst k1; clear Hk1.
        inversion Hk2; subst k2; clear Hk2.
        assert (nth_default Pzero pl k = p) as Hpeq by (apply ListUtil.nth_error_value_eq_nth_default; auto); rewrite Hpeq in *; clear Hpeq.
        generalize Hp'. unfold cyclotomic_decomposition. rewrite nth_error_map.
        destruct (nth_error (cyclotomic_decompose i) k) as [x|] eqn:Hx; [|simpl; congruence].
        destruct (cyclotomic_decompose_S_nth_error i Hle k x Hx) as [Hx0 [Hx1 Hxx]].
        assert (nth_default _ _ _ = x / 2)%N as -> by (apply ListUtil.nth_error_value_eq_nth_default; rewrite PeanoNat.Nat.add_0_r; apply Hx0).
        intro Z. simpl in Z; inversion Z; subst p'; clear Z.
        assert (Z: nth_default Pzero (cyclotomic_decomposition n (S i)) (k + (k + 0)) = posicyclic (Nat.pow 2 (n - (S i))) (zeta ^ (x/2))).
        { apply ListUtil.nth_error_value_eq_nth_default.
          unfold cyclotomic_decomposition. rewrite nth_error_map.
          cbn [Nat.mul] in Hx0. rewrite Hx0. simpl. reflexivity. }
        rewrite Z in *; clear Z.
        assert (Z: nth_default Pzero (cyclotomic_decomposition n (S i)) (k + (k + 0) + 1) = posicyclic (Nat.pow 2 (n - (S i))) (zeta ^ (2^km1 + x/2))).
        { apply ListUtil.nth_error_value_eq_nth_default.
          unfold cyclotomic_decomposition. rewrite nth_error_map.
          cbn [Nat.mul] in Hx1. rewrite Hx1. simpl. reflexivity. }
        rewrite Z in *; clear Z.
        set (d1 := (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (x / 2)))).
        set (d2 := (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (2 ^ km1 + x / 2)))).
        assert (Hd2: Peq d2 (negacyclic (Nat.pow 2 (n - S i)) (zeta ^ (x / 2)))).
        { unfold d2. rewrite <- neg_zeta_power_eq, Polynomial.posicyclic_opp. reflexivity. }
        set (pmul := (posicyclic (Nat.pow 2 (n - i)) (zeta ^ x))).
        assert (coprime d1 d2 /\ Peq pmul (Pmul d1 d2)) as [Hcoprime Hpmul].
        { destruct (cyclotomic_decomposition_S i Hle k d1 d2 ltac:(unfold cyclotomic_decomposition; rewrite nth_error_map, Hx0; reflexivity) ltac:(unfold cyclotomic_decomposition; rewrite nth_error_map, Hx1; reflexivity)) as [HA HB].
          split; auto. destruct HB as [pp [HB1 HB2]]. rewrite <- HB2.
          unfold cyclotomic_decomposition in HB1. rewrite nth_error_map, Hx in HB1.
          simpl in HB1. unfold pmul; congruence. }
        assert (Hngt0 : Nat.pow 2 (n - S i) > 0) by (generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); Lia.lia).
        assert (Hanz : zeta ^ (x / 2) <> 0) by (apply zeta_pow_nz).
        replace (Nat.pow 2 (n - i)) with (2 * Nat.pow 2 (n - S i))%nat in Hpp by (rewrite <- PeanoNat.Nat.pow_succ_r'; f_equal; Lia.lia).
        rewrite Hxx, <- F.pow_pow_l, F.pow_2_r, F.pow_mul_l in Hpp.
        generalize (Polynomial.NTT_base_psi_phi_id (poly_defs:=poly_defs) (Nat.pow 2 (n - S i)) (zeta ^(x / 2)) _ _ _ Hngt0 Hanz ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) (exist _ p Hpp)).
        unfold Polynomial.eq1, Polynomial.to_P. simpl.
        inversion Hp1; inversion Hp2.
        intro X. etransitivity; eauto.
        apply Polynomial.peq_NTT_base_psi_unpacked_proper; [reflexivity|].
        apply Polynomial.peq_mod_proper; [reflexivity|].
        fold d2. apply Hd2.
    Qed.

    Lemma NTT_psi_layer_inj (i: nat) (Hle: (S i <= N.to_nat km1)):
      forall (a b : Pquotl (cyclotomic_decomposition n (S i))),
        Polynomial.eql (NTT_psi_layer i Hle a) (NTT_psi_layer i Hle b) <->
        Polynomial.eql a b.
    Proof.
      intros a b. split.
      - destruct a as [a Ha]. destruct b as [b Hb].
        unfold Polynomial.eql; simpl.
        unfold NTT_psi_layer_aux.
        repeat rewrite <- ListUtil.eq_flat_map_fold_left.
        do 2 rewrite Forall2_nth_error_iff.
        rewrite (flat_map_constant_length (c:=1%nat)) by reflexivity.
        rewrite (flat_map_constant_length (c:=1%nat)) by reflexivity.
        intros [_ HH].
        rewrite (Forall2_length Ha), (Forall2_length Hb).
        split; [reflexivity|]. intros k v1 v2 Hv1 Hv2.
        set (k1 := PeanoNat.Nat.div k 2).
        set (r1 := PeanoNat.Nat.modulo k 2).
        assert (Hkeq: (k = 2 * k1 + r1)%nat) by (rewrite (PeanoNat.Nat.Div0.div_mod k 2); reflexivity).
        set (k' := (2 * k1 + (1 - r1))%nat).
        assert (Hr1: (r1 = 0 \/ r1 = 1)%nat).
        { generalize (PeanoNat.Nat.mod_upper_bound k 2 ltac:(Lia.lia)). Lia.lia. }
        assert (Hk1': k1 = PeanoNat.Nat.div k' 2).
        { eapply PeanoNat.Nat.div_unique; [|reflexivity]. Lia.lia. }
        assert (Hr1': PeanoNat.Nat.modulo k' 2 = (1 - r1)%nat).
        { symmetry; eapply PeanoNat.Nat.mod_unique; [|reflexivity]. Lia.lia. }
        apply Forall2_nth_error_iff in Ha.
        destruct Ha as [Hal Ha].
        apply Forall2_nth_error_iff in Hb.
        destruct Hb as [Hbl Hb].
        assert (Hklt: (k < 2 * Nat.pow 2 i)) by (apply ListUtil.nth_error_value_length in Hv1; rewrite Hal, cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r' in Hv1; Lia.lia).
        assert (Hklt1: (k1 < Nat.pow 2 i)) by Lia.lia.
        destruct (ListUtil.nth_error_length_exists_value k1 (cyclotomic_decomposition n i) ltac:(rewrite cyclotomic_decomposition_length; Lia.lia)) as [p Hpeq].
        destruct (ListUtil.nth_error_length_exists_value k (cyclotomic_decomposition n (S i)) ltac:(rewrite cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)) as [p1 Hpeq1].
        destruct (ListUtil.nth_error_length_exists_value k' (cyclotomic_decomposition n (S i)) ltac:(rewrite cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)) as [p2 Hpeq2].
        assert (HX: exists k,
                   Peq (if (Decidable.dec_eq_nat r1 0) then p1 else p2)
                     (posicyclic (Nat.pow 2 (n - S i)) (zeta^k)) /\
                     Peq (if (Decidable.dec_eq_nat r1 0) then p2 else p1)
                       (negacyclic (Nat.pow 2 (n - S i)) (zeta^k)) /\
                     Peq p (posicyclic (2 * Nat.pow 2 (n - S i)) (zeta^k * zeta^k))).
        { generalize (cyclotomic_decomposition_S_chunks2 i Hle).
          intros Hchunks. apply Forall2_nth_error_iff in Hchunks.
          destruct Hchunks as [Hlchunks Hchunks].
          assert (exists ll, nth_error (chunks2 (cyclotomic_decomposition n (S i))) k1 = Some ll) as [ll Hll].
          { generalize (chunks2_nth_error (cyclotomic_decomposition n (S i)) k).
            fold k1. rewrite Hpeq1. destruct (nth_error (chunks2 _) k1); simpl; [|congruence].
            exists l; reflexivity. }
          destruct (Hchunks k1 _ _ Hpeq Hll) as [p1' [p2' [Hlleq [Hco [Hpmul X]]]]]; subst ll.
          rewrite (chunks2_nth_error) in Hpeq1, Hpeq2.
          fold k1 in Hpeq1. rewrite <- Hk1' in Hpeq2. rewrite Hll in Hpeq1, Hpeq2.
          cbn [Option.bind] in Hpeq1, Hpeq2.
          fold r1 in Hpeq1. rewrite Hr1' in Hpeq2.
          assert (Y: p1' = (if (Decidable.dec_eq_nat r1 0) then p1 else p2) /\ (p2' = if (Decidable.dec_eq_nat r1 0) then p2 else p1)) by (destruct Hr1 as [Hr1|Hr1]; rewrite Hr1 in Hpeq1, Hpeq2; simpl in Hpeq1, Hpeq2; destruct (Decidable.dec_eq_nat r1 0); try Lia.lia; split; congruence).
          destruct Y; subst p1'; subst p2'.
          destruct X as [kk [HA [HB HC]]].
          exists kk. destruct (Decidable.dec_eq_nat r1 0); repeat split; assumption. }
        destruct HX as [x [Hpdef1 [Hpdef2 Hpmul]]].
        destruct (ListUtil.nth_error_length_exists_value k' a ltac:(rewrite Hal, cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)) as [u1 Hu1].
        destruct (ListUtil.nth_error_length_exists_value k' b ltac:(rewrite Hbl, cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)) as [u2 Hu2].
        generalize (Ha _ _ _ Hv1 Hpeq1). intros Hvp1.
        generalize (Hb _ _ _ Hv2 Hpeq1). intros Hvp2.
        generalize (Ha _ _ _ Hu1 Hpeq2). intros Hup1.
        generalize (Hb _ _ _ Hu2 Hpeq2). intros Hup2.
        assert (Hvu1: Peq (if Decidable.dec_eq_nat r1 0 then v1 else u1) (Pmod (if Decidable.dec_eq_nat r1 0 then v1 else u1) (if Decidable.dec_eq_nat r1 0 then p1 else p2))) by (destruct (Decidable.dec_eq_nat r1 0); auto).
        assert (Hvu2: Peq (if Decidable.dec_eq_nat r1 0 then v2 else u2) (Pmod (if Decidable.dec_eq_nat r1 0 then v2 else u2) (if Decidable.dec_eq_nat r1 0 then p1 else p2))) by (destruct (Decidable.dec_eq_nat r1 0); auto).
        assert (Huv1: Peq (if Decidable.dec_eq_nat r1 0 then u1 else v1) (Pmod (if Decidable.dec_eq_nat r1 0 then u1 else v1) (if Decidable.dec_eq_nat r1 0 then p2 else p1))) by (destruct (Decidable.dec_eq_nat r1 0); auto).
        assert (Huv2: Peq (if Decidable.dec_eq_nat r1 0 then u2 else v2) (Pmod (if Decidable.dec_eq_nat r1 0 then u2 else v2) (if Decidable.dec_eq_nat r1 0 then p2 else p1))) by (destruct (Decidable.dec_eq_nat r1 0); auto).
        generalize (proj1 (Polynomial.NTT_base_psi_inj_aux(poly_defs:=poly_defs) (Nat.pow 2 (n - S i)) (zeta ^ x) p _ _ ltac:(generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); Lia.lia) (zeta_pow_nz _) Hpmul Hpdef1 Hpdef2 _ Hvu1 _ Hvu2 _ Huv1 _ Huv2)).
        intro AA.
        set (ma := (flat_map (fun y : nat => [NTT_psi2 (Nat.pow 2 (n - S i)) (zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * y)) (nth_default Pzero a (2 * y)) (nth_default Pzero a (2 * y + 1))]) (seq 0 (Nat.pow 2 i)))).
        set (mb := (flat_map (fun y : nat => [NTT_psi2 (Nat.pow 2 (n - S i)) (zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * y)) (nth_default Pzero b (2 * y)) (nth_default Pzero b (2 * y + 1))]) (seq 0 (Nat.pow 2 i)))).
        generalize (ListUtil.nth_error_length_exists_value k1 ma ltac:(unfold ma; rewrite (flat_map_constant_length (c:=1%nat)), seq_length by reflexivity; Lia.lia)).
        intros [x1 Hx1].
        generalize (ListUtil.nth_error_length_exists_value k1 mb ltac:(unfold mb; rewrite (flat_map_constant_length (c:=1%nat)), seq_length by reflexivity; Lia.lia)).
        intros [x2 Hx2].
        generalize (HH _ _ _ Hx1 Hx2). intros Hxx.
        eapply (@flat_map_constant_nth_error _ _ 1%nat) in Hx1; [|reflexivity].
        eapply (@flat_map_constant_nth_error _ _ 1%nat) in Hx2; [|reflexivity].
        rewrite PeanoNat.Nat.div_1_r, PeanoNat.Nat.mod_1_r in Hx1.
        rewrite PeanoNat.Nat.div_1_r, PeanoNat.Nat.mod_1_r in Hx2.
        cbn [nth_error] in Hx1, Hx2.
        rewrite ListUtil.nth_error_seq in Hx1, Hx2.
        rewrite PeanoNat.Nat.add_0_l in Hx1, Hx2.
        destruct (Compare_dec.lt_dec k1 (Nat.pow 2 i)) as [_|]; [|contradiction].
        destruct Hx1 as [kk [Hkk Hx1]].
        inversion Hkk; subst kk; clear Hkk.
        destruct Hx2 as [kk [Hkk Hx2]].
        inversion Hkk; subst kk; clear Hkk.
        assert (Hx: zeta ^ nth_default 0%N (cyclotomic_decompose (S i)) (2 * k1) = zeta ^ x).
        { assert (2 * k1 = if (Decidable.dec_eq_nat r1 0) then k else k')%nat as -> by (destruct (Decidable.dec_eq_nat r1 0); destruct Hr1; Lia.lia).
          unfold cyclotomic_decomposition in Hpeq1, Hpeq2.
          rewrite nth_error_map in Hpeq1, Hpeq2.
          destruct (nth_error (cyclotomic_decompose (S i)) k) as [xk|] eqn:Hxk; simpl in Hpeq1; [|congruence].
          destruct (nth_error (cyclotomic_decompose (S i)) k') as [xk'|] eqn:Hxk'; simpl in Hpeq2; [|congruence].
          assert (nth_default 0%N (cyclotomic_decompose (S i)) (if Decidable.dec_eq_nat r1 0 then k else k') = if Decidable.dec_eq_nat r1 0 then xk else xk') as -> by (destruct (Decidable.dec_eq_nat r1 0); apply ListUtil.nth_error_value_eq_nth_default; auto).
          assert (p1 = (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ xk))) by congruence. subst p1.
          assert (p2 = (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ xk'))) by congruence; subst p2.
          destruct (Decidable.dec_eq_nat r1 0).
          - generalize (Hpdef1 0%nat).
            unfold posicyclic. intro X.
            repeat rewrite (Polynomial.sub_definition (base _)) in X.
            rewrite Polynomial.base_definition, Polynomial.const_definition, Polynomial.const_definition in X.
            generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); intro; destruct (Decidable.dec_eq_nat (Nat.pow 2 (n - S i)) 0); try Lia.lia.
            rewrite Hierarchy.ring_sub_definition, Hierarchy.left_identity in X.
            rewrite Hierarchy.ring_sub_definition, Hierarchy.left_identity in X.
            apply Group.inv_bijective. auto.
          - generalize (Hpdef1 0%nat).
            unfold posicyclic. intro X.
            repeat rewrite (Polynomial.sub_definition (base _)) in X.
            rewrite Polynomial.base_definition, Polynomial.const_definition, Polynomial.const_definition in X.
            generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); intro; destruct (Decidable.dec_eq_nat (Nat.pow 2 (n - S i)) 0); try Lia.lia.
            rewrite Hierarchy.ring_sub_definition, Hierarchy.left_identity in X.
            rewrite Hierarchy.ring_sub_definition, Hierarchy.left_identity in X.
            apply Group.inv_bijective. auto. }
        rewrite Hx in *.
        replace (2 * k1 + 1)%nat with (if Decidable.dec_eq_nat r1 0 then k' else k)%nat in Hx1, Hx2 by (destruct (Decidable.dec_eq_nat r1 0); Lia.lia).
        replace (2 * k1)%nat with (if Decidable.dec_eq_nat r1 0 then k else k')%nat in Hx1, Hx2 by (destruct (Decidable.dec_eq_nat r1 0); Lia.lia).
        destruct (Decidable.dec_eq_nat r1 0); apply AA.
        + do 2 (erewrite ListUtil.nth_error_value_eq_nth_default in Hx1; [|eassumption]).
          do 2 (erewrite ListUtil.nth_error_value_eq_nth_default in Hx2; [|eassumption]).
          congruence.
        + do 2 (erewrite ListUtil.nth_error_value_eq_nth_default in Hx1; [|eassumption]).
          do 2 (erewrite ListUtil.nth_error_value_eq_nth_default in Hx2; [|eassumption]).
          congruence.
      - intros Heq. rewrite Heq. reflexivity.
    Qed.

    Lemma NTT_phi_psi_layer (i: nat) (Hle: S i <= N.to_nat km1) pl:
      Polynomial.eql (NTT_phi_layer i (NTT_psi_layer i Hle pl)) pl.
    Proof.
      apply (proj1 (NTT_psi_layer_inj i Hle _ _)).
      rewrite NTT_psi_phi_layer. reflexivity.
    Qed.

    Lemma NTT_psi_phi (i: nat) (Hle: i <= N.to_nat km1) pl:
      Polynomial.eql (NTT_psi i Hle (NTT_phi i pl)) pl.
    Proof.
      induction i.
      - rewrite NTT_phi_0. apply NTT_psi_0.
      - assert (Hle': i <= N.to_nat km1) by Lia.lia.
        rewrite (NTT_psi_S i Hle _ Hle'), NTT_phi_S.
        rewrite NTT_psi_phi_layer. apply IHi.
    Qed.

    Lemma NTT_phi_psi (i: nat) (Hle: i <= N.to_nat km1) pl:
      Polynomial.eql (NTT_phi i (NTT_psi i Hle pl)) pl.
    Proof.
      induction i.
      - rewrite NTT_phi_0. apply NTT_psi_0.
      - assert (Hle': i <= N.to_nat km1) by Lia.lia.
        rewrite (NTT_psi_S _ Hle _ Hle'). rewrite NTT_phi_S.
        rewrite IHi. apply NTT_phi_psi_layer.
    Qed.

    Lemma NTT_phi_layer_opp (i: nat) (Hle: i <= N.to_nat km1):
      forall a : Pquotl (cyclotomic_decomposition n i),
        Polynomial.eql (NTT_phi_layer i (Polynomial.oppl a)) (Polynomial.oppl (NTT_phi_layer i a)).
    Proof.
      intros a. destruct a as [a Ha].
      unfold Polynomial.eql; simpl. unfold NTT_phi_layer_aux.
      do 2 rewrite <- ListUtil.eq_flat_map_fold_left.
      rewrite ListUtil.map_flat_map.
      apply Forall2_flat_map; [reflexivity|].
      intros k Hk. cbn [map].
      apply in_seq in Hk.
      repeat rewrite (ListUtil.map_nth_default _ _ _ _ Pzero) by (rewrite (Forall2_length Ha), cyclotomic_decomposition_length; Lia.lia).
      repeat constructor; rewrite <- (Polynomial.Pmod_opp (poly_defs:=poly_defs)); apply (Polynomial.peq_mod_proper); try reflexivity.
    Qed.

    Lemma NTT_phi_layer_add (i: nat) (Hle: i <= N.to_nat km1):
      forall a b : Pquotl (cyclotomic_decomposition n i),
        Polynomial.eql (NTT_phi_layer i (Polynomial.addl a b))
          (Polynomial.addl (NTT_phi_layer i a) (NTT_phi_layer i b)).
    Proof.
      intros a b. destruct a as [a Ha]. destruct b as [b Hb].
      unfold Polynomial.eql; simpl. unfold NTT_phi_layer_aux.
      repeat rewrite <- ListUtil.eq_flat_map_fold_left.
      rewrite flat_map_map2 by reflexivity. simpl.
      apply Forall2_flat_map; [reflexivity|].
      intros k Hk. apply in_seq in Hk. rewrite PeanoNat.Nat.add_0_l in Hk.
      repeat constructor; rewrite <- (Polynomial.Pmod_distr); apply Polynomial.peq_mod_proper; try reflexivity; rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero), (Forall2_length Ha), (Forall2_length Hb), PeanoNat.Nat.min_id, cyclotomic_decomposition_length; destruct (Compare_dec.lt_dec _ _); try Lia.lia; reflexivity.
    Qed.

    Lemma NTT_phi_layer_sub (i: nat) (Hle: i <= N.to_nat km1):
      forall a b : Pquotl (cyclotomic_decomposition n i),
        Polynomial.eql (NTT_phi_layer i (Polynomial.subl a b))
          (Polynomial.subl (NTT_phi_layer i a) (NTT_phi_layer i b)).
    Proof.
      intros a b. rewrite Hierarchy.ring_sub_definition.
      rewrite (@Hierarchy.ring_sub_definition _ _ _ _ _ _ _ _ (Polynomial.PquotlRing (poly_defs:=poly_defs) (field:=field) (ql:=cyclotomic_decomposition n (S i))).(Hierarchy.commutative_ring_ring)).
      rewrite NTT_phi_layer_add, NTT_phi_layer_opp by Lia.lia.
      reflexivity.
    Qed.

    Lemma NTT_phi_layer_mul (i: nat) (Hle: S i <= N.to_nat km1):
      forall a b : Pquotl (cyclotomic_decomposition n i),
        Polynomial.eql (NTT_phi_layer i (Polynomial.mull a b))
          (Polynomial.mull (NTT_phi_layer i a) (NTT_phi_layer i b)).
    Proof.
      intros a b. destruct a as [a Ha]. destruct b as [b Hb].
      unfold Polynomial.eql; simpl. unfold NTT_phi_layer_aux.
      repeat rewrite <- ListUtil.eq_flat_map_fold_left.
      rewrite flat_map_map2 by reflexivity. cbn [ListUtil.List.map2].
      unfold cyclotomic_decomposition at 9. cbn [cyclotomic_decompose].
      rewrite ListUtil.map_flat_map. simpl.
      assert (cyclotomic_decompose i = map (fun k => nth_default 0%N (cyclotomic_decompose i) k) (seq 0 (Nat.pow 2 i))) as Hgen.
      { apply nth_error_ext; intros.
        rewrite nth_error_map, ListUtil.nth_error_seq.
        destruct (Compare_dec.lt_dec _ _); simpl.
        - apply ListUtil.nth_error_Some_nth_default.
          rewrite cyclotomic_decompose_length. Lia.lia.
        - apply ListUtil.nth_error_length_error.
          rewrite cyclotomic_decompose_length. Lia.lia. }
      rewrite Hgen, ListUtil.flat_map_map.
      rewrite flat_map_map2 by reflexivity. simpl.
      apply Forall2_flat_map; [reflexivity|].
      intros x Hx. apply in_seq in Hx.
      rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
      rewrite ListUtil.map2_length, (Forall2_length Ha), (Forall2_length Hb), PeanoNat.Nat.min_id, PeanoNat.Nat.min_id, cyclotomic_decomposition_length.
      destruct (Compare_dec.lt_dec x (Nat.pow 2 i)) as [_|]; [|Lia.lia].
      rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
      rewrite (Forall2_length Ha), (Forall2_length Hb), PeanoNat.Nat.min_id, cyclotomic_decomposition_length.
      destruct (Compare_dec.lt_dec x (Nat.pow 2 i)) as [_|]; [|Lia.lia].
      assert (x + (x + 0) = 2 * x)%nat as -> by Lia.lia.
      assert (Hdiv1: PeanoNat.Nat.div (2 * x) 2 = x) by (symmetry; apply (PeanoNat.Nat.div_unique _ _ _ O); Lia.lia).
      assert (Hdiv2: PeanoNat.Nat.div (2 * x + 1) 2 = x) by (symmetry; apply (PeanoNat.Nat.div_unique _ _ _ 1); Lia.lia).
      assert (Hmod1: (PeanoNat.Nat.modulo (2 * x) 2 = 0)%nat) by (symmetry; apply (PeanoNat.Nat.mod_unique _ _ x O); Lia.lia).
      assert (Hmod2: (PeanoNat.Nat.modulo (2 * x + 1) 2 = 1)%nat) by (symmetry; apply (PeanoNat.Nat.mod_unique _ _ x 1); Lia.lia).
      generalize (proj1 (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero (Forall2_length Ha)) Ha x ltac:(rewrite (Forall2_length Ha), cyclotomic_decomposition_length; Lia.lia)); intro Hax.
      unfold cyclotomic_decomposition in Hax. erewrite (ListUtil.map_nth_default _ _ _ _ 0%N) in Hax by (rewrite cyclotomic_decompose_length; Lia.lia).
      generalize (proj1 (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero (Forall2_length Hb)) Hb x ltac:(rewrite (Forall2_length Hb), cyclotomic_decomposition_length; Lia.lia)); intro Hbx.
      unfold cyclotomic_decomposition in Hbx. erewrite (ListUtil.map_nth_default _ _ _ _ 0%N) in Hbx by (rewrite cyclotomic_decompose_length; Lia.lia).
      assert (nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * x) = posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (nth_default 0%N (cyclotomic_decompose i) x / 2)) /\ (nth_default Pzero (cyclotomic_decomposition n (S i)) (2 * x + 1)) = (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (2 ^ km1 + nth_default 0%N (cyclotomic_decompose i) x / 2)))) as [-> ->].
      { unfold cyclotomic_decomposition. cbn [cyclotomic_decompose].
        rewrite ListUtil.map_flat_map.
        assert (flat_map _ (cyclotomic_decompose i) = flat_map _ (map _ (seq _ _))) as -> by (rewrite Hgen; reflexivity).
        rewrite ListUtil.flat_map_map. cbn [map].
        split; apply ListUtil.nth_error_value_eq_nth_default;
        match goal with
        | |- nth_error ?m ?j = _ =>
            generalize (ListUtil.nth_error_length_exists_value j m ltac:(rewrite (flat_map_constant_length (c:=2%nat)), seq_length by reflexivity; Lia.lia))
        end;
        intros [y Hy]; rewrite Hy;
        (apply (@flat_map_constant_nth_error _ _ 2%nat) in Hy; [|reflexivity]);
        [rewrite Hdiv1, Hmod1 in Hy|rewrite Hdiv2, Hmod2 in Hy];
        cbn [nth_error] in Hy;
        rewrite ListUtil.nth_error_seq, PeanoNat.Nat.add_0_l in Hy;
        (destruct (Compare_dec.lt_dec x (Nat.pow 2 i)) as [_|]; [|Lia.lia]);
        destruct Hy as [y' [Hy' Hy]]; inversion Hy'; subst y'; clear Hy'; congruence. }
      assert (nth_default Pzero (cyclotomic_decomposition n i) x = posicyclic (Nat.pow 2 (n - i)) (zeta ^ (nth_default 0%N (cyclotomic_decompose i) x))) as ->.
      { unfold cyclotomic_decomposition.
        erewrite ListUtil.map_nth_default; [reflexivity|].
        rewrite cyclotomic_decompose_length; Lia.lia. }
      set (p := (posicyclic (Nat.pow 2 (n - i)) (zeta ^ nth_default 0%N (cyclotomic_decompose i) x))).
      set (p1 := (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (nth_default 0%N (cyclotomic_decompose i) x / 2)))).
      set (p2 := (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (2 ^ km1 + nth_default 0%N (cyclotomic_decompose i) x / 2)))).
      assert (Hpeq : Peq p (posicyclic (2 * Nat.pow 2 (n - S i)) (zeta ^ (nth_default 0%N (cyclotomic_decompose i) x / 2) * zeta ^ (nth_default 0%N (cyclotomic_decompose i) x / 2)))).
      { rewrite <- PeanoNat.Nat.pow_succ_r'.
        assert (S (n - S i) = n - i)%nat as -> by Lia.lia.
        rewrite <- F.pow_add_r.
        assert ((nth_default 0%N (cyclotomic_decompose i) x / 2) + (nth_default 0%N (cyclotomic_decompose i) x / 2) = 2 * (nth_default 0%N (cyclotomic_decompose i) x / 2))%N as -> by Lia.lia.
        rewrite <- (proj2 (N.Div0.div_exact (nth_default 0%N (cyclotomic_decompose i) x) 2)); [reflexivity|].
        apply N.Div0.mod_divides.
        assert (Hin: (In (nth_default 0%N (cyclotomic_decompose i) x) (cyclotomic_decompose i))) by (eapply nth_error_In; apply ListUtil.nth_error_Some_nth_default; rewrite cyclotomic_decompose_length; Lia.lia).
        generalize (cyclotomic_decompose_mod i ltac:(Lia.lia) (nth_default 0%N (cyclotomic_decompose i) x) Hin); intros [HA _].
        apply N.Div0.mod_divides in HA.
        destruct HA as [d HA]. rewrite HA.
        assert (km1 - N.of_nat i = N.succ (km1 - N.of_nat (S i)))%N as -> by Lia.lia.
        rewrite N.pow_succ_r'. exists (2 ^ (km1 - N.of_nat (S i)) * d)%N. Lia.lia. }
      assert (Hpeq1 : Peq p1 (posicyclic (Nat.pow 2 (n - S i)) (zeta ^ (nth_default 0%N (cyclotomic_decompose i) x / 2)))) by reflexivity.
      assert (Hpeq2 : Peq p2 (negacyclic (Nat.pow 2 (n - S i)) (zeta ^ (nth_default 0%N (cyclotomic_decompose i) x / 2)))).
      { rewrite <- Polynomial.posicyclic_opp.
        rewrite neg_zeta_power_eq. reflexivity. }
      destruct (Polynomial.NTT_ring_isomorphism2 (poly_defs:=poly_defs) (Nat.pow 2 (n - S i)) (zeta ^ (nth_default 0%N (cyclotomic_decompose i) x / 2)) p p1 p2 ltac:(generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); Lia.lia) ltac:(apply zeta_pow_nz) Hpeq Hpeq1 Hpeq2) as [_ [hom1 hom2]].
      generalize (hom1.(Ring.homomorphism_mul) (exist _ (nth_default Pzero a x) Hax) (exist _ (nth_default Pzero b x) Hbx)).
      unfold Polynomial.EQ2, Polynomial.eq1; simpl. intros [XA XB].
      repeat constructor; [apply XA|apply XB].
    Qed.

    Lemma NTT_layer_homomorphism (i: nat) (Hle: S i <= N.to_nat km1):
      @Ring.is_homomorphism
        (Pquotl (cyclotomic_decomposition n (S i)))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (Pquotl (cyclotomic_decomposition n i))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (NTT_psi_layer i Hle) /\
      @Ring.is_homomorphism
        (Pquotl (cyclotomic_decomposition n i))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (Pquotl (cyclotomic_decomposition n (S i)))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (NTT_phi_layer i).
    Proof.
      eapply Ring.ring_by_isomorphism.
      - apply NTT_phi_psi_layer.
      - intros a b. split; intros HEQ.
        + rewrite <- (NTT_psi_phi_layer i Hle a), <- (NTT_psi_phi_layer i Hle b).
          apply NTT_psi_layer_inj; auto.
        + rewrite HEQ. reflexivity.
      - instantiate (1:=Polynomial.zerol).
        unfold Polynomial.eql; simpl. unfold NTT_phi_layer_aux.
        rewrite <- ListUtil.eq_flat_map_fold_left.
        apply Forall2_nth_error_iff.
        rewrite (flat_map_constant_length (c:=2%nat)); [|reflexivity].
        rewrite repeat_length, seq_length, cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'.
        split; [Lia.lia|].
        intros k v1 v2 Hv1 Hv2. apply ListUtil.nth_error_repeat in Hv2.
        subst v2. apply (@flat_map_constant_nth_error _ _ 2%nat) in Hv1; [|reflexivity].
        destruct Hv1 as [k' [Hk' Hv1]].
        assert (Hp: nth_default Pzero (repeat Pzero (length (cyclotomic_decomposition n i))) k' = Pzero).
        { rewrite ListUtil.nth_default_repeat.
          destruct (Decidable.dec _); reflexivity. }
        rewrite Hp in Hv1.
        generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)). intro Hklt.
        destruct (PeanoNat.Nat.modulo k 2); [simpl in Hv1; inversion Hv1; subst v1; rewrite Polynomial.Pmod_0_l; reflexivity|].
        destruct n0; [|Lia.lia].
        simpl in Hv1; inversion Hv1; subst v1; rewrite Polynomial.Pmod_0_l; reflexivity.
      - generalize (Polynomial.of_pl_obligation_1 (poly_defs:=poly_defs) (ql:=cyclotomic_decomposition n i) (repeat Pone (length (cyclotomic_decomposition n i))) (repeat_length Pone (length _))). intro HF.
        generalize (Polynomial.of_pl_obligation_1 (poly_defs:=poly_defs) (ql:=cyclotomic_decomposition n (S i)) (repeat Pone (length (cyclotomic_decomposition n (S i)))) (repeat_length Pone (length _))). intro HFS.
        unfold Polynomial.eql. simpl. unfold NTT_phi_layer_aux.
        rewrite <- ListUtil.eq_flat_map_fold_left.
        apply Forall2_nth_error_iff.
        rewrite (flat_map_constant_length (c:=2%nat)); [|reflexivity].
        rewrite ListUtil.map2_length, seq_length, repeat_length, PeanoNat.Nat.min_id, cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'.
        split; [Lia.lia|].
        intros k v1 v2 Hv1 Hv2. apply (@flat_map_constant_nth_error _ _ 2%nat) in Hv1; [|reflexivity].
        destruct Hv1 as [kk [Hkk Hv1]].
        rewrite ListUtil.nth_error_seq, PeanoNat.Nat.add_0_l in Hkk.
        destruct (Compare_dec.lt_dec (PeanoNat.Nat.div k 2) (Nat.pow 2 i)) as [Hkklt|]; [|congruence].
        generalize (ListUtil.nth_error_value_length _ _ _ _ Hv2).
        rewrite ListUtil.map2_length, repeat_length, cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.min_id. intro Hklt.
        assert (Peq v2 Pone) as ->.
        { generalize (nth_error_repeat Pone Hklt). intro Hrepeat.
          generalize (ListUtil.nth_error_length_exists_value k (cyclotomic_decomposition n (S i)) ltac:(rewrite cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)). intros [x Hx].
          rewrite (nth_error_map2 _ _ _ k _ _ Hrepeat Hx) in Hv2.
          inversion Hv2; subst v2. rewrite Polynomial.Pmod_small; [reflexivity|].
          rewrite (Polynomial.degree_one (poly_defs:=poly_defs)).
          rewrite (cyclotomic_decomposition_degree _ Hle _ _ Hx).
          cbv [Polynomial.degree_lt Polynomial.convert].
          generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)). Lia.lia. }
        assert (Peq v1 Pone) as ->; [|reflexivity].
        assert (Hv1eq: v1 = Pmod (nth_default Pzero (ListUtil.List.map2 (fun p q0 : P => Pmod p q0) (repeat Pone (length (cyclotomic_decomposition n i))) (cyclotomic_decomposition n i)) kk) (nth_default Pzero (cyclotomic_decomposition n (S i)) (kk + (kk + 0))) \/ v1 = Pmod (nth_default Pzero (ListUtil.List.map2 (fun p q0 : P => Pmod p q0) (repeat Pone (length (cyclotomic_decomposition n i))) (cyclotomic_decomposition n i)) kk) (nth_default Pzero (cyclotomic_decomposition n (S i)) (kk + (kk + 0) + 1))) by (destruct (PeanoNat.Nat.modulo k 2) as [|n']; [simpl in Hv1; inversion Hv1; subst v1; auto|destruct n' as [|n']; simpl in Hv1; [inversion Hv1; subst v1; auto|rewrite ListUtil.nth_error_nil_error in Hv1; congruence]]).
        assert (Hone: Peq (nth_default Pzero (ListUtil.List.map2 (fun p q0 : P => Pmod p q0) (repeat Pone (length (cyclotomic_decomposition n i))) (cyclotomic_decomposition n i)) kk) Pone).
        { assert (kk = PeanoNat.Nat.div k 2) as Hkkeq by congruence.
          rewrite <- Hkkeq in *. rewrite cyclotomic_decomposition_length.
          generalize (nth_error_repeat Pone Hkklt). intro Hrepeat.
          generalize (ListUtil.nth_error_length_exists_value kk (cyclotomic_decomposition n i) ltac:(rewrite cyclotomic_decomposition_length; Lia.lia)). intros [x Hx].
          erewrite ListUtil.nth_error_value_eq_nth_default; [|eapply nth_error_map2; eauto].
          rewrite Polynomial.Pmod_small; [reflexivity|].
          rewrite (Polynomial.degree_one (poly_defs:=poly_defs)).
          rewrite (cyclotomic_decomposition_degree i ltac:(Lia.lia) _ _ Hx).
          cbv [Polynomial.degree_lt Polynomial.convert].
          generalize (NatUtil.pow_nonzero 2 (n - i) ltac:(Lia.lia)). Lia.lia. }
        replace (kk + (kk + 0))%nat with (2 * kk)%nat in Hv1eq by Lia.lia.
        assert (Hkklt2: (2 * kk + 1 < 2 * Nat.pow 2 i)).
        { assert (kk = PeanoNat.Nat.div k 2) by congruence. Lia.lia. }
        generalize (ListUtil.nth_error_length_exists_value (2 * kk) (cyclotomic_decomposition n (S i)) ltac:(rewrite cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)). intros [x1 Hx1].
        generalize (ListUtil.nth_error_length_exists_value (2 * kk + 1) (cyclotomic_decomposition n (S i)) ltac:(rewrite cyclotomic_decomposition_length, PeanoNat.Nat.pow_succ_r'; Lia.lia)). intros [x2 Hx2].
        rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hx1), (ListUtil.nth_error_value_eq_nth_default _ _ _ Hx2) in Hv1eq.
        destruct Hv1eq; subst v1; rewrite Polynomial.Pmod_small; try apply Hone; [rewrite (cyclotomic_decomposition_degree (S i) ltac:(Lia.lia) _ _ Hx1)|rewrite (cyclotomic_decomposition_degree (S i) ltac:(Lia.lia) _ _ Hx2)]; rewrite (Polynomial.peq_proper_degree (poly_defs:=poly_defs) _ _ Hone), (Polynomial.degree_one (poly_defs:=poly_defs)); cbv [Polynomial.degree_lt Polynomial.convert]; generalize (NatUtil.pow_nonzero 2 (n - S i) ltac:(Lia.lia)); Lia.lia.
      - apply NTT_phi_layer_opp. Lia.lia.
      - apply NTT_phi_layer_add. Lia.lia.
      - apply NTT_phi_layer_sub. Lia.lia.
      - apply NTT_phi_layer_mul. Lia.lia.
    Qed.

    Local Instance NTT_psi_layer_homomorphism (i: nat) (Hle: S i <= N.to_nat km1):
      @Ring.is_homomorphism
        (Pquotl (cyclotomic_decomposition n (S i)))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (Pquotl (cyclotomic_decomposition n i))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (NTT_psi_layer i Hle).
    Proof. apply NTT_layer_homomorphism. Qed.

    Local Instance NTT_phi_layer_homomorphism (i: nat) (Hle: S i <= N.to_nat km1):
      @Ring.is_homomorphism
        (Pquotl (cyclotomic_decomposition n i))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (Pquotl (cyclotomic_decomposition n (S i)))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (NTT_phi_layer i).
    Proof. apply NTT_layer_homomorphism; auto. Qed.

    Theorem NTT_homomorphism (i: nat) (Hle: i <= N.to_nat km1):
      @Ring.is_homomorphism
        (Pquotl (cyclotomic_decomposition n i))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (Pquotl (cyclotomic_decomposition n 0%nat))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (NTT_psi i Hle) /\
      @Ring.is_homomorphism
        (Pquotl (cyclotomic_decomposition n 0%nat))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (Pquotl (cyclotomic_decomposition n i))
        Polynomial.eql Polynomial.onel Polynomial.addl Polynomial.mull
        (NTT_phi i).
    Proof.
      induction i.
      - split; constructor.
        + constructor; [|apply eql_NTT_psi_proper].
          intros a b. repeat rewrite (NTT_psi_0). reflexivity.
        + intros a b. repeat rewrite (NTT_psi_0). reflexivity.
        + rewrite (NTT_psi_0). reflexivity.
        + constructor; [|apply eql_NTT_phi_proper].
          intros a b. reflexivity.
        + intros a b. reflexivity.
        + reflexivity.
      - assert (Hle': i <= N.to_nat km1) by Lia.lia.
        specialize (IHi Hle').
        split; [destruct IHi as [[Hpsi_add Hpsi_mul Hpsi_one] _]|destruct IHi as [_ [Hphi_add Hphi_mul Hphi_one]]]; constructor.
        + constructor; [|apply eql_NTT_psi_proper].
          intros a b. do 3 rewrite (NTT_psi_S _ _ _ Hle').
          rewrite <- Monoid.homomorphism, (NTT_psi_layer_homomorphism i Hle).(Ring.homomorphism_is_homomorphism).(Monoid.homomorphism).
          reflexivity.
        + intros a b. do 3 rewrite (NTT_psi_S _ _ _ Hle').
          rewrite <- Hpsi_mul, (NTT_psi_layer_homomorphism i Hle).(Ring.homomorphism_mul).
          reflexivity.
        + rewrite (NTT_psi_S _ _ _ Hle').
          rewrite (NTT_psi_layer_homomorphism i Hle).(Ring.homomorphism_one).
          apply Hpsi_one.
        + constructor; [|apply eql_NTT_phi_proper].
          intros a b. do 3 rewrite NTT_phi_S.
          rewrite <- (NTT_phi_layer_homomorphism i Hle).(Ring.homomorphism_is_homomorphism).(Monoid.homomorphism), <- Monoid.homomorphism.
          reflexivity.
        + intros a b. do 3 rewrite NTT_phi_S.
          rewrite <- (NTT_phi_layer_homomorphism i Hle).(Ring.homomorphism_mul), <- Hphi_mul.
          reflexivity.
        + rewrite NTT_phi_S, Hphi_one, (NTT_phi_layer_homomorphism i Hle).(Ring.homomorphism_one).
          reflexivity.
    Qed.

  End NTT.

End CyclotomicDecomposition.

Section SanityCheck.
  Local Definition bitrev (n: nat) (i: N): N :=
    let fix aux k := match k with
                     | O => if N.testbit i 0%N then N.setbit 0%N (N.of_nat (n - 1)%nat) else 0%N
                     | S k' => if N.testbit i (N.of_nat k) then N.setbit (aux k') (N.of_nat (n - 1 - k)%nat)%N else aux k'
                     end in
    aux (n - 1)%nat.

  Local Notation bitrev8 := (bitrev 8%nat). (* Dilithium *)
  Local Notation bitrev7 := (bitrev 7%nat). (* Kyber *)

  (* Making sure the decomposition returns the same order expected by ML-DSA
     aka Dilithium *)
  (* See Section 7.5 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf *)
  Local Lemma dilithium_ok:
    (@cyclotomic_decompose 8%N 8%nat) = List.map (fun k => (2 * (bitrev8 (N.of_nat k)) + 1)%N) (seq 0 256%nat).
  Proof. reflexivity. Qed.

  (* Making sure the decomposition returns the same order expected by ML-KEM
     aka Kyber *)
  (* See Section 4.3 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf *)
  Local Lemma kyber_ok:
    (@cyclotomic_decompose 7%N 7%nat) = List.map (fun k => (2 * (bitrev7 (N.of_nat k)) + 1)%N) (seq 0 128%nat).
  Proof. reflexivity. Qed.
End SanityCheck.
