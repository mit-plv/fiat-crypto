Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.Structures.OrderedType.
Require Export Crypto.Util.FixCoqMistakes.

(** This is copied verbatim from coq/theories/Structures/OrderedTypeEx.v, and should be removed once we bump the version requirement to 8.12, where we get the benefit of https://github.com/coq/coq/pull/12044 *)
(** See the original file in the Coq sources for the license *)

Module Ascii_as_OT <: UsualOrderedType.
  Definition t := ascii.

  Definition eq := @eq ascii.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition cmp (a b : ascii) : comparison :=
    N.compare (N_of_ascii a) (N_of_ascii b).

  Lemma cmp_eq (a b : ascii):
    cmp a b = Eq  <->  a = b.
  Proof.
    unfold cmp.
    rewrite N.compare_eq_iff.
    split. 2:{ intro. now subst. }
    intro H.
    rewrite<- (ascii_N_embedding a).
    rewrite<- (ascii_N_embedding b).
    now rewrite H.
  Qed.

  Lemma cmp_lt_nat (a b : ascii):
    cmp a b = Lt  <->  (nat_of_ascii a < nat_of_ascii b)%nat.
  Proof.
    unfold cmp. unfold nat_of_ascii.
    rewrite N2Nat.inj_compare.
    rewrite Nat.compare_lt_iff.
    reflexivity.
  Qed.

  Lemma cmp_antisym (a b : ascii):
    cmp a b = CompOpp (cmp b a).
  Proof.
    unfold cmp.
    apply N.compare_antisym.
  Qed.

  Definition lt (x y : ascii) := (N_of_ascii x < N_of_ascii y)%N.

  Lemma lt_trans (x y z : ascii):
    lt x y -> lt y z -> lt x z.
  Proof.
    apply N.lt_trans.
  Qed.

  Lemma lt_not_eq (x y : ascii):
     lt x y -> x <> y.
  Proof.
    intros L H. subst.
    exact (N.lt_irrefl _ L).
  Qed.

  Local Lemma compare_helper_eq {a b : ascii} (E : cmp a b = Eq):
    a = b.
  Proof.
    now apply cmp_eq.
  Qed.

  Local Lemma compare_helper_gt {a b : ascii} (G : cmp a b = Gt):
    lt b a.
  Proof.
    now apply N.compare_gt_iff.
  Qed.

  Definition compare (a b : ascii) : Compare lt eq a b :=
    match cmp a b as z return _ = z -> _ with
    | Lt => fun E => LT E
    | Gt => fun E => GT (compare_helper_gt E)
    | Eq => fun E => EQ (compare_helper_eq E)
    end Logic.eq_refl.

  Definition eq_dec (x y : ascii): {x = y} + { ~ (x = y)} := ascii_dec x y.
End Ascii_as_OT.

(** [String] is an ordered type with respect to the usual lexical order. *)

Module String_as_OT <: UsualOrderedType.

  Definition t := string.

  Definition eq := @eq string.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Inductive lts : string -> string -> Prop :=
    | lts_empty : forall a s, lts EmptyString (String a s)
    | lts_tail : forall a s1 s2, lts s1 s2 -> lts (String a s1) (String a s2)
    | lts_head : forall (a b : ascii) s1 s2,
        lt (nat_of_ascii a) (nat_of_ascii b) ->
        lts (String a s1) (String b s2).

  Definition lt := lts.

  Lemma nat_of_ascii_inverse a b : nat_of_ascii a = nat_of_ascii b -> a = b.
  Proof.
    intro H.
    rewrite <- (ascii_nat_embedding a).
    rewrite <- (ascii_nat_embedding b).
    apply f_equal; auto.
  Qed.

  Lemma lts_tail_unique a s1 s2 : lt (String a s1) (String a s2) ->
    lt s1 s2.
  Proof.
    intro H; inversion H; subst; auto.
    remember (nat_of_ascii a) as x.
    apply lt_irrefl in H1; inversion H1.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    induction x; intros y z H1 H2.
    - destruct y as [| b y']; inversion H1.
      destruct z as [| c z']; inversion H2; constructor.
    - destruct y as [| b y']; inversion H1; subst;
        destruct z as [| c z']; inversion H2; subst.
      + constructor. eapply IHx; eauto.
      + constructor; assumption.
      + constructor; assumption.
      + constructor. eapply lt_trans; eassumption.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    induction x; intros y LT.
    - inversion LT. intro. inversion H.
    - inversion LT; subst; intros EQ.
      * specialize (IHx s2 H2).
        inversion EQ; subst; auto.
        apply IHx; unfold eq; auto.
      * inversion EQ; subst; auto.
        apply Nat.lt_irrefl in H2; auto.
  Qed.

  Fixpoint cmp (a b : string) : comparison :=
    match a, b with
    | EmptyString, EmptyString => Eq
    | EmptyString, _ => Lt
    | String _ _, EmptyString => Gt
    | String a_head a_tail, String b_head b_tail =>
      match Ascii_as_OT.cmp a_head b_head with
      | Lt => Lt
      | Gt => Gt
      | Eq => cmp a_tail b_tail
      end
    end.

  Lemma cmp_eq (a b : string):
    cmp a b = Eq  <->  a = b.
  Proof.
    revert b.
    induction a, b; try easy.
    cbn.
    remember (Ascii_as_OT.cmp _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; split; try discriminate;
      try rewrite Ascii_as_OT.cmp_eq in Heqc; try subst;
      try rewrite IHa; intro H.
    { now subst. }
    { now inversion H. }
    { inversion H; subst. rewrite<- Heqc. now rewrite Ascii_as_OT.cmp_eq. }
    { inversion H; subst. rewrite<- Heqc. now rewrite Ascii_as_OT.cmp_eq. }
  Qed.

  Lemma cmp_antisym (a b : string):
    cmp a b = CompOpp (cmp b a).
  Proof.
    revert b.
    induction a, b; try easy.
    cbn. rewrite IHa. clear IHa.
    remember (Ascii_as_OT.cmp _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; rewrite Ascii_as_OT.cmp_antisym in Heqc;
      destruct Ascii_as_OT.cmp; cbn in *; easy.
  Qed.

  Lemma cmp_lt (a b : string):
    cmp a b = Lt  <->  lt a b.
  Proof.
    revert b.
    induction a as [ | a_head a_tail ], b; try easy; cbn.
    { split; trivial. intro. apply lts_empty. }
    remember (Ascii_as_OT.cmp _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; split; intro H; try discriminate; trivial.
    {
      rewrite Ascii_as_OT.cmp_eq in Heqc. subst.
      apply String_as_OT.lts_tail.
      apply IHa_tail.
      assumption.
    }
    {
      rewrite Ascii_as_OT.cmp_eq in Heqc. subst.
      inversion H; subst. { rewrite IHa_tail. assumption. }
      exfalso. apply (Nat.lt_irrefl (nat_of_ascii a)). assumption.
    }
    {
      apply String_as_OT.lts_head.
      rewrite<- Ascii_as_OT.cmp_lt_nat.
      assumption.
    }
    {
      exfalso. inversion H; subst.
      {
         assert(X: Ascii_as_OT.cmp a a = Eq). { apply Ascii_as_OT.cmp_eq. trivial. }
         rewrite Heqc in X. discriminate.
      }
      rewrite<- Ascii_as_OT.cmp_lt_nat in *. rewrite Heqc in *. discriminate.
    }
  Qed.

  Local Lemma compare_helper_lt {a b : string} (L : cmp a b = Lt):
    lt a b.
  Proof.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_gt {a b : string} (G : cmp a b = Gt):
    lt b a.
  Proof.
    rewrite cmp_antisym in G.
    rewrite CompOpp_iff in G.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_eq {a b : string} (E : cmp a b = Eq):
    a = b.
  Proof.
    now apply cmp_eq.
  Qed.

  Definition compare (a b : string) : Compare lt eq a b :=
    match cmp a b as z return _ = z -> _ with
    | Lt => fun E => LT (compare_helper_lt E)
    | Gt => fun E => GT (compare_helper_gt E)
    | Eq => fun E => EQ (compare_helper_eq E)
    end Logic.eq_refl.

  Definition eq_dec (x y : string): {x = y} + { ~ (x = y)} := string_dec x y.
End String_as_OT.
