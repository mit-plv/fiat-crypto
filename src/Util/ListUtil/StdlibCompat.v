(* Compat file for newer results from the stdlib *)
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Module Export List.
  Section Facts.

    Variable A : Type.

    (** *** Generic facts *)

    (** Destruction *)

    (** *** Head and tail *)
    (**************************)
    (** *** Facts about [app] *)
    (**************************)

    Lemma elt_eq_unit l1 l2 (a b : A) :
      l1 ++ a :: l2 = [b] -> a = b /\ l1 = [] /\ l2 = [].
    Proof using Type.
      intros Heq.
      apply app_eq_unit in Heq.
      now destruct Heq as [[Heq1 Heq2]|[Heq1 Heq2]]; inversion_clear Heq2.
    Qed.

    Theorem app_eq_app X (x1 x2 y1 y2: list X) : x1++x2 = y1++y2 ->
                                                 exists l, (x1 = y1++l /\ y2 = l++x2) \/ (y1 = x1++l /\ x2 = l++y2).
    Proof using Type.
      revert y1. induction x1 as [|a x1 IH].
      - cbn. intros y1 ->. exists y1. now right.
      - intros [|b y1]; cbn.
        + intros <-. exists (a :: x1). now left.
        + intros [=-> [l Hl] %IH]. exists l.
          now destruct Hl as [[-> ->]|[-> ->]]; [left|right].
    Qed.

    Lemma app_inj_tail_iff :
      forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] <-> x = y /\ a = b.
    Proof using Type.
      intros. now split; [apply app_inj_tail|intros [-> ->]].
    Qed.

    (** Compatibility with other operations *)

    Lemma last_length : forall (l : list A) a, length (l ++ a :: nil) = S (length l).
    Proof using Type.
      intros ; rewrite app_length ; simpl.
      rewrite Nat.add_succ_r, Nat.add_0_r; reflexivity.
    Qed.

    Lemma app_inv_head_iff:
      forall l l1 l2 : list A, l ++ l1 = l ++ l2 <-> l1 = l2.
    Proof using Type.
      intro l; induction l as [|? l IHl]; split; intros H; simpl; auto.
      - apply IHl. inversion H. auto.
      - subst. auto.
    Qed.

    Lemma app_inv_tail_iff:
      forall l l1 l2 : list A, l1 ++ l = l2 ++ l <-> l1 = l2.
    Proof using Type.
      split; [apply app_inv_tail | now intros ->].
    Qed.

    (************************)
    (** *** Facts about [In] *)
    (************************)


    (** Characterization of [In] *)

    Lemma in_elt : forall (x:A) l1 l2, In x (l1 ++ x :: l2).
    Proof using Type.
      intros.
      apply in_or_app.
      right; left; reflexivity.
    Qed.

    Lemma in_elt_inv : forall (x y : A) l1 l2,
        In x (l1 ++ y :: l2) -> x = y \/ In x (l1 ++ l2).
    Proof using Type.
      intros x y l1 l2 Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin|[Hin|Hin]]; [right|left|right]; try apply in_or_app; intuition.
    Qed.

  End Facts.

  (*******************************************)
  (** * Operations on the elements of a list *)
  (*******************************************)

  Section Elts.

    Variable A : Type.

    (*****************************)
    (** ** Nth element of a list *)
    (*****************************)


    (** Results about [nth] *)

    Lemma app_nth2_plus : forall l l' d n,
        @nth A (length l + n) (l ++ l') d = nth n l' d.
    Proof using Type.
      intros.
      now rewrite app_nth2, Nat.add_comm, Nat.add_sub; [|apply Nat.le_add_r].
    Qed.

    Lemma nth_middle : forall l l' a d,
        @nth A (length l) (l ++ a :: l') d = a.
    Proof using Type.
      intros.
      rewrite <- Nat.add_0_r at 1.
      apply app_nth2_plus.
    Qed.

    Lemma nth_ext : forall l l' d d', length l = length l' ->
                                      (forall n, n < length l -> @nth A n l d = nth n l' d') -> l = l'.
    Proof using Type.
      intro l; induction l as [|a l IHl];
        intros l' d d' Hlen Hnth; destruct l' as [| b l'].
      - reflexivity.
      - inversion Hlen.
      - inversion Hlen.
      - change a with (nth 0 (a :: l) d).
        change b with (nth 0 (b :: l') d').
        rewrite Hnth; f_equal.
        + apply IHl with d d'; [ now inversion Hlen | ].
          intros n Hlen'; apply (Hnth (S n)).
          now apply (Nat.succ_lt_mono n (length l)).
        + simpl; apply Nat.lt_0_succ.
    Qed.

    (** Results about [nth_error] *)

    (** Results directly relating [nth] and [nth_error] *)

    (******************************)
    (** ** Last element of a list *)
    (******************************)

    (** [last l d] returns the last element of the list [l],
    or the default value [d] if [l] is empty. *)

    Lemma last_last : forall l a d, @last A (l ++ [a]) d = a.
    Proof using Type.
      intro l; induction l as [|? l IHl]; intros; [ reflexivity | ].
      simpl; rewrite IHl.
      destruct l; reflexivity.
    Qed.

    (** [removelast l] remove the last element of [l] *)

    Lemma removelast_last : forall l a, @removelast A (l ++ [a]) = l.
    Proof using Type.
      intros. rewrite removelast_app.
      - apply app_nil_r.
      - intros Heq; inversion Heq.
    Qed.


    (*****************)
    (** ** Remove    *)
    (*****************)

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Local Notation remove := (@remove A eq_dec).

    Lemma remove_cons : forall x l, remove x (x :: l) = remove x l.
    Proof using Type.
      intros x l; simpl; destruct (eq_dec x x); [ reflexivity | now exfalso ].
    Qed.

    Lemma remove_app : forall x l1 l2,
        remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
    Proof using Type.
      intros x l1; induction l1 as [|a l1 IHl1]; intros l2; simpl.
      - reflexivity.
      - destruct (eq_dec x a).
        + apply IHl1.
        + rewrite <- app_comm_cons; f_equal.
          apply IHl1.
    Qed.

    Lemma notin_remove: forall l x, ~ In x l -> remove x l = l.
    Proof using Type.
      intros l x; induction l as [|y l IHl]; simpl; intros Hnin.
      - reflexivity.
      - destruct (eq_dec x y); [subst|f_equal]; tauto.
    Qed.

    Lemma in_remove: forall l x y, In x (remove y l) -> In x l /\ x <> y.
    Proof using Type.
      intro l; induction l as [|z l IHl]; intros x y Hin.
      - inversion Hin.
      - simpl in Hin.
        destruct (eq_dec y z) as [Heq|Hneq]; subst; split.
        + right; now apply IHl with z.
        + intros Heq; revert Hin; subst; apply remove_In.
        + inversion Hin; subst; [left; reflexivity|right].
          now apply IHl with y.
        + destruct Hin as [Hin|Hin]; subst.
          * now intros Heq; apply Hneq.
          * intros Heq; revert Hin; subst; apply remove_In.
    Qed.

    Lemma in_in_remove : forall l x y, x <> y -> In x l -> In x (remove y l).
    Proof using Type.
      intro l; induction l as [|z l IHl]; simpl; intros x y Hneq Hin.
      - apply Hin.
      - destruct (eq_dec y z); subst.
        + destruct Hin.
          * exfalso; now apply Hneq.
          * now apply IHl.
        + simpl; destruct Hin; [now left|right].
          now apply IHl.
    Qed.

    Lemma remove_remove_comm : forall l x y,
        remove x (remove y l) = remove y (remove x l).
    Proof using Type.
      intro l; induction l as [| z l IHl]; simpl; intros x y.
      - reflexivity.
      - destruct (eq_dec y z); simpl; destruct (eq_dec x z); try rewrite IHl; auto.
        + subst; symmetry; apply remove_cons.
        + simpl; destruct (eq_dec y z); tauto.
    Qed.

    Lemma remove_remove_eq : forall l x, remove x (remove x l) = remove x l.
    Proof using Type. intros l x; now rewrite (notin_remove _ _ (remove_In eq_dec l x)). Qed.

    Lemma remove_length_le : forall l x, length (remove x l) <= length l.
    Proof using Type.
      intro l; induction l as [|y l IHl]; simpl; intros x; trivial.
      destruct (eq_dec x y); simpl.
      - rewrite IHl; constructor; reflexivity.
      - apply (proj1 (Nat.succ_le_mono _ _) (IHl x)).
    Qed.

    Lemma remove_length_lt : forall l x, In x l -> length (remove x l) < length l.
    Proof using Type.
      intro l; induction l as [|y l IHl]; simpl; intros x Hin.
      - contradiction Hin.
      - destruct Hin as [-> | Hin].
        + destruct (eq_dec x x); [|easy].
          apply Nat.lt_succ_r, remove_length_le.
        + specialize (IHl _ Hin); destruct (eq_dec x y); simpl; auto.
          now apply Nat.succ_lt_mono in IHl.
    Qed.


    (******************************************)
    (** ** Counting occurrences of an element *)
    (******************************************)

    (** Compatibility of count_occ with operations on list *)
    Local Notation count_occ := (@count_occ A eq_dec).

    Lemma count_occ_app l1 l2 x :
      count_occ (l1 ++ l2) x = count_occ l1 x + count_occ l2 x.
    Proof using Type.
      induction l1 as [ | h l1 IHl1]; cbn; trivial.
      now destruct (eq_dec h x); [ rewrite IHl1 | ].
    Qed.

    Lemma count_occ_elt_eq l1 l2 x y : x = y ->
                                       count_occ (l1 ++ x :: l2) y = S (count_occ (l1 ++ l2) y).
    Proof using Type.
      intros ->.
      rewrite ? count_occ_app; cbn.
      destruct (eq_dec y y) as [Heq | Hneq];
        [ apply Nat.add_succ_r | now contradiction Hneq ].
    Qed.

    Lemma count_occ_elt_neq l1 l2 x y : x <> y ->
                                        count_occ (l1 ++ x :: l2) y = count_occ (l1 ++ l2) y.
    Proof using Type.
      intros Hxy.
      rewrite ? count_occ_app; cbn.
      now destruct (eq_dec x y) as [Heq | Hneq]; [ contradiction Hxy | ].
    Qed.

    Lemma count_occ_bound x l : count_occ l x <= length l.
    Proof using Type.
      induction l as [|h l]; cbn; auto.
      destruct (eq_dec h x); [ apply (proj1 (Nat.succ_le_mono _ _)) | ]; intuition.
    Qed.

  End Elts.

  (*******************************)
  (** * Manipulating whole lists *)
  (*******************************)

  Section ListOps.

    Variable A : Type.

    (*************************)
    (** ** Reverse           *)
    (*************************)
    Local Notation rev := (@rev A).
    Lemma rev_eq_app : forall l l1 l2, rev l = l1 ++ l2 -> l = rev l2 ++ rev l1.
    Proof using Type.
      intros l l1 l2 Heq.
      rewrite <- (rev_involutive l), Heq.
      apply rev_app_distr.
    Qed.

    (*********************************************)
    (** Reverse Induction Principle on Lists     *)
    (*********************************************)

    (** Compatibility with other operations *)

    (**  An alternative tail-recursive definition for reverse *)

    (*************************)
    (** ** Concatenation     *)
    (*************************)

    Local Notation concat := (@concat A).

    Lemma in_concat : forall l y,
        In y (concat l) <-> exists x, In x l /\ In y x.
    Proof using Type.
      intro l; induction l as [|a l IHl]; simpl; intro y; split; intros H.
      contradiction.
      destruct H as (x,(H,_)); contradiction.
      destruct (in_app_or _ _ _ H) as [H0|H0].
      exists a; auto.
      destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
      exists x; auto.
      apply in_or_app.
      destruct H as (x,(H0,H1)); destruct H0.
      subst; auto.
      right; destruct (IHl y) as (_,H2); apply H2.
      exists x; auto.
    Qed.


    (***********************************)
    (** ** Decidable equality on lists *)
    (***********************************)

    Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

    Lemma count_occ_rev l x : count_occ eq_dec (rev l) x = count_occ eq_dec l x.
    Proof using Type.
      induction l as [|a l IHl]; trivial.
      cbn; rewrite count_occ_app, IHl; cbn.
      destruct (eq_dec a x); rewrite Nat.add_comm; reflexivity.
    Qed.

  End ListOps.

  (***************************************************)
  (** * Applying functions to the elements of a list *)
  (***************************************************)

  (************)
  (** ** Map  *)
  (************)

  Section Map.
    Variables (A : Type) (B : Type).
    Variable f : A -> B.

    Local Notation map := (@map A B f).

    Lemma nth_error_map : forall n l,
        nth_error (map l) n = option_map f (nth_error l n).
    Proof using Type.
      intro n. induction n as [|n IHn]; intro l.
      - now destruct l.
      - destruct l as [|? l]; [reflexivity|exact (IHn l)].
    Qed.

    Lemma map_last : forall l a,
        map (l ++ [a]) = (map l) ++ [f a].
    Proof using Type.
      intro l; induction l as [|a l IHl]; intros; [ reflexivity | ].
      simpl; rewrite IHl; reflexivity.
    Qed.

    Lemma map_eq_cons : forall l l' b,
        map l = b :: l' -> exists a tl, l = a :: tl /\ f a = b /\ map tl = l'.
    Proof using Type.
      intros l l' b Heq.
      destruct l as [|a l]; inversion_clear Heq.
      exists a, l; repeat split.
    Qed.

    Lemma map_eq_app  : forall l l1 l2,
        map l = l1 ++ l2 -> exists l1' l2', l = l1' ++ l2' /\ map l1' = l1 /\ map l2' = l2.
    Proof using Type.
      intro l; induction l as [|a l IHl]; simpl; intros l1 l2 Heq.
      - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
        exists nil, nil; repeat split.
      - destruct l1; simpl in Heq; inversion Heq as [[Heq2 Htl]].
        + exists nil, (a :: l); repeat split.
        + destruct (IHl _ _ Htl) as (l1' & l2' & ? & ? & ?); subst.
          exists (a :: l1'), l2'; repeat split.
    Qed.

    (** [map] and count of occurrences *)

  End Map.

  (*****************)
  (** ** Flat Map  *)
  (*****************)

  Section FlatMap.
    Variables (A : Type) (B : Type).
    Variable f : A -> list B.

    (** [flat_map] *)

    Local Notation flat_map := (@flat_map A B f).

    Lemma flat_map_app l1 l2 :
      flat_map (l1 ++ l2) = flat_map l1 ++ flat_map l2.
    Proof using Type.
      now rewrite !flat_map_concat_map, map_app, concat_app.
    Qed.

  End FlatMap.

  Lemma remove_concat A (eq_dec : forall x y : A, {x = y}+{x <> y}) : forall l x,
      remove eq_dec x (concat l) = flat_map (remove eq_dec x) l.
  Proof using Type.
    intros l x; induction l as [|? ? IHl]; [ reflexivity | simpl ].
    rewrite remove_app, IHl; reflexivity.
  Qed.

  Lemma flat_map_ext : forall (A B : Type)(f g : A -> list B),
      (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
  Proof using Type.
    intros A B f g Hext l.
    rewrite 2 flat_map_concat_map.
    now rewrite (map_ext _ g).
  Qed.

  Lemma nth_nth_nth_map A : forall (l : list A) n d ln dn, n < length ln \/ length l <= dn ->
                                                           nth (nth n ln dn) l d = nth n (map (fun x => nth x l d) ln) d.
  Proof using Type.
    intros l n d ln dn Hlen.
    rewrite <- (map_nth (fun m => nth m l d)).
    destruct Hlen.
    - apply nth_indep. now rewrite map_length.
    - now rewrite (nth_overflow l).
  Qed.


  (************************************)
  (** Left-to-right iterator on lists *)
  (************************************)

  (************************************)
  (** Right-to-left iterator on lists *)
  (************************************)

  (*************************************)
  (** ** Boolean operations over lists *)
  (*************************************)

  (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

  Section Filtering.
    Variables (A : Type).

    (** Remove by filtering *)

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Definition remove' (x : A) : list A -> list A :=
      filter (fun y => if eq_dec x y then false else true).

    Lemma remove_alt (x : A) (l : list A) : remove' x l = remove eq_dec x l.
    Proof using Type.
      induction l; [reflexivity|].
      simpl. now destruct eq_dec; [|f_equal].
    Qed.

    (** Counting occurrences by filtering *)

    Definition count_occ' (l : list A) (x : A) : nat :=
      length (filter (fun y => if eq_dec y x then true else false) l).

    Lemma count_occ_alt (l : list A) (x : A) :
      count_occ' l x = count_occ eq_dec l x.
    Proof using Type.
      unfold count_occ'. induction l; [reflexivity|].
      simpl. now destruct eq_dec; simpl; [f_equal|].
    Qed.

  End Filtering.


  (******************************************************)
  (** ** Operations on lists of pairs or lists of lists *)
  (******************************************************)

  (******************************)
  (** ** Set inclusion on list  *)
  (******************************)

  Section SetIncl.

    Variable A : Type.

    Local Notation incl := (@incl A).

    Lemma incl_nil_l : forall l, incl nil l.
    Proof using Type.
      intros l a Hin; inversion Hin.
    Qed.

    Lemma incl_l_nil : forall l, incl l nil -> l = nil.
    Proof using Type.
      intro l; destruct l as [|a l]; intros Hincl.
      - reflexivity.
      - exfalso; apply Hincl with a; simpl; auto.
    Qed.

    Lemma incl_cons_inv : forall (a:A) (l m:list A),
        incl (a :: l) m -> In a m /\ incl l m.
    Proof using Type.
      intros a l m Hi.
      split; [ | intros ? ? ]; apply Hi; simpl; auto.
    Qed.

    Lemma incl_app_app : forall l1 l2 m1 m2:list A,
        incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
    Proof using Type.
      intros.
      apply incl_app; [ apply incl_appl | apply incl_appr]; assumption.
    Qed.

    Lemma incl_app_inv : forall l1 l2 m : list A,
        incl (l1 ++ l2) m -> incl l1 m /\ incl l2 m.
    Proof using Type.
      intro l1; induction l1 as [|a l1 IHl1]; intros l2 m Hin; split; auto.
      - apply incl_nil_l.
      - intros b Hb; inversion_clear Hb; subst; apply Hin.
        + now constructor.
        + simpl; apply in_cons.
          apply incl_appl with l1; [ apply incl_refl | assumption ].
      - apply IHl1.
        now apply incl_cons_inv in Hin.
    Qed.

    Lemma incl_filter f l : incl (filter f l) l.
    Proof using Type. intros x Hin; now apply filter_In in Hin. Qed.

    Lemma remove_incl (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall l1 l2 x,
        incl l1 l2 -> incl (remove eq_dec x l1) (remove eq_dec x l2).
    Proof using Type.
      intros l1 l2 x Hincl y Hin.
      apply in_remove in Hin; destruct Hin as [Hin Hneq].
      apply in_in_remove; intuition.
    Qed.

  End SetIncl.

  Lemma incl_map A B (f : A -> B) l1 l2 : incl l1 l2 -> incl (map f l1) (map f l2).
  Proof using Type.
    intros Hincl x Hinx.
    destruct (proj1 (in_map_iff _ _ _) Hinx) as [y [<- Hiny]].
    now apply in_map, Hincl.
  Qed.

  #[global]
   Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
   incl_app incl_map: datatypes.


  (**************************************)
  (** * Cutting a list at some position *)
  (**************************************)

  Section Cutting.

    Variable A : Type.
    Local Notation firstn := (@firstn A).

    Lemma removelast_firstn_len : forall l,
        removelast l = firstn (pred (length l)) l.
    Proof using Type.
      intro l; induction l as [|a l IHl]; [ reflexivity | simpl ].
      destruct l; [ | rewrite IHl ]; reflexivity.
    Qed.

  End Cutting.

  Section CuttingMap.
    Variables A B : Type.
    Variable f : A -> B.

    Lemma firstn_map : forall n l,
        firstn n (map f l) = map f (firstn n l).
    Proof using Type.
      intro n; induction n; intros []; simpl; f_equal; trivial.
    Qed.

    Lemma skipn_map : forall n l,
        skipn n (map f l) = map f (skipn n l).
    Proof using Type.
      intro n; induction n; intros []; simpl; trivial.
    Qed.
  End CuttingMap.

  (**************************************************************)
  (** ** Combining pairs of lists of possibly-different lengths *)
  (**************************************************************)

  (**********************************************************************)
  (** ** Predicate for List addition/removal (no need for decidability) *)
  (**********************************************************************)

  (********************************)
  (** ** Lists without redundancy *)
  (********************************)

  Section ReDun.

    Variable A : Type.

    Local Notation NoDup := (@NoDup A).
    Lemma NoDup_rev l : NoDup l -> NoDup (rev l).
    Proof using Type.
      induction l as [|a l IHl]; simpl; intros Hnd; [ constructor | ].
      inversion_clear Hnd as [ | ? ? Hnin Hndl ].
      assert (Add a (rev l) (rev l ++ a :: nil)) as Hadd
          by (rewrite <- (app_nil_r (rev l)) at 1; apply Add_app).
      apply NoDup_Add in Hadd; apply Hadd; intuition.
      now apply Hnin, in_rev.
    Qed.

    Lemma NoDup_filter f l : NoDup l -> NoDup (filter f l).
    Proof using Type.
      induction l as [|a l IHl]; simpl; intros Hnd; auto.
      apply NoDup_cons_iff in Hnd.
      destruct (f a); [ | intuition ].
      apply NoDup_cons_iff; split; [intro H|]; intuition.
      apply filter_In in H; intuition.
    Qed.

    (** Effective computation of a list without duplicates *)

    Hypothesis decA: forall x y : A, {x = y} + {x <> y}.

    Local Notation nodup := (@nodup A decA).

    Lemma nodup_incl l1 l2 : incl l1 (nodup l2) <-> incl l1 l2.
    Proof using Type.
      split; intros Hincl a Ha; eapply nodup_In; intuition.
    Qed.

    Lemma NoDup_incl_NoDup (l l' : list A) : NoDup l ->
                                             length l' <= length l -> incl l l' -> NoDup l'.
    Proof using Type.
      revert l'; induction l as [|a l IHl]; simpl; intros l' Hnd Hlen Hincl.
      - now destruct l'; inversion Hlen.
      - assert (In a l') as Ha by now apply Hincl; left.
        apply in_split in Ha as [l1' [l2' ->]].
        inversion_clear Hnd as [|? ? Hnin Hnd'].
        apply (NoDup_Add (Add_app a l1' l2')); split.
        + apply IHl; auto.
          * rewrite app_length.
            rewrite app_length in Hlen; simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
            now apply Nat.succ_le_mono.
          * apply (incl_Add_inv (u:= l1' ++ l2')) in Hincl; auto.
            apply Add_app.
        + intros Hnin'.
          assert (incl (a :: l) (l1' ++ l2')) as Hincl''.
          { apply incl_tran with (l1' ++ a :: l2'); auto.
            intros x Hin.
            apply in_app_or in Hin as [Hin|[->|Hin]]; intuition; apply in_or_app; intuition. }
          apply NoDup_incl_length in Hincl''; [ | now constructor ].
          apply (Nat.nle_succ_diag_l (length l1' + length l2')).
          rewrite_all app_length.
          simpl in Hlen; rewrite Nat.add_succ_r in Hlen.
          now transitivity (S (length l)).
    Qed.

  End ReDun.

  (** NoDup and map *)

  (** NB: the reciprocal result holds only for injective functions,
    see FinFun.v *)

  (***********************************)
  (** ** Sequence of natural numbers *)
  (***********************************)

  Section NatSeq.

    (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

    Lemma cons_seq : forall len start, start :: seq (S start) len = seq start (S len).
    Proof using Type.
      reflexivity.
    Qed.

    Lemma seq_S : forall len start, seq start (S len) = seq start len ++ [start + len].
    Proof using Type.
      intros len start.
      change [start + len] with (seq (start + len) 1).
      rewrite <- seq_app.
      rewrite Nat.add_succ_r, Nat.add_0_r; reflexivity.
    Qed.

  End NatSeq.

  Section Exists_Forall.

    (** * Existential and universal predicates over lists *)

    Variable A:Type.

    Section One_predicate.

      Variable P:A->Prop.

      #[local]
       Hint Constructors Exists : core.

      Local Notation Exists := (@Exists A P).

      Lemma Exists_nth l :
        Exists l <-> exists i d, i < length l /\ P (nth i l d).
      Proof using Type.
        split.
        - intros HE; apply Exists_exists in HE.
          destruct HE as [a [Hin HP]].
          apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
          rewrite <- Heq in HP.
          now exists i; exists a.
                     - intros [i [d [Hl HP]]].
                       apply Exists_exists; exists (nth i l d); split.
                       apply nth_In; assumption.
                       assumption.
      Qed.

      Lemma Exists_app l1 l2 :
        Exists (l1 ++ l2) <-> Exists l1 \/ Exists l2.
      Proof using Type.
        induction l1; simpl; split; intros HE; try now intuition.
        - inversion_clear HE; intuition.
        - destruct HE as [HE|HE]; intuition.
          inversion_clear HE; intuition.
      Qed.

      Lemma Exists_rev l : Exists l -> Exists (rev l).
      Proof using Type.
        induction l; intros HE; intuition.
        inversion_clear HE; simpl; apply Exists_app; intuition.
      Qed.

      Lemma Exists_fold_right l :
        Exists l <-> fold_right (fun x => or (P x)) False l.
      Proof using Type.
        induction l; simpl; split; intros HE; try now inversion HE; intuition.
      Qed.

      Lemma incl_Exists l1 l2 : incl l1 l2 -> Exists l1 -> Exists l2.
      Proof using Type.
        intros Hincl HE.
        apply Exists_exists in HE; destruct HE as [a [Hin HP]].
        apply Exists_exists; exists a; intuition.
      Qed.

      #[local]
       Hint Constructors Forall : core.

      Local Notation Forall := (@Forall A P).

      Lemma Forall_nil_iff : Forall [] <-> True.
      Proof using Type.
        easy.
      Qed.

      Lemma Forall_cons_iff : forall (a:A) l, Forall (a :: l) <-> P a /\ Forall l.
      Proof using Type.
        intros. now split; [intro H; inversion H|constructor].
      Qed.

      Lemma Forall_nth l :
        Forall l <-> forall i d, i < length l -> P (nth i l d).
      Proof using Type.
        split.
        - intros HF i d Hl.
          apply (Forall_forall P l).
          assumption.
          apply nth_In; assumption.
        - intros HF.
          apply Forall_forall; intros a Hin.
          apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
          rewrite <- Heq; intuition.
      Qed.

      Lemma Forall_app l1 l2 :
        Forall (l1 ++ l2) <-> Forall l1 /\ Forall l2.
      Proof using Type.
        induction l1 as [|a l1 IH]; cbn.
        - now rewrite Forall_nil_iff.
        - now rewrite !Forall_cons_iff, IH, and_assoc.
      Qed.

      Lemma Forall_elt a l1 l2 : Forall (l1 ++ a :: l2) -> P a.
      Proof using Type.
        intros HF; apply Forall_app in HF; destruct HF as [HF1 HF2]; now inversion HF2.
      Qed.

      Lemma Forall_rev l : Forall l -> Forall (rev l).
      Proof using Type.
        induction l; intros HF; [assumption|].
        inversion_clear HF; simpl; apply Forall_app; intuition.
      Qed.

      Lemma Forall_fold_right l :
        Forall l <-> fold_right (fun x => and (P x)) True l.
      Proof using Type.
        induction l; simpl; split; intros HF; try now inversion HF; intuition.
      Qed.

      Lemma incl_Forall l1 l2 : incl l2 l1 -> Forall l1 -> Forall l2.
      Proof using Type.
        intros Hincl HF.
        apply Forall_forall; intros a Ha.
        apply (Forall_forall P l1); intuition.
      Qed.

    End One_predicate.

    Lemma map_ext_Forall B : forall (f g : A -> B) l,
        Forall (fun x => f x = g x) l -> map f l = map g l.
    Proof using Type.
      intros; apply map_ext_in, Forall_forall; assumption.
    Qed.

    Lemma Exists_or : forall (P Q : A -> Prop) l,
        Exists P l \/ Exists Q l -> Exists (fun x => P x \/ Q x) l.
    Proof using Type.
      intros P Q l; induction l as [|a l IHl]; intros [H | H]; inversion H; subst.
      1,3: apply Exists_cons_hd; auto.
      all: apply Exists_cons_tl, IHl; auto.
    Qed.

    Lemma Exists_or_inv : forall (P Q : A -> Prop) l,
        Exists (fun x => P x \/ Q x) l -> Exists P l \/ Exists Q l.
    Proof using Type.
      intros P Q l; induction l as [|a l IHl];
        intro Hl; inversion Hl as [ ? ? H | ? ? H ]; subst.
      - inversion H; now repeat constructor.
      - destruct (IHl H); now repeat constructor.
    Qed.

    Lemma Forall_and : forall (P Q : A -> Prop) l,
        Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
    Proof using Type.
      intros P Q l; induction l; intros HP HQ; constructor; inversion HP; inversion HQ; auto.
    Qed.

    Lemma Forall_and_inv : forall (P Q : A -> Prop) l,
        Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
    Proof using Type.
      intros P Q l; induction l; intro Hl; split; constructor; inversion Hl; firstorder.
    Qed.

    Lemma incl_Forall_in_iff l l' :
      incl l l' <-> @Forall A (fun x => In x l') l.
    Proof using Type. now rewrite Forall_forall; split. Qed.

  End Exists_Forall.

  Lemma Exists_map A B (f : A -> B) P l :
    Exists P (map f l) <-> Exists (fun x => P (f x)) l.
  Proof using Type.
    induction l as [|a l IHl].
    - cbn. now rewrite Exists_nil.
    - cbn. now rewrite ?Exists_cons, IHl.
  Qed.

  Lemma Exists_concat A P (ls : list (list A)) :
    Exists P (concat ls) <-> Exists (Exists P) ls.
  Proof using Type.
    induction ls as [|l ls IHls].
    - cbn. now rewrite Exists_nil.
    - cbn. now rewrite Exists_app, Exists_cons, IHls.
  Qed.

  Lemma Exists_flat_map A B P ls (f : A -> list B) :
    Exists P (flat_map f ls) <-> Exists (fun d => Exists P (f d)) ls.
  Proof using Type.
    now rewrite flat_map_concat_map, Exists_concat, Exists_map.
  Qed.

  Lemma Forall_map A B (f : A -> B) P l :
    Forall P (map f l) <-> Forall (fun x => P (f x)) l.
  Proof using Type.
    induction l as [|a l IHl]; cbn.
    - now rewrite !Forall_nil_iff.
    - now rewrite !Forall_cons_iff, IHl.
  Qed.

  Lemma Forall_concat A P (ls : list (list A)) :
    Forall P (concat ls) <-> Forall (Forall P) ls.
  Proof using Type.
    induction ls as [|l ls IHls]; cbn.
    - now rewrite !Forall_nil_iff.
    - now rewrite Forall_app, Forall_cons_iff, IHls.
  Qed.

  Lemma Forall_flat_map A B P ls (f : A -> list B) :
    Forall P (flat_map f ls) <-> Forall (fun d => Forall P (f d)) ls.
  Proof using Type.
    now rewrite flat_map_concat_map, Forall_concat, Forall_map.
  Qed.

  Lemma exists_Forall A B : forall (P : A -> B -> Prop) l,
      (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l.
  Proof using Type.
    intros P l; induction l as [|a l IHl]; intros [k HF]; constructor; inversion_clear HF.
    - now exists k.
                 - now apply IHl; exists k.
  Qed.

  Lemma Forall_image A B : forall (f : A -> B) l,
      Forall (fun y => exists x, y = f x) l <-> exists l', l = map f l'.
  Proof using Type.
    intros f l; induction l as [|a l IHl]; split; intros HF.
    - exists nil; reflexivity.
    - constructor.
    - apply Forall_cons_iff in HF as [[x ->] [l' ->] %IHl].
      now exists (x :: l').
                 - destruct HF as [l' Heq].
                   symmetry in Heq; apply map_eq_cons in Heq.
                   destruct Heq as (x & tl & ? & ? & ?); subst.
                   constructor.
                   + now exists x.
                                + now apply IHl; exists tl.
  Qed.

  Lemma concat_nil_Forall A : forall (l : list (list A)),
      concat l = nil <-> Forall (fun x => x = nil) l.
  Proof using Type.
    intro l; induction l as [|a l IHl]; simpl; split; intros Hc; auto.
    - apply app_eq_nil in Hc.
      constructor; firstorder.
    - inversion Hc; subst; simpl.
      now apply IHl.
  Qed.

  Lemma in_flat_map_Exists A B : forall (f : A -> list B) x l,
      In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
  Proof using Type.
    intros f x l; rewrite in_flat_map.
    split; apply Exists_exists.
  Qed.

  Lemma notin_flat_map_Forall A B : forall (f : A -> list B) x l,
      ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
  Proof using Type.
    intros f x l; rewrite Forall_Exists_neg.
    apply not_iff_compat, in_flat_map_Exists.
  Qed.

  Section Repeat.

    Variable A : Type.
    Local Notation repeat := (@repeat A).
    Lemma repeat_cons n a :
      a :: repeat a n = repeat a n ++ (a :: nil).
    Proof using Type.
      induction n as [|n IHn]; simpl.
      - reflexivity.
      - f_equal; apply IHn.
    Qed.

    Lemma repeat_app x n m :
      repeat x (n + m) = repeat x n ++ repeat x m.
    Proof using Type.
      induction n as [|n IHn]; simpl; auto.
      now rewrite IHn.
    Qed.

    Lemma repeat_eq_app x n l1 l2 :
      repeat x n = l1 ++ l2 -> repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
    Proof using Type.
      revert n; induction l1 as [|a l1 IHl1]; simpl; intros n Hr; subst.
      - repeat split; now rewrite repeat_length.
      - destruct n; inversion Hr as [ [Heq Hr0] ]; subst.
        now apply IHl1 in Hr0 as [-> ->].
    Qed.

    Lemma repeat_eq_cons x y n l :
      repeat x n = y :: l -> x = y /\ repeat x (pred n) = l.
    Proof using Type.
      intros Hr.
      destruct n; inversion_clear Hr; auto.
    Qed.

    Lemma repeat_eq_elt x y n l1 l2 :
      repeat x n = l1 ++ y :: l2 -> x = y /\ repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
    Proof using Type.
      intros Hr; apply repeat_eq_app in Hr as [Hr1 Hr2]; subst.
      apply repeat_eq_cons in Hr2; intuition.
    Qed.

    Lemma Forall_eq_repeat x l :
      Forall (eq x) l -> l = repeat x (length l).
    Proof using Type.
      induction l as [|a l IHl]; simpl; intros HF; auto.
      inversion_clear HF as [ | ? ? ? HF']; subst.
      now rewrite (IHl HF') at 1.
    Qed.

    Hypothesis decA : forall x y : A, {x = y}+{x <> y}.

    Lemma count_occ_repeat_eq x y n : x = y -> count_occ decA (repeat y n) x = n.
    Proof using Type.
      intros ->.
      induction n; cbn; auto.
      destruct (decA y y); auto.
      exfalso; intuition.
    Qed.

    Lemma count_occ_repeat_neq x y n : x <> y -> count_occ decA (repeat y n) x = 0.
    Proof using Type.
      intros Hneq.
      induction n; cbn; auto.
      destruct (decA y x); auto.
      exfalso; intuition.
    Qed.

    Lemma count_occ_unique x l : count_occ decA l x = length l -> l = repeat x (length l).
    Proof using Type.
      induction l as [|h l]; cbn; intros Hocc; auto.
      destruct (decA h x).
      - f_equal; intuition.
      - assert (Hb := count_occ_bound decA x l).
        rewrite Hocc in Hb.
        exfalso; apply (Nat.nle_succ_diag_l _ Hb).
    Qed.

    Lemma count_occ_repeat_excl x l :
      (forall y, y <> x -> count_occ decA l y = 0) -> l = repeat x (length l).
    Proof using Type.
      intros Hocc.
      apply Forall_eq_repeat, Forall_forall; intros z Hin.
      destruct (decA z x) as [Heq|Hneq]; auto.
      apply Hocc, count_occ_not_In in Hneq; intuition.
    Qed.

    Lemma count_occ_sgt l x : l = x :: nil <->
                                count_occ decA l x = 1 /\ forall y, y <> x -> count_occ decA l y = 0.
    Proof using Type.
      split.
      - intros ->; cbn; split; intros; destruct decA; subst; intuition.
      - intros [Heq Hneq].
        apply count_occ_repeat_excl in Hneq.
        rewrite Hneq, count_occ_repeat_eq in Heq; trivial.
        now rewrite Heq in Hneq.
    Qed.

    Lemma nth_repeat a m n :
      nth n (repeat a m) a = a.
    Proof using Type.
      revert n. induction m as [|m IHm].
      - now intros [|n].
      - intros [|n]; [reflexivity|exact (IHm n)].
    Qed.

    Lemma nth_error_repeat a m n :
      n < m -> nth_error (repeat a m) n = Some a.
    Proof using Type.
      intro Hnm. rewrite (nth_error_nth' _ a).
      - now rewrite nth_repeat.
      - now rewrite repeat_length.
    Qed.

  End Repeat.

  Lemma repeat_to_concat A n (a:A) :
    repeat a n = concat (repeat [a] n).
  Proof using Type.
    induction n as [|n IHn]; simpl.
    - reflexivity.
    - f_equal; apply IHn.
  Qed.


  (** Sum of elements of a list of [nat]: [list_sum] *)

  Definition list_sum l := fold_right plus 0 l.

  Lemma list_sum_app : forall l1 l2,
      list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
  Proof using Type.
    intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
    simpl; rewrite IHl1.
    apply Nat.add_assoc.
  Qed.

  (** Max of elements of a list of [nat]: [list_max] *)

  Definition list_max l := fold_right max 0 l.

  Lemma list_max_app : forall l1 l2,
      list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
  Proof using Type.
    intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
    now simpl; rewrite IHl1, Nat.max_assoc.
  Qed.

  Lemma list_max_le : forall l n,
      list_max l <= n <-> Forall (fun k => k <= n) l.
  Proof using Type.
    intro l; induction l as [|a l IHl]; simpl; intros n; split.
    - now intros.
    - intros. now apply Nat.le_0_l.
    - intros [? ?] %Nat.max_lub_iff. now constructor; [|apply IHl].
    - now rewrite Forall_cons_iff, <- IHl, Nat.max_lub_iff.
  Qed.

  Lemma list_max_lt : forall l n, l <> nil ->
                                  list_max l < n <-> Forall (fun k => k < n) l.
  Proof using Type.
    intro l; induction l as [|a l IHl]; simpl; intros n Hnil; split; intros H; intuition.
    - destruct l.
      + repeat constructor.
        now simpl in H; rewrite Nat.max_0_r in H.
      + apply Nat.max_lub_lt_iff in H.
        now constructor; [ | apply IHl ].
    - destruct l; inversion_clear H as [ | ? ? Hlt HF ].
      + now simpl; rewrite Nat.max_0_r.
      + apply IHl in HF.
        * now apply Nat.max_lub_lt_iff.
        * intros Heq; inversion Heq.
  Qed.
End List.

From Coq Require Import List Setoid Compare_dec Morphisms FinFun PeanoNat.
Import ListNotations. (* For notations [] and [a;b;c] *)
Module Export Sorting.
  Module Export Permutation.
    (************************************************************************)
    (*         *   The Coq Proof Assistant / The Coq Development Team       *)
    (*  v      *         Copyright INRIA, CNRS and contributors             *)
    (* <O___,, * (see version control and CREDITS file for authors & dates) *)
    (*   \VV/  **************************************************************)
    (*    //   *    This file is distributed under the terms of the         *)
    (*         *     GNU Lesser General Public License Version 2.1          *)
    (*         *     (see LICENSE file for the text of the license)         *)
    (************************************************************************)

    (*********************************************************************)
    (** * List permutations as a composition of adjacent transpositions  *)
    (*********************************************************************)

    (* Adapted in May 2006 by Jean-Marc Notin from initial contents by
   Laurent Théry (Huffmann contribution, October 2003) *)

    (* Set Universe Polymorphism. *)


    (* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

    Local Hint Resolve perm_swap perm_trans : core.
    Local Hint Resolve Permutation_sym Permutation_trans : core.

    (* This provides reflexivity, symmetry and transitivity and rewriting
   on morphims to come *)

    Lemma Permutation_morph_transp A : forall P : list A -> Prop,
        (forall a b l1 l2, P (l1 ++ a :: b :: l2) -> P (l1 ++ b :: a :: l2)) ->
        Proper (@Permutation A ==> Basics.impl) P.
    Proof using Type.
      intros P HT l1 l2 HP.
      enough (forall l0, P (l0 ++ l1) -> P (l0 ++ l2)) as IH
          by (intro; rewrite <- (app_nil_l l2); now apply (IH nil)).
      induction HP; intuition.
      rewrite <- (app_nil_l l'), app_comm_cons, app_assoc.
      now apply IHHP; rewrite <- app_assoc.
    Qed.

    Section Permutation_properties.

      Variable A B:Type.

      Implicit Types a b : A.
      Implicit Types l m : list A.

      (** Compatibility with others operations on lists *)

      Local Hint Resolve Permutation_app_comm : core.

      Lemma Permutation_app_rot : forall l1 l2 l3: list A,
          Permutation (l1 ++ l2 ++ l3) (l2 ++ l3 ++ l1).
      Proof using Type.
        intros l1 l2 l3; now rewrite (app_assoc l2).
      Qed.
      Local Hint Resolve Permutation_app_rot : core.

      Lemma Permutation_app_swap_app : forall l1 l2 l3: list A,
          Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
      Proof using Type.
        intros.
        rewrite 2 app_assoc.
        apply Permutation_app_tail, Permutation_app_comm.
      Qed.
      Local Hint Resolve Permutation_app_swap_app : core.

      Lemma Permutation_app_middle : forall l l1 l2 l3 l4,
          Permutation (l1 ++ l2) (l3 ++ l4) ->
          Permutation (l1 ++ l ++ l2) (l3 ++ l ++ l4).
      Proof using Type.
        intros l l1 l2 l3 l4 HP.
        now rewrite Permutation_app_swap_app, HP, Permutation_app_swap_app.
      Qed.

      Local Hint Resolve Permutation_cons_app : core.
      Local Hint Resolve Permutation_middle : core.

      Lemma Permutation_middle2 : forall l1 l2 l3 a b,
          Permutation (a :: b :: l1 ++ l2 ++ l3) (l1 ++ a :: l2 ++ b :: l3).
      Proof using Type.
        intros l1 l2 l3 a b.
        apply Permutation_cons_app.
        rewrite 2 app_assoc.
        now apply Permutation_cons_app.
      Qed.
      Local Hint Resolve Permutation_middle2 : core.

      Lemma Permutation_elt : forall l1 l2 l1' l2' (a:A),
          Permutation (l1 ++ l2) (l1' ++ l2') ->
          Permutation (l1 ++ a :: l2) (l1' ++ a :: l2').
      Proof using Type.
        intros l1 l2 l1' l2' a HP.
        transitivity (a :: l1 ++ l2); auto.
      Qed.

      Global Instance Permutation_Forall (P : A -> Prop) :
        Proper ((@Permutation A) ==> Basics.impl) (Forall P).
      Proof using Type.
        intros l1 l2 HP.
        induction HP; intro HF; auto.
        - inversion_clear HF; auto.
        - inversion_clear HF as [ | ? ? HF1 HF2].
          inversion_clear HF2; auto.
      Qed.

      Global Instance Permutation_Exists (P : A -> Prop) :
        Proper ((@Permutation A) ==> Basics.impl) (Exists P).
      Proof using Type.
        intros l1 l2 HP.
        induction HP; intro HF; auto.
        - inversion_clear HF; auto.
        - inversion_clear HF as [ | ? ? HF1 ]; auto.
          inversion_clear HF1; auto.
      Qed.

      Lemma Permutation_Forall2 (P : A -> B -> Prop) :
        forall l1 l1' (l2 : list B), Permutation l1 l1' -> Forall2 P l1 l2 ->
                                     exists l2' : list B, Permutation l2 l2' /\ Forall2 P l1' l2'.
      Proof using Type.
        intros l1 l1' l2 HP.
        revert l2; induction HP; intros l2 HF; inversion HF as [ | ? b ? ? HF1 HF2 ]; subst.
        - now exists nil.
                     - apply IHHP in HF2 as [l2' [HP2 HF2]].
                       exists (b :: l2'); auto.
                     - inversion_clear HF2 as [ | ? b' ? l2' HF3 HF4 ].
                       exists (b' :: b :: l2'); auto.
                     - apply Permutation_nil in HP1; subst.
                       apply Permutation_nil in HP2; subst.
                       now exists nil.
                                  - apply IHHP1 in HF as [l2' [HP2' HF2']].
                                    apply IHHP2 in HF2' as [l2'' [HP2'' HF2'']].
                                    exists l2''; split; auto.
                                    now transitivity l2'.
      Qed.

      Ltac InvAdd := repeat (match goal with
                             | H: Add ?x _ (_ :: _) |- _ => inversion H; clear H; subst
                             end).

      Ltac finish_basic_perms H :=
        try constructor; try rewrite perm_swap; try constructor; trivial;
        (rewrite <- H; now apply Permutation_Add) ||
                                                  (rewrite H; symmetry; now apply Permutation_Add).

      Lemma Permutation_app_inv_m l l1 l2 l3 l4 :
        Permutation (l1 ++ l ++ l2) (l3 ++ l ++ l4) ->
        Permutation (l1 ++ l2) (l3 ++ l4).
      Proof using Type.
        intros HP.
        apply (Permutation_app_inv_l l).
        transitivity (l1 ++ l ++ l2); auto.
        transitivity (l3 ++ l ++ l4); auto.
      Qed.

      Lemma Permutation_vs_elt_inv : forall l l1 l2 a,
          Permutation l (l1 ++ a :: l2) -> exists l' l'', l = l' ++ a :: l''.
      Proof using Type.
        intros l l1 l2 a HP.
        symmetry in HP.
        apply (Permutation_in a), in_split in HP; trivial.
        apply in_elt.
      Qed.

      Lemma Permutation_vs_cons_inv : forall l l1 a,
          Permutation l (a :: l1) -> exists l' l'', l = l' ++ a :: l''.
      Proof using Type.
        intros l l1 a HP.
        rewrite <- (app_nil_l (a :: l1)) in HP.
        apply (Permutation_vs_elt_inv _ _ _ HP).
      Qed.

      Lemma Permutation_vs_cons_cons_inv : forall l l' a b,
          Permutation l (a :: b :: l') ->
          exists l1 l2 l3, l = l1 ++ a :: l2 ++ b :: l3 \/ l = l1 ++ b :: l2 ++ a :: l3.
      Proof using Type.
        intros l l' a b HP.
        destruct (Permutation_vs_cons_inv HP) as [l1 [l2]]; subst.
        symmetry in HP.
        apply Permutation_cons_app_inv in HP.
        apply (Permutation_in b), in_app_or in HP; [|now apply in_eq].
        destruct HP as [(l3 & l4 & ->)%in_split | (l3 & l4 & ->)%in_split].
        - exists l3, l4, l2; right.
          now rewrite <-app_assoc; simpl.
        - now exists l1, l3, l4; left.
      Qed.

      Lemma Permutation_repeat x n l :
        Permutation l (repeat x n) -> l = repeat x n.
      Proof using Type.
        revert n; induction l as [|y l IHl] ; simpl; intros n HP; auto.
        - now apply Permutation_nil in HP; inversion HP.
        - assert (y = x) as Heq by (now apply repeat_spec with n, (Permutation_in _ HP); left); subst.
          destruct n; simpl; simpl in HP.
          + symmetry in HP; apply Permutation_nil in HP; inversion HP.
          + f_equal; apply IHl.
            now apply Permutation_cons_inv with x.
      Qed.

      Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

      Lemma Permutation_count_occ l1 l2 :
        Permutation l1 l2 <-> forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x.
      Proof using Type.
        split.
        - induction 1 as [ | y l1 l2 HP IHP | y z l | l1 l2 l3 HP1 IHP1 HP2 IHP2 ];
            cbn; intros a; auto.
          + now rewrite IHP.
          + destruct (eq_dec y a); destruct (eq_dec z a); auto.
          + now rewrite IHP1, IHP2.
        - revert l2; induction l1 as [|y l1 IHl1]; cbn; intros l2 Hocc.
          + replace l2 with (@nil A); auto.
            symmetry; apply (count_occ_inv_nil eq_dec); intuition.
          + assert (exists l2' l2'', l2 = l2' ++ y :: l2'') as [l2' [l2'' ->]].
            { specialize (Hocc y).
              destruct (eq_dec y y); intuition.
              apply in_split, (count_occ_In eq_dec).
              rewrite <- Hocc; apply Nat.lt_0_succ. }
            apply Permutation_cons_app, IHl1.
            intros z; specialize (Hocc z); destruct (eq_dec y z) as [Heq | Hneq].
            * rewrite (count_occ_elt_eq _ _ _ Heq) in Hocc.
              now injection Hocc.
            * now rewrite (count_occ_elt_neq _ _ _ Hneq) in Hocc.
      Qed.

    End Permutation_properties.

    Section Permutation_map.

      Variable A B : Type.
      Variable f : A -> B.

      Lemma Permutation_map_inv : forall l1 l2,
          Permutation l1 (map f l2) -> exists l3, l1 = map f l3 /\ Permutation l2 l3.
      Proof using Type.
        induction l1; intros l2 HP.
        - exists nil; split; auto.
          apply Permutation_nil in HP.
          destruct l2; auto.
          inversion HP.
        - symmetry in HP.
          destruct (Permutation_vs_cons_inv HP) as [l3 [l4 Heq]].
          destruct (map_eq_app _ _ _ _ Heq) as [l1' [l2' [Heq1 [Heq2 Heq3]]]]; subst.
          destruct (map_eq_cons _ _ Heq3) as [b [l1'' [Heq1' [Heq2' Heq3']]]]; subst.
          rewrite map_app in HP; simpl in HP.
          symmetry in HP.
          apply Permutation_cons_app_inv in HP.
          rewrite <- map_app in HP.
          destruct (IHl1 _ HP) as [l3 [Heq1'' Heq2'']]; subst.
          exists (b :: l3); split; auto.
          symmetry in Heq2''; symmetry; apply (Permutation_cons_app _ _ _ Heq2'').
      Qed.

      Lemma Permutation_image : forall a l l',
          Permutation (a :: l) (map f l') -> exists a', a = f a'.
      Proof using Type.
        intros a l l' HP.
        destruct (Permutation_map_inv _ HP) as [l'' [Heq _]].
        destruct l'' as [ | a' l'']; inversion_clear Heq.
        now exists a'.
      Qed.

      Lemma Permutation_elt_map_inv: forall l1 l2 l3 l4 a,
          Permutation (l1 ++ a :: l2) (l3 ++ map f l4) -> (forall b, a <> f b) ->
          exists l1' l2', l3 = l1' ++ a :: l2'.
      Proof using Type.
        intros l1 l2 l3 l4 a HP Hf.
        apply (Permutation_in a), in_app_or in HP; [| now apply in_elt].
        destruct HP as [HP%in_split | (x & Heq & ?)%in_map_iff]; trivial; subst.
        now contradiction (Hf x).
      Qed.

      Global Instance Permutation_flat_map (g : A -> list B) :
        Proper ((@Permutation A) ==> (@Permutation B)) (flat_map g).
      Proof using Type.
        intros l1; induction l1; intros l2 HP.
        - now apply Permutation_nil in HP; subst.
        - symmetry in HP.
          destruct (Permutation_vs_cons_inv HP) as [l' [l'']]; subst.
          symmetry in HP.
          apply Permutation_cons_app_inv in HP.
          rewrite flat_map_app; simpl.
          rewrite <- (app_nil_l _).
          apply Permutation_app_middle; simpl.
          rewrite <- flat_map_app.
          apply (IHl1 _ HP).
      Qed.

    End Permutation_map.

    #[global]
     Instance Permutation_list_sum : Proper (@Permutation nat ==> eq) list_sum | 10.
    Proof using Type.
      intros l1 l2 HP; induction HP; simpl; intuition.
      - rewrite 2 (Nat.add_comm x).
        apply Nat.add_assoc.
      - now transitivity (list_sum l').
    Qed.

    #[global]
     Instance Permutation_list_max : Proper (@Permutation nat ==> eq) list_max | 10.
    Proof using Type.
      intros l1 l2 HP; induction HP; simpl; intuition.
      - rewrite 2 (Nat.max_comm x).
        apply Nat.max_assoc.
      - now transitivity (list_max l').
    Qed.

    Section Permutation_transp.

      Variable A:Type.

      (** Permutation definition based on transpositions for induction with fixed length *)
      Inductive Permutation_transp : list A -> list A -> Prop :=
      | perm_t_refl : forall l, Permutation_transp l l
      | perm_t_swap : forall x y l1 l2, Permutation_transp (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)
      | perm_t_trans l l' l'' :
        Permutation_transp l l' -> Permutation_transp l' l'' -> Permutation_transp l l''.

      Instance Permutation_transp_sym : Symmetric Permutation_transp.
      Proof using Type.
        intros l1 l2 HP; induction HP; subst; try (now constructor).
        now apply (perm_t_trans IHHP2).
      Qed.

      Global Instance Permutation_transp_equiv : Equivalence Permutation_transp | 100.
      Proof using Type.
        split.
        - intros l; apply perm_t_refl.
        - apply Permutation_transp_sym.
        - intros l1 l2 l3 ;apply perm_t_trans.
      Qed.

      Lemma Permutation_transp_cons : forall (x : A) l1 l2,
          Permutation_transp l1 l2 -> Permutation_transp (x :: l1) (x :: l2).
      Proof using Type.
        intros x l1 l2 HP.
        induction HP.
        - reflexivity.
        - rewrite 2 app_comm_cons.
          apply perm_t_swap.
        - now transitivity (x :: l').
      Qed.

      Lemma Permutation_Permutation_transp : forall l1 l2 : list A,
          Permutation l1 l2 <-> Permutation_transp l1 l2.
      Proof using Type.
        intros l1 l2; split; intros HP; induction HP; intuition; try now constructor.
        - now apply Permutation_transp_cons.
        - rewrite <- (app_nil_l (y :: _)).
          rewrite <- (app_nil_l (x :: y :: _)).
          apply perm_t_swap.
        - now transitivity l'.
        - apply Permutation_app_head.
          apply perm_swap.
        - now transitivity l'.
      Qed.

      Lemma Permutation_ind_transp : forall P : list A -> list A -> Prop,
          (forall l, P l l) ->
          (forall x y l1 l2, P (l1 ++ y :: x :: l2) (l1 ++ x :: y :: l2)) ->
          (forall l l' l'',
              Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
          forall l1 l2, Permutation l1 l2 -> P l1 l2.
      Proof using Type.
        intros P Hr Ht Htr l1 l2 HP; apply Permutation_Permutation_transp in HP.
        revert Hr Ht Htr; induction HP; intros Hr Ht Htr; auto.
        apply (Htr _ l'); intuition; now apply Permutation_Permutation_transp.
      Qed.

    End Permutation_transp.

    (* begin hide *)
    Notation Permutation_app_swap := Permutation_app_comm (only parsing).
    (* end hide *)
  End Permutation.
End Sorting.
