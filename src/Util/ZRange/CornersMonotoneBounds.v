Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Stabilization.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.

Local Open Scope Z_scope.

Module ZRange.
  Import Operations.ZRange.
  Local Arguments is_bounded_by' !_ _ _ / .
  Local Coercion is_true : bool >-> Sortclass.

  Fixpoint app' {A B} {n : nat} : nary_T A B (S n) -> tuple' A n -> B
    := match n with
       | O => fun f x => f x
       | S n => fun f '(xs, x) => @app' A B n (f x) xs
       end.
  Definition app {A B} {n : nat} : nary_T A B n -> tuple A n -> B
    := match n with
       | O => fun x _ => x
       | S n => @app' A B n
       end.

  Local Notation R b := (match b with true => Z.le | false => Basics.flip Z.le end).

  Local Notation Rp b := (match b with true => Pos.le | false => Basics.flip Pos.le end).

  Fixpoint is_monotone_on_projections {n : nat} : nary_T Z Z n -> Prop
    := match n with
       | O => fun _ => True
       | S n' => fun f
                => (forall x, is_monotone_on_projections (f x))
                  /\ (forall args, exists b, Proper (R b ==> Z.le) (fun x => app (f x) args))
       end.

  Fixpoint is_piecewise_monotone_on_projections {n : nat} : nary_T Z Z n -> Prop
    := match n with
       | O => fun _ => True
       | S n'
         => fun f
            => (forall x, is_piecewise_monotone_on_projections (f x))
               /\ (forall args, exists b, Proper (Rp b ==> Z.le) (fun x => app (f (Zpos x)) args))
               /\ (forall args, exists b, Proper (Rp b ==> Z.le) (fun x => app (f (Zneg x)) args))
       end.

  Definition all_are_bounded_by_bool {n} (v : tuple Z n) (v_bs : tuple zrange n) : bool
    := Tuple.fieldwiseb is_bounded_by_bool v v_bs.

  Local Ltac fast_split_min_max := rewrite ?Z.min_le_iff, ?Z.max_le_iff.

  Local Ltac t_fin_common_step :=
    first [ progress cbv [all_are_bounded_by_bool is_bounded_by_bool is_monotone_on_projections is_true is_tighter_than_bool] in *
          | progress cbv [Proper respectful Basics.flip] in *
          | progress cbn in *
          | progress rewrite ?Bool.orb_true_iff, ?Bool.orb_false_iff, ?Bool.andb_true_iff, ?Z.leb_le, ?Z.ltb_lt in *
          | progress Z.ltb_to_lt
          | progress fast_split_min_max
          | progress destruct_head'_and
          | progress destruct_head'_prod
          | progress destruct_head'_ex
          | progress specialize_by exact tt
          | progress specialize_by exact I
          | progress destruct_head' zrange
          | solve [ auto using or_introl, or_intror, Z.le_refl ]
          | match goal with
            | [ H : _ -> True |- _ ] => clear H
            | [ H : ?x <= ?x |- _ ] => clear H
            | [ H : ?x \/ ?x |- _ ] => assert x by (destruct H; assumption); clear H
            | [ H : ?x < ?x |- _ ] => exfalso; clear -H; lia
            | [ H : 0 <= Z.pos _ |- _ ] => clear H
            | [ H : 0 < Z.pos _ |- _ ] => clear H
            | [ H : Z.neg _ <= 0 |- _ ] => clear H
            | [ H : Z.neg _ < 0 |- _ ] => clear H
            | [ H : Z.pos _ <= Z.neg _ |- _ ] => exfalso; clear -H; lia
            | [ H : Z.pos _ <= 0 |- _ ] => exfalso; clear -H; lia
            | [ H : 0 <= Z.neg _ |- _ ] => exfalso; clear -H; lia
            | [ H : Z.pos _ < 0 |- _ ] => exfalso; clear -H; lia
            | [ |- context[Z.max 1 (Z.pos ?x)] ] => rewrite (Z.max_r 1 (Zpos x)) by (clear; lia)
            | [ |- context[Z.min 1 (Z.pos ?x)] ] => rewrite (Z.min_l 1 (Zpos x)) by (clear; lia)
            | [ H : ?x > ?y |- _ ] => assert (y < x) by (clear -H; lia); clear H
            | [ H : ?x >= ?y |- _ ] => assert (y <= x) by (clear -H; lia); clear H
            | [ |- context[Z.max (Z.neg ?x) (-1)] ] => rewrite (Z.max_r (Zneg x) (-1)) by (clear; lia)
            | [ |- context[Z.min (Z.neg ?x) (-1)] ] => rewrite (Z.min_l (Zneg x) (-1)) by (clear; lia)
            end ].
  Local Ltac t_fin_saturate_step :=
    first [ progress destruct_head'_bool
          | match goal with
            | [ H : forall (x : Z) (y : Z), _ <= _ -> _ <= _, v : Z |- _ ]
              => unique pose proof (H v v ltac:(reflexivity))
            | [ H : forall (x : Z) (y : Z), _ <= _ -> _ <= _, v : Z, v' : Z |- _ ]
              => unique pose proof (H v v' ltac:(auto || reflexivity))
            end
          | apply conj ].
  Local Ltac t_fin_specific_pos_step :=
    first [ match goal with
            | [ H : _ \/ _ |- _ ] => destruct H as [H|H]; try (exfalso; clear -H; lia); []
            | [ H : Z.pos _ <= ?v |- _ ] => is_var v; destruct v as [|v|v]; try (exfalso; clear -H; lia)
            | [ H : ?v <= Z.neg _ |- _ ] => is_var v; destruct v as [|v|v]; try (exfalso; clear -H; lia)
            | [ H : 0 <= ?v |- _ ] => is_var v; destruct v as [|v|v]; try (exfalso; clear -H; lia)
            | [ H : ?v <= 0 |- _ ] => is_var v; destruct v as [|v|v]; try (exfalso; clear -H; lia)
            | [ H : 0 < ?v |- _ ] => is_var v; destruct v as [|v|v]; try (exfalso; clear -H; lia)
            | [ H : ?v < 0 |- _ ] => is_var v; destruct v as [|v|v]; try (exfalso; clear -H; lia)
            end
          | break_innermost_match_step
          | progress destruct_head'_bool
          | match goal with
            | [ H' : Z.le (?f ?p) (?g ?q) |- _ ]
              => first [ unique assert (Pos.le p q) by (clear -H'; lia)
                       | unique assert (Pos.le q p) by (clear -H'; lia) ]
            | [ H : forall x y, Pos.le _ _ -> _ <= _, H' : Pos.le _ _ |- _ ]
              => unique pose proof (H _ _ H')
            | [ H : forall x y, Pos.le x _ -> _ <= _, v : positive |- _ ]
              => unique pose proof (H 1%positive v ltac:(clear; lia))
            | [ H : forall x y, Pos.le _ x -> _ <= _, v : positive |- _ ]
              => unique pose proof (H v 1%positive ltac:(clear; lia))
            end
          | apply conj
          | progress destruct_head' Z ].
  Local Ltac t_fin :=
    repeat first [ t_fin_common_step
                 | t_fin_saturate_step ].
  Local Ltac t_fin_pos :=
    repeat first [ t_fin_common_step
                 | t_fin_specific_pos_step ].

  Lemma pull_union_under_args2 A n f g bs
    : @app' A _ n (under_args2 union f g) bs
      = union (app' f bs) (app' g bs).
  Proof. induction n; t_fin. Qed.

  Lemma monotone_n_corners_genb
        n f
        (Hmonotone : @is_monotone_on_projections n f)
        v v_bs
        (Hboundedx : @all_are_bounded_by_bool n v v_bs)
    : is_bounded_by_bool (app f v) (app (n_corners f) v_bs).
  Proof.
    destruct n as [|n].
    { cbv [all_are_bounded_by_bool is_bounded_by_bool is_monotone_on_projections is_true] in *; cbn in *.
      rewrite Bool.andb_true_iff, Z.leb_le; split; reflexivity. }
    cbv [app tuple all_are_bounded_by_bool fieldwiseb] in *.
    induction n as [|n IHn].
    { t_fin. }
    { destruct v_bs as [ v_bs [l u] ], v as [vs v]; cbn [lower upper] in *.
      cbn [fieldwiseb' fst snd] in Hboundedx.
      cbv [is_true] in *.
      rewrite Bool.andb_true_iff in Hboundedx.
      destruct Hboundedx as [Hboundedx0 Hboundedx1].
      destruct Hmonotone as [Hmonotone0 Hmonotone1].
      specialize (fun x => IHn (f x) (Hmonotone0 _) vs v_bs Hboundedx0).
      cbn [app'].
      set (Sn := S n) in *.
      cbn [n_corners].
      set (f' := fun x => @n_corners Sn (f x)).
      lazymatch type of IHn with
      | forall x, is_bounded_by_bool (@?B x) (app' _ ?v_bs) = true
        => change (forall x, is_bounded_by_bool (B x) (app' (f' x) v_bs) = true) in IHn
      end; cbv beta in *.
      clearbody f'.
      cbn -[Sn] in *.
      rewrite pull_union_under_args2.
      cbv [is_bounded_by_bool app] in *.
      unfold Sn in Hmonotone1.
      setoid_rewrite Bool.andb_true_iff in IHn.
      rewrite ?Bool.andb_true_iff in *.
      setoid_rewrite Z.leb_le in IHn.
      rewrite !Z.leb_le in *.
      specialize (Hmonotone1 vs).
      destruct Hmonotone1 as [? Hmonotone1].
      clear -IHn Hboundedx1 Hmonotone1.
      cbn [lower upper] in *.
      destruct_head'_bool.
      all: split; etransitivity; [ | eapply Hmonotone1, Hboundedx1 | eapply Hmonotone1, Hboundedx1 | ].
      all: first [ etransitivity; [ eapply IHn | ] | etransitivity; [ | eapply IHn ] ].
      all: clear; t_fin. }
  Qed.

  Lemma monotone_n_corners_and_zero_genb
        n f
        (Hmonotone : @is_piecewise_monotone_on_projections n f)
        v v_bs
        (Hboundedx : @all_are_bounded_by_bool n v v_bs)
    : is_bounded_by_bool (app f v) (app (n_corners_and_zero f) v_bs).
  Proof.
    destruct n as [|n].
    { cbv [all_are_bounded_by_bool is_bounded_by_bool is_piecewise_monotone_on_projections is_true] in *; cbn in *.
      rewrite Bool.andb_true_iff, Z.leb_le; split; reflexivity. }
    cbv [app tuple all_are_bounded_by_bool fieldwiseb] in *.
    induction n as [|n IHn].
    { t_fin_pos. }
    { destruct v_bs as [ v_bs [l u] ], v as [vs v]; cbn [lower upper] in *.
      cbn [fieldwiseb' fst snd] in Hboundedx.
      cbv [is_true] in *.
      rewrite Bool.andb_true_iff in Hboundedx.
      destruct Hboundedx as [Hboundedx0 Hboundedx1].
      destruct Hmonotone as [Hmonotone0 [Hmonotone1 Hmonotone2] ].
      specialize (fun f pf => IHn f pf vs v_bs Hboundedx0).
      specialize (fun x => IHn (f x) (Hmonotone0 _)).
      cbn [app'].
      set (Sn := S n) in *.
      cbn [n_corners_and_zero].
      set (f' := fun x => @n_corners_and_zero Sn (f x)).
      lazymatch type of IHn with
      | forall x, is_bounded_by_bool (@?B x) (app' _ ?v_bs) = true
        => change (forall x, is_bounded_by_bool (B x) (app' (f' x) v_bs) = true) in IHn
      end; cbv beta in *.
      clearbody f'.
      cbn -[Sn] in *.
      cbv [is_bounded_by_bool app] in *.
      unfold Sn in Hmonotone1, Hmonotone2.
      setoid_rewrite Bool.andb_true_iff in IHn.
      rewrite ?Bool.andb_true_iff in *.
      setoid_rewrite Z.leb_le in IHn.
      rewrite !Z.leb_le in *.
      specialize (Hmonotone1 vs).
      specialize (Hmonotone2 vs).
      destruct Hmonotone1 as [? Hmonotone1].
      destruct Hmonotone2 as [? Hmonotone2].
      clear -IHn Hboundedx1 Hmonotone1 Hmonotone2.
      cbn [lower upper] in *.
      destruct l as [|l|l], u as [|u|u], v as [|v|v].
      all: try (exfalso; clear -Hboundedx1; lia).
      all: cbn -[Sn] in *.
      all: rewrite !pull_union_under_args2.
      all: cbv [union]; cbn [lower upper].
      all: repeat match goal with
                  | [ H : context[Zpos ?p <= Zpos ?q] |- _ ]
                    => unique assert (Pos.le p q) by lia
                  | [ H : context[Zneg ?p <= Zneg ?q] |- _ ]
                    => unique assert (Pos.le q p) by lia
                  end.
      all: destruct_head'_bool.
      all: first [ split; etransitivity;
                   [ | first [ eapply Hmonotone1 | eapply Hmonotone2 ];
                       first [ eassumption | eapply Pos.le_1_l ]
                     | first [ eapply Hmonotone1 | eapply Hmonotone2 ];
                       first [ eassumption | eapply Pos.le_1_l ] | ]
                 | split ].
      all: first [ etransitivity; [ eapply IHn | ] | etransitivity; [ | eapply IHn ] ].
      all: fast_split_min_max.
      all: auto using Z.le_refl.
      all: repeat t_fin_common_step. }
  Qed.


  Lemma monotone_two_corners_genb'
        (f : Z -> Z)
        (Hmonotone : exists b, Proper (R b ==> Z.le) f)
        x_bs x
        (Hboundedx : is_bounded_by_bool x x_bs)
    : is_tighter_than_bool (constant (f x)) (two_corners f x_bs).
  Proof.
    exact (@monotone_n_corners_genb 1 f (ltac:(repeat split; auto)) x x_bs Hboundedx).
  Qed.

  Lemma monotone_two_corners_and_zero_genb'
        (f : Z -> Z)
        (Hmonotonep : exists b, Proper (Rp b ==> Z.le) (fun x => f (Zpos x)))
        (Hmonotonen : exists b, Proper (Rp b ==> Z.le) (fun x => f (Zneg x)))
        x_bs x
        (Hboundedx : is_bounded_by_bool x x_bs)
    : is_tighter_than_bool (constant (f x)) (two_corners_and_zero f x_bs).
  Proof.
    unshelve eapply (@monotone_n_corners_and_zero_genb 1 f _ x x_bs Hboundedx).
    repeat split; auto.
  Qed.

  Lemma monotoneb_two_corners_gen
        (f : Z -> Z)
        (Hmonotone : Proper (Z.le ==> Z.le) f \/ Proper (Basics.flip Z.le ==> Z.le) f)
        x_bs x
        (Hboundedx : ZRange.is_bounded_by_bool x x_bs = true)
    : ZRange.is_bounded_by_bool (f x) (ZRange.two_corners f x_bs) = true.
  Proof.
    apply (fun pf => monotone_two_corners_genb' f pf _ _ Hboundedx).
    rewrite Bool.ex_bool_iff_or; auto.
  Qed.

  Lemma monotoneb_two_corners_and_zero_gen
        (f : Z -> Z)
        (Hmonotonep : Proper (Pos.le ==> Z.le) (fun x => f (Zpos x)) \/ Proper (Basics.flip Pos.le ==> Z.le) (fun x => f (Zpos x)))
        (Hmonotonen : Proper (Pos.le ==> Z.le) (fun x => f (Zneg x)) \/ Proper (Basics.flip Pos.le ==> Z.le) (fun x => f (Zneg x)))
        x_bs x
        (Hboundedx : ZRange.is_bounded_by_bool x x_bs = true)
    : ZRange.is_bounded_by_bool (f x) (ZRange.two_corners_and_zero f x_bs) = true.
  Proof.
    apply (fun pf1 pf2 => monotone_two_corners_and_zero_genb' f pf1 pf2 _ _ Hboundedx).
    all: rewrite Bool.ex_bool_iff_or; auto.
  Qed.

  Local Ltac t_fill :=
    intros; rewrite ?Bool.ex_bool_iff_or; auto;
    cbn in *; cbv [is_true] in *; rewrite ?Bool.andb_true_iff; intuition eauto.

  Local Ltac t_red :=
    cbv [eight_corners_and_zero four_corners_and_zero two_corners_and_zero n_corners_and_zero apply_to_split_range apply_to_split_range_under_args apply_to_each_split_range apply_to_each_split_range_under_args under_args2 apply_to_range apply_to_range_under_args].

  Lemma two_corners_and_zero_eq f x
    : two_corners_and_zero f x = @n_corners_and_zero 1 f x.
  Proof. reflexivity. Qed.

  Lemma monotone_four_corners_genb'
        (f : Z -> Z -> Z)
        (Hmonotone1 : forall x, exists b, Proper (R b ==> Z.le) (fun y => f x y))
        (Hmonotone2 : forall y, exists b, Proper (R b ==> Z.le) (fun x => f x y))
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
    : is_tighter_than_bool (constant (f x y)) (four_corners f x_bs y_bs).
  Proof.
    apply (fun pf => @monotone_n_corners_genb 2 f pf (y, x) (y_bs, x_bs)).
    all: t_fill.
  Qed.

  Lemma four_corners_and_zero_eq f x y
    : four_corners_and_zero f x y = @n_corners_and_zero 2 f x y.
  Proof.
    set (n:=1%nat).
    cbv [four_corners_and_zero].
    cbn [n_corners_and_zero].
    generalize (fun x => two_corners_and_zero_eq (f x)).
    subst n.
    generalize (@two_corners_and_zero) (@n_corners_and_zero 1).
    t_red.
    break_innermost_match; intros ?? H; rewrite ?H; reflexivity.
  Qed.

  Lemma monotone_four_corners_and_zero_genb'
        (f : Z -> Z -> Z)
        (Hmonotone1p : forall x, exists b, Proper (Rp b ==> Z.le) (fun y => f x (Zpos y)))
        (Hmonotone1n : forall x, exists b, Proper (Rp b ==> Z.le) (fun y => f x (Zneg y)))
        (Hmonotone2p : forall y, exists b, Proper (Rp b ==> Z.le) (fun x => f (Zpos x) y))
        (Hmonotone2n : forall y, exists b, Proper (Rp b ==> Z.le) (fun x => f (Zneg x) y))
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
    : is_tighter_than_bool (constant (f x y)) (four_corners_and_zero f x_bs y_bs).
  Proof.
    rewrite four_corners_and_zero_eq.
    exact (@monotone_n_corners_and_zero_genb 2 f ltac:(t_fill) (y, x) (y_bs, x_bs) ltac:(t_fill)).
  Qed.

  Lemma monotoneb_four_corners_gen
        (f : Z -> Z -> Z)
        (Hmonotone1 : forall x, Proper (R true ==> Z.le) (fun y => f x y) \/ Proper (R false ==> Z.le) (fun y => f x y))
        (Hmonotone2 : forall y, Proper (R true ==> Z.le) (fun x => f x y) \/ Proper (R false ==> Z.le) (fun x => f x y))
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
    : is_tighter_than_bool (constant (f x y)) (four_corners f x_bs y_bs).
  Proof.
    apply monotone_four_corners_genb'; t_fill.
  Qed.

  Lemma monotoneb_four_corners_and_zero_gen
        (f : Z -> Z -> Z)
        (Hmonotone1p : forall x, Proper (Rp true ==> Z.le) (fun y => f x (Zpos y)) \/ Proper (Rp false ==> Z.le) (fun y => f x (Zpos y)))
        (Hmonotone1n : forall x, Proper (Rp true ==> Z.le) (fun y => f x (Zneg y)) \/ Proper (Rp false ==> Z.le) (fun y => f x (Zneg y)))
        (Hmonotone2p : forall y, Proper (Rp true ==> Z.le) (fun x => f (Zpos x) y) \/ Proper (Rp false ==> Z.le) (fun x => f (Zpos x) y))
        (Hmonotone2n : forall y, Proper (Rp true ==> Z.le) (fun x => f (Zneg x) y) \/ Proper (Rp false ==> Z.le) (fun x => f (Zneg x) y))
        x x_bs y y_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
    : is_tighter_than_bool (constant (f x y)) (four_corners_and_zero f x_bs y_bs).
  Proof.
    apply monotone_four_corners_and_zero_genb'; t_fill.
  Qed.


  Lemma monotone_eight_corners_genb'
        (f : Z -> Z -> Z -> Z)
        (Hmonotone1 : forall x y, exists b, Proper (R b ==> Z.le) (fun z => f x y z))
        (Hmonotone2 : forall x z, exists b, Proper (R b ==> Z.le) (fun y => f x y z))
        (Hmonotone3 : forall y z, exists b, Proper (R b ==> Z.le) (fun x => f x y z))
        x x_bs y y_bs z z_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
        (Hboundedz : is_bounded_by_bool z z_bs)
    : is_tighter_than_bool (constant (f x y z)) (eight_corners f x_bs y_bs z_bs).
  Proof.
    apply (fun pf => @monotone_n_corners_genb 3 f pf (z, y, x) (z_bs, y_bs, x_bs)).
    all: t_fill.
  Qed.

  Lemma eight_corners_and_zero_eq f x y z
    : eight_corners_and_zero f x y z = @n_corners_and_zero 3 f x y z.
  Proof.
    set (n:=2%nat).
    cbv [eight_corners_and_zero].
    cbn [n_corners_and_zero].
    generalize (fun x => four_corners_and_zero_eq (f x)).
    subst n.
    generalize (@four_corners_and_zero) (@n_corners_and_zero 2).
    t_red.
    break_innermost_match; intros ?? H; rewrite ?H; reflexivity.
  Qed.

  Lemma monotone_eight_corners_and_zero_genb'
        (f : Z -> Z -> Z -> Z)
        (Hmonotone1p : forall x y, exists b, Proper (Rp b ==> Z.le) (fun z => f x y (Zpos z)))
        (Hmonotone1n : forall x y, exists b, Proper (Rp b ==> Z.le) (fun z => f x y (Zneg z)))
        (Hmonotone2p : forall x z, exists b, Proper (Rp b ==> Z.le) (fun y => f x (Zpos y) z))
        (Hmonotone2n : forall x z, exists b, Proper (Rp b ==> Z.le) (fun y => f x (Zneg y) z))
        (Hmonotone3p : forall y z, exists b, Proper (Rp b ==> Z.le) (fun x => f (Zpos x) y z))
        (Hmonotone3n : forall y z, exists b, Proper (Rp b ==> Z.le) (fun x => f (Zneg x) y z))
        x x_bs y y_bs z z_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
        (Hboundedz : is_bounded_by_bool z z_bs)
    : is_tighter_than_bool (constant (f x y z)) (eight_corners_and_zero f x_bs y_bs z_bs).
  Proof.
    rewrite eight_corners_and_zero_eq.
    exact (@monotone_n_corners_and_zero_genb 3 f ltac:(t_fill) (z, y, x) (z_bs, y_bs, x_bs) ltac:(t_fill)).
  Qed.

  Lemma monotoneb_eight_corners_gen
        (f : Z -> Z -> Z -> Z)
        (Hmonotone1 : forall x y, Proper (R true ==> Z.le) (fun z => f x y z) \/ Proper (R false ==> Z.le) (fun z => f x y z))
        (Hmonotone2 : forall x z, Proper (R true ==> Z.le) (fun y => f x y z) \/ Proper (R false ==> Z.le) (fun y => f x y z))
        (Hmonotone3 : forall y z, Proper (R true ==> Z.le) (fun x => f x y z) \/ Proper (R false ==> Z.le) (fun x => f x y z))
        x x_bs y y_bs z z_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
        (Hboundedz : is_bounded_by_bool z z_bs)
    : is_tighter_than_bool (constant (f x y z)) (eight_corners f x_bs y_bs z_bs).
  Proof.
    apply monotone_eight_corners_genb'; t_fill.
  Qed.

  Lemma monotoneb_eight_corners_and_zero_gen
        (f : Z -> Z -> Z -> Z)
        (Hmonotone1p : forall x y, Proper (Rp true ==> Z.le) (fun z => f x y (Zpos z)) \/ Proper (Rp false ==> Z.le) (fun z => f x y (Zpos z)))
        (Hmonotone1n : forall x y, Proper (Rp true ==> Z.le) (fun z => f x y (Zneg z)) \/ Proper (Rp false ==> Z.le) (fun z => f x y (Zneg z)))
        (Hmonotone2p : forall x z, Proper (Rp true ==> Z.le) (fun y => f x (Zpos y) z) \/ Proper (Rp false ==> Z.le) (fun y => f x (Zpos y) z))
        (Hmonotone2n : forall x z, Proper (Rp true ==> Z.le) (fun y => f x (Zneg y) z) \/ Proper (Rp false ==> Z.le) (fun y => f x (Zneg y) z))
        (Hmonotone3p : forall y z, Proper (Rp true ==> Z.le) (fun x => f (Zpos x) y z) \/ Proper (Rp false ==> Z.le) (fun x => f (Zpos x) y z))
        (Hmonotone3n : forall y z, Proper (Rp true ==> Z.le) (fun x => f (Zneg x) y z) \/ Proper (Rp false ==> Z.le) (fun x => f (Zneg x) y z))
        x x_bs y y_bs z z_bs
        (Hboundedx : is_bounded_by_bool x x_bs)
        (Hboundedy : is_bounded_by_bool y y_bs)
        (Hboundedz : is_bounded_by_bool z z_bs)
    : is_tighter_than_bool (constant (f x y z)) (eight_corners_and_zero f x_bs y_bs z_bs).
  Proof.
    apply monotone_eight_corners_and_zero_genb'; t_fill.
  Qed.
End ZRange.
