Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.DestructHead.

Module ZRange.
  Import Operations.ZRange.
  Local Open Scope zrange_scope.
  Local Coercion is_true : bool >-> Sortclass.

  Local Notation eta v := r[ lower v ~> upper v ].

  Local Ltac t_step :=
    first [ reflexivity
          | progress destruct_head' zrange
          | progress cbv -[Z.min Z.max Z.le Z.lt Z.ge Z.gt andb Z.leb Z.geb] in *
          | progress split_min_max
          | match goal with
            | [ |- _ = _ :> zrange ] => apply f_equal2
            end
          | omega
          | solve [ auto ] ].
  Local Ltac t := repeat t_step.

  Lemma flip_flip v : flip (flip v) = v.
  Proof. destruct v; reflexivity. Qed.

  Lemma normalize_flip v : normalize (flip v) = normalize v.
  Proof. t. Qed.

  Lemma normalize_idempotent v : normalize (normalize v) = normalize v.
  Proof. t. Qed.

  Definition normalize_or v : normalize v = v \/ normalize v = flip v.
  Proof. t. Qed.

  Local Ltac t2_step :=
    first [ t_step
          | rewrite !Bool.andb_true_iff
          | rewrite !Z.leb_le
          | rewrite !Z.leb_gt
          | rewrite Bool.andb_true_iff in *
          | rewrite Z.leb_le in *
          | rewrite Z.leb_gt in *
          | progress intros
          | match goal with
            | [ H : context[andb _ _ = true] |- _ ] => setoid_rewrite Bool.andb_true_iff in H
            | [ |- context[andb _ _ = true] ] => setoid_rewrite Bool.andb_true_iff
            | [ H : context[Z.leb _ _ = true] |- _ ] => setoid_rewrite Z.leb_le in H
            | [ |- context[Z.leb _ _ = true] ] => setoid_rewrite Z.leb_le
            | [ H : context[Z.leb _ _ = false] |- _ ] => setoid_rewrite Z.leb_gt in H
            | [ |- context[Z.leb _ _ = false] ] => setoid_rewrite Z.leb_gt
            | [ |- and _ _ ] => apply conj
            | [ |- or _ (true = false) ] => left
            | [ |- or _ (false = true) ] => left
            | [ |- or _ (?x = ?x) ] => right
            | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
            end
          | progress specialize_by omega
          | progress destruct_head'_or ].

  Lemma is_bounded_by_iff_is_tighter_than r1 r2
    : (forall v, is_bounded_by_bool v r1 = true -> is_bounded_by_bool v r2 = true)
      <-> (is_tighter_than_bool r1 r2 = true \/ goodb r1 = false).
  Proof. repeat t2_step; specialize_all_ways; repeat t2_step. Qed.

  Lemma is_bounded_by_iff_is_tighter_than_good r1 r2 (Hgood : goodb r1 = true)
    : (forall v, is_bounded_by_bool v r1 = true -> is_bounded_by_bool v r2 = true)
      <-> (is_tighter_than_bool r1 r2 = true).
  Proof. rewrite is_bounded_by_iff_is_tighter_than; intuition (congruence || auto). Qed.

  Global Instance is_tighter_than_bool_Reflexive : Reflexive is_tighter_than_bool.
  Proof.
    cbv [is_tighter_than_bool is_true]; cbn [lower upper]; repeat intro.
    rewrite ?Bool.andb_true_iff, ?Z.leb_le_iff in *; repeat apply conj; reflexivity.
  Qed.
  Global Instance is_tighter_than_bool_Transitive : Transitive is_tighter_than_bool.
  Proof.
    cbv [is_tighter_than_bool is_true]; cbn [lower upper]; repeat intro.
    rewrite ?Bool.andb_true_iff, ?Z.leb_le_iff in *; repeat apply conj; etransitivity; destruct_head'_and; eassumption.
  Qed.

  Lemma is_bounded_by_bool_Proper_if_sumbool_union {A B} (b : sumbool A B) x y rx ry
    : is_bounded_by_bool x rx = true
      -> is_bounded_by_bool y ry = true
      -> is_bounded_by_bool (if b then x else y) (Operations.ZRange.union rx ry) = true.
  Proof.
    destruct b; cbv [Operations.ZRange.union is_bounded_by_bool];
      intros; Bool.split_andb; rewrite Bool.andb_true_iff; split; Z.ltb_to_lt; cbn [lower upper] in *; split_min_max.
    all: lia.
  Qed.
End ZRange.
