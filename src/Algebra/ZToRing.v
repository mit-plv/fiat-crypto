Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.PArith.
Require Import Crypto.Algebra.
Require Import Crypto.Util.Tactics.
Local Open Scope Z_scope.

Section ZToRing.
  Context {R Req Rzero Rone Ropp Radd Rsub Rmul}
          {Rring : @ring R Req Rzero Rone Ropp Radd Rsub Rmul}.
  Local Infix "=" := Req. Local Infix "=" := Req : type_scope.

  Fixpoint natToRing (n:nat) : R :=
    match n with
    | O => Rzero
    | S n' => Radd (natToRing n') Rone
    end.
  Definition ZToRing (x:Z) : R :=
    match x with
    | Z0 => Rzero
    | Zpos p => natToRing (Pos.to_nat p)
    | Zneg p => Ropp (natToRing (Pos.to_nat p))
    end.

  Lemma ZToRing_zero_correct : ZToRing 0 = Rzero.
  Proof. reflexivity. Qed.

  Lemma natToRing_plus_correct x :
    natToRing (Nat.add x 1) = Radd (natToRing x) Rone.
  Proof. destruct x; rewrite ?Nat.add_1_r; reflexivity. Qed.

  Lemma natToRing_minus_correct x (H: (0 < x)%nat):
    natToRing (Nat.sub x 1) = Rsub (natToRing x) Rone.
  Proof.
    induction x; [omega|simpl].
    rewrite <-natToRing_plus_correct.
    rewrite Nat.sub_0_r, Nat.add_1_r.
    simpl natToRing.
    rewrite ring_sub_definition, <-associative.
    rewrite right_inverse, right_identity.
    reflexivity.
  Qed.

  Lemma ZToRing_plus_correct :
    forall x, ZToRing (Z.add x 1) = Radd (ZToRing x) Rone.
  Proof.
    destruct x; [reflexivity| | ]; simpl ZToRing.
    { rewrite Pos2Nat.inj_add, natToRing_plus_correct.
      reflexivity. }
    { rewrite Z.pos_sub_spec; break_match;
        match goal with
        | H : _ |- _ => rewrite Pos.compare_eq_iff in H
        | H : _ |- _ => rewrite Pos.compare_lt_iff in H
        | H : _ |- _ => rewrite Pos.compare_gt_iff in H;
                          apply Pos.nlt_1_r in H; tauto
        end;
        subst; simpl ZToRing; simpl natToRing.
      { rewrite left_identity, left_inverse; reflexivity. }
      { rewrite Pos2Nat.inj_sub by assumption.
        rewrite natToRing_minus_correct by apply Pos2Nat.is_pos.
        rewrite ring_sub_definition, Group.inv_op, Group.inv_inv.
        rewrite commutative; reflexivity. } }
  Qed.

  Lemma ZToRing_minus_correct :
    forall x, ZToRing (Z.sub x 1) = Rsub (ZToRing x) Rone.
  Proof.
    induction x.
    { simpl; rewrite ring_sub_definition, !left_identity;
        reflexivity. }
    { case_eq (1 ?= p)%positive; intros;
        match goal with
        | H : _ |- _ => rewrite Pos.compare_eq_iff in H
        | H : _ |- _ => rewrite Pos.compare_lt_iff in H
        | H : _ |- _ => rewrite Pos.compare_gt_iff in H;
                          apply Pos.nlt_1_r in H; tauto
        end.
      { subst. simpl; rewrite ring_sub_definition, !left_identity,
                      right_inverse; reflexivity. }
      { rewrite <-Pos2Z.inj_sub by assumption; simpl ZToRing.
        rewrite Pos2Nat.inj_sub by assumption.
        rewrite natToRing_minus_correct by apply Pos2Nat.is_pos.
        reflexivity. } }
    { simpl. rewrite Pos2Nat.inj_add, natToRing_plus_correct.
      rewrite ring_sub_definition, Group.inv_op, commutative.
      reflexivity. }
  Qed.

  Lemma ZToRing_inj_opp : forall a,
      ZToRing (Z.opp a) = Ropp (ZToRing a).
  Proof.
    destruct a; simpl; rewrite ?Group.inv_id, ?Group.inv_inv;
      reflexivity.
  Qed.

  Lemma ZToRing_inj_add : forall a b,
      ZToRing (Z.add a b) = Radd (ZToRing a) (ZToRing b).
  Proof.
    intros.
    let x := match goal with |- ?x => x end in
    let f := match (eval pattern b in x) with ?f _ => f end in
    apply (Z.peano_ind f); intros.
    { rewrite !right_identity; reflexivity. }
    { replace (a + Z.succ x) with ((a + x) + 1) by ring.
      replace (Z.succ x) with (x+1) by ring.
      rewrite !ZToRing_plus_correct, H.
      rewrite associative; reflexivity. }
    { replace (a + Z.pred x) with ((a+x)-1)
        by (rewrite <-Z.sub_1_r; ring).
      replace (Z.pred x) with (x-1) by apply Z.sub_1_r.
      rewrite !ZToRing_minus_correct, H.
      rewrite !ring_sub_definition.
      rewrite associative; reflexivity. }
  Qed.

  Lemma ZToRing_inj_mul : forall a b,
      ZToRing (Z.mul a b) = Rmul (ZToRing a) (ZToRing b).
  Proof.
    intros.
    let x := match goal with |- ?x => x end in
    let f := match (eval pattern b in x) with ?f _ => f end in
    apply (Z.peano_ind f); intros until 0; try intro IHb.
    { rewrite !Ring.mul_0_r; reflexivity. }
    { rewrite Z.mul_succ_r, <-Z.add_1_r.
      rewrite ZToRing_inj_add, ZToRing_plus_correct.
      rewrite IHb.
      rewrite left_distributive, right_identity.
      reflexivity. }
    { rewrite Z.mul_pred_r, <-Z.sub_1_r.
      rewrite ZToRing_minus_correct.
      rewrite <-Z.add_opp_r.
      rewrite ZToRing_inj_add, ZToRing_inj_opp.
      rewrite IHb.
      rewrite ring_sub_definition, left_distributive.
      rewrite Ring.mul_opp_r,right_identity.
      reflexivity. }
  Qed.


  Lemma ZToRingHomom : @Ring.is_homomorphism
                         Z Z.eq Z.one Z.add Z.mul
                         R Req  Rone  Radd  Rmul
                         ZToRing.
  Proof.
    repeat constructor; intros.
    { apply ZToRing_inj_add. }
    { repeat intro. cbv [Z.eq] in *. subst. reflexivity. }
    { apply ZToRing_inj_mul. }
    { simpl. rewrite left_identity; reflexivity. }
  Qed.
End ZToRing.
