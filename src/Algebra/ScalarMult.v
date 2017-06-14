Require Import Coq.ZArith.BinInt Coq.omega.Omega Crypto.Util.ZUtil.Peano.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Group.
Local Open Scope Z_scope.

Section ScalarMultProperties.
  Context {G eq add zero opp} `{groupG:@group G eq add zero opp}.
  Context {mul:Z->G->G}.
  Local Infix "=" := eq : type_scope. Local Infix "=" := eq.
  Local Infix "+" := add. Local Infix "*" := mul.
  Class is_scalarmult :=
    {
      scalarmult_0_l : forall P, 0 * P = zero;
      scalarmult_succ_l_nn : forall n P, 0 <= n -> Z.succ n * P = P + n * P;
      scalarmult_pred_l_np : forall n P, n <= 0 -> Z.pred n * P = opp P + n * P;

      scalarmult_Proper : Proper (Logic.eq==>eq==>eq) mul
    }.
  Global Existing Instance scalarmult_Proper.
  Context `{mul_is_scalarmult:is_scalarmult}.

  Lemma scalarmult_succ_l n P : Z.succ n * P = P + n * P.
  Proof.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega;
      repeat (rewrite ?scalarmult_0_l, ?scalarmult_succ_l_nn, ?scalarmult_pred_l_np, ?left_identity, ?right_identity, ?Z.succ_pred, ?Z.pred_succ, ?associative, ?right_inverse, ?left_inverse by omega); reflexivity.
  Qed.

  Lemma scalarmult_pred_l n P : Z.pred n * P = opp P + n * P.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega;
      repeat (rewrite ?scalarmult_0_l, ?scalarmult_succ_l_nn, ?scalarmult_pred_l_np, ?left_identity, ?right_identity, ?Z.succ_pred, ?Z.pred_succ, ?associative, ?right_inverse, ?left_inverse by omega); reflexivity.
  Qed.

  Definition scalarmult_ref (n:Z) (P:G) : G :=
    Z.peano_rect
      (fun _ => G)
      (zero)
      (fun _ => add P)
      (fun _ => add (opp P))
      n
  .

  Global Instance Proper_scalarmult_ref : Proper (Logic.eq==>eq==>eq) scalarmult_ref.
  Proof using groupG.
    intros n n' H; subst n';
      induction n using Z.peano_rect_strong;
      cbv [Proper respectful] in *;
      intros;
      cbv [scalarmult_ref] in *; break_match; try reflexivity;
      rewrite ?Z.peano_rect_succ, ?Z.peano_rect_pred in * by omega;
      rewrite IHn by eassumption;
      match goal with H : _ = _ |- _ => rewrite H; reflexivity end.
  Qed.

  Lemma scalarmult_ext n P : mul n P = scalarmult_ref n P.
  Proof using Type*.
    revert P.
    destruct mul_is_scalarmult.
    induction n using Z.peano_rect_strong; intros;
      cbv [scalarmult_ref] in *; break_match;
        rewrite ?Z.peano_rect_succ, ?Z.peano_rect_pred, ?Z.succ'_succ, ?Z.pred'_pred in *;
        try rewrite <-IHn; try match goal with [H:_|-_] => eapply H end; omega.
  Qed.

  Lemma scalarmult_1_l P : 1*P = P.
  Proof using Type*.
    intros. change 1 with (Z.succ 0).
    rewrite scalarmult_succ_l, scalarmult_0_l, right_identity; reflexivity.
  Qed.

  Lemma scalarmult_opp1_l P : -1*P = opp P.
    change (-1) with (Z.pred 0).
    rewrite scalarmult_pred_l, scalarmult_0_l, right_identity; reflexivity.
  Qed.

  Lemma scalarmult_add_l (n m:Z) (P:G) : ((n + m)%Z * P = n * P + m * P).
  Proof using Type*.
    revert P.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega;
        rewrite ?Z.add_0_l, ?Z.add_succ_l, ?Z.add_pred_l;
        rewrite ?scalarmult_0_l, ?scalarmult_succ_l, ?scalarmult_pred_l, ?left_identity, <-?associative, <-?IHn; try reflexivity.
  Qed.

  Lemma scalarmult_opp_l (n:Z) (P:G) : (-n) * P = opp (n*P).
  Proof using Type*.
    revert P.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega.
    { change (-0) with (0). rewrite !scalarmult_0_l, inv_id; reflexivity. }
    { rewrite scalarmult_succ_l_nn, inv_op, <-IHn by omega.
      replace (-Z.succ n) with (-n + (- 1))%Z by auto with zarith.
      rewrite scalarmult_add_l, scalarmult_opp1_l; reflexivity. }
    { rewrite scalarmult_pred_l_np, inv_op, <-IHn, inv_inv by omega.
      replace (- Z.pred n) with (-n+1)%Z by auto with zarith.
      rewrite scalarmult_add_l, scalarmult_1_l; reflexivity. }
  Qed.

  Lemma scalarmult_zero_r (n:Z) : n * zero = zero.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega;
        rewrite ?scalarmult_0_l, ?scalarmult_succ_l_nn, ?scalarmult_pred_l_np, ?IHn, ?inv_id, ?left_identity by omega;
        try reflexivity.
  Qed.

  Lemma scalarmult_assoc (n m : Z) P : n * (m * P) = (m * n)%Z * P.
  Proof using Type*.
    revert P.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega.
    { rewrite Z.mul_0_r, 2scalarmult_0_l by omega; reflexivity. }
    { rewrite scalarmult_succ_l, IHn by omega.
      rewrite (Z.mul_comm m (Z.succ n)), Z.mul_succ_l, (Z.mul_comm n m), (Z.add_comm (m*n) m).
      rewrite scalarmult_add_l. reflexivity. }
    { rewrite scalarmult_pred_l, IHn by omega.
      rewrite (Z.mul_comm m (Z.pred n)), Z.mul_pred_l, (Z.mul_comm n m), <-Z.add_opp_l.
      rewrite scalarmult_add_l, scalarmult_opp_l. reflexivity. }
  Qed.

  Lemma scalarmult_sub_l (a b:Z) (P:G) : (a - b)*P = a*P + opp(b*P).
  Proof using Type*.
    rewrite <-Z.add_opp_r, scalarmult_add_l, scalarmult_opp_l; reflexivity.
  Qed.

  Lemma scalarmult_opp_r (n:Z) (P:G) : n*opp P = opp (n * P).
  Proof using Type*.
    revert P.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega;
      rewrite <-?Z.add_1_l, <-?Z.sub_1_r;
      [|rewrite Z.add_comm at 1|rewrite <-Z.add_opp_l; rewrite Z.add_comm at 1];
      repeat (rewrite ?scalarmult_0_l, ?scalarmult_opp_l, ?scalarmult_add_l, ?inv_id, ?inv_op, ?inv_inv, ?IHn, ?scalarmult_1_l);
      reflexivity.
  Qed.

  Lemma scalarmult_times_order : forall l B, l*B = zero -> forall n, (l * n) * B = zero.
  Proof using Type*. intros ? ? Hl ?. rewrite <-scalarmult_assoc, Hl, scalarmult_zero_r. reflexivity. Qed.

  Lemma scalarmult_mod_order : forall l B, l <> 0 -> l*B = zero -> forall n, n mod l * B = n * B.
  Proof using Type*.
    intros l B Hnz Hmod n.
    rewrite (Z.div_mod n l Hnz) at 2.
    rewrite scalarmult_add_l, scalarmult_times_order, left_identity by auto. reflexivity.
  Qed.

End ScalarMultProperties.

Section ScalarMultHomomorphism.
  Context {G EQ ADD ZERO OPP} {groupG:@group G EQ ADD ZERO OPP}.
  Context {H eq add zero opp} {groupH:@group H eq add zero opp}.
  Local Infix "=" := eq : type_scope. Local Infix "=" := eq : eq_scope.
  Context {MUL} {MUL_is_scalarmult:@is_scalarmult G EQ ADD ZERO OPP MUL}.
  Context {mul} {mul_is_scalarmult:@is_scalarmult H eq add zero opp mul}.
  Context {phi} {homom:@Monoid.is_homomorphism G EQ ADD H eq add phi}.

  Lemma homomorphism_scalarmult : forall n P, phi (MUL n P) = mul n (phi P).
  Proof using Type*.
    induction n using Z.peano_rect_strong; intros; rewrite ?Z.succ'_succ, ?Z.pred'_pred in * by omega;
      rewrite ?scalarmult_0_l, ?scalarmult_succ_l, ?scalarmult_pred_l by omega.
    { apply homomorphism_id. }
    { rewrite <-IHn. rewrite Monoid.homomorphism. reflexivity. }
    { rewrite <-IHn. rewrite Monoid.homomorphism, Group.homomorphism_inv. reflexivity. }
  Qed.
End ScalarMultHomomorphism.

Global Instance scalarmult_ref_is_scalarmult {G eq add zero opp} {groupG:@group G eq add zero opp}
  : @is_scalarmult G eq add zero opp (@scalarmult_ref G add zero opp).
Proof.
  split; try exact _; cbv [scalarmult_ref] in *; intros;
    rewrite <-?Z.succ'_succ, <-?Z.pred'_pred, ?Z.peano_rect_succ, ?Z.peano_rect_pred in * by omega;
    reflexivity.
Qed.