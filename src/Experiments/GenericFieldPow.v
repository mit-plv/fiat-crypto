Require Import Coq.setoid_ring.Cring.
Require Import Coq.omega.Omega.
Generalizable All Variables.


(*TODO: move *)
Lemma Z_pos_pred_0 p : Z.pos p - 1 = 0 -> p=1%positive.
Proof. destruct p; simpl in *; try discriminate; auto. Qed.

Lemma Z_neg_succ_neg : forall a b, (Z.neg a + 1)%Z = Z.neg b -> a = Pos.succ b.
Admitted.

Lemma Z_pos_pred_pos : forall a b, (Z.pos a - 1)%Z = Z.pos b -> a = Pos.succ b.
Admitted.

Lemma Z_pred_neg p : (Z.neg p - 1)%Z = Z.neg (Pos.succ p).
Admitted.

(* teach nsatz to deal with the definition of power we are use *)
Instance  reify_pow_pos (R:Type) `{Ring R}
e1 lvar t1 n
`{Ring (T:=R)}
{_:reify e1 lvar t1}
: reify (PEpow e1 (N.pos n)) lvar (pow_pos t1 n)|1.

Class Field_ops (F:Type)
      `{Ring_ops F}
      {inv:F->F} := {}.

Class Division (A B C:Type) := division : A -> B -> C.

Local Notation "_/_" := division.
Local Notation "n / d" := (division n d).

Module F.

  Definition div `{Field_ops F} n d := n * (inv d).
  Global Instance div_notation `{Field_ops F} : @Division F F F := div.

  Class Field {F inv} `{FieldCring:Cring (R:=F)} {Fo:Field_ops F (inv:=inv)} :=
    {
      field_inv_comp : Proper (_==_ ==> _==_) inv;
      field_inv_def : forall x, (x == 0 -> False) -> inv x * x == 1;
      field_one_neq_zero : not (1 == 0)
    }.
  Global Existing Instance field_inv_comp.

  Definition powZ `{Field_ops F} (x:F) (n:Z) :=
    match n with
    | Z0 => 1
    | Zpos p => pow_pos x p
    | Zneg p => inv (pow_pos x p)
    end.
  Global Instance power_field `{Field_ops F} : Power | 5 := { power := powZ }.

  Section FieldProofs.
    Context `{Field F}.

    Definition unfold_div (x y:F) : x/y = x * inv y := eq_refl.

    Global Instance Proper_div :
      Proper (_==_ ==> _==_ ==> _==_) div.
    Proof.
      unfold div; repeat intro.
      repeat match goal with
             | [H: _ == _ |- _ ] => rewrite H; clear H
             end; reflexivity.
    Qed.

    Global Instance Proper_pow_pos : Proper (_==_==>eq==>_==_) pow_pos.
    Proof.
      cut (forall n (y x : F), x == y -> pow_pos x n == pow_pos y n);
        [repeat intro; subst; eauto|].
      induction n; simpl; intros; trivial;
        repeat eapply ring_mult_comp; eauto.
    Qed.

    Global Instance Propper_powZ : Proper (_==_==>eq==>_==_) powZ.
    Proof.
      repeat intro; subst; unfold powZ.
      match goal with |- context[match ?x with _ => _ end] => destruct x end;
        repeat (eapply Proper_pow_pos || f_equiv; trivial).
    Qed.

    Require Import Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
    Lemma field_theory_for_tactic : field_theory 0 1 _+_ _*_ _-_ -_ _/_ inv _==_.
    Proof.
      split; repeat constructor; repeat intro; gen_rewrite; try cring;
        eauto using field_one_neq_zero, field_inv_def. Qed.

    Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.NArithRing.
    Lemma power_theory_for_tactic : power_theory 1 _*_ _==_ NtoZ power.
    Proof. constructor; destruct n; reflexivity. Qed.

    Create HintDb field_nonzero discriminated.
    Hint Resolve field_one_neq_zero : field_nonzero.
    Ltac field_nonzero := repeat split; auto 3 with field_nonzero.
    Ltac field_power_isconst t := Ncst t.
    Add Field FieldProofsAddField : field_theory_for_tactic
                                      (postprocess [field_nonzero],
                                       power_tac power_theory_for_tactic [field_power_isconst]).

    Lemma div_mul_idemp_l : forall a b, (a==0 -> False) -> a*b/a == b.
    Proof. intros. field. Qed.

    Context {eq_dec:forall x y : F, {x==y}+{x==y->False}}.
    Lemma mul_zero_why : forall a b, a*b == 0 -> a == 0 \/ b == 0.
      intros; destruct (eq_dec a 0); intuition.
      assert (a * b / a == 0) by
          (match goal with [H: _ == _ |- _ ] => rewrite H; field end).
      rewrite div_mul_idemp_l in *; auto.
    Qed.

    Require Import Coq.nsatz.Nsatz.
    Global Instance Integral_domain_Field : Integral_domain (R:=F).
    Proof.
      constructor; intros; eauto using mul_zero_why, field_one_neq_zero.
    Qed.

    Tactic Notation (at level 0) "field_simplify_eq" "in" hyp(H) :=
      let t := type of H in
      generalize H;
      field_lookup (PackField FIELD_SIMPL_EQ) [] t;
      try (exact I);
      try (idtac; []; clear H;intro H).

    Require Import Util.Tactics.
    Inductive field_simplify_done {x y:F} : (x==y) -> Type :=
      Field_simplify_done : forall (H:x==y), field_simplify_done H.
    Ltac field_nsatz :=
      repeat match goal with
               [ H: (_:F) == _ |- _ ] =>
               match goal with
               | [ Ha : field_simplify_done H |- _ ] => fail
               | _ => idtac
               end;
               field_simplify_eq in H;
               unique pose proof (Field_simplify_done H)
             end;
      repeat match goal with [ H: field_simplify_done _ |- _] => clear H end;
      try field_simplify_eq;
      try nsatz.

    Create HintDb field discriminated.
    Hint Extern 5 (_ == _) => field_nsatz : field.
    Hint Extern 5 (_ <-> _) => split.

    Lemma mul_inv_l : forall x, not (x == 0) -> inv x * x == 1. Proof. auto with field. Qed.

    Lemma mul_inv_r : forall x, not (x == 0) -> x * inv x == 1. Proof. auto with field. Qed.

    Lemma mul_cancel_r' (x y z:F) : not (z == 0) -> x * z == y * z -> x == y.
    Proof.
      intros.
      assert (x * z * inv z == y * z * inv z) by
          (match goal with [H: _ == _ |- _ ] => rewrite H; auto with field end).
      assert (x * z * inv z == x * (z * inv z)) by auto with field.
      assert (y * z * inv z == y * (z * inv z)) by auto with field.
      rewrite mul_inv_r, @ring_mul_1_r in *; auto with field.
    Qed.

    Lemma mul_cancel_r (x y z:F) : not (z == 0) -> (x * z == y * z <-> x == y).
    Proof. intros;split;intros Heq; try eapply mul_cancel_r' in Heq; eauto with field. Qed.

    Lemma mul_cancel_l (x y z:F) : not (z == 0) -> (z * x == z * y <-> x == y).
    Proof. intros;split;intros; try eapply mul_cancel_r; eauto with field. Qed.

    Lemma mul_cancel_r_eq : forall x z:F, not(z==0) -> (x*z == z <-> x == 1).
    Proof.
      intros;split;intros Heq; [|nsatz].
      pose proof ring_mul_1_l z as Hz; rewrite <- Hz in Heq at 2; rewrite  mul_cancel_r in Heq; eauto.
    Qed.

    Lemma mul_cancel_l_eq : forall x z:F, not(z==0) -> (z*x == z <-> x == 1).
    Proof. intros;split;intros Heq; try eapply mul_cancel_r_eq; eauto with field. Qed.

    Lemma inv_unique (a:F) : forall x y, x * a == 1 -> y * a == 1 -> x == y. Proof. auto with field. Qed.

    Lemma mul_nonzero_nonzero (a b:F) : not (a == 0) -> not (b == 0) -> not (a*b == 0).
    Proof. intros; intro Hab. destruct (mul_zero_why _ _ Hab); auto. Qed.
    Hint Resolve mul_nonzero_nonzero : field_nonzero.

    Lemma inv_nonzero (x:F) : not(x == 0) -> not(inv x==0).
    Proof.
      intros Hx Hi.
      assert (Hc:not (inv x*x==0)) by (rewrite field_inv_def; eauto with field_nonzero); contradict Hc.
      ring [Hi].
    Qed.
    Hint Resolve inv_nonzero : field_nonzero.

    Lemma div_nonzero (x y:F) : not(x==0) -> not(y==0) -> not(x/y==0).
    Proof.
      unfold division, div_notation, div; auto with field_nonzero.
    Qed.
    Hint Resolve div_nonzero : field_nonzero.

    Lemma pow_pos_nonzero (x:F) p : not(x==0) -> not(Ncring.pow_pos x p == 0).
    Proof.
      intros; induction p using Pos.peano_ind; try assumption; [].
      rewrite Ncring.pow_pos_succ; eauto using mul_nonzero_nonzero.
    Qed.
    Hint Resolve pow_pos_nonzero : field_nonzero.

    Lemma sub_diag_iff (x y:F) : x - y == 0 <-> x == y. Proof. auto with field. Qed.

    Lemma mul_same (x:F) : x*x == x^2%Z. Proof. auto with field. Qed.

    Lemma inv_mul (x y:F) : not(x==0) -> not (y==0) -> inv (x*y) == inv x * inv y.
    Proof. intros;field;intuition. Qed.

    Lemma pow_0_r (x:F) : x^0 == 1. Proof. auto with field. Qed.
    Lemma pow_1_r : forall x:F, x^1%Z == x. Proof. auto with field. Qed.
    Lemma pow_2_r : forall x:F, x^2%Z == x*x. Proof. auto with field. Qed.
    Lemma pow_3_r : forall x:F, x^3%Z == x*x*x. Proof. auto with field. Qed.

    Lemma pow_succ_r (x:F) (n:Z) : not (x==0)\/(n>=0)%Z -> x^(n+1) == x * x^n.
    Proof.
      intros Hnz; unfold power, powZ, power_field, powZ; destruct n eqn:HSn.
      - simpl; ring.
      - setoid_rewrite <-Pos2Z.inj_succ; rewrite Ncring.pow_pos_succ; ring.
      - destruct (Z.succ (Z.neg p)) eqn:Hn.
        + assert (p=1%positive) by (destruct p; simpl in *; try discriminate; auto).
          subst; simpl in *; field. destruct Hnz; auto with field_nonzero.
        + destruct p, p0; discriminate.
        + setoid_rewrite Hn.
          apply Z_neg_succ_neg in Hn; subst.
          rewrite Ncring.pow_pos_succ; field;
            destruct Hnz; auto with field_nonzero.
    Qed.

    Lemma pow_pred_r (x:F) (n:Z) : not (x==0) -> x^(n-1) == x^n/x.
    Proof.
      intros; unfold power, powZ, power_field, powZ; destruct n eqn:HSn.
      - simpl. rewrite unfold_div; field.
      - destruct (Z.pos p - 1) eqn:Hn.
        + apply Z_pos_pred_0 in Hn; subst; simpl; field.
        + apply Z_pos_pred_pos in Hn; subst.
          rewrite Ncring.pow_pos_succ; field; auto with field_nonzero.
        + destruct p; discriminate.
      - rewrite Z_pred_neg, Ncring.pow_pos_succ; field; auto with field_nonzero.
    Qed.

    Local Ltac pow_peano :=
      repeat (setoid_rewrite pow_0_r
              || setoid_rewrite pow_succ_r
              || setoid_rewrite pow_pred_r).

    Lemma pow_mul (x y:F) : forall (n:Z), not(x==0)/\not(y==0)\/(n>=0)%Z -> (x * y)^n == x^n * y^n.
    Proof.
      match goal with |- forall n, @?P n => eapply (Z.order_induction'_0 P) end.
      { repeat intro. subst. reflexivity. }
      - intros; cbv [power power_field powZ]; ring.
      - intros n Hn IH Hxy.
        repeat setoid_rewrite pow_succ_r; try rewrite IH; try ring; (right; omega).
      - intros n Hn IH Hxy. destruct Hxy as [[]|?]; try omega; [].
        repeat setoid_rewrite pow_pred_r; try rewrite IH; try field; auto with field_nonzero.
    Qed.

    Lemma pow_nonzero (x:F) : forall (n:Z), not(x==0) -> not(x^n==0).
      match goal with |- forall n, @?P n => eapply (Z.order_induction'_0 P) end; intros; pow_peano;
        eauto with field_nonzero.
      { repeat intro. subst. reflexivity. }
    Qed.
    Hint Resolve pow_nonzero : field_nonzero.

    Lemma pow_inv (x:F) : forall (n:Z), not(x==0) -> inv x^n == inv (x^n).
      match goal with |- forall n, @?P n => eapply (Z.order_induction'_0 P) end.
      { repeat intro. subst. reflexivity. }
      - intros; cbv [power power_field powZ]. field; eauto with field_nonzero.
      - intros n Hn IH Hx.
        repeat setoid_rewrite pow_succ_r; try rewrite IH; try field; eauto with field_nonzero.
      - intros n Hn IH Hx.
        repeat setoid_rewrite pow_pred_r; try rewrite IH; try field; eauto 3 with field_nonzero.
    Qed.

    Lemma pow_0_l : forall n, (n>0)%Z -> (0:F)^n==0.
      match goal with |- forall n, @?P n => eapply (Z.order_induction'_0 P) end; intros; try omega.
      { repeat intro. subst. reflexivity. }
      setoid_rewrite pow_succ_r; [auto with field|right;omega].
    Qed.

    Lemma pow_div (x y:F) (n:Z) : not (y==0) -> not(x==0)\/(n >= 0)%Z -> (x/y)^n == x^n/y^n.
    Proof.
      intros Hy Hxn. unfold division, div_notation, div.
      rewrite pow_mul, pow_inv; try field; destruct Hxn; auto with field_nonzero.
    Qed.

    Hint Extern 3 (_ >= _)%Z => omega : field_nonzero.
    Lemma issquare_mul (x y z:F) : not (y == 0) -> x^2%Z == z * y^2%Z -> (x/y)^2%Z == z.
    Proof. intros. rewrite pow_div by (auto with field_nonzero); auto with field. Qed.

    Lemma issquare_mul_sub (x y z:F) : 0 == z*y^2%Z - x^2%Z -> (x/y)^2%Z == z \/ x == 0.
    Proof. destruct (eq_dec y 0); [right|left]; auto using issquare_mul with field. Qed.

    Lemma div_mul : forall x y z : F, not(y==0) -> (z == (x / y) <-> z * y == x).
    Proof. auto with field. Qed.

    Lemma div_1_r : forall x : F, x/1 == x.
    Proof. eauto with field field_nonzero. Qed.

    Lemma div_1_l : forall x : F, not(x==0) -> 1/x == inv x.
    Proof. auto with field. Qed.

    Lemma div_opp_l : forall x y, not (y==0) -> (-_ x) / y == -_ (x / y).
    Proof. auto with field. Qed.

    Lemma div_opp_r : forall x y, not (y==0) -> x / (-_ y) == -_ (x / y).
    Proof. auto with field. Qed.

    Lemma eq_opp_zero : forall x : F, (~ 1 + 1 == (0:F)) -> (x == -_ x <-> x == 0).
    Proof. auto with field. Qed.

    Lemma add_cancel_l : forall x y z:F, z+x == z+y <-> x == y.
    Proof. auto with field. Qed.

    Lemma add_cancel_r : forall x y z:F, x+z == y+z <-> x == y.
    Proof. auto with field. Qed.

    Lemma add_cancel_r_eq : forall x z:F, x+z == z <-> x == 0.
    Proof. auto with field. Qed.

    Lemma add_cancel_l_eq : forall x z:F, z+x == z <-> x == 0.
    Proof. auto with field. Qed.

    Lemma sqrt_solutions : forall x y:F, y ^ 2%Z == x ^ 2%Z -> y == x \/ y == -_ x.
    Proof.
      intros ? ? squares_eq.
      remember (y - x) as z eqn:Heqz.
      assert (y == x + z) as Heqy by (subst; ring); rewrite Heqy in *; clear Heqy Heqz.
      assert (Hw:(x + z)^2%Z == z * (x + (x + z)) + x^2%Z)
        by (auto with field); rewrite Hw in squares_eq; clear Hw.
      rewrite add_cancel_r_eq in squares_eq.
      apply mul_zero_why in squares_eq; destruct squares_eq;  auto with field.
    Qed.

  End FieldProofs.
End F.
