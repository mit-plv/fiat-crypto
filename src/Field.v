Require Import Coq.setoid_ring.Cring.
Generalizable All Variables.

Class Field_ops (F:Type)
      `{Ring_ops F}
      {inv:F->F} := {}.

Class Division (A B:Type) := division : A -> B -> A.

Notation "_/_" := division.
Notation "n / d" := (division n d).

Module F.

  Definition div `{Field_ops F} n d := mul n (inv d).
  Global Instance div_notation `{Field_ops F} : @Division F F := div.

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

    Global Instance Proper_div :
      Proper (_==_ ==> _==_ ==> _==_) div.
    Proof.
      unfold div; repeat intro.
      repeat match goal with
             | [H: _ == _ |- _ ] => rewrite H; clear H
             end; reflexivity.
    Qed.

    Require Import Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
    Lemma field_theory_for_tactic : field_theory 0 1 _+_ _*_ _-_ -_ _/_ inv _==_.
    Proof.
      split; repeat constructor; repeat intro; gen_rewrite; try cring;
        eauto using field_one_neq_zero, field_inv_def. Qed.

    Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.NArithRing.
    Lemma power_theory_for_tactic : power_theory 1 _*_ _==_ NtoZ power.
    Proof. constructor; destruct n; reflexivity. Qed.

    Ltac field_power_isconst t := Ncst t.
    Add Field FieldProofsAddField : field_theory_for_tactic
                                      (postprocess [trivial],
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

    Lemma mul_inv_l : forall x, not (x == 0) -> inv x * x == 1.
    Proof. intros. field. Qed.

    Lemma mul_inv_r : forall x, not (x == 0) -> x * inv x == 1.
    Proof. intros. field. Qed.

    Lemma mul_cancel_r (x y z:F) : not (z == 0) -> x * z == y * z -> x == y.
    Proof.
      intros.
      assert (x * z * inv z == y * z * inv z) by
          (match goal with [H: _ == _ |- _ ] => rewrite H; field end).
      assert (x * z * inv z == x * (z * inv z)) by field.
      assert (y * z * inv z == y * (z * inv z)) by field.
      rewrite mul_inv_r, @ring_mul_1_r in * by assumption.
      nsatz.
    Qed.

    Lemma mul_cancel_l (x y z:F) : not (z == 0) -> z * x == z * y -> x == y.
    Proof. intros. eapply mul_cancel_r; eauto. nsatz. Qed.

    Lemma inv_unique (a:F) : forall x y, x * a == 1 -> y * a == 1 -> x == y.
    Proof. nsatz. Qed.
    
    Lemma mul_nonzero_nonzero (a b:F) : not (a == 0) -> not (b == 0) -> not (a*b == 0).
    Proof. intros. intro Hab. destruct (mul_zero_why _ _ Hab); intuition. Qed.

    Lemma sub_diag_iff (x y:F) : x - y == 0 <-> x == y. Proof. split; nsatz. Qed.

    Lemma mul_same (x:F) : x*x == x^2%Z. reflexivity. Qed.
 
    Lemma issquare_mul (x y z:F) : not (y == 0) -> x^2%Z == z * y^2%Z -> (x/y)^2%Z == z.
    Proof. intros. rewrite <-!mul_same; field_simplify_eq; nsatz. Qed.

    Lemma issquare_mul_sub (x y z:F) : 0 == z*y^2%Z - x^2%Z -> (x/y)^2%Z == z \/ x == 0.
    Proof.
      destruct (eq_dec y 0); [right|left].
      -
