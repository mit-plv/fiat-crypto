(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapInterface.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.CommonSubexpressionElimination.

Local Open Scope list_scope.

Local Open Scope ctype_scope.
Section symbolic.
  (** Holds decidably-equal versions of raw expressions, for lookup. *)
  Context (base_type_code : Type)
          (op_code : Type)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (op_code_beq : op_code -> op_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (op_code_bl : forall x y, op_code_beq x y = true -> x = y)
          (op_code_lb : forall x y, x = y -> op_code_beq x y = true)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (symbolize_op : forall s d, op s d -> op_code)
          (op_code_leb : op_code -> op_code -> bool)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (op_code_leb_total : forall x y, op_code_leb x y = true \/ op_code_leb y x = true)
          (base_type_leb_total : forall x y, base_type_leb x y = true \/ base_type_leb y x = true).
  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Context (normalize_symbolic_op_arguments : op_code -> symbolic_expr -> symbolic_expr).

  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Notation symbolic_expr_leb := (@symbolic_expr_leb base_type_code op_code base_type_code_beq op_code_beq op_code_leb base_type_leb).
  Local Notation flat_type_leb := (@flat_type_leb base_type_code base_type_code_beq base_type_leb).
  Local Notation flat_type_beq := (@flat_type_beq base_type_code base_type_code_beq).
  Local Notation flat_type_bl := (@internal_flat_type_dec_bl base_type_code base_type_code_beq base_type_code_bl).

  Theorem flat_type_leb_total : forall a1 a2, flat_type_leb a1 a2 = true \/ flat_type_leb a2 a1 = true.
  Proof.
    induction a1, a2;
      repeat first [ progress simpl
                   | progress subst
                   | solve [ auto ]
                   | match goal with
                     | [ H : forall a2', ?leb ?a1 a2' = true \/ _ |- context[?leb ?a1 ?a2] ]
                       => let H' := fresh in destruct (H a2) as [H'|H']; rewrite H'
                     | [ H : flat_type_beq _ _ = true |- _ ] => apply flat_type_bl in H
                     | [ |- context[flat_type_beq ?x ?y] ]
                       => destruct (flat_type_beq x y) eqn:?
                     end ].
  Qed.

  Theorem symbolic_expr_leb_total : forall a1 a2, symbolic_expr_leb a1 a2 = true \/ symbolic_expr_leb a2 a1 = true.
  Proof.
    induction a1, a2;
      repeat first [ rewrite !PeanoNat.Nat.leb_le
                   | progress subst
                   | progress simpl
                   | solve [ auto ]
                   | omega
                   | match goal with
                     | [ H : flat_type_beq _ _ = true |- _ ] => apply flat_type_bl in H
                     | [ H : op_code_beq _ _ = true |- _ ] => apply op_code_bl in H
                     | [ H : symbolic_expr_beq _ _ = true |- _ ] => apply symbolic_expr_bl in H
                     | [ |- context[flat_type_beq ?x ?y] ]
                       => destruct (flat_type_beq x y) eqn:?
                     | [ |- context[op_code_beq ?x ?y] ]
                       => destruct (op_code_beq x y) eqn:?
                     | [ |- context[symbolic_expr_beq ?x ?y] ]
                       => destruct (symbolic_expr_beq x y) eqn:?
                     | [ H : forall a2', ?leb ?a1 a2' = true \/ _ |- context[?leb ?a1 ?a2] ]
                       => let H' := fresh in destruct (H a2) as [H'|H']; rewrite H'
                     | [ |- context[flat_type_leb ?a1 ?a2] ]
                       => let H' := fresh in destruct (flat_type_leb_total a1 a2) as [H'|H']; rewrite H'
                     | [ |- context[op_code_leb ?a1 ?a2] ]
                       => let H' := fresh in destruct (op_code_leb_total a1 a2) as [H'|H']; rewrite H'
                     end ].
  Qed.
End symbolic.
