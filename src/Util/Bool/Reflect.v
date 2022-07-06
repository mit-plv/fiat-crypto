(** * Some lemmas about [Bool.reflect] *)
Require Import Coq.Bool.Bool.
Require Export Crypto.Util.FixCoqMistakes.

Lemma reflect_to_dec_iff {P b1 b2} : reflect P b1 -> (b1 = b2) <-> (if b2 then P else ~P).
Proof.
  intro H; destruct H, b2; split; intuition congruence.
Qed.

Lemma reflect_to_dec {P b1 b2} : reflect P b1 -> (b1 = b2) -> (if b2 then P else ~P).
Proof. intro; apply reflect_to_dec_iff; assumption. Qed.

Lemma reflect_of_dec {P} {b1 b2 : bool} : reflect P b1 -> (if b2 then P else ~P) -> (b1 = b2).
Proof. intro; apply reflect_to_dec_iff; assumption. Qed.

Lemma reflect_of_beq {A beq} (bl : forall a a' : A, beq a a' = true -> a = a')
      (lb : forall a a' : A, a = a' -> beq a a' = true)
  : forall x y, reflect (x = y) (beq x y).
Proof.
  intros x y; specialize (bl x y); specialize (lb x y).
  destruct (beq x y); constructor; intuition congruence.
Qed.

Definition mark {T} (v : T) := v.

Ltac beq_to_eq beq bl lb :=
  let lem := constr:(@reflect_of_beq _ beq bl lb) in
  repeat match goal with
         | [ |- context[bl ?x ?y ?pf] ] => generalize dependent (bl x y pf); try clear pf; intros
         | [ H : beq ?x ?y = true |- _ ] => apply (@reflect_to_dec _ _ true (lem x y)) in H; cbv beta iota in H
         | [ H : beq ?x ?y = false |- _ ] => apply (@reflect_to_dec _ _ false (lem x y)) in H; cbv beta iota in H
         | [ |- beq ?x ?y = true ] => refine (@reflect_of_dec _ _ true (lem x y) _)
         | [ |- beq ?x ?y = false ] => refine (@reflect_of_dec _ _ false (lem x y) _)
         | [ H : beq ?x ?y = true |- ?G ]
           => change (mark G); generalize dependent (bl x y H); clear H;
              intros; cbv beta delta [mark]
         | [ H : context[beq ?x ?x] |- _ ] => rewrite (lb x x eq_refl) in H
         end.
