Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.Equivalence.
Require Import NArith BinPosDef.
Local Open Scope equiv_scope.

Generalizable All Variables.
Section IterAssocOp.
  Context `{Equivalence T}
          (op:T->T->T) {op_proper:Proper (equiv==>equiv==>equiv) op}
          (assoc: forall a b c, op a (op b c) === op (op a b) c)
          (neutral:T) (neutral_neutral : forall a, op a neutral === a).
  Existing Instance op_proper.

  Fixpoint nat_iter_op n a :=
    match n with
    | 0%nat => neutral
    | S n' => op a (nat_iter_op n' a)
    end.

  Definition N_iter_op n a :=
    match n with
    | 0%N => neutral
    | Npos p => Pos.iter_op op p a
    end.

  Lemma Pos_iter_op_succ : forall p a, Pos.iter_op op (Pos.succ p) a === op a (Pos.iter_op op p a).
  Proof.
   induction p; intros; simpl; rewrite ?assoc, ?IHp; reflexivity.
  Qed.

  Lemma N_iter_op_succ : forall n a, N_iter_op (N.succ n) a  === op a (N_iter_op n a).
  Proof.
    destruct n; simpl; intros; rewrite ?Pos_iter_op_succ, ?neutral_neutral; reflexivity.
  Qed.

  Lemma N_iter_op_is_nat_iter_op : forall n a, N_iter_op n a === nat_iter_op (N.to_nat n) a.
  Proof.
    induction n using N.peano_ind; intros; rewrite ?N2Nat.inj_succ, ?N_iter_op_succ, ?IHn; reflexivity.
  Qed.
End IterAssocOp.