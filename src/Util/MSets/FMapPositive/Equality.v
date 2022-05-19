Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Decidable.

Module PositiveMap.
  Scheme Induction for PositiveMap.tree Sort Type.
  Scheme Induction for PositiveMap.tree Sort Set.
  Scheme Induction for PositiveMap.tree Sort Prop.
  Scheme Equality for PositiveMap.tree.

  Notation t_beq := tree_beq.
  Notation t_eq_dec := tree_eq_dec.
  Notation internal_t_dec_bl := internal_tree_dec_bl.
  Notation internal_t_dec_lb := internal_tree_dec_lb.

  Lemma tree_eq_dec' {A} (A_dec : forall x y : A, {x = y} + {x <> y})
    : forall x y : PositiveMap.tree A, {x = y} + {x <> y}.
  Proof.
    intros; do 2 decide equality.
  Qed.

  Global Instance tree_dec_eq {A} {A_dec : DecidableRel (@eq A)}
    : DecidableRel (@eq (PositiveMap.tree A))
    := @tree_eq_dec' A A_dec.
  Global Instance t_dec_eq {A} {A_dec : DecidableRel (@eq A)}
    : DecidableRel (@eq (PositiveMap.t A))
    := @tree_eq_dec' A A_dec.
End PositiveMap.
