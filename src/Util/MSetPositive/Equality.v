Require Import Coq.MSets.MSetPositive.
Require Import Crypto.Util.Bool.Equality.
Require Import Crypto.Util.Decidable.

Module PositiveSet.
  Scheme Equality for PositiveSet.tree.

  Notation t_beq := tree_beq.
  Notation t_eq_dec := tree_eq_dec.
  Notation internal_t_dec_bl := internal_tree_dec_bl.
  Notation internal_t_dec_lb := internal_tree_dec_lb.

  Global Instance tree_dec_eq : DecidableRel (@eq PositiveSet.tree) := tree_eq_dec.
  Global Instance t_dec_eq : DecidableRel (@eq PositiveSet.t) := t_eq_dec.
End PositiveSet.
