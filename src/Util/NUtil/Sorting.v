Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.
Require Coq.Sorting.Mergesort.

Module N.
  Module Order <: Orders.TotalLeBool.
    Local Open Scope N_scope.
    Definition t := N.
    Definition ltb := N.ltb.
    Definition leb := N.leb.
    Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
    Proof.
      cbv [leb ltb]; intros a1 a2.
      repeat first [ rewrite !Bool.andb_true_iff
                   | rewrite !Bool.orb_true_iff
                   | rewrite !N.eqb_eq
                   | rewrite !N.ltb_lt
                   | rewrite !N.leb_le ].
      lia.
    Qed.
  End Order.

  Module Sort := Mergesort.Sort Order.
  Notation sort := Sort.sort.
End N.
