Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Sorting.Mergesort Coq.Structures.Orders.

Module Z.
  Module Order <: TotalLeBool.
    Definition t := Z.
    Definition leb := Z.leb.
    Infix "<=?" := leb.
    Local Coercion is_true : bool >-> Sortclass.
    Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
    Proof. intros x y; destruct (Z.le_ge_cases x y); [ left | right ]; unfold is_true, leb; rewrite Z.leb_le; lia. Qed.
  End Order.

  Module Sort := Mergesort.Sort Order.

  Notation sort := Sort.sort.
  Notation Sorted_sort := Sort.Sorted_sort.
  Notation LocallySorted_sort := Sort.LocallySorted_sort.
  Notation StronglySorted_sort := Sort.StronglySorted_sort.
  Notation Permuted_sort := Sort.Permuted_sort.
End Z.
