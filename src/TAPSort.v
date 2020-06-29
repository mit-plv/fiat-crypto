Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Mergesort.


Module TAPOrder <: Orders.TotalLeBool.
  Local Coercion is_true : bool >-> Sortclass.
  Definition t := (Z * Z)%type.
  Definition leb (x y : t) := Z.geb (snd x) (snd y).
  Infix "<=?" := leb.
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof.
    intros; cbv [is_true leb]; rewrite !Z.geb_le; lia.
  Qed.
End TAPOrder.

Module TAPSort := Sort TAPOrder.

Notation sort := TAPSort.sort.
