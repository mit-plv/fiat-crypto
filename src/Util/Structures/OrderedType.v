Require Import Coq.Structures.OrderedType.

(* variant that can be included nicely *)
Module OT_of_MOT (Import O : MiniOrderedType).
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof with auto with ordered_type.
   intros x y; elim (compare x y); intro H; [ right | left | right ]...
   assert (~ eq y x)...
  Defined.
End OT_of_MOT.
