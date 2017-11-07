Require Import Crypto.Util.Decidable.

Definition vm_decide_package (P : Prop) := P.
Definition cbv_minus_then_vm_decide_package {T} (ident : T) (P : Prop) := P.
Definition vm_compute_reflexivity_package (P : Prop) := P.

Ltac autosolve else_tac :=
  lazymatch goal with
  | [ |- vm_decide_package ?P ] => cbv beta delta [vm_decide_package]; vm_decide
  | [ |- cbv_minus_then_vm_decide_package ?ident ?P ] => cbv -[ident]; vm_decide
  | [ |- vm_compute_reflexivity_package ?P ] => vm_compute; reflexivity
  | _ => else_tac ()
  end.
