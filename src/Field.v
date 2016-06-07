Require Import Coq.setoid_ring.Cring.
Generalizable All Variables.

Class Field_ops (F:Type)
      `{Ring_ops F}
      {inv:F->F} := {}.

Class Division (A B:Type) := division : A -> B -> A.

Notation "_/_" := division.
Notation "n / d" := (division n d).

Module Field.

  Definition div `{Field_ops F} n d := mul n (inv d).
  Global Instance div_notation `{Field_ops F} : @Division F F := div.

  Class Field {F inv} `{FieldCring:Cring (R:=F)} {Fo:Field_ops F (inv:=inv)} :=
    {
      field_inv_comp : Proper (_==_ ==> _==_) inv;
      field_inv_def : forall x, (x == 0 -> False) -> inv x * x == 1;
      field_zero_neq_one : 0 == 1 -> False
    }.
  Global Existing Instance field_inv_comp.

  Definition powZ `{Field_ops F} (x:F) (n:Z) :=
    match n with
      | Z0 => 1
      | Zpos p => pow_pos x p
      | Zneg p => inv (pow_pos x p)
    end.
  Global Instance power_field `{Field_ops F} : Power | 5 := { power := powZ }.

  Section FieldProofs.
    Context F `{Field F}.
    Require Import Coq.setoid_ring.Field_theory.
    Lemma Field_theory_for_tactic : field_theory 0 1 _+_ _*_ _-_ -_ _/_ inv _==_.
    Proof.
      split; repeat constructor; repeat intro; gen_rewrite; try cring.
      { apply field_zero_neq_one. symmetry; assumption. }
      { apply field_inv_def. assumption. }
    Qed.

  End FieldProofs.
End Field.