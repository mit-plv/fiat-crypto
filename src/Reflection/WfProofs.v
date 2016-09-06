Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tactics.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type_gen interp_base_type.
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation wff := (@wff base_type_code interp_base_type op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.
    Local Hint Constructors Syntax.wff.
    Lemma wff_in_impl_Proper G0 G1 {t} e1 e2
      : @wff var1 var2 G0 t e1 e2
        -> (forall x, List.In x G0 -> List.In x G1)
        -> @wff var1 var2 G1 t e1 e2.
    Proof.
      intro wf; revert G1; induction wf;
        repeat match goal with
               | _ => setoid_rewrite List.in_app_iff
               | _ => progress intros
               | _ => progress simpl in *
               | [ |- wff _ _ _ ] => constructor
               | [ H : _ |- _ ] => apply H
               | _ => solve [ intuition eauto ]
               end.
    Qed.
  End with_var.
End language.
