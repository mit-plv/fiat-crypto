Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tactics.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Type).
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type_gen interp_base_type.
  Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

  Lemma interpf_SmartVar t v
    : Syntax.interpf interp_op (SmartVar (t:=t) v) = v.
  Proof.
    unfold SmartVar; induction t;
      repeat match goal with
             | _ => reflexivity
             | _ => progress simpl in *
             | _ => progress rewrite_hyp *
             | _ => rewrite <- surjective_pairing
             end.
  Qed.
End language.
