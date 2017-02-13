Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.SmartCast.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
          {base_type_beq : base_type_code -> base_type_code -> bool}
          {base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y}
          {Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A')}
          (interpf_Cast_id : forall A x, interpf interp_op (Cast _ A A x) = interpf interp_op x)
          {cast_val : forall A A', interp_base_type A -> interp_base_type A'}
          (interpf_cast : forall A A' e, interpf interp_op (Cast _ A A' e) = cast_val A A' (interpf interp_op e)).

  Local Notation exprf := (@exprf base_type_code op).
  Local Notation SmartCast_base := (@SmartCast_base _ _ _ base_type_bl_transparent Cast).
  Local Notation SmartCast := (@SmartCast _ _ _ base_type_bl_transparent Cast).

  Lemma interpf_SmartCast_base {A A'} (x : exprf (Tbase A))
    : interpf interp_op (SmartCast_base x) = interpf interp_op (Cast _ A A' x).
  Proof.
    clear dependent cast_val.
    unfold SmartCast_base.
    destruct (Sumbool.sumbool_of_bool (base_type_beq A A')) as [H|H].
    { destruct (base_type_bl_transparent A A' H).
      rewrite interpf_Cast_id; reflexivity. }
    { reflexivity. }
  Qed.
End language.
