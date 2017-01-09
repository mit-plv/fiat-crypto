Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Application.

Section language.
  Context {base_type1 base_type2 : Type}
          {interp_base_type1 : base_type1 -> Type}
          {interp_base_type2 : base_type2 -> Type}
          {op1 : flat_type base_type1 -> flat_type base_type1 -> Type}
          {op2 : flat_type base_type2 -> flat_type base_type2 -> Type}
          {interp_op1 : forall src dst, op1 src dst -> interp_flat_type interp_base_type1 src -> interp_flat_type interp_base_type1 dst}
          {interp_op2 : forall src dst, op2 src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst}
          (R : forall t1 t2, interp_base_type1 t1 -> interp_base_type2 t2 -> Prop).

  Fixpoint rel_interp_all_binders_for' {t1 : type base_type1} {t2 : type base_type2}
    : interp_all_binders_for' t1 interp_base_type1 -> interp_all_binders_for' t2 interp_base_type2 -> Prop
    := match t1, t2 return interp_all_binders_for' t1 _ -> interp_all_binders_for' t2 _ -> Prop with
       | Tflat T1, Tflat T2 => fun _ _ => True
       | Arrow A1 B1, Arrow A2 B2
         => fun x y => R _ _ (fst x) (fst y) /\ @rel_interp_all_binders_for' _ _ (snd x) (snd y)
       | Tflat _, _
       | Arrow _ _, _
         => fun _ _ => False
       end.
  Definition rel_interp_all_binders_for {t1 : type base_type1} {t2 : type base_type2}
             (x : interp_all_binders_for t1 interp_base_type1) (y : interp_all_binders_for t2 interp_base_type2)
    : Prop
    := rel_interp_all_binders_for' (interp_all_binders_for_to' x) (interp_all_binders_for_to' y).
End language.
