Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.SmartCast.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (wff_Cast : forall var1 var2 G A A' e1 e2,
              wff G e1 e2 -> wff G (Cast var1 A A' e1) (Cast var2 A A' e2)).

  Local Notation exprf := (@exprf base_type_code op).
  Local Notation SmartCast_base := (@SmartCast_base _ _ _ base_type_bl_transparent Cast).
  Local Notation SmartCast := (@SmartCast _ _ _ base_type_bl_transparent Cast).

  Lemma wff_SmartCast_base {var1 var2 A A'} G e1 e2
        (Hwf : wff (var1:=var1) (var2:=var2) G (t:=Tbase A) e1 e2)
    : wff G (t:=Tbase A') (SmartCast_base e1) (SmartCast_base e2).
  Proof using wff_Cast.
    unfold SmartCast_base; destruct (Sumbool.sumbool_of_bool (base_type_beq A A')) as [H|H].
    { destruct (base_type_bl_transparent A A' H); assumption. }
    { auto. }
  Qed.

  Local Hint Resolve List.in_or_app wff_in_impl_Proper.
  Local Hint Extern 1 => progress simpl.

  Lemma wff_SmartCast_match {var1 var2} A B
    : match SmartCast A B, SmartCast A B with
      | Some f1, Some f2
        => forall e1 e2,
          wff (var1:=var1) (var2:=var2) (flatten_binding_list e1 e2) (f1 e1) (f2 e2)
      | None, None => True
      | Some _, None | None, Some _ => False
      end.
  Proof using wff_Cast.
    break_innermost_match; revert dependent B; induction A, B;
      repeat match goal with
             | _ => progress simpl in *
             | _ => intro
             | _ => progress subst
             | _ => progress inversion_option
             | [ |- wff _ (SmartCast_base _) (SmartCast_base _) ]
               => apply wff_SmartCast_base
             | _ => progress break_match_hyps
             | _ => solve [ eauto with wf ]
             | [ H : forall B f1 f2, SmartCast ?A B = Some f1 -> SmartCast ?A B = Some f2 -> _,
                   H' : SmartCast ?A ?Bv = Some _, H'' : SmartCast ?A ?Bv = Some _ |- _ ]
               => specialize (H _ _ _ H' H'')
             | [ |- wff _ (Pair _ _) (Pair _ _) ] => constructor
             | [ |- wff _ _ _ ] => solve [ eauto with wf ]
             end.
  Qed.

  Lemma wff_SmartCast {var1 var2} A B f1 f2
    : SmartCast A B = Some f1 -> SmartCast A B = Some f2
      -> forall e1 e2,
          wff (var1:=var1) (var2:=var2) (flatten_binding_list e1 e2) (f1 e1) (f2 e2).
  Proof using wff_Cast.
    intros H1 H2; generalize (@wff_SmartCast_match var1 var2 A B).
    rewrite H1, H2; trivial.
  Qed.

  Lemma wff_SmartCast_app {var1 var2} G A B f1 f2
    : SmartCast A B = Some f1 -> SmartCast A B = Some f2
      -> forall e1 e2,
          wff (var1:=var1) (var2:=var2) (flatten_binding_list e1 e2 ++ G) (f1 e1) (f2 e2).
  Proof using wff_Cast.
    intros; eapply wff_in_impl_Proper; [ eapply wff_SmartCast; eassumption | auto ].
  Qed.
End language.

Hint Resolve wff_SmartCast_base wff_SmartCast wff_SmartCast_app : wf.
