Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.

Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type_gen := interp_flat_type.
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation Expr := (@Expr base_type_code op).

  Fixpoint codomain (t : type) : flat_type
    := match t with
       | Tflat T => T
       | Arrow src dst => codomain dst
       end.

  Section with_var.
    Context {var : base_type_code -> Type}.

    Local Notation exprf := (@exprf base_type_code op var).
    Local Notation expr := (@expr base_type_code op var).

    Definition invert_Var {t} (e : exprf (Tbase t)) : option (var t)
      := match e in Syntax.exprf _ _ t'
               return option (var match t' with
                                  | Tbase t' => t'
                                  | _ => t
                                  end)
         with
         | Var _ v => Some v
         | _ => None
         end.
    Definition invert_Op {t} (e : exprf t) : option { t1 : flat_type & op t1 t * exprf t1 }%type
      := match e with Op _ _ opc args => Some (existT _ _ (opc, args)) | _ => None end.
    Definition invert_LetIn {A} (e : exprf A) : option { B : _ & exprf B * (Syntax.interp_flat_type var B -> exprf A) }%type
      := match e in Syntax.exprf _ _ t return option { B : _ & _ * (_ -> exprf t) }%type with
         | LetIn _ ex _ eC => Some (existT _ _ (ex, eC))
         | _ => None
         end.
    Definition invert_Pair {A B} (e : exprf (Prod A B)) : option (exprf A * exprf B)
      := match e in Syntax.exprf _ _ t
               return option match t with
                             | Prod _ _ => _
                             | _ => unit
                             end with
         | Pair _ x _ y => Some (x, y)%core
         | _ => None
         end.
    Definition invert_Abs {A B} (e : expr (Arrow A B)) : var A -> expr B
      := match e with Abs _ _ f => f end.
    Definition invert_Return {t} (e : expr (Tflat t)) : exprf t
      := match e with Return _ v => v end.

    Local Ltac t' :=
      repeat first [ intro
                   | progress simpl in *
                   | reflexivity
                   | assumption
                   | progress destruct_head False
                   | progress subst
                   | progress inversion_option
                   | progress inversion_sigma
                   | progress break_match ].
    Local Ltac t :=
      lazymatch goal with
      | [ |- _ = Some ?v -> ?e = _ ]
        => revert v;
           refine match e with
                  | Var _ _ => _
                  | _ => _
                  end
      | [ |- _ = ?v -> ?e = _ ]
        => revert v;
           refine match e with
                  | Abs _ _ _ => _
                  | Return _ _ => _
                  end
      end;
      t'.

    Lemma invert_Var_Some {t e v}
      : @invert_Var t e = Some v -> e = Var v.
    Proof. t. Defined.

    Lemma invert_Op_Some {t e v}
      : @invert_Op t e = Some v -> e = Op (fst (projT2 v)) (snd (projT2 v)).
    Proof. t. Defined.

    Lemma invert_LetIn_Some {t e v}
      : @invert_LetIn t e = Some v -> e = LetIn (fst (projT2 v)) (snd (projT2 v)).
    Proof. t. Defined.

    Lemma invert_Pair_Some {A B e v}
      : @invert_Pair A B e = Some v -> e = Pair (fst v) (snd v).
    Proof. t. Defined.

    Lemma invert_Abs_Some {A B e v}
      : @invert_Abs A B e = v -> e = Abs v.
    Proof. t. Defined.

    Lemma invert_Return_Some {t e v}
      : @invert_Return t e = v -> e = Return v.
    Proof. t. Qed.
  End with_var.

  Lemma interpf_invert_Abs interp_op {A B e} x
    : Syntax.interp interp_op (@invert_Abs interp_base_type A B e x)
      = Syntax.interp interp_op e x.
  Proof.
    refine (match e in expr _ _ t
                  return match t return expr _ _ t -> _ with
                         | Arrow src dst
                           => fun e
                              => (forall x : interp_base_type src,
                                     interp _ (invert_Abs e x) = interp _ e x)
                         | Tflat _ => fun _ => True
                         end e with
            | Abs _ _ _ => fun _ => eq_refl
            | Return _ _ => I
            end x).
  Qed.
End language.

Global Arguments codomain {_} _.
Global Arguments invert_Var {_ _ _ _} _.
Global Arguments invert_Op {_ _ _ _} _.
Global Arguments invert_LetIn {_ _ _ _} _.
Global Arguments invert_Pair {_ _ _ _ _} _.
Global Arguments invert_Abs {_ _ _ _ _} _ _.
Global Arguments invert_Return {_ _ _ _} _.

Ltac invert_expr_subst_step :=
  match goal with
  | _ => progress subst
  | [ H : invert_Var ?e = Some _ |- _ ] => apply invert_Var_Some in H
  | [ H : invert_Op ?e = Some _ |- _ ] => apply invert_Op_Some in H
  | [ H : invert_LetIn ?e = Some _ |- _ ] => apply invert_LetIn in H
  | [ H : invert_Pair ?e = Some _ |- _ ] => apply invert_Pair_Some in H
  | [ H : invert_Abs ?e = _ |- _ ] => apply invert_Abs_Some in H
  | [ H : invert_Return ?e = _ |- _ ] => apply invert_Return_Some in H
  end.
Ltac invert_expr_subst := repeat invert_expr_subst_step.
