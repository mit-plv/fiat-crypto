Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
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
    Definition invert_Abs {T} (e : expr T) : interp_flat_type_gen var (domain T) -> exprf (codomain T)
      := match e with Abs _ _ f => f end.

    Definition exprf_code {t} (e : exprf t) : exprf t -> Prop
      := match e with
         | TT => fun e' => TT = e'
         | Var _ v => fun e' => invert_Var e' = Some v
         | Pair _ x _ y => fun e' => invert_Pair e' = Some (x, y)%core
         | Op _ _ opc args => fun e' => invert_Op e' = Some (existT _ _ (opc, args)%core)
         | LetIn _ ex _ eC => fun e' => invert_LetIn e' = Some (existT _ _ (ex, eC)%core)
         end.

    Definition expr_code {t} (e1 e2 : expr t) : Prop
      := invert_Abs e1 = invert_Abs e2.

    Definition exprf_encode {t} (x y : exprf t) : x = y -> exprf_code x y.
    Proof. intro p; destruct p, x; reflexivity. Defined.
    Definition expr_encode {t} (x y : expr t) : x = y -> expr_code x y.
    Proof. intro p; destruct p, x; reflexivity. Defined.

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
      : @invert_Abs (Arrow A B) e = v -> e = Abs v.
    Proof. t. Defined.

    Definition exprf_decode {t} (x y : exprf t) : exprf_code x y -> x = y.
    Proof.
      destruct x; simpl; trivial;
        intro H;
        first [ apply invert_Var_Some in H
              | apply invert_Op_Some in H
              | apply invert_LetIn_Some in H
              | apply invert_Pair_Some in H ];
        symmetry; assumption.
    Defined.
    Definition expr_decode {t} (x y : expr t) : expr_code x y -> x = y.
    Proof.
      destruct x; unfold expr_code; simpl.
      intro H; symmetry in H.
      apply invert_Abs_Some in H.
      symmetry; assumption.
    Defined.
    Definition path_exprf_rect {t} {x y : exprf t} (Q : x = y -> Type)
               (f : forall p, Q (exprf_decode x y p))
      : forall p, Q p.
    Proof. intro p; specialize (f (exprf_encode x y p)); destruct x, p; exact f. Defined.
    Definition path_expr_rect {t} {x y : expr t} (Q : x = y -> Type)
               (f : forall p, Q (expr_decode x y p))
      : forall p, Q p.
    Proof. intro p; specialize (f (expr_encode x y p)); destruct x, p; exact f. Defined.
  End with_var.

  Lemma interpf_invert_Abs interp_op {T e} x
    : Syntax.interpf interp_op (@invert_Abs interp_base_type T e x)
      = Syntax.interp interp_op e x.
  Proof using Type. destruct e; reflexivity. Qed.
End language.

Global Arguments invert_Var {_ _ _ _} _.
Global Arguments invert_Op {_ _ _ _} _.
Global Arguments invert_LetIn {_ _ _ _} _.
Global Arguments invert_Pair {_ _ _ _ _} _.
Global Arguments invert_Abs {_ _ _ _} _ _.

Ltac invert_one_expr e :=
  preinvert_one_type e;
  intros ? e;
  destruct e;
  try exact I.

Ltac invert_expr_step :=
  match goal with
  | [ e : exprf _ _ (Tbase _) |- _ ] => invert_one_expr e
  | [ e : exprf _ _ (Prod _ _) |- _ ] => invert_one_expr e
  | [ e : exprf _ _ Unit |- _ ] => invert_one_expr e
  | [ e : expr _ _ (Arrow _ _) |- _ ] => invert_one_expr e
  end.

Ltac invert_expr := repeat invert_expr_step.

Ltac invert_match_expr_step :=
  match goal with
  | [ |- context[match ?e with TT => _ | _ => _ end] ]
    => invert_one_expr e
  | [ |- context[match ?e with Abs _ _ _ => _ end] ]
    => invert_one_expr e
  | [ H : context[match ?e with TT => _ | _ => _ end] |- _ ]
    => invert_one_expr e
  | [ H : context[match ?e with Abs _ _ _ => _ end] |- _ ]
    => invert_one_expr e
  end.

Ltac invert_match_expr := repeat invert_match_expr_step.

Ltac invert_expr_subst_step_helper guard_tac :=
  match goal with
  | [ H : invert_Var ?e = Some _ |- _ ] => guard_tac H; apply invert_Var_Some in H
  | [ H : invert_Op ?e = Some _ |- _ ] => guard_tac H; apply invert_Op_Some in H
  | [ H : invert_LetIn ?e = Some _ |- _ ] => guard_tac H; apply invert_LetIn_Some in H
  | [ H : invert_Pair ?e = Some _ |- _ ] => guard_tac H; apply invert_Pair_Some in H
  | [ e : expr _ _ _ |- _ ]
    => guard_tac e;
       let f := fresh e in
       let H := fresh in
       rename e into f;
       remember (invert_Abs f) as e eqn:H;
       symmetry in H;
       apply invert_Abs_Some in H;
       subst f
  | [ H : invert_Abs ?e = _ |- _ ] => guard_tac H; apply invert_Abs_Some in H
  end.
Ltac invert_expr_subst_step :=
  first [ invert_expr_subst_step_helper ltac:(fun _ => idtac)
        | subst ].
Ltac invert_expr_subst := repeat invert_expr_subst_step.

Ltac induction_expr_in_using H rect :=
  induction H as [H] using (rect _ _ _);
  cbv [exprf_code expr_code invert_Var invert_LetIn invert_Pair invert_Op invert_Abs] in H;
  try lazymatch type of H with
      | Some _ = Some _ => apply option_leq_to_eq in H; unfold option_eq in H
      | Some _ = None => exfalso; clear -H; solve [ inversion H ]
      | None = Some _ => exfalso; clear -H; solve [ inversion H ]
      end;
  let H1 := fresh H in
  let H2 := fresh H in
  try lazymatch type of H with
      | existT _ _ _ = existT _ _ _ => induction_sigma_in_using H @path_sigT_rect
      end;
  try lazymatch type of H2 with
      | _ = (_, _)%core => induction_path_prod H2
      end.
Ltac inversion_expr_step :=
  match goal with
  | [ H : _ = Var _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : _ = TT |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : _ = Op _ _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : _ = Pair _ _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : _ = LetIn _ _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : _ = Abs _ |- _ ]
    => induction_expr_in_using H @path_expr_rect
  | [ H : Var _ = _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : TT = _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : Op _ _ = _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : Pair _ _ = _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : LetIn _ _ = _ |- _ ]
    => induction_expr_in_using H @path_exprf_rect
  | [ H : Abs _ = _ |- _ ]
    => induction_expr_in_using H @path_expr_rect
  end.
Ltac inversion_expr := repeat inversion_expr_step.
