Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.

Module Compilers.
  Import Language.Compilers.
  Module type.
    Section with_base.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).

      Section encode_decode.
        Definition code (t1 t2 : type) : Prop
          := match t1, t2 with
             | type.base t1, type.base t2 => t1 = t2
             | type.arrow s1 d1, type.arrow s2 d2 => s1 = s2 /\ d1 = d2
             | type.base _, _
             | type.arrow _ _, _
               => False
             end.

        Definition encode (x y : type) : x = y -> code x y.
        Proof. intro p; destruct p, x; repeat constructor. Defined.
        Definition decode (x y : type) : code x y -> x = y.
        Proof. destruct x, y; intro p; try assumption; destruct p; f_equal; assumption. Defined.

        Definition path_rect {x y : type} (Q : x = y -> Type)
                   (f : forall p, Q (decode x y p))
          : forall p, Q p.
        Proof. intro p; specialize (f (encode x y p)); destruct x, p; exact f. Defined.
      End encode_decode.
    End with_base.

    Ltac induction_type_in_using H rect :=
      induction H as [H] using (rect _ _ _);
      cbv [code] in H;
      let H1 := fresh H in
      let H2 := fresh H in
      try lazymatch type of H with
          | False => exfalso; exact H
          | True => destruct H
          | _ /\ _ => destruct H as [H1 H2]
          end.
    Ltac inversion_type_step :=
      lazymatch goal with
      | [ H : _ = type.base _ |- _ ]
        => induction_type_in_using H @path_rect
      | [ H : type.base _ = _ |- _ ]
        => induction_type_in_using H @path_rect
      | [ H : _ = type.arrow _ _ |- _ ]
        => induction_type_in_using H @path_rect
      | [ H : type.arrow _ _ = _ |- _ ]
        => induction_type_in_using H @path_rect
      end.
    Ltac inversion_type := repeat inversion_type_step.
  End type.

  Module base.
    Module type.
      Section encode_decode.
          Definition code (t1 t2 : base.type) : Prop
            := match t1, t2 with
               | base.type.type_base t1, base.type.type_base t2 => t1 = t2
               | base.type.prod A1 B1, base.type.prod A2 B2 => A1 = A2 /\ B1 = B2
               | base.type.list A1, base.type.list A2 => A1 = A2
               | base.type.type_base _, _
               | base.type.prod _ _, _
               | base.type.list _, _
                 => False
               end.

          Definition encode (x y : base.type) : x = y -> code x y.
          Proof. intro p; destruct p, x; repeat constructor. Defined.
          Definition decode (x y : base.type) : code x y -> x = y.
          Proof. destruct x, y; intro p; try assumption; destruct p; f_equal; assumption. Defined.

          Definition path_rect {x y : base.type} (Q : x = y -> Type)
                     (f : forall p, Q (decode x y p))
            : forall p, Q p.
          Proof. intro p; specialize (f (encode x y p)); destruct x, p; exact f. Defined.
      End encode_decode.

      Ltac induction_type_in_using H rect :=
        induction H as [H] using (rect _ _);
        cbv [code] in H;
        let H1 := fresh H in
        let H2 := fresh H in
        try lazymatch type of H with
            | False => exfalso; exact H
            | True => destruct H
            | ?x = ?x => clear H
            | _ = _ :> base.type.base => try solve [ exfalso; inversion H ]
            | _ /\ _ => destruct H as [H1 H2]
            end.

      Ltac inversion_type_step :=
        cbv [defaults.type_base] in *;
        lazymatch goal with
        | [ H : _ = base.type.type_base _ |- _ ]
          => induction_type_in_using H @path_rect
        | [ H : base.type.type_base _ = _ |- _ ]
          => induction_type_in_using H @path_rect
        | [ H : _ = base.type.prod _ _ |- _ ]
          => induction_type_in_using H @path_rect
        | [ H : base.type.prod _ _ = _ |- _ ]
          => induction_type_in_using H @path_rect
        | [ H : _ = base.type.list _ |- _ ]
          => induction_type_in_using H @path_rect
        | [ H : base.type.list _ = _ |- _ ]
          => induction_type_in_using H @path_rect
        end.
      Ltac inversion_type := repeat inversion_type_step.
    End type.
  End base.

  Module expr.
    Section with_var.
      Context {base_type : Type}
              {ident var : type.type base_type -> Type}.
      Local Notation type := (type.type base_type).
      Local Notation expr := (@expr.expr base_type ident var).

      Section encode_decode.
        Definition code {t} (e1 : expr t) : expr t -> Prop
          := match e1 with
             | expr.Ident t idc => fun e' => invert_expr.invert_Ident e' = Some idc
             | expr.Var t v => fun e' => invert_expr.invert_Var e' = Some v
             | expr.Abs s d f => fun e' => invert_expr.invert_Abs e' = Some f
             | expr.App s d f x => fun e' => invert_expr.invert_App e' = Some (existT _ _ (f, x))
             | expr.LetIn A B x f => fun e' => invert_expr.invert_LetIn e' = Some (existT _ _ (x, f))
             end.

        Definition encode {t} (x y : expr t) : x = y -> code x y.
        Proof. intro p; destruct p, x; reflexivity. Defined.

        Local Ltac t' :=
          repeat first [ intro
                       | progress cbn in *
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
                      | expr.Var _ _ => _
                      | _ => _
                      end
          end;
          t'.

        Lemma invert_Ident_Some {t} {e : expr t} {v} : invert_expr.invert_Ident e = Some v -> e = expr.Ident v.
        Proof. t. Defined.
        Lemma invert_Var_Some {t} {e : expr t} {v} : invert_expr.invert_Var e = Some v -> e = expr.Var v.
        Proof. t. Defined.
        Lemma invert_Abs_Some {s d} {e : expr (s -> d)} {v} : invert_expr.invert_Abs e = Some v -> e = expr.Abs v.
        Proof. t. Defined.
        Lemma invert_App_Some {t} {e : expr t} {v} : invert_expr.invert_App e = Some v -> e = expr.App (fst (projT2 v)) (snd (projT2 v)).
        Proof. t. Defined.
        Lemma invert_LetIn_Some {t} {e : expr t} {v} : invert_expr.invert_LetIn e = Some v -> e = expr.LetIn (fst (projT2 v)) (snd (projT2 v)).
        Proof. t. Defined.

        Definition decode {t} (x y : expr t) : code x y -> x = y.
        Proof.
          destruct x; cbn [code]; intro p; symmetry;
            first [ apply invert_Ident_Some in p
                  | apply invert_Var_Some in p
                  | apply invert_Abs_Some in p
                  | apply invert_App_Some in p
                  | apply invert_LetIn_Some in p ];
            assumption.
        Defined.

        Definition path_rect {t} {x y : expr t} (Q : x = y -> Type)
                   (f : forall p, Q (decode x y p))
          : forall p, Q p.
        Proof. intro p; specialize (f (encode x y p)); destruct x, p; exact f. Defined.
      End encode_decode.
    End with_var.

    Ltac invert_one e :=
      generalize_eqs_vars e;
      destruct e;
      type.inversion_type;
      base.type.inversion_type;
      try discriminate.

    Ltac invert_step :=
      match goal with
      | [ e : expr (type.base _) |- _ ] => invert_one e
      | [ e : expr (type.arrow _ _) |- _ ] => invert_one e
      end.

    Ltac invert := repeat invert_step.

    Ltac invert_match_step :=
      match goal with
      | [ |- context[match ?e with expr.Ident _ _ => _ | _ => _ end] ]
        => invert_one e
      | [ |- context[match ?e with expr.Var _ _ => _ end] ]
        => invert_one e
      | [ |- context[match ?e with expr.App _ _ _ _ => _ end] ]
        => invert_one e
      | [ |- context[match ?e with expr.LetIn _ _ _ _ => _ end] ]
        => invert_one e
      | [ |- context[match ?e with expr.Abs _ _ _ => _ end] ]
        => invert_one e
      end.

    Ltac invert_match := repeat invert_match_step.

    Ltac invert_subst_step_helper guard_tac :=
      match goal with
      | [ H : invert_expr.invert_Var ?e = Some _ |- _ ] => guard_tac H; apply invert_Var_Some in H
      | [ H : invert_expr.invert_Ident ?e = Some _ |- _ ] => guard_tac H; apply invert_Ident_Some in H
      | [ H : invert_expr.invert_LetIn ?e = Some _ |- _ ] => guard_tac H; apply invert_LetIn_Some in H
      | [ H : invert_expr.invert_App ?e = Some _ |- _ ] => guard_tac H; apply invert_App_Some in H
      | [ H : invert_expr.invert_Abs ?e = Some _ |- _ ] => guard_tac H; apply invert_Abs_Some in H
      end.
    Ltac invert_subst_step :=
      first [ invert_subst_step_helper ltac:(fun _ => idtac)
            | subst ].
    Ltac invert_subst := repeat invert_subst_step.

    Ltac induction_expr_in_using H rect :=
      induction H as [H] using (rect _ _ _);
      cbv [code invert_expr.invert_Var invert_expr.invert_LetIn invert_expr.invert_App invert_expr.invert_LetIn invert_expr.invert_Ident invert_expr.invert_Abs] in H;
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
      | [ H : _ = expr.Var _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : _ = expr.Ident _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : _ = expr.App _ _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : _ = expr.LetIn _ _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : _ = expr.Abs _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : expr.Var _ = _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : expr.Ident = _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : expr.App _ _ = _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : expr.LetIn _ _ = _ |- _ ]
        => induction_expr_in_using H @path_rect
      | [ H : expr.Abs _ = _ |- _ ]
        => induction_expr_in_using H @path_rect
      end.
    Ltac inversion_expr := repeat inversion_expr_step.
  End expr.
End Compilers.
