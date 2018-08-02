Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.FixCoqMistakes.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.

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
          Proof. destruct x, y; intro p; try assumption; destruct p; (apply f_equal || apply f_equal2); (assumption || reflexivity). Defined.

          Definition path_rect {x y : base.type} (Q : x = y -> Type)
                     (f : forall p, Q (decode x y p))
            : forall p, Q p.
          Proof. intro p; specialize (f (encode x y p)); destruct x, p; exact f. Defined.
      End encode_decode.

      Global Instance base_eq_Decidable : DecidableRel (@eq base.type.base) := base.type.base_eq_dec.
      Global Instance base_type_eq_Decidable : DecidableRel (@eq base.type.type) := base.type.type_eq_dec.
      Global Instance base_eq_HProp : IsHPropRel (@eq base.type.base) := _.
      Global Instance base_type_eq_HProp : IsHPropRel (@eq base.type.type) := _.

      Ltac induction_type_in_using H rect :=
        induction H as [H] using (rect _ _);
        cbv [code defaults.type_base] in H;
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
        first [ lazymatch goal with
                | [ H : ?x = ?x :> base.type.type |- _ ] => clear H || eliminate_hprop_eq_helper H base_type_eq_HProp
                | [ H : ?x = ?x :> base.type.base |- _ ] => clear H || eliminate_hprop_eq_helper H base_eq_HProp
                | [ H : ?x = ?y :> base.type.type |- _ ] => subst x || subst y
                | [ H : ?x = ?y :> base.type.base |- _ ] => subst x || subst y
                end
              | lazymatch goal with
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
                end ];
        cbn [f_equal f_equal2 eq_rect decode] in *.
      Ltac inversion_type := repeat inversion_type_step.
    End type.

    Global Instance Decidable_type_eq : DecidableRel (@eq base.type)
      := base.type.type_eq_dec.

    Local Ltac t_red :=
      repeat first [ progress intros
                   | progress cbn [type.type_beq base.type.type_beq base.type.base_beq base.try_make_transport_cps base.try_make_base_transport_cps eq_rect andb] in *
                   | progress cbv [cpsreturn cpsbind cps_option_bind Option.bind cpscall] in * ].
    Local Ltac t :=
      repeat first [ progress t_red
                   | reflexivity
                   | progress split_andb
                   | progress subst
                   | progress break_innermost_match
                   | progress eliminate_hprop_eq
                   | congruence
                   | match goal with
                     | [ H : base.type.type_beq _ _ = true |- _ ] => apply base.type.internal_type_dec_bl in H; auto
                     | [ H : context[base.type.type_beq ?x ?x] |- _ ] => rewrite base.type.internal_type_dec_lb in H by auto
                     | [ |- context[base.type.internal_type_dec_bl ?x ?y ?pf] ] => generalize (base.type.internal_type_dec_bl x y pf); intro
                     | [ H : base.type.base_beq _ _ = true |- _ ] => apply base.type.internal_base_dec_bl in H; auto
                     | [ H : context[base.type.base_beq ?x ?x] |- _ ] => rewrite base.type.internal_base_dec_lb in H by auto
                     | [ |- context[base.type.internal_base_dec_bl ?x ?y ?pf] ] => generalize (base.type.internal_base_dec_bl x y pf); intro
                     | [ H : _ |- _ ] => rewrite H
                     end ].

    Lemma try_make_base_transport_cps_correct P t1 t2 T k
      : base.try_make_base_transport_cps P t1 t2 T k
        = k match Sumbool.sumbool_of_bool (base.type.base_beq t1 t2) with
            | left pf => Some (rew [fun t => P t1 -> P t] (base.type.internal_base_dec_bl _ _ pf) in id)
            | right _ => None
            end.
    Proof. revert P t2 T k; induction t1, t2; t. Qed.

    Lemma try_make_transport_cps_correct P t1 t2 T k
      : base.try_make_transport_cps P t1 t2 T k
        = k match Sumbool.sumbool_of_bool (base.type.type_beq t1 t2) with
            | left pf => Some (rew [fun t => P t1 -> P t] (base.type.internal_type_dec_bl _ _ pf) in id)
            | right _ => None
            end.
    Proof. revert P t2 T k; induction t1, t2; t_red; rewrite ?try_make_base_transport_cps_correct; t. Qed.

    Lemma try_transport_cps_correct P t1 t2 v T k
      : base.try_transport_cps P t1 t2 v T k
        = k match Sumbool.sumbool_of_bool (base.type.type_beq t1 t2) with
            | left pf => Some (rew [P] (base.type.internal_type_dec_bl _ _ pf) in v)
            | right _ => None
            end.
    Proof.
      cbv [base.try_transport_cps cpscall cps_option_bind cpsreturn cpsbind Option.bind]; rewrite try_make_transport_cps_correct;
        t.
    Qed.

    Lemma try_transport_correct P t1 t2 v
      : base.try_transport P t1 t2 v
        = match Sumbool.sumbool_of_bool (base.type.type_beq t1 t2) with
          | left pf => Some (rew [P] (base.type.internal_type_dec_bl _ _ pf) in v)
          | right _ => None
          end.
    Proof. cbv [base.try_transport]; rewrite try_transport_cps_correct; reflexivity. Qed.
  End base.

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
        Proof. destruct x, y; intro p; try assumption; destruct p; (apply f_equal || apply f_equal2); (assumption || reflexivity). Defined.

        Definition path_rect {x y : type} (Q : x = y -> Type)
                   (f : forall p, Q (decode x y p))
          : forall p, Q p.
        Proof. intro p; specialize (f (encode x y p)); destruct x, p; exact f. Defined.
      End encode_decode.

      Lemma preinvert_one_type (P : type -> Type) t (Q : P t -> Type)
        : (forall t' (v : P t') (pf : t' = t), Q (rew [P] pf in v)) -> (forall (v : P t), Q v).
      Proof. intros H v; apply (H _ _ eq_refl). Qed.
    End with_base.

    Ltac induction_type_in_using H rect :=
      induction H as [H] using (rect _ _ _);
      cbv [code defaults.type_base] in H;
      let H1 := fresh H in
      let H2 := fresh H in
      try lazymatch type of H with
          | False => exfalso; exact H
          | True => destruct H
          | _ /\ _ => destruct H as [H1 H2]
          end.
    Ltac inversion_type_step :=
      cbv [defaults.type_base] in *;
      first [ lazymatch goal with
              | [ H : ?x = ?x :> type.type _ |- _ ] => clear H
              | [ H : ?x = ?y :> type.type _ |- _ ] => subst x || subst y
              end
            | lazymatch goal with
              | [ H : _ = type.base _ |- _ ]
                => induction_type_in_using H @path_rect
              | [ H : type.base _ = _ |- _ ]
                => induction_type_in_using H @path_rect
              | [ H : _ = type.arrow _ _ |- _ ]
                => induction_type_in_using H @path_rect
              | [ H : type.arrow _ _ = _ |- _ ]
                => induction_type_in_using H @path_rect
              end ];
      cbn [f_equal f_equal2 eq_rect decode] in *.
    Ltac inversion_type := repeat inversion_type_step.

    Definition mark {T} (v : T) := v.
    Ltac generalize_one_eq_var e :=
      match goal with
      | [ |- ?G ] => change (mark G)
      end;
      revert dependent e;
      lazymatch goal with
      | [ |- forall e' : ?P ?t, @?Q e' ]
        => refine (@preinvert_one_type _ P t Q _)
      end;
      intros ? e ?; intros; cbv [mark].

    Ltac invert_one e :=
      generalize_one_eq_var e;
      destruct e;
      try discriminate;
      type.inversion_type;
      base.type.inversion_type;
      cbn [type.decode base.type.decode f_equal f_equal2 eq_rect] in *.

    Section transport_cps.
      Context {base_type}
              (base_type_beq : base_type -> base_type -> bool)
              (base_type_bl : forall t1 t2, base_type_beq t1 t2 = true -> t1 = t2)
              (base_type_lb : forall t1 t2, t1 = t2 -> base_type_beq t1 t2 = true)
              (try_make_transport_base_type_cps : forall (P : base_type -> Type) t1 t2, ~> option (P t1 -> P t2))
              (try_make_transport_base_type_cps_correct
               : forall P t1 t2 T k,
                  try_make_transport_base_type_cps P t1 t2 T k
                  = k match Sumbool.sumbool_of_bool (base_type_beq t1 t2) with
                      | left pf => Some (rew [fun t => P t1 -> P t] (base_type_bl _ _ pf) in id)
                      | right _ => None
                      end).

      Let base_type_eq_dec : DecidableRel (@eq base_type)
        := dec_rel_of_bool_dec_rel base_type_beq base_type_bl base_type_lb.

      Local Instance Decidable_type_eq : DecidableRel (@eq (@type.type base_type))
        := type.type_eq_dec _ base_type_beq base_type_bl base_type_lb.

      Local Ltac t :=
        repeat first [ progress intros
                     | progress cbn [type.type_beq type.try_make_transport_cps eq_rect andb] in *
                     | progress cbv [cpsreturn cpsbind cps_option_bind Option.bind cpscall] in *
                     | reflexivity
                     | progress split_andb
                     | progress subst
                     | rewrite !try_make_transport_base_type_cps_correct
                     | progress break_innermost_match
                     | progress eliminate_hprop_eq
                     | congruence
                     | match goal with
                       | [ H : type.type_beq _ _ _ _ = true |- _ ] => apply type.internal_type_dec_bl in H; auto
                       | [ H : context[type.type_beq _ _ ?x ?x] |- _ ] => rewrite type.internal_type_dec_lb in H by auto
                       | [ |- context[base_type_bl ?x ?y ?pf] ] => generalize (base_type_bl x y pf); intro
                       | [ |- context[type.internal_type_dec_bl ?a ?b ?c ?d ?e ?f] ]
                         => generalize (type.internal_type_dec_bl a b c d e f); intro
                       | [ H : _ |- _ ] => rewrite H
                       end ].

      Lemma try_make_transport_cps_correct P t1 t2 T k
        : type.try_make_transport_cps try_make_transport_base_type_cps P t1 t2 T k
          = k match Sumbool.sumbool_of_bool (type.type_beq _ base_type_beq t1 t2) with
              | left pf => Some (rew [fun t => P t1 -> P t] (type.internal_type_dec_bl _ _ base_type_bl _ _ pf) in id)
              | right _ => None
              end.
      Proof. revert P t2 T k; induction t1, t2; t. Qed.

      Lemma try_transport_cps_correct P t1 t2 v T k
        : type.try_transport_cps try_make_transport_base_type_cps P t1 t2 v T k
          = k match Sumbool.sumbool_of_bool (type.type_beq _ base_type_beq t1 t2) with
              | left pf => Some (rew [P] (type.internal_type_dec_bl _ _ base_type_bl _ _ pf) in v)
              | right _ => None
              end.
      Proof.
        cbv [type.try_transport_cps cpscall cps_option_bind cpsreturn cpsbind Option.bind]; rewrite try_make_transport_cps_correct;
          t.
      Qed.

      Lemma try_transport_correct P t1 t2 v
        : type.try_transport try_make_transport_base_type_cps P t1 t2 v
          = match Sumbool.sumbool_of_bool (type.type_beq _ base_type_beq t1 t2) with
            | left pf => Some (rew [P] (type.internal_type_dec_bl _ _ base_type_bl _ _ pf) in v)
            | right _ => None
            end.
      Proof. cbv [type.try_transport]; rewrite try_transport_cps_correct; reflexivity. Qed.
    End transport_cps.
  End type.

  Global Instance Decidable_type_eq : DecidableRel (@eq (@type.type base.type))
    := type.type_eq_dec _ base.type.type_beq base.type.internal_type_dec_bl base.type.internal_type_dec_lb.

  Ltac type_beq_to_eq :=
    repeat match goal with
           | [ H : type.type_beq _ _ _ _ = true |- _ ]
             => apply type.internal_type_dec_bl in H; [ | apply base.type.internal_type_dec_bl ]
           | [ H : context[type.type_beq _ _ ?x ?x] |- _ ]
             => rewrite type.internal_type_dec_lb in H by (reflexivity || exact base.type.internal_type_dec_lb)
           | [ H : type.type_beq _ _ ?x ?y = true |- _ ]
             => generalize dependent (type.internal_type_dec_bl _ _ base.type.internal_type_dec_bl _ _ H); clear H; intros
           | [ |- type.type_beq _ _ _ _ = true ]
             => apply type.internal_type_dec_lb; [ apply base.type.internal_type_dec_lb | ]
           | [ H : base.type.type_beq _ _ = true |- _ ]
             => apply base.type.internal_type_dec_bl in H
           | [ H : context[base.type.type_beq ?x ?x] |- _ ]
             => rewrite base.type.internal_type_dec_lb in H by reflexivity
           | [ H : base.type.type_beq ?x ?y = true |- _ ]
             => generalize dependent (base.type.internal_type_dec_bl _ _ H); clear H; intros
           | [ |- base.type.type_beq _ _ = true ]
             => apply base.type.internal_type_dec_lb
           | [ H : base.type.type_beq _ _ = true |- _ ]
             => apply base.type.internal_base_dec_bl in H
           | [ H : context[base.type.base_beq ?x ?x] |- _ ]
             => rewrite base.type.internal_base_dec_lb in H by reflexivity
           | [ H : base.type.base_beq ?x ?y = true |- _ ]
             => generalize dependent (base.type.internal_base_dec_bl _ _ H); clear H; intros
           | [ |- base.type.base_beq _ _ = true ]
             => apply base.type.internal_base_dec_lb
           end.

  Ltac rewrite_type_transport_correct :=
    cbv [type.try_transport_cps type.try_transport base.try_transport base.try_transport_cps] in *;
    cbn [type.try_make_transport_cps] in *;
    cbv [cpscall cpsbind cps_option_bind cpsreturn id] in *;
    repeat match goal with
           | [ |- context[type.try_make_transport_cps ?bmt ?P ?t1 ?t2] ]
             => erewrite type.try_make_transport_cps_correct
               by first [ exact base.try_make_transport_cps_correct | exact base.type.internal_type_dec_lb ]
           | [ H : context[type.try_make_transport_cps ?bmt ?P ?t1 ?t2] |- _ ]
             => erewrite type.try_make_transport_cps_correct in H
               by first [ exact base.try_make_transport_cps_correct | exact base.type.internal_type_dec_lb ]
           | [ |- context[base.try_make_transport_cps ?P ?t1 ?t2] ]
             => rewrite base.try_make_transport_cps_correct
           | [ H : context[base.try_make_transport_cps ?P ?t1 ?t2] |- _ ]
             => rewrite base.try_make_transport_cps_correct in H
           end.

  Module ident.
    Ltac invert_step :=
      match goal with
      | [ e : ident (type.base _) |- _ ] => type.invert_one e
      | [ e : ident (type.arrow _ _) |- _ ] => type.invert_one e
      end.

    Ltac invert := repeat invert_step.

    Ltac invert_match_step :=
      match goal with
      | [ H : context[match ?e with ident.Literal _ _ => _ | _ => _ end] |- _ ]
        => type.invert_one e
      | [ |- context[match ?e with ident.Literal _ _ => _ | _ => _ end] ]
        => type.invert_one e
      end.

    Ltac invert_match := repeat invert_match_step.
  End ident.

  Module expr.
    Ltac invert_step :=
      match goal with
      | [ e : expr.expr (type.base _) |- _ ] => type.invert_one e
      | [ e : expr.expr (defaults.type_base _) |- _ ] => type.invert_one e
      | [ e : expr.expr (type.arrow _ _) |- _ ] => type.invert_one e
      end.

    Ltac invert := repeat invert_step.

    Ltac invert_match_step :=
      match goal with
      | [ H : context[match ?e with expr.Var _ _ => _ | _ => _ end] |- _ ]
        => type.invert_one e
      | [ |- context[match ?e with expr.Var _ _ => _ | _ => _ end] ]
        => type.invert_one e
      end.

    Ltac invert_match := repeat invert_match_step.

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

        Local Ltac t'' :=
          cbv [invert_expr.invert_App2 invert_expr.invert_AppIdent2 invert_expr.invert_App invert_expr.invert_AppIdent invert_expr.invert_Ident]; intros;
          repeat first [ reflexivity
                       | progress subst
                       | progress cbn [Option.bind] in *
                       | progress inversion_option
                       | progress invert_match_step ].
        Lemma invert_App2_Some {t} {e : expr t} {v} : invert_expr.invert_App2 e = Some v -> e = expr.App (expr.App (fst (fst (projT2 v))) (snd (fst (projT2 v)))) (snd (projT2 v)).
        Proof. t''. Qed.
        Lemma invert_AppIdent_Some {t} {e : expr t} {v} : invert_expr.invert_AppIdent e = Some v -> e = expr.App (expr.Ident (fst (projT2 v))) (snd (projT2 v)).
        Proof. t''. Qed.
        Lemma invert_AppIdent2_Some {t} {e : expr t} {v} : invert_expr.invert_AppIdent2 e = Some v -> e = expr.App (expr.App (expr.Ident (fst (fst (projT2 v)))) (snd (fst (projT2 v)))) (snd (projT2 v)).
        Proof. t''. Qed.

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

    Section with_var2.
      Context {var : type base.type -> Type}.
      Local Notation expr := (@expr base.type ident var).
      Local Notation try_transportP P := (@type.try_transport base.type (@base.try_make_transport_cps) P _ _).
      Local Notation try_transport := (try_transportP _).
      Let type_base (v : base.type) : defaults.type := type.base v.
      Coercion type_base : base.type >-> type.type.

      Local Ltac t :=
        repeat first [ progress intros
                     | progress cbv [type_base] in *
                     | progress subst
                     | progress cbn [eq_rect f_equal f_equal2 Option.bind fst snd projT1 projT2] in *
                     | progress destruct_head'_sig
                     | progress inversion_option
                     | progress inversion_prod
                     | discriminate
                     | reflexivity
                     | progress type.inversion_type
                     | progress base.type.inversion_type
                     | progress invert_match
                     | progress ident.invert_match
                     | progress break_innermost_match_hyps
                     | exists eq_refl; cbn
                     | progress cbv [type.try_transport type.try_transport_cps type.try_make_transport_cps cpsbind cpscall cps_option_bind cpsreturn id] in *
                     | rewrite base.try_make_transport_cps_correct in *
                     | progress type_beq_to_eq
                     | congruence ].

      Lemma invert_Z_opp_Some {t} {e : expr t} {v}
        : invert_expr.invert_Z_opp e = Some v -> { pf : base.type.Z = t :> defaults.type
                                                | e = rew [expr] pf in (#ident.Z_opp @ (rew [expr] (eq_sym pf) in v))%expr }.
      Proof. cbv [invert_expr.invert_Z_opp]; intros; t. Qed.
      Lemma invert_Z_opp_SomeZ {e : expr base.type.Z} {v}
        : invert_expr.invert_Z_opp e = Some v -> e = (#ident.Z_opp @ v)%expr.
      Proof. intro H; apply invert_Z_opp_Some in H; t. Qed.
      Lemma invert_Z_cast_Some {e : expr base.type.Z} {v} : invert_expr.invert_Z_cast e = Some v -> e = (#(ident.Z_cast (fst v)) @ snd v)%expr.
      Proof. cbv [invert_expr.invert_Z_cast]; t. Qed.
      Lemma invert_Z_cast2_Some {e : expr (base.type.Z * base.type.Z)} {v}
        : invert_expr.invert_Z_cast2 e = Some v -> e = (#(ident.Z_cast2 (fst v)) @ snd v)%expr.
      Proof. cbv [invert_expr.invert_Z_cast2]; t. Qed.
      Lemma invert_pair_Some {A B} {e : expr (A * B)} {v}
        : invert_expr.invert_pair e = Some v -> e = (fst v, snd v)%expr.
      Proof. cbv [invert_expr.invert_pair]; t. Qed.
      Lemma invert_Literal_Some {t} {e : expr t} {v}
        : invert_expr.invert_Literal e = Some v -> match t return expr t -> type.interp base.interp t -> Prop with
                                                  | type.base (base.type.type_base _) => fun e v => e = expr.Ident (ident.Literal v)
                                                  | _ => fun _ _ => False
                                                  end e v.
      Proof. cbv [invert_expr.invert_Literal invert_expr.ident.invert_Literal]; t. Qed.
      Lemma invert_Literal_Some_base {t : base.type} {e : expr t} {v} : invert_expr.invert_Literal e = Some v -> e = ident.smart_Literal v.
      Proof. intro H; apply invert_Literal_Some in H; cbv [type_base] in *; break_innermost_match_hyps; subst; try reflexivity; tauto. Qed.
      Lemma invert_nil_Some {t} {e : expr (base.type.list t)}
        : invert_expr.invert_nil e = true -> e = (#ident.nil)%expr.
      Proof. cbv [invert_expr.invert_nil invert_expr.invert_Ident]; t. Qed.
      Lemma invert_cons_Some {t} {e : expr (base.type.list t)} {v}
        : invert_expr.invert_cons e = Some v -> e = (fst v :: snd v)%expr.
      Proof.
        cbv [invert_expr.invert_cons type_base] in *.
        destruct (invert_expr.invert_AppIdent2 e) eqn:H; [ | congruence ].
        apply invert_AppIdent2_Some in H; subst; break_innermost_match.
        t.
      Qed.

      Lemma reflect_list_cps'_id_nil {t} (e : expr _ := (#(@ident.nil t))%expr)
        : forall T k, invert_expr.reflect_list_cps' e T k = k (invert_expr.reflect_list_cps' e _ id).
      Proof. reflexivity. Qed.
      Lemma reflect_list_cps'_id_cons_body {t} (x : expr _) (xs : expr (base.type.list t)) (e := (x :: xs)%expr)
            (rec : forall T k, invert_expr.reflect_list_cps' xs T k = k (invert_expr.reflect_list_cps' xs _ id))
        : forall T k, invert_expr.reflect_list_cps' e T k = k (invert_expr.reflect_list_cps' e _ id).
      Proof.
        intros T k; subst e; cbn [invert_expr.reflect_list_cps']; cbv [id type_base] in *.
        rewrite_type_transport_correct; break_innermost_match; type_beq_to_eq; subst; cbn [eq_rect]; try reflexivity.
        etransitivity; rewrite rec; clear rec; [ | reflexivity ]; cbv [id]; break_innermost_match; try reflexivity.
        all: do 2 (rewrite_type_transport_correct; break_innermost_match; type_beq_to_eq; subst; cbn [eq_rect]; try reflexivity).
      Qed.


      Lemma reflect_list_cps'_id {t} {e : expr t}
        : forall T k, invert_expr.reflect_list_cps' e T k = k (invert_expr.reflect_list_cps' e _ id).
      Proof.
        induction e; try exact (fun T k => eq_refl (k None));
          [ destruct_head' ident; first [ exact (fun T k => eq_refl (k None))
                                        | exact (fun T k => eq_refl (k (Some nil))) ]
          | ].
        do 2 (let f := match goal with f : expr (_ -> _) |- _ => f end in
              type.invert_one f; try (exact (fun T k => eq_refl (k None))); []).
        ident.invert; break_innermost_match_hyps; subst; destruct_head' False; try (exact (fun T k => eq_refl (k None))); [].
        cbn [f_equal f_equal2 eq_rect].
        apply reflect_list_cps'_id_cons_body; assumption.
      Qed.

      Lemma reflect_list_step {t} {e : expr (base.type.list t)}
        : invert_expr.reflect_list e
          = match invert_expr.invert_nil e, invert_expr.invert_cons e with
            | true, _ => Some nil
            | false, Some (x, xs) => option_map (cons x) (invert_expr.reflect_list xs)
            | false, None => None
            end.
      Proof.
        type.invert_one e; cbv [invert_expr.invert_nil invert_expr.invert_Ident type_base]; try reflexivity;
          [ ident.invert_match; cbv [type_base] in *; base.type.inversion_type; reflexivity | ].
        do 2 (let f := match goal with f : expr (_ -> _) |- _ => f end in
              type.invert_one f; try reflexivity; []).
        cbv [type_base] in *; ident.invert; break_innermost_match_hyps; subst; destruct_head' False; try reflexivity; [].
        cbn [invert_expr.invert_cons f_equal2 f_equal eq_rect].
        cbv [invert_expr.reflect_list invert_expr.invert_cons invert_expr.invert_AppIdent2 invert_expr.invert_App2 invert_expr.invert_App Option.bind invert_expr.invert_Ident].
        cbv [invert_expr.reflect_list_cps].
        cbn [invert_expr.reflect_list_cps'].
        rewrite_type_transport_correct; break_innermost_match_step; type_beq_to_eq; try discriminate; base.type.inversion_type; [].
        rewrite reflect_list_cps'_id; cbv [id]; break_innermost_match; try reflexivity; [].
        rewrite_type_transport_correct; break_innermost_match_step; type_beq_to_eq; base.type.inversion_type; try discriminate; reflexivity.
      Qed.

      Lemma reify_list_nil {t} : reify_list nil = ([])%expr :> expr (base.type.list t).
      Proof. reflexivity. Qed.
      Lemma reify_list_cons {t} (x : expr (type.base t)) xs : reify_list (x :: xs) = (x :: reify_list xs)%expr.
      Proof. reflexivity. Qed.
      Lemma reflect_list_Some {t} {e : expr (base.type.list t)} {v} : invert_expr.reflect_list e = Some v -> e = reify_list v.
      Proof.
        revert e; induction v as [|v vs IHvs]; intro e; rewrite ?reify_list_cons, ?reify_list_nil;
          rewrite reflect_list_step; cbv [option_map]; break_innermost_match; auto using invert_nil_Some; try congruence; [].
        match goal with H : _ |- _ => apply invert_cons_Some in H end; subst.
        cbn [fst snd] in *.
        intro; erewrite <- IHvs; [ f_equal; reflexivity || congruence | congruence ].
      Qed.
      Lemma reflect_list_Some_nil {t} {e : expr (base.type.list t)} : invert_expr.reflect_list e = Some nil -> e = (#ident.nil)%expr.
      Proof. exact (@reflect_list_Some _ e nil). Qed.
      Lemma reflect_reify_list {t} {v} : invert_expr.reflect_list (var:=var) (reify_list (t:=t) v) = Some v.
      Proof.
        induction v as [|v vs IHvs]; rewrite ?reify_list_cons, ?reify_list_nil, reflect_list_step; [ reflexivity | ].
        cbn; cbv [option_map]; cbv [type_base] in *; rewrite IHvs; reflexivity.
      Qed.
      Lemma reflect_list_Some_iff  {t} {e : expr (base.type.list t)} {v} : invert_expr.reflect_list e = Some v <-> e = reify_list v.
      Proof. split; intro; subst; apply reflect_reify_list || apply reflect_list_Some; assumption. Qed.
    End with_var2.

    Ltac invert_subst_step_helper guard_tac :=
      cbv [defaults.type_base] in *;
      match goal with
      | [ H : invert_expr.invert_Var ?e = Some _ |- _ ] => guard_tac H; apply invert_Var_Some in H
      | [ H : invert_expr.invert_Ident ?e = Some _ |- _ ] => guard_tac H; apply invert_Ident_Some in H
      | [ H : invert_expr.invert_LetIn ?e = Some _ |- _ ] => guard_tac H; apply invert_LetIn_Some in H
      | [ H : invert_expr.invert_App ?e = Some _ |- _ ] => guard_tac H; apply invert_App_Some in H
      | [ H : invert_expr.invert_Abs ?e = Some _ |- _ ] => guard_tac H; apply invert_Abs_Some in H
      | [ H : invert_expr.invert_App2 ?e = Some _ |- _ ] => guard_tac H; apply invert_App2_Some in H
      | [ H : invert_expr.invert_AppIdent ?e = Some _ |- _ ] => guard_tac H; apply invert_AppIdent_Some in H
      | [ H : invert_expr.invert_AppIdent2 ?e = Some _ |- _ ] => guard_tac H; apply invert_AppIdent2_Some in H
      | [ H : invert_expr.invert_Z_opp ?e = Some _ |- _ ] => guard_tac H; first [ apply invert_Z_opp_SomeZ in H | apply invert_Z_opp_Some in H ]
      | [ H : invert_expr.invert_Z_cast ?e = Some _ |- _ ] => guard_tac H; apply invert_Z_cast_Some in H
      | [ H : invert_expr.invert_Z_cast2 ?e = Some _ |- _ ] => guard_tac H; apply invert_Z_cast2_Some in H
      | [ H : invert_expr.invert_pair ?e = Some _ |- _ ] => guard_tac H; apply invert_pair_Some in H
      | [ H : invert_expr.invert_Literal ?e = Some _ |- _ ] => guard_tac H; apply invert_Literal_Some in H
      | [ H : invert_expr.invert_nil ?e = Some _ |- _ ] => guard_tac H; apply invert_nil_Some in H
      | [ H : invert_expr.invert_cons ?e = Some _ |- _ ] => guard_tac H; apply invert_cons_Some in H
      | [ H : invert_expr.reflect_list ?e = Some _ |- _ ]
        => guard_tac H; first [ apply reflect_list_Some_nil in H | apply reflect_list_Some in H ];
          rewrite ?reify_list_cons, ?reify_list_nil in H
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
