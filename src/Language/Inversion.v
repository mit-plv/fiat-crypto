Require Import Crypto.Language.Language.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.FixCoqMistakes.

Local Set Primitive Projections.
Import EqNotations.
Module Compilers.
  Import Language.Compilers.

  Module type.
    Definition type_eq_Decidable {base_type} {base_type_eq_Decidable : DecidableRel (@eq base_type)}
      : DecidableRel (@eq (type.type base_type))
      := type.type_eq_dec _ _ (br_of_dec_rel _) (rb_of_dec_rel _).
    Global Hint Extern 0 (DecidableRel (@eq (type.type ?base_type))) => notypeclasses refine (@type_eq_Decidable base_type _) : typeclass_instances.
    Global Hint Extern 0 (Decidable (@eq (type.type ?base_type) _ _)) => notypeclasses refine (@type_eq_Decidable base_type _ _ _) : typeclass_instances.

    Global Instance type_eq_HProp {base_type} {base_type_eq_Decidable : DecidableRel (@eq base_type)}
      : IsHPropRel (@eq (type.type base_type)) := hprop_eq_dec.

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
      cbv [code] in H;
      let H1 := fresh H in
      let H2 := fresh H in
      try lazymatch type of H with
          | False => exfalso; exact H
          | True => destruct H
          | _ /\ _ => destruct H as [H1 H2]
          end.
    Ltac inversion_type_step :=
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
      cbv [decode] in *;
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
      type.inversion_type.

    Section transport_cps.
      Context {base_type}
              {base_type_beq : base_type -> base_type -> bool}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
              {reflect_base_type_beq : reflect_rel (@eq base_type) base_type_beq}
              {try_make_transport_base_type_cps_correct
               : @type.try_make_transport_cps_correctT base_type base_type_beq _ _}.

      Local Ltac t :=
        repeat first [ progress intros
                     | progress cbn [type.type_beq type.try_make_transport_cps eq_rect andb] in *
                     | progress cbv [cpsreturn cpsbind cps_option_bind Option.bind cpscall type.try_make_transport_cpsv] in *
                     | reflexivity
                     | progress split_andb
                     | progress subst
                     | rewrite !(@type.try_make_transport_cps_correctP base_type _ _ _ try_make_transport_base_type_cps_correct)
                     | rewrite !(@type.try_make_transport_cps_correctP (type.type base_type) _ _ _ _)
                     | progress break_innermost_match
                     | progress eliminate_hprop_eq
                     | congruence
                     | progress Reflect.reflect_beq_to_eq (type.type_beq _ base_type_beq)
                     | match goal with
                       | [ H : _ |- _ ] => rewrite H
                       end ].

      Global Instance try_make_transport_cps_correct
        : type.try_make_transport_cps_correctT (type.type base_type).
      Proof. intros P t1 t2; revert P t2; induction t1, t2; t. Qed.

      Lemma try_transport_cps_correct P t1 t2
        : type.try_transport_cps P t1 t2
          = fun v T k
            => k match Sumbool.sumbool_of_bool (type.type_beq _ base_type_beq t1 t2) with
                | left pf => Some (rew [P] (reflect_to_dec _ pf) in v)
                | right _ => None
                end.
      Proof. cbv [type.try_transport_cps]; t. Qed.

      Lemma try_transport_correct P t1 t2
        : type.try_transport P t1 t2
          = fun v
            => match Sumbool.sumbool_of_bool (type.type_beq _ base_type_beq t1 t2) with
              | left pf => Some (rew [P] (reflect_to_dec _ pf) in v)
              | right _ => None
              end.
      Proof. cbv [type.try_transport]; rewrite try_transport_cps_correct; reflexivity. Qed.
    End transport_cps.
  End type.

  Module base.
    Module type.
      Section encode_decode.
        Context {base : Type}.
        Local Notation base_type := (base.type base).

        Definition code (t1 t2 : base_type) : Prop
          := match t1, t2 with
             | base.type.type_base t1, base.type.type_base t2 => t1 = t2
             | base.type.prod A1 B1, base.type.prod A2 B2 => A1 = A2 /\ B1 = B2
             | base.type.list A1, base.type.list A2 => A1 = A2
             | base.type.option A1, base.type.option A2 => A1 = A2
             | base.type.unit, base.type.unit => True
             | base.type.type_base _, _
             | base.type.prod _ _, _
             | base.type.list _, _
             | base.type.option _, _
             | base.type.unit, _
               => False
             end.

        Definition encode (x y : base_type) : x = y -> code x y.
        Proof. intro p; destruct p, x; repeat constructor. Defined.
        Definition decode (x y : base_type) : code x y -> x = y.
        Proof.
          destruct x, y; intro p; try assumption; try reflexivity;
            destruct p; (apply f_equal || apply f_equal2); (assumption || reflexivity).
        Defined.

        Definition path_rect {x y : base_type} (Q : x = y -> Type)
                   (f : forall p, Q (decode x y p))
          : forall p, Q p.
        Proof. intro p; specialize (f (encode x y p)); destruct x, p; exact f. Defined.
      End encode_decode.

      Definition base_type_eq_Decidable {base} {base_eq_Decidable : DecidableRel (@eq base)}
        : DecidableRel (@eq (base.type.type base))
        := base.type.type_eq_dec _ _ (br_of_dec_rel _) (rb_of_dec_rel _).
      Global Hint Extern 0 (DecidableRel (@eq (base.type.type ?base))) => notypeclasses refine (@base_type_eq_Decidable base _) : typeclass_instances.
      Global Hint Extern 0 (Decidable (@eq (base.type.type ?base) _ _)) => notypeclasses refine (@base_type_eq_Decidable base _ _ _) : typeclass_instances.

      Global Instance base_type_eq_HProp {base} {base_eq_Decidable : DecidableRel (@eq base)}
        : IsHPropRel (@eq (base.type.type base)) := hprop_eq_dec.

      Ltac induction_type_in_using base H rect :=
        induction H as [H] using (rect base _ _);
        cbv [code] in H;
        let H1 := fresh H in
        let H2 := fresh H in
        try lazymatch type of H with
            | False => exfalso; exact H
            | True => destruct H
            | ?x = ?x => clear H
            | _ = _ :> base => try solve [ exfalso; clear -H; inversion H ]
            | _ /\ _ => destruct H as [H1 H2]
            end.

      Ltac inversion_type_step_with base base_eq_Decidable :=
        let base_eq_HProp := constr:(@hprop_eq_dec base base_eq_Decidable) in
        first [ lazymatch goal with
                | [ H : ?x = ?x :> base.type.type base |- _ ] => clear H || eliminate_hprop_eq_helper H (@base_type_eq_HProp base base_eq_Decidable)
                | [ H : ?x = ?x :> base |- _ ] => clear H || eliminate_hprop_eq_helper H base_eq_HProp
                | [ H : ?x = ?y :> base.type.type base |- _ ] => subst x || subst y
                | [ H : ?x = ?y :> base |- _ ] => subst x || subst y
                end
              | lazymatch goal with
                | [ H : _ = base.type.type_base _ |- _ ]
                  => induction_type_in_using base H @path_rect
                | [ H : base.type.type_base _ = _ |- _ ]
                  => induction_type_in_using base H @path_rect
                | [ H : _ = base.type.prod _ _ |- _ ]
                  => induction_type_in_using base H @path_rect
                | [ H : base.type.prod _ _ = _ |- _ ]
                  => induction_type_in_using base H @path_rect
                | [ H : _ = base.type.list _ |- _ ]
                  => induction_type_in_using base H @path_rect
                | [ H : base.type.list _ = _ |- _ ]
                  => induction_type_in_using base H @path_rect
                | [ H : _ = base.type.option _ |- _ ]
                  => induction_type_in_using base H @path_rect
                | [ H : base.type.option _ = _ |- _ ]
                  => induction_type_in_using base H @path_rect
                end
              | Compilers.type.inversion_type_step ];
        cbv [decode] in *;
        cbn [f_equal f_equal2 eq_rect decode] in *.
      Ltac inversion_type_with base base_eq_Decidable := repeat inversion_type_step_with base base_eq_Decidable.
      Ltac with_base_eq_Decidable tac :=
        let base := lazymatch goal with
                    | [ |- context[base.type.type ?base] ] => base
                    | [ H : context[base.type.type ?base] |- _ ] => base
                    end in
        let base_eq_Decidable := constr:(_ : DecidableRel (@eq base)) in
        tac base base_eq_Decidable.
      Ltac inversion_type_step := with_base_eq_Decidable inversion_type_step_with.
      Ltac inversion_type := with_base_eq_Decidable inversion_type_with.
    End type.

    Local Ltac t_red :=
      repeat first [ progress intros
                   | progress cbn [type.type_beq base.type.type_beq base.try_make_transport_cps eq_rect andb] in * ].
    Section try_transport.
      Context {base : Type}
              {base_beq : base -> base -> bool}
              {reflect_base_beq : reflect_rel (@eq base) base_beq}
              {try_make_transport_base_cps : @type.try_make_transport_cpsT base}
              {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}.

      Local Ltac t :=
        repeat first [ progress t_red
                     | reflexivity
                     | progress split_andb
                     | progress subst
                     | progress break_innermost_match
                     | progress eliminate_hprop_eq
                     | congruence
                     | progress Reflect.reflect_beq_to_eq (@base.type.type_beq base base_beq)
                     | progress Reflect.reflect_beq_to_eq base_beq
                     | match goal with
                       | [ H : _ |- _ ] => rewrite H
                       end ].

      Global Instance try_make_transport_cps_correct
        : type.try_make_transport_cps_correctT (base.type base).
      Proof.
        intros P t1 t2; revert P t2; induction t1, t2; t.
      Qed.

      Lemma try_transport_cps_correct P t1 t2 v
        : base.try_transport_cps P t1 t2 v
          = fun T k
            => k match Sumbool.sumbool_of_bool (base.type.type_beq _ base_beq t1 t2) with
                 | left pf => Some (rew [P] (Reflect.reflect_to_dec _ pf) in v)
                 | right _ => None
                 end.
      Proof.
        cbv [base.try_transport_cps]; rewrite try_make_transport_cps_correct;
          t.
      Qed.

      Lemma try_transport_correct P t1 t2 v
        : base.try_transport P t1 t2 v
          = match Sumbool.sumbool_of_bool (base.type.type_beq _ base_beq t1 t2) with
            | left pf => Some (rew [P] (Reflect.reflect_to_dec _ pf) in v)
            | right _ => None
            end.
      Proof. cbv [base.try_transport]; rewrite try_transport_cps_correct; reflexivity. Qed.
    End try_transport.
  End base.

  Ltac inversion_type_step := first [ type.inversion_type_step | base.type.inversion_type_step ].
  Ltac inversion_type := repeat inversion_type_step.

  Ltac eta_contract_for_type_beq_to_eq_in_type_of lem :=
    lazymatch type of lem with
    | context T[@type.type_beq ?base_type (fun x y => ?beq x y)]
      => let T' := context T[@type.type_beq base_type beq] in
         eta_contract_for_type_beq_to_eq_in_type_of (lem : T')
    | context T[@base.type.type_beq ?base (fun x y => ?beq x y)]
      => let T' := context T[@base.type.type_beq base beq] in
         eta_contract_for_type_beq_to_eq_in_type_of (lem : T')
    | _ => lem
    end.
  Ltac eta_contract_for_type_beq_to_eq :=
    repeat match goal with
           | [ H : context[@type.type_beq ?base_type (fun x y : ?T => ?beq x y)] |- _ ]
             => change (fun x y : T => beq x y) with beq in *
           | [ |- context[@type.type_beq ?base_type (fun x y : ?T => ?beq x y)] ]
             => change (fun x y : T => beq x y) with beq in *
           | [ H : context[@base.type.type_beq ?base (fun x y : ?T => ?beq x y)] |- _ ]
             => change (fun x y : T => beq x y) with beq in *
           | [ |- context[@base.type.type_beq ?base (fun x y : ?T => ?beq x y)] ]
             => change (fun x y : T => beq x y) with beq in *
           end.

  Ltac type_beq_to_eq_internal reflect_for_base reflect_for_base_type reflect_for_type :=
    repeat first [ progress eta_contract_for_type_beq_to_eq
                 | progress Reflect.reflect_beq_to_eq_using reflect_for_base
                 | progress Reflect.reflect_beq_to_eq_using reflect_for_base_type
                 | progress Reflect.reflect_beq_to_eq_using reflect_for_type
                 | match goal with
                   | [ H : ?x <> ?x |- _ ] => exfalso; exact (H eq_refl)
                   end ].

  Ltac type_beq_to_eq_with do_type_beq_to_eq :=
    do_type_beq_to_eq ().

  Ltac find_type_beq_to_eq _ :=
    let ty := lazymatch goal with
              | [ H : context[type.type_beq ?base_type] |- _ ] => constr:(type.type base_type)
              | [ |- context[type.type_beq ?base_type] ] => constr:(type.type base_type)
              | [ H : context[base.type.type_beq ?base] |- _ ] => constr:(type.type (base.type base))
              | [ |- context[base.type.type_beq ?base] ] => constr:(type.type (base.type base))
              | [ H : context[base.type ?base] |- _ ] => constr:(type.type (base.type base))
              | [ |- context[base.type ?base] ] => constr:(type.type (base.type base))
              | [ H : context[type.type ?base_type] |- _ ] => constr:(type.type base_type)
              | [ |- context[type.type ?base_type] ] => constr:(type.type base_type)
              | _ => open_constr:(type.type (base.type _))
              end in
    lazymatch ty with
    | type.type (base.type ?base)
      => let reflect_for_type := eta_contract_for_type_beq_to_eq_in_type_of constr:(_ : reflect_rel (@eq ty) (@type.type_beq (base.type base) (@base.type.type_beq base _))) in
         let reflect_for_base_type := eta_contract_for_type_beq_to_eq_in_type_of constr:(_ : reflect_rel (@eq (base.type base)) (@base.type.type_beq base _)) in
         let reflect_for_base := eta_contract_for_type_beq_to_eq_in_type_of constr:(_ : reflect_rel (@eq base) _) in
         ltac:(fun _ => type_beq_to_eq_internal reflect_for_base reflect_for_base_type reflect_for_type)
    | type.type ?base_type
      => let reflect_for_type := eta_contract_for_type_beq_to_eq_in_type_of constr:(_ : reflect_rel (@eq ty) (@type.type_beq base_type _)) in
         let reflect_for_base_type := eta_contract_for_type_beq_to_eq_in_type_of constr:(_ : reflect_rel (@eq base_type) _) in
         ltac:(fun _ => type_beq_to_eq_internal () reflect_for_base_type reflect_for_type)
    end.

  Ltac type_beq_to_eq :=
    let type_beq_to_eq_info := find_type_beq_to_eq () in
    type_beq_to_eq_with type_beq_to_eq_info.

  Ltac rewrite_type_transport_correct :=
    cbv [cpsbind cpscall cpsreturn id cps_option_bind] in *;
    repeat match goal with
           | [ H : context[type.try_transport] |- _ ]
             => rewrite type.try_transport_correct in H
           | [ |- context[type.try_transport] ]
             => rewrite type.try_transport_correct
           | [ H : context[type.try_transport_cps] |- _ ]
             => rewrite type.try_transport_cps_correct in H
           | [ |- context[type.try_transport_cps] ]
             => rewrite type.try_transport_cps_correct
           | [ H : context[type.try_make_transport_cps] |- _ ]
             => rewrite type.try_make_transport_cps_correct in H
           | [ |- context[type.try_make_transport_cps] ]
             => rewrite type.try_make_transport_cps_correct

           | [ H : context[base.try_transport] |- _ ]
             => rewrite base.try_transport_correct in H
           | [ |- context[base.try_transport] ]
             => rewrite base.try_transport_correct
           | [ H : context[base.try_transport_cps] |- _ ]
             => rewrite base.try_transport_cps_correct in H
           | [ |- context[base.try_transport_cps] ]
             => rewrite base.try_transport_cps_correct
           | [ H : context[base.try_make_transport_cps] |- _ ]
             => rewrite base.try_make_transport_cps_correct in H
           | [ |- context[base.try_make_transport_cps] ]
             => rewrite base.try_make_transport_cps_correct
           end.

  Module ident.
    Ltac invert_step_for ident :=
      match goal with
      | [ e : ident (type.base _) |- _ ] => type.invert_one e
      | [ e : ident (type.arrow _ _) |- _ ] => type.invert_one e
      end.

    Ltac invert_for ident := repeat invert_step_for ident.

    Ltac invert_match_step_for ident :=
      let is_ident term := match type of term with ident _ => idtac end in
      match goal with
      | [ H : context[match ?e with _ => _ end] |- _ ]
        => is_ident e; type.invert_one e
      | [ |- context[match ?e with _ => _ end] ]
        => is_ident e; type.invert_one e
      end.

    Ltac invert_match_for ident := repeat invert_match_step_for ident.
  End ident.

  Module expr.
    Ltac invert_step :=
      match goal with
      | [ e : expr.expr (type.base _) |- _ ] => type.invert_one e
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

    Ltac invert_subst_simple_step_helper guard_tac :=
      match goal with
      | [ H : @invert_expr.invert_Var ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_Var_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_Ident ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_Ident_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_LetIn ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_LetIn_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_App ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_App_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_Abs ?base_type ?ident ?var ?s ?d ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_Abs_Some base_type ident var s d e) in H
      | [ H : @invert_expr.invert_App2 ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_App2_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_AppIdent ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_AppIdent_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_AppIdent2 ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_AppIdent2_Some base_type ident var t e) in H
      end.
    Ltac invert_subst_simple_step :=
      first [ progress cbv beta iota in *
            | invert_subst_simple_step_helper ltac:(fun _ => idtac)
            | subst ].
    Ltac invert_subst_simple := repeat invert_subst_simple_step.

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

    Section with_container.
      Import invert_expr.
      Context {base : Type}
              {base_interp : base -> Type}
              {try_make_transport_base_cps : @type.try_make_transport_cpsT base}
              {base_beq : base -> base -> bool}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Context {ident : type -> Type}.
      Context {invertIdent : @InvertIdentT base base_interp ident}.
      Context {buildIdent : @ident.BuildIdentT base base_interp ident}.
      Context {reflect_base_beq : reflect_rel (@eq base) base_beq}
              {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}.
      Context {buildInvertIdentCorrect : BuildInvertIdentCorrectT}.

      Lemma invert_ident_Literal_ident_Literal
        : forall {t v}, invert_ident_Literal (ident.ident_Literal (t:=t) v) = Some v.
      Proof. intros t v; now apply (proj2 (invert_ident_Literal_correct (idc:=ident.ident_Literal (t:=t) v))). Qed.
      Lemma is_nil_ident_nil : forall {t}, is_nil (ident.ident_nil (t:=t)) = true.
      Proof. intros t; now apply (proj2 (is_nil_correct (idc:=ident.ident_nil (t:=t)))). Qed.
      Lemma is_cons_ident_cons : forall {t}, is_cons (ident.ident_cons (t:=t)) = true.
      Proof. intros t; now apply (proj2 (is_cons_correct (idc:=ident.ident_cons (t:=t)))). Qed.
      Lemma is_Some_ident_Some : forall {t}, is_Some (ident.ident_Some (t:=t)) = true.
      Proof. intros t; now apply (proj2 (is_Some_correct (idc:=ident.ident_Some (t:=t)))). Qed.
      Lemma is_None_ident_None : forall {t}, is_None (ident.ident_None (t:=t)) = true.
      Proof. intros t; now apply (proj2 (is_None_correct (idc:=ident.ident_None (t:=t)))). Qed.
      Lemma is_pair_ident_pair : forall {A B}, is_pair (ident.ident_pair (A:=A) (B:=B)) = true.
      Proof. intros A B; now apply (proj2 (is_pair_correct (idc:=ident.ident_pair (A:=A) (B:=B)))). Qed.
      Lemma is_tt_ident_tt : is_tt ident.ident_tt = true.
      Proof. now apply (proj2 (is_tt_correct (idc:=ident.ident_tt))). Qed.

      Let type_base (x : base) : @base.type base := base.type.type_base x.
      Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base' : base.type >-> type.type.
      Local Coercion type_base : base >-> base.type.

      Section with_var1.
        Context {var : type -> Type}.

        Local Notation expr := (@expr.expr base_type ident var).

        Local Ltac t_step :=
          first [ progress intros
                | progress cbv [type_base base'] in *
                | progress subst
                | progress cbn [eq_rect f_equal f_equal2 Option.bind fst snd projT1 projT2] in *
                | progress inversion_option
                | progress inversion_prod
                | progress inversion_sigma
                | progress destruct_head'_sig
                | progress destruct_head'_prod
                | exfalso; assumption
                | match goal with
                  | [ H : invert_ident_Literal _ = Some _ |- _ ] => apply invert_ident_Literal_correct in H
                  | [ H : is_nil _ = true |- _ ] => apply is_nil_correct in H
                  | [ H : is_cons _ = true |- _ ] => apply is_cons_correct in H
                  | [ H : is_Some _ = true |- _ ] => apply is_Some_correct in H
                  | [ H : is_None _ = true |- _ ] => apply is_None_correct in H
                  | [ H : is_pair _ = true |- _ ] => apply is_pair_correct in H
                  | [ H : is_tt _ = true |- _ ] => apply is_tt_correct in H
                  | [ H : context[invert_ident_Literal (ident.ident_Literal (t:=?T) ?V)] |- _ ]
                    => rewrite (invert_ident_Literal_ident_Literal (t:=T) (v:=V)) in H
                  | [ |- context[invert_ident_Literal (ident.ident_Literal (t:=?T) ?V)] ]
                    => rewrite (invert_ident_Literal_ident_Literal (t:=T) (v:=V))
                  | [ H : context[is_nil ident.ident_nil] |- _ ] => rewrite is_nil_ident_nil in H
                  | [ |- context[is_nil ident.ident_nil] ] => rewrite is_nil_ident_nil
                  | [ H : context[is_cons ident.ident_cons] |- _ ] => rewrite is_cons_ident_cons in H
                  | [ |- context[is_cons ident.ident_cons] ] => rewrite is_cons_ident_cons
                  | [ H : context[is_Some ident.ident_Some] |- _ ] => rewrite is_Some_ident_Some in H
                  | [ |- context[is_Some ident.ident_Some] ] => rewrite is_Some_ident_Some
                  | [ H : context[is_None ident.ident_None] |- _ ] => rewrite is_None_ident_None in H
                  | [ |- context[is_None ident.ident_None] ] => rewrite is_None_ident_None
                  | [ H : context[is_pair ident.ident_pair] |- _ ] => rewrite is_pair_ident_pair in H
                  | [ |- context[is_pair ident.ident_pair] ] => rewrite is_pair_ident_pair
                  | [ H : context[is_tt ident.ident_tt] |- _ ] => rewrite is_tt_ident_tt in H
                  | [ |- context[is_tt ident.ident_tt] ] => rewrite is_tt_ident_tt
                  end
                | progress invert_subst_simple_step
                | discriminate
                | reflexivity
                | progress inversion_expr
                | apply conj
                | progress inversion_type
                | progress invert_match
                | progress ident.invert_match_for ident
                | progress break_innermost_match_hyps
                | exists eq_refl; cbn
                | progress rewrite_type_transport_correct
                | progress type_beq_to_eq
                | congruence
                | break_innermost_match_step
                | progress eliminate_hprop_eq ].
        Local Ltac t := repeat t_step.

        Lemma invert_pair_Some_iff {A B} {e : expr (A * B)} {v}
          : invert_expr.invert_pair e = Some v <-> e = (fst v, snd v)%expr.
        Proof. cbv [invert_expr.invert_pair]; t. Qed.
        Lemma invert_Literal_Some_iff {t} {e : expr t} {v}
          : invert_expr.invert_Literal e = Some v <-> match t return expr t -> type.interp (base.interp base_interp) t -> Prop with
                                                      | type.base (base.type.type_base t) => fun e v => e = expr.Ident (ident.ident_Literal (t:=t) v)
                                                      | _ => fun _ _ => False
                                                      end e v.
        Proof. cbv [invert_expr.invert_Literal]; t. Qed.
        Lemma invert_nil_Some_iff {t} {e : expr (base.type.list t)}
          : invert_expr.invert_nil e = true <-> e = []%expr.
        Proof. cbv [invert_expr.invert_nil]; t. Qed.
        Lemma invert_cons_Some_iff {t} {e : expr (base.type.list t)} {v}
          : invert_expr.invert_cons e = Some v <-> e = (fst v :: snd v)%expr.
        Proof. cbv [invert_expr.invert_cons]; t. Qed.
        Lemma invert_None_Some_iff {t} {e : expr (base.type.option t)}
          : invert_expr.invert_None e = true <-> e = (#ident.ident_None)%expr.
        Proof. cbv [invert_expr.invert_None]; t. Qed.
        Lemma invert_Some_Some_iff {t} {e : expr (base.type.option t)} {v}
          : invert_expr.invert_Some e = Some v <-> e = (#ident.ident_Some @ v)%expr.
        Proof. cbv [invert_expr.invert_Some]; t. Qed.
        Lemma invert_tt_Some_iff {e : expr base.type.unit}
          : invert_expr.invert_tt e = true <-> e = (#ident.ident_tt)%expr.
        Proof. cbv [invert_expr.invert_tt]; t. Qed.

        Lemma invert_pair_Some {A B} {e : expr (A * B)} {v}
          : invert_expr.invert_pair e = Some v -> e = (fst v, snd v)%expr.
        Proof. intros; now apply (proj1 invert_pair_Some_iff). Qed.
        Lemma invert_Literal_Some {t} {e : expr t} {v}
          : invert_expr.invert_Literal e = Some v -> match t return expr t -> type.interp (base.interp base_interp) t -> Prop with
                                                     | type.base (base.type.type_base t) => fun e v => e = expr.Ident (ident.ident_Literal (t:=t) v)
                                                     | _ => fun _ _ => False
                                                     end e v.
        Proof. intros; now apply (proj1 invert_Literal_Some_iff). Qed.
        Lemma invert_Literal_Some_base {t : base.type base} {e : expr t} {v} : invert_expr.invert_Literal e = Some v -> e = ident.smart_Literal v.
        Proof. intro H; apply invert_Literal_Some in H; cbv [base'] in *; break_innermost_match_hyps; subst; try reflexivity; tauto. Qed.
        Lemma invert_nil_Some {t} {e : expr (base.type.list t)}
          : invert_expr.invert_nil e = true -> e = []%expr.
        Proof. intros; now apply (proj1 invert_nil_Some_iff). Qed.
        Lemma invert_cons_Some {t} {e : expr (base.type.list t)} {v}
          : invert_expr.invert_cons e = Some v -> e = (fst v :: snd v)%expr.
        Proof. intros; now apply (proj1 invert_cons_Some_iff). Qed.
        Lemma invert_None_Some {t} {e : expr (base.type.option t)}
          : invert_expr.invert_None e = true -> e = (#ident.ident_None)%expr.
        Proof. intros; now apply (proj1 invert_None_Some_iff). Qed.
        Lemma invert_Some_Some {t} {e : expr (base.type.option t)} {v}
          : invert_expr.invert_Some e = Some v -> e = (#ident.ident_Some @ v)%expr.
        Proof. intros; now apply (proj1 invert_Some_Some_iff). Qed.
        Lemma invert_tt_Some {e : expr base.type.unit}
          : invert_expr.invert_tt e = true -> e = (#ident.ident_tt)%expr.
        Proof. intros; now apply (proj1 invert_tt_Some_iff). Qed.

        Lemma invert_pair_ident_pair {A B} {v1 v2}
          : invert_expr.invert_pair (var:=var) (A:=A) (B:=B) (v1, v2) = Some (v1, v2).
        Proof. intros; now apply (proj2 invert_pair_Some_iff). Qed.
        Lemma invert_Literal_ident_Literal {t} {v}
          : invert_expr.invert_Literal (var:=var) (#(ident.ident_Literal (t:=t) v)) = Some v.
        Proof. intros; now apply (proj2 (invert_Literal_Some_iff (t:=t))). Qed.
        Lemma invert_nil_ident_nil {t}
          : invert_expr.invert_nil (var:=var) (#(ident.ident_nil (t:=t))) = true.
        Proof. intros; now apply (proj2 invert_nil_Some_iff). Qed.
        Lemma invert_cons_ident_cons {t} {x xs}
          : invert_expr.invert_cons (var:=var) (t:=t) (x :: xs) = Some (x, xs).
        Proof. intros; now apply (proj2 invert_cons_Some_iff). Qed.
        Lemma invert_None_ident_None {t}
          : invert_expr.invert_None (var:=var) (#(ident.ident_None (t:=t))) = true.
        Proof. intros; now apply (proj2 invert_None_Some_iff). Qed.
        Lemma invert_Some_ident_Some {t x}
          : invert_expr.invert_Some (var:=var) (#(ident.ident_Some (t:=t)) @ x) = Some x.
        Proof. intros; now apply (proj2 invert_Some_Some_iff). Qed.
        Lemma invert_tt_ident_tt
          : invert_expr.invert_tt (var:=var) (#(ident.ident_tt)) = true.
        Proof. intros; now apply (proj2 invert_tt_Some_iff). Qed.


        Lemma reify_option_None {t} : reify_option None = (#ident.ident_None)%expr :> expr (base.type.option t).
        Proof. reflexivity. Qed.
        Lemma reify_option_Some {t} (x : expr (type.base t)) : reify_option (Some x) = (#ident.ident_Some @ x)%expr.
        Proof. reflexivity. Qed.
        Lemma reflect_option_ident_None {t} : reflect_option (var:=var) (#(ident.ident_None (t:=t))) = Some None.
        Proof. cbv [reflect_option]; cbn; now rewrite (proj2 is_None_correct). Qed.
        Lemma reflect_option_ident_Some {t e} : reflect_option (var:=var) (#(ident.ident_Some (t:=t)) @ e) = Some (Some e).
        Proof. cbv [reflect_option]; cbn; rewrite (proj2 is_Some_correct) by reflexivity; t. Qed.
        Lemma reflect_option_Some {t} {e : expr (base.type.option t)} {v} : invert_expr.reflect_option e = Some v -> e = reify_option v.
        Proof.
          cbv [invert_expr.reflect_option].
          destruct (invert_expr.invert_None _) eqn:H;
            [ | destruct (invert_expr.invert_Some _) eqn:H' ];
            try apply invert_None_Some in H;
            try apply invert_Some_Some in H';
            intros; inversion_option; subst; reflexivity.
        Qed.
        Lemma reflect_option_Some_None {t} {e : expr (base.type.option t)} : invert_expr.reflect_option e = Some None -> e = (#ident.ident_None)%expr.
        Proof. exact (@reflect_option_Some _ e None). Qed.
        Lemma reflect_reify_option {t} {v} : invert_expr.reflect_option (var:=var) (reify_option (t:=t) v) = Some v.
        Proof.
          destruct v; rewrite ?reify_option_Some, ?reify_option_None, ?reflect_option_ident_None, ?reflect_option_ident_Some; reflexivity.
        Qed.
        Lemma reflect_option_Some_iff  {t} {e : expr (base.type.option t)} {v} : invert_expr.reflect_option e = Some v <-> e = reify_option v.
        Proof. split; intro; subst; apply reflect_reify_option || apply reflect_option_Some; assumption. Qed.

        Local Lemma reflect_list_cps'_id_ident {t} {idc : ident t}
          : forall T k, invert_expr.reflect_list_cps' (var:=var) (#idc) T k = k (invert_expr.reflect_list_cps' (#idc) _ id).
        Proof. cbv [reflect_list_cps']; t. Qed.
        Local Lemma reflect_list_cps'_id_app2 {A B C} {idc : ident (A -> B -> C)} {x xs}
              (e := (#(idc) @ x @ xs)%expr)
              (rec : forall T k, invert_expr.reflect_list_cps' xs T k = k (invert_expr.reflect_list_cps' xs _ id))
          : forall T k, invert_expr.reflect_list_cps' (var:=var) e T k = k (invert_expr.reflect_list_cps' e _ id).
        Proof.
          subst e; cbn [invert_expr.reflect_list_cps']; (destruct (is_cons idc) eqn:?);
            [ repeat (t || rewrite rec)
            | reflexivity ].
        Qed.
        Lemma reflect_list_cps'_id {t} {e : expr t}
          : forall T k, invert_expr.reflect_list_cps' e T k = k (invert_expr.reflect_list_cps' e _ id).
        Proof.
          induction e; try exact (fun T k => eq_refl (k None));
            [ now apply reflect_list_cps'_id_ident
            | ].
          do 2 (let f := match goal with f : expr (_ -> _) |- _ => f end in
                type.invert_one f; try (exact (fun T k => eq_refl (k None))); []).
          now apply reflect_list_cps'_id_app2.
        Qed.

        Lemma reflect_list_cps_id {t} {e : expr (base.type.list t)}
          : forall T k, invert_expr.reflect_list_cps e (T:=T) k = k (invert_expr.reflect_list e).
        Proof. exact (@reflect_list_cps'_id _ e). Qed.

        Lemma reflect_list_step {t} {e : expr (base.type.list t)}
          : invert_expr.reflect_list e
            = match invert_expr.invert_nil e, invert_expr.invert_cons e with
              | true, _ => Some nil
              | false, Some (x, xs) => option_map (cons x) (invert_expr.reflect_list xs)
              | false, None => None
              end.
        Proof.
          destruct (invert_nil e) eqn:Hnil;
            [ | destruct (invert_cons e) eqn:Hcons ];
            [ try apply invert_nil_Some in Hnil; try apply invert_cons_Some in Hcons;
              subst;
              cbv [reflect_list reflect_list_cps]; cbn [reflect_list_cps'];
              t;
              now (rewrite reflect_list_cps'_id; t).. | ].
          type.invert_one e;
            cbv [reflect_list reflect_list_cps base']; cbn [reflect_list_cps']; try reflexivity;
              [ t
              | do 2 (let f := match goal with f : expr (_ -> _) |- _ => f end in
                      type.invert_one f; try reflexivity; []) ].
          { rewrite (proj2 invert_nil_Some_iff) in Hnil; congruence. }
          { let idc := match goal with |- context[is_cons ?idc] => idc end in
            destruct (is_cons idc) eqn:Hcons'; [ | reflexivity ].
            t.
            erewrite (proj2 (invert_cons_Some_iff (v:=(_, _)))) in Hcons by reflexivity.
            congruence. }
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
        Lemma reflect_list_Some_nil {t} {e : expr (base.type.list t)} : invert_expr.reflect_list e = Some nil -> e = (#ident.ident_nil)%expr.
        Proof. exact (@reflect_list_Some _ e nil). Qed.
        Lemma reflect_reify_list {t} {v} : invert_expr.reflect_list (var:=var) (reify_list (t:=t) v) = Some v.
        Proof.
          induction v as [|v vs IHvs]; rewrite ?reify_list_cons, ?reify_list_nil, reflect_list_step; [ now rewrite (proj2 invert_nil_Some_iff) | ].
          erewrite (proj2 (invert_cons_Some_iff (v:=(_,_)))) by (cbn; reflexivity).
          now rewrite IHvs.
        Qed.
        Lemma reflect_list_Some_iff  {t} {e : expr (base.type.list t)} {v} : invert_expr.reflect_list e = Some v <-> e = reify_list v.
        Proof. split; intro; subst; apply reflect_reify_list || apply reflect_list_Some; assumption. Qed.


        Lemma reflect_smart_Literal_smart_Literal {t v} : reflect_smart_Literal (var:=var) (ident.smart_Literal (t:=t) v) = Some v.
        Proof.
          induction t; cbn -[reflect_list]; t.
          all: repeat first [ rewrite invert_pair_ident_pair
                            | progress cbn [Option.bind fst snd option_map List.map List.fold_right]
                            | rewrite reflect_reify_list
                            | rewrite List.map_map
                            | rewrite reflect_reify_option
                            | progress destruct_head_hnf' unit
                            | progress destruct_head_hnf' option
                            | reflexivity
                            | match goal with H : _ |- _ => rewrite H; clear H end
                            | match goal with
                              | [ |- OptionList.Option.List.lift (List.map _ ?ls) = Some ?ls ]
                                => cbv [OptionList.Option.List.lift]; induction ls
                              end ].
        Qed.
        Lemma reflect_reify_smart_Literal {t v} : reflect_smart_Literal (var:=var) (GallinaReify.base.reify (t:=t) v) = Some v.
        Proof. apply reflect_smart_Literal_smart_Literal. Qed.
        Lemma reflect_smart_Literal_Some {t} {e : expr (type.base t)} {v}
          : reflect_smart_Literal (t:=t) e = Some v -> e = ident.smart_Literal (t:=t) v.
        Proof.
          induction t; cbn -[reflect_list]; intro H; t.
          all: repeat first [ progress t
                            | progress cbv [Option.bind option_map] in *
                            | progress cbn [List.map List.fold_right] in *
                            | match goal with
                              | [ H : invert_Literal ?e = Some ?v |- _ ] => apply (@invert_Literal_Some_base _ e v) in H
                              | [ H : invert_pair ?e = Some ?v |- _ ] => apply invert_pair_Some in H
                              | [ H : invert_tt ?e = true |- _ ] => apply invert_tt_Some in H
                              | [ H : reflect_list ?e = Some ?v |- _ ] => apply reflect_list_Some in H
                              | [ H : reflect_option ?e = Some ?v |- _ ] => apply reflect_option_Some in H
                              | [ IH : context[reflect_smart_Literal _ = Some _ -> _ = ident.smart_Literal _],
                                       H : reflect_smart_Literal _ = Some _ |- _ ]
                                => apply IH in H
                              | [ H : OptionList.Option.List.lift (List.map reflect_smart_Literal ?l) = Some ?v |- _ ]
                                => cbv [OptionList.Option.List.lift] in H; revert dependent v; induction l; intro v; destruct v; intros
                              | [ H : context[match ?x with Some _ => _ | _ => _ end] |- _ ] => destruct x eqn:?
                              | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
                              | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                              | [ H : forall x, Some x = Some _ -> _ |- _ ] => specialize (H _ eq_refl)
                              end
                            | rewrite reify_list_cons ].
        Qed.
        Lemma reflect_smart_Literal_Some_iff  {t} {e : expr (type.base t)} {v} : invert_expr.reflect_smart_Literal e = Some v <-> e = ident.smart_Literal (t:=t) v.
        Proof. split; intro; subst; apply reflect_reify_smart_Literal || apply reflect_smart_Literal_Some; assumption. Qed.


        Section with_interp.
          Context {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}.

          Context {buildInterpIdentCorrect : ident.BuildInterpIdentCorrectT ident_interp}.

          Local Ltac rewrite_interp_ident :=
            repeat match goal with
                   | [ H : context[ident_interp _ (ident.ident_Literal (t:=?T) ?V)] |- _ ]
                     => rewrite (ident.interp_ident_Literal (t:=T) (v:=V)) in H
                   | [ |- context[ident_interp _ (ident.ident_Literal (t:=?T) ?V)] ]
                     => rewrite (ident.interp_ident_Literal (t:=T) (v:=V))
                   | _ => progress rewrite ?ident.interp_ident_nil, ?ident.interp_ident_cons, ?ident.interp_ident_Some, ?ident.interp_ident_None, ?ident.interp_ident_pair in *
                   end.

          Lemma reify_list_interp_related_gen_iff {R t ls v}
            : expr.interp_related_gen (var:=var) (@ident_interp) R (reify_list (t:=t) ls) v
              <-> List.Forall2 (expr.interp_related_gen (@ident_interp) R) ls v.
          Proof using buildInterpIdentCorrect.
            revert v; induction ls as [|l ls IHls], v as [|v vs].
            all: repeat first [ rewrite reify_list_nil
                              | rewrite reify_list_cons
                              | progress cbn [expr.interp_related_gen type.related] in *
                              | progress rewrite_interp_ident
                              | progress cbv [Morphisms.respectful] in *
                              | progress destruct_head'_ex
                              | progress destruct_head'_and
                              | progress subst
                              | reflexivity
                              | assumption
                              | apply conj
                              | progress intros
                              | match goal with
                                | [ H : List.Forall2 _ nil _ |- _ ] => inversion_clear H
                                | [ H : List.Forall2 _ (cons _ _) _ |- _ ] => inversion_clear H
                                | [ |- List.Forall2 _ _ _ ] => constructor
                                | [ H : nil = cons _ _ |- _ ] => solve [ inversion H ]
                                | [ H : cons _ _ = nil |- _ ] => solve [ inversion H ]
                                | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
                                | [ H : forall x y, x = y -> _ |- _ ] => specialize (fun x => H x x eq_refl)
                                | [ H : forall a x y, x = y -> _ |- _ ] => specialize (fun a x => H a x x eq_refl)
                                | [ H : forall x y, _ = ?f x y, H' : context[?f _ _] |- _ ] => rewrite <- H in H'
                                | [ H : _ |- _ ] => apply H; clear H
                                | [ |- ex _ ] => do 2 eexists; repeat apply conj; [ | | reflexivity ]
                                end ].
          Qed.

          Lemma reflect_list_interp_related_gen_iff {R t ls ls' v}
                (Hls : invert_expr.reflect_list (t:=t) ls = Some ls')
            : List.Forall2 (expr.interp_related_gen (var:=var) (@ident_interp) R) ls' v
              <-> expr.interp_related_gen (@ident_interp) R ls v.
          Proof using buildInterpIdentCorrect try_make_transport_base_cps_correct buildInvertIdentCorrect.
            apply reflect_list_Some in Hls; subst.
            rewrite reify_list_interp_related_gen_iff; reflexivity.
          Qed.
        End with_interp.
      End with_var1.

      Section with_interp.
        Context {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}.
        Context {buildInterpIdentCorrect : ident.BuildInterpIdentCorrectT ident_interp}.

        Lemma reify_list_interp_related_iff {t ls v}
          : expr.interp_related (@ident_interp) (reify_list (t:=t) ls) v
            <-> List.Forall2 (expr.interp_related (@ident_interp)) ls v.
        Proof using buildInterpIdentCorrect. apply reify_list_interp_related_gen_iff. Qed.

        Lemma reflect_list_interp_related_iff {t ls ls' v}
              (Hls : invert_expr.reflect_list (t:=t) ls = Some ls')
          : List.Forall2 (expr.interp_related (@ident_interp)) ls' v
            <-> expr.interp_related (@ident_interp) ls v.
        Proof using buildInterpIdentCorrect buildInvertIdentCorrect try_make_transport_base_cps_correct. now apply reflect_list_interp_related_gen_iff. Qed.
      End with_interp.
    End with_container.

    Ltac invert_subst_step_helper guard_tac :=
      first [ invert_subst_simple_step_helper guard_tac
            | match goal with
              | [ H : invert_expr.invert_pair ?e = Some _ |- _ ] => guard_tac H; apply invert_pair_Some in H
              | [ H : invert_expr.invert_Literal ?e = Some _ |- _ ] => guard_tac H; apply invert_Literal_Some in H
              | [ H : invert_expr.reflect_smart_Literal ?e = Some _ |- _ ] => guard_tac H; apply reflect_smart_Literal_Some in H
              | [ H : invert_expr.invert_nil ?e = true |- _ ] => guard_tac H; apply invert_nil_Some in H
              | [ H : invert_expr.invert_cons ?e = Some _ |- _ ] => guard_tac H; apply invert_cons_Some in H
              | [ H : invert_expr.invert_tt ?e = true |- _ ] => guard_tac H; apply invert_tt_Some in H
              | [ H : invert_expr.reflect_list ?e = Some _ |- _ ]
                => guard_tac H; first [ apply reflect_list_Some_nil in H | apply reflect_list_Some in H ];
                   rewrite ?reify_list_cons, ?reify_list_nil in H
              | [ H : invert_expr.invert_None ?e = true |- _ ] => guard_tac H; apply invert_None_Some in H
              | [ H : invert_expr.invert_Some ?e = Some _ |- _ ] => guard_tac H; apply invert_Some_Some in H
              | [ H : invert_expr.reflect_option ?e = Some _ |- _ ]
                => guard_tac H; first [ apply reflect_option_Some_None in H | apply reflect_option_Some in H ];
                   rewrite ?reify_option_Some, ?reify_option_None in H
              | [ H : context[invert_expr.invert_pair (_, _)] |- _ ] => guard_tac H; rewrite invert_pair_ident_pair in H
              | [ H : context[invert_expr.invert_Literal (#(ident.ident_Literal (t:=?T) ?V))] |- _ ] => guard_tac H; rewrite (invert_Literal_ident_Literal (t:=T) (v:=V)) in H
              | [ H : context[invert_expr.invert_ident_Literal (ident.ident_Literal (t:=?T) ?V)] |- _ ] => guard_tac H; rewrite (expr.invert_ident_Literal_ident_Literal (t:=T) (v:=V)) in H
              | [ H : context[invert_expr.invert_nil [] ] |- _ ] => guard_tac H; rewrite invert_nil_ident_nil in H
              | [ H : context[invert_expr.invert_cons (_ :: _)] |- _ ] => guard_tac H; rewrite invert_cons_ident_cons in H
              | [ H : context[invert_expr.invert_None (#ident.ident_None)] |- _ ] => guard_tac H; rewrite invert_None_ident_None in H
              | [ H : context[invert_expr.invert_Some (#ident.ident_Some @ _)] |- _ ] => guard_tac H; rewrite invert_Some_ident_Some in H
              | [ H : context[invert_expr.invert_tt (#ident.ident_tt)] |- _ ] => guard_tac H; rewrite invert_tt_ident_tt in H
              | [ H : context[invert_expr.reflect_option (#ident.ident_None)] |- _ ] => guard_tac H; rewrite reflect_option_ident_None in H
              | [ H : context[invert_expr.reflect_option (#ident.ident_Some @ _)] |- _ ] => guard_tac H; rewrite reflect_option_ident_Some in H
              end ].
    Ltac invert_subst_step :=
      first [ progress cbv beta iota in *
            | invert_subst_step_helper ltac:(fun _ => idtac)
            | subst ].
    Ltac invert_subst := repeat invert_subst_step.
  End expr.
End Compilers.
