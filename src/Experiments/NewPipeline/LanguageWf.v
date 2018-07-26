Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope list_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import expr.Notations.
  Module type.
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

    Section eqv.
      Context {base_type} {interp_base_type : base_type -> Type}.
      Local Notation eqv := (@type.eqv base_type interp_base_type).

      Global Instance eqv_Symmetric {t} : Symmetric (@eqv t) | 10.
      Proof. induction t; cbn [type.eqv type.interp] in *; repeat intro; eauto. Qed.

      Global Instance eqv_Transitive {t} : Transitive (@eqv t) | 10.
      Proof.
        induction t; cbn [eqv]; [ exact _ | ].
        cbv [respectful]; cbn [type.interp].
        intros f g h Hfg Hgh x y Hxy.
        etransitivity; [ eapply Hfg; eassumption | eapply Hgh ].
        etransitivity; first [ eassumption | symmetry; eassumption ].
      Qed.
    End eqv.
  End type.

  Module base.
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
           end.

  Module ident.
    Local Open Scope etype_scope.
    Global Instance eqv_Reflexive_Proper {t} (idc : ident t) : Proper type.eqv (ident.interp idc) | 1.
    Proof.
      destruct idc; cbv [ident.interp]; cbn [type.eqv ident.gen_interp type.interp base.interp base.base_interp];
        try solve [ typeclasses eauto
                  | cbv [respectful]; repeat intro; subst; destruct_head_hnf bool; destruct_head_hnf prod; eauto
                  | cbv [respectful]; repeat intro; (apply nat_rect_Proper_nondep || apply list_rect_Proper || apply list_case_Proper); repeat intro; eauto ].
    Qed.

    Global Instance interp_Proper {t} : Proper (@eq (ident t) ==> type.eqv) ident.interp | 1.
    Proof. intros idc idc' ?; subst idc'; apply eqv_Reflexive_Proper. Qed.

    Global Instance eqv_Reflexive {t} : Reflexive (fun idc1 idc2 : ident t => type.eqv (ident.interp idc1) (ident.interp idc2)) | 20.
    Proof. intro; apply eqv_Reflexive_Proper. Qed.

    Global Instance eqv_Transitive {t} : Transitive (fun idc1 idc2 : ident t => type.eqv (ident.interp idc1) (ident.interp idc2)) | 20.
    Proof. repeat intro; etransitivity; eassumption. Qed.

    Global Instance eqv_Symmetric {t} : Symmetric (fun idc1 idc2 : ident t => type.eqv (ident.interp idc1) (ident.interp idc2)) | 20.
    Proof. repeat intro; symmetry; eassumption. Qed.
  End ident.

  Module expr.
    Section with_ty.
      Context {base_type}
              {ident : type.type base_type -> Type}.
      Section with_var.
        Context {var1 var2 : type.type base_type -> Type}.
        Local Notation wfvP := (fun t => (var1 t * var2 t)%type).
        Local Notation wfvT := (list (sigT wfvP)).
        Local Notation expr := (@expr.expr base_type ident). (* But can't use this to define other notations, see COQBUG(https://github.com/coq/coq/issues/8126) *)
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Inductive wf : wfvT -> forall {t}, expr1 t -> expr2 t -> Prop :=
        | WfIdent
          : forall G {t} (idc : ident t), wf G (expr.Ident idc) (expr.Ident idc)
        | WfVar
          : forall G {t} (v1 : var1 t) (v2 : var2 t), List.In (existT _ t (v1, v2)) G -> wf G (expr.Var v1) (expr.Var v2)
        | WfAbs
          : forall G {s d} (f1 : var1 s -> expr1 d) (f2 : var2 s -> expr2 d),
            (forall (v1 : var1 s) (v2 : var2 s), wf (existT _ s (v1, v2) :: G) (f1 v1) (f2 v2))
            -> wf G (expr.Abs f1) (expr.Abs f2)
        | WfApp
          : forall G {s d}
                   (f1 : expr1 (s -> d)) (f2 : expr2 (s -> d)) (wf_f : wf G f1 f2)
                   (x1 : expr1 s) (x2 : expr2 s) (wf_x : wf G x1 x2),
            wf G (expr.App f1 x1) (expr.App f2 x2)
        | WfLetIn
          : forall G {A B}
                   (x1 : expr1 A) (x2 : expr2 A) (wf_x : wf G x1 x2)
                   (f1 : var1 A -> expr1 B) (f2 : var2 A -> expr2 B),
            (forall (v1 : var1 A) (v2 : var2 A), wf (existT _ A (v1, v2) :: G) (f1 v1) (f2 v2))
            -> wf G (expr.LetIn x1 f1) (expr.LetIn x2 f2).

        Section inversion.
          Local Notation "x == y" := (existT wfvP _ (x, y)).

          Definition wf_code (G : wfvT) {t} (e1 : expr1 t) : forall (e2 : expr2 t), Prop
            := match e1 in expr.expr t return expr2 t -> Prop with
               | expr.Ident t idc1
                 => fun e2
                    => match invert_expr.invert_Ident e2 with
                       | Some idc2 => idc1 = idc2
                       | None => False
                       end
               | expr.Var t v1
                 => fun e2
                    => match invert_expr.invert_Var e2 with
                       | Some v2 => List.In (v1 == v2) G
                       | None => False
                       end
               | expr.Abs s d f1
                 => fun e2
                    => match invert_expr.invert_Abs e2 with
                       | Some f2 => forall v1 v2, wf (existT _ s (v1, v2) :: G) (f1 v1) (f2 v2)
                       | None => False
                       end
               | expr.App s1 d f1 x1
                 => fun e2
                    => match invert_expr.invert_App e2 with
                       | Some (existT s2 (f2, x2))
                         => { pf : s1 = s2
                            | wf G (rew [fun s => expr1 (s -> d)] pf in f1) f2 /\ wf G (rew [expr1] pf in x1) x2 }
                       | None => False
                       end
               | expr.LetIn s1 d x1 f1
                 => fun e2
                    => match invert_expr.invert_LetIn e2 with
                       | Some (existT s2 (x2, f2))
                         => { pf : s1 = s2
                            | wf G (rew [expr1] pf in x1) x2
                              /\ forall v1 v2, wf (existT _ s2 (rew [var1] pf in v1, v2) :: G) (f1 v1) (f2 v2) }
                       | None => False
                       end
               end.

          Local Ltac t :=
            repeat match goal with
                   | _ => progress cbn in *
                   | _ => progress subst
                   | _ => progress inversion_option
                   | _ => progress expr.invert_subst
                   | [ H : Some _ = _ |- _ ] => symmetry in H
                   | _ => assumption
                   | _ => reflexivity
                   | _ => constructor
                   | _ => progress destruct_head False
                   | _ => progress destruct_head and
                   | _ => progress destruct_head sig
                   | _ => progress break_match_hyps
                   | _ => progress break_match
                   | [ |- and _ _ ] => split
                   | _ => exists eq_refl
                   | _ => intro
                   end.

          Definition wf_encode {G t e1 e2} (v : @wf G t e1 e2) : @wf_code G t e1 e2.
          Proof. destruct v; t. Defined.

          Definition wf_decode {G t e1 e2} (v : @wf_code G t e1 e2) : @wf G t e1 e2.
          Proof. destruct e1; t. Defined.
        End inversion.
      End with_var.

      Definition Wf {t} (e : @expr.Expr base_type ident t) : Prop
        := forall var1 var2, @wf var1 var2 nil t (e var1) (e var2).
    End with_ty.

    Ltac is_expr_constructor arg :=
      lazymatch arg with
      | expr.Ident _ => idtac
      | expr.Var _ => idtac
      | expr.App _ _ => idtac
      | expr.LetIn _ _ => idtac
      | expr.Abs _ => idtac
      end.

    Ltac inversion_wf_step_gen guard_tac :=
      let postprocess H :=
          (cbv [wf_code wf_code] in H;
           simpl in H;
           try match type of H with
               | True => clear H
               | False => exfalso; exact H
               end) in
      match goal with
      | [ H : wf _ ?x ?y |- _ ]
        => guard_tac x y;
          apply wf_encode in H; postprocess H
      | [ H : wf ?x ?y |- _ ]
        => guard_tac x y;
          apply wf_encode in H; postprocess H
      end.
    Ltac inversion_wf_step_constr :=
      inversion_wf_step_gen ltac:(fun x y => is_expr_constructor x; is_expr_constructor y).
    Ltac inversion_wf_step_one_constr :=
      inversion_wf_step_gen ltac:(fun x y => first [ is_expr_constructor x | is_expr_constructor y]).
    Ltac inversion_wf_step_var :=
      inversion_wf_step_gen ltac:(fun x y => first [ is_var x; is_var y; fail 1 | idtac ]).
    Ltac inversion_wf_step := first [ inversion_wf_step_constr | inversion_wf_step_var ].
    Ltac inversion_wf_constr := repeat inversion_wf_step_constr.
    Ltac inversion_wf_one_constr := repeat inversion_wf_step_one_constr.
    Ltac inversion_wf := repeat inversion_wf_step.

    Section wf_properties.
      Context {base_type}
              {ident : type.type base_type -> Type}.
      Local Notation wf := (@wf base_type ident).
      Lemma wf_sym {var1 var2} G1 G2
            (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v2, v1)) G2)
            t e1 e2
            (Hwf : @wf var1 var2 G1 t e1 e2)
        : @wf var2 var1 G2 t e2 e1.
      Proof.
        revert dependent G2; induction Hwf; constructor;
          repeat first [ progress cbn in *
                       | solve [ eauto ]
                       | progress intros
                       | progress subst
                       | progress destruct_head'_or
                       | progress inversion_sigma
                       | progress inversion_prod
                       | match goal with H : _ |- _ => apply H; clear H end ].
      Qed.

      Lemma wf_Proper_list {var1 var2} G1 G2
            (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
            t e1 e2
            (Hwf : @wf var1 var2 G1 t e1 e2)
        : @wf var1 var2 G2 t e1 e2.
      Proof.
        revert dependent G2; induction Hwf; constructor;
          repeat first [ progress cbn in *
                       | progress intros
                       | solve [ eauto ]
                       | progress subst
                       | progress destruct_head'_or
                       | progress inversion_sigma
                       | progress inversion_prod
                       | match goal with H : _ |- _ => apply H; clear H end ].
      Qed.

      Lemma wf_sym_map_iff {var1 var2} G
            t e1 e2
        : @wf var2 var1 (List.map (fun '(existT t (v1, v2)) => existT _ t (v2, v1)) G) t e2 e1
          <-> @wf var1 var2 G t e1 e2.
      Proof.
        split; apply wf_sym; intros ???; rewrite in_map_iff;
          intros; destruct_head'_ex; destruct_head'_sigT; destruct_head_prod; destruct_head'_and; inversion_sigma; inversion_prod; subst.
        { assumption. }
        { refine (ex_intro _ (existT _ _ (_, _)) _); split; (reflexivity || eassumption). }
      Qed.

      Lemma wf_trans_map_iff {var1 var2 var3} G
            (G1 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v2)) G)
            (G2 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v2, v3)) G)
            (G3 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v3)) G)
            t e1 e2 e3
            (Hwf12 : @wf var1 var2 G1 t e1 e2)
            (Hwf23 : @wf var2 var3 G2 t e2 e3)
        : @wf var1 var3 G3 t e1 e3.
      Proof.
        remember G1 as G1' eqn:HG1 in *; subst G1 G2 G3.
        revert dependent e3; revert dependent G; induction Hwf12;
          repeat first [ progress cbn in *
                       | solve [ eauto ]
                       | progress intros
                       | progress subst
                       | progress destruct_head' False
                       | progress destruct_head'_ex
                       | progress destruct_head'_sig
                       | progress destruct_head'_and
                       | progress inversion_sigma
                       | progress inversion_prod
                       | progress inversion_wf
                       | progress destruct_head'_or
                       | break_innermost_match_hyps_step
                       | progress expr.invert_subst
                       | rewrite in_map_iff in *
                       | match goal with |- wf _ _ _ => constructor end
                       | match goal with
                         | [ H : _ |- wf _ _ _ ]
                           => solve [ eapply (fun v1 v2 G => H v1 v2 ((existT _ _ (_, _, _)) :: G)); cbn; eauto ]
                         | [ |- exists x, _ ] => refine (ex_intro _ (existT _ _ (_, _, _)) _); cbn; split; [ reflexivity | ]
                         end ].
        (* Seems false? *)
      Abort.
    End wf_properties.

    Section for_interp.
      Local Open Scope etype_scope.
      Import defaults.
      Lemma wf_interp_Proper G {t} e1 e2
            (Hwf : @wf _ _ _ _ G t e1 e2)
            (HG : forall t v1 v2, In (existT _ t (v1, v2)) G -> v1 == v2)
        : interp e1 == interp e2.
      Proof.
        induction Hwf;
          repeat first [ reflexivity
                       | assumption
                       | progress destruct_head' False
                       | progress destruct_head'_sig
                       | progress inversion_sigma
                       | progress inversion_prod
                       | progress destruct_head'_or
                       | progress intros
                       | progress subst
                       | inversion_wf_step
                       | progress expr.invert_subst
                       | break_innermost_match_hyps_step
                       | progress cbn [expr.interp fst snd projT1 projT2 List.In eq_rect type.eqv] in *
                       | progress cbn [type.app_curried]
                       | progress cbv [LetIn.Let_In respectful Proper] in *
                       | progress destruct_head'_and
                       | solve [ eauto with nocore ]
                       | match goal with
                         | [ |- ident.interp ?x == ident.interp ?x ] => apply ident.eqv_Reflexive
                         | [ |- Proper type.eqv (ident.interp _) ] => apply ident.eqv_Reflexive_Proper
                         | [ H : context[interp _ == interp _] |- interp _ == interp _ ] => eapply H; eauto with nocore
                         end ].
      Qed.

      Lemma Wf_Interp_Proper {t} (e : Expr t) : Wf e -> Proper type.eqv (Interp e).
      Proof. repeat intro; apply wf_interp_Proper with (G:=nil); cbn [List.In]; intuition eauto. Qed.
    End for_interp.
  End expr.

  Local Ltac destructure_step :=
    first [ progress subst
          | progress inversion_option
          | progress inversion_prod
          | progress inversion_sigma
          | progress destruct_head'_sigT
          | progress destruct_head'_ex
          | progress destruct_head'_and
          | progress split_andb
          | progress type_beq_to_eq
          | progress eliminate_hprop_eq
          | match goal with
            | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
            end ].

  Local Ltac destructure_destruct_step :=
    first [ progress destruct_head'_or
          | break_innermost_match_hyps_step
          | break_innermost_match_step
          | match goal with
            | [ H : None = option_map _ _ |- _ ] => cbv [option_map] in H
            | [ |- context[andb _ _ = true] ] => rewrite Bool.andb_true_iff
            end ].
  Local Ltac destructure_split_step :=
    first [ destructure_destruct_step
          | apply conj ].

  Local Ltac saturate_pos :=
    cbv [PositiveMap.key] in *;
    repeat match goal with
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q, p' : BinNums.positive |- _ ]
             => lazymatch goal with
                | [ H' : context[BinPos.Pos.lt p' q] |- _ ] => fail
                | _ => pose proof (H p')
                end
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q |- context[BinPos.Pos.succ ?p'] ]
             => is_var p';
                lazymatch goal with
                | [ H' : context[BinPos.Pos.lt (BinPos.Pos.succ p') q] |- _ ] => fail
                | _ => pose proof (H (BinPos.Pos.succ p'))
                end
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q, H' : context[BinPos.Pos.succ ?p'] |- _ ]
             => is_var p';
                lazymatch goal with
                | [ H' : context[BinPos.Pos.lt (BinPos.Pos.succ p') q] |- _ ] => fail
                | _ => pose proof (H (BinPos.Pos.succ p'))
                end
           end.
  Local Ltac saturate_pos_fast :=
    cbv [PositiveMap.key] in *;
    repeat match goal with
           | [ H : forall p : BinNums.positive, _ -> BinPos.Pos.lt p ?q |- _ ]
             => lazymatch goal with
                | [ H' : context[BinPos.Pos.lt q q] |- _ ] => fail
                | _ => pose proof (H q)
                end
           end.

  Local Ltac rewrite_find_add :=
    repeat match goal with
           | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
           | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
           end.

  Ltac wf_safe_t_step :=
    first [ progress intros
          | progress subst
          | progress inversion_sigma
          | progress inversion_prod
          | progress destruct_head'_sig
          | progress destruct_head'_and
          | progress cbn [List.In eq_rect] in *
          | match goal with
            | [ |- expr.wf _ _ _ ] => constructor
            end
          | solve [ eauto using conj, eq_refl, or_introl, or_intror with nocore ]
          | progress destruct_head'_or
          | match goal with
            | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ]
              => eapply H; clear H; eauto with nocore; solve [ repeat wf_safe_t_step ]
            end ].
  Ltac wf_unsafe_t_step :=
    first [ solve [ eauto with nocore ]
          | match goal with
            | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ]
              => eapply H; eauto with nocore; match goal with |- ?G => tryif has_evar G then fail else idtac end
            | [ |- expr.wf _ _ _ ]
              => eapply expr.wf_Proper_list; [ | solve [ eauto with nocore ] ]
            end ].
  Ltac wf_safe_t := repeat wf_safe_t_step.
  Ltac wf_unsafe_t := repeat wf_unsafe_t_step.
  Ltac wf_t_step := first [ wf_safe_t_step | wf_unsafe_t_step ].
  Ltac wf_t := repeat wf_t_step.

  Ltac interp_safe_t_step :=
    first [ progress intros
          | progress subst
          | progress inversion_sigma
          | progress inversion_prod
          | progress cbn [List.In eq_rect expr.interp ident.interp type.interp base.interp base.base_interp type.eqv] in *
          | progress cbv [respectful LetIn.Let_In] in *
          | solve [ eauto using conj, eq_refl, or_introl, or_intror with nocore ]
          | progress destruct_head'_or
          | match goal with
            | [ |- ident.interp ?x == ident.interp ?x ] => apply ident.eqv_Reflexive
            | [ |- Proper (fun x y => ident.interp x == ident.interp y) _ ] => apply ident.eqv_Reflexive_Proper
            | [ H : context[expr.interp _ _ == expr.interp _ _] |- expr.interp _ _ == expr.interp _ _ ]
              => eapply H; eauto with nocore; solve [ repeat interp_safe_t_step ]
            end ].
  Ltac interp_unsafe_t_step :=
    first [ solve [ eauto with nocore ]
          | match goal with
            | [ H : context[expr.interp _ _ == expr.interp _ _] |- expr.interp _ _ == expr.interp _ _ ]
              => eapply H; eauto with nocore; match goal with |- ?G => tryif has_evar G then fail else idtac end
            end ].
  Ltac interp_safe_t := repeat interp_safe_t_step.
  Ltac interp_unsafe_t := repeat interp_unsafe_t_step.
  Ltac interp_t_step := first [ interp_safe_t_step | interp_unsafe_t_step ].
  Ltac interp_t := repeat interp_t_step.



  Import defaults.
  Module GeneralizeVar.
    Import Language.Compilers.GeneralizeVar.
    Local Open Scope etype_scope.
    Module Flat.
      Fixpoint wf (G : PositiveMap.t type) {t} (e : Flat.expr t) : bool
        := match e with
           | Flat.Ident t idc => true
           | Flat.Var t n
             => match PositiveMap.find n G with
                | Some t' => type.type_beq _ base.type.type_beq t t'
                | None => false
                end
           | Flat.Abs s n d f
             => match PositiveMap.find n G with
                | None => @wf (PositiveMap.add n s G) _ f
                | Some _ => false
                end
           | Flat.App s d f x
             => andb (@wf G _ f) (@wf G _ x)
           | Flat.LetIn A B n ex eC
             => match PositiveMap.find n G with
                | None => andb (@wf G _ ex) (@wf (PositiveMap.add n A G) _ eC)
                | Some _ => false
                end
           end.
    End Flat.

    Section with_var.
      Context {var1 var2 : type -> Type}.

      Lemma wf_from_flat_gen
            {t}
            (e : Flat.expr t)
        : forall (G1 : PositiveMap.t type) (G2 : list { t : _ & var1 t * var2 t }%type)
                 (ctx1 : PositiveMap.t { t : type & var1 t })
                 (ctx2 : PositiveMap.t { t : type & var2 t })
                 (H_G1_ctx1 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx1))
                 (H_G1_ctx2 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx2))
                 (H_ctx_G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G2
                                             <-> (exists p, PositiveMap.find p ctx1 = Some (existT _ t v1) /\ PositiveMap.find p ctx2 = Some (existT _ t v2))),
          Flat.wf G1 e = true -> expr.wf G2 (from_flat e var1 ctx1) (from_flat e var2 ctx2).
      Proof.
        induction e;
          repeat first [ progress cbn [Flat.wf from_flat option_map projT1 projT2 List.In fst snd] in *
                       | progress intros
                       | destructure_step
                       | progress cbv [Option.bind type.try_transport type.try_transport_cps cpsreturn cpsbind cpscall cps_option_bind eq_rect id] in *
                       | match goal with |- expr.wf _ _ _ => constructor end
                       | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                       | congruence
                       | destructure_split_step
                       | erewrite type.try_make_transport_cps_correct
                         by first [ exact base.type.internal_type_dec_lb | exact base.try_make_transport_cps_correct ]
                       | match goal with
                         | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ] => eapply H; clear H; eauto with nocore
                         | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
                         | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
                         | [ H : forall t v1 v2, In _ ?G2 <-> _ |- context[In _ ?G2] ] => rewrite H
                         | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 <-> _ |- _ ] => rewrite H' in H
                         | [ |- exists p, PositiveMap.find p (PositiveMap.add ?n (existT _ ?t ?v) _) = Some (existT _ ?t _) /\ _ ]
                           => exists n
                         | [ H : PositiveMap.find ?n ?ctx = ?v |- exists p, PositiveMap.find p (PositiveMap.add _ _ ?ctx) = ?v /\ _ ]
                           => exists n
                         | [ |- _ \/ exists p, PositiveMap.find p (PositiveMap.add ?n (existT _ ?t ?v) _) = Some (existT _ ?t _) /\ _ ]
                           => right; exists n
                         | [ H : PositiveMap.find ?n ?ctx = ?v |- _ \/ exists p, PositiveMap.find p (PositiveMap.add _ _ ?ctx) = ?v /\ _ ]
                           => right; exists n
                         | [ H : PositiveMap.find ?n ?G = ?a, H' : PositiveMap.find ?n ?G' = ?b, H'' : forall p, PositiveMap.find p ?G = option_map _ (PositiveMap.find p ?G') |- _ ]
                           => (tryif assert (a = option_map (@projT1 _ _) b) by (cbn [projT1 option_map]; (reflexivity || congruence))
                                then fail
                                else let H1 := fresh in
                                     pose proof (H'' n) as H1;
                                     rewrite H, H' in H1;
                                     cbn [option_map projT1] in H1)
                         end ].
      Qed.

      Lemma wf_from_flat
            {t}
            (e : Flat.expr t)
        : Flat.wf (PositiveMap.empty _) e = true -> expr.wf nil (from_flat e var1 (PositiveMap.empty _)) (from_flat e var2 (PositiveMap.empty _)).
      Proof.
        apply wf_from_flat_gen; intros *;
          repeat setoid_rewrite PositiveMap.gempty;
          cbn [In option_map];
          intuition (destruct_head'_ex; intuition (congruence || auto)).
      Qed.
    End with_var.

    Lemma Wf_FromFlat {t} (e : Flat.expr t) : Flat.wf (PositiveMap.empty _) e = true -> expr.Wf (FromFlat e).
    Proof. intros H ??; apply wf_from_flat, H. Qed.

    Lemma Wf_via_flat {t} (e : Expr t)
      : (e = GeneralizeVar (e _) /\ Flat.wf (PositiveMap.empty _) (to_flat (e _)) = true)
        -> expr.Wf e.
    Proof. intros [H0 H1]; rewrite H0; cbv [GeneralizeVar]; apply Wf_FromFlat, H1. Qed.

    Lemma wf_to_flat'_gen
          {t}
          (e1 e2 : expr t)
          G
          (Hwf : expr.wf G e1 e2)
      : forall (ctx1 ctx2 : PositiveMap.t type)
               (H_G_ctx : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                          -> (PositiveMap.find v1 ctx1 = Some t /\ PositiveMap.find v2 ctx2 = Some t))
               cur_idx1 cur_idx2
               (Hidx1 : forall p, PositiveMap.mem p ctx1 = true -> BinPos.Pos.lt p cur_idx1)
               (Hidx2 : forall p, PositiveMap.mem p ctx2 = true -> BinPos.Pos.lt p cur_idx2),
        Flat.wf ctx1 (to_flat' e1 cur_idx1) = true
        /\ Flat.wf ctx2 (to_flat' e2 cur_idx2) = true.
    Proof.
      setoid_rewrite PositiveMap.mem_find; induction Hwf;
        repeat first [ progress cbn [Flat.wf to_flat' option_map projT1 projT2 List.In fst snd eq_rect] in *
                     | progress intros
                     | destructure_step
                     | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                     | congruence
                     | lazymatch goal with
                       | [ H : BinPos.Pos.lt ?x ?x |- _ ] => exfalso; clear -H; lia
                       | [ H : BinPos.Pos.lt (BinPos.Pos.succ ?x) ?x |- _ ] => exfalso; clear -H; lia
                       | [ H : BinPos.Pos.lt ?x ?y, H' : BinPos.Pos.lt ?y ?x |- _ ] => exfalso; clear -H H'; lia
                       | [ |- BinPos.Pos.lt _ _ ] => progress saturate_pos
                       end
                     | match goal with
                       | [ H : ?x = Some _ |- context[?x] ] => rewrite H
                       | [ H : ?x = None |- context[?x] ] => rewrite H
                       | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                       | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                       | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 -> _ |- _ ] => apply H' in H
                       end
                     | progress rewrite_find_add
                     | destructure_destruct_step
                     | progress saturate_pos_fast
                     | match goal with
                       | [ H : context[Flat.wf _ _ = true /\ Flat.wf _ _ = true] |- Flat.wf _ _ = true /\ Flat.wf _ _ = true ]
                         => eapply H; clear H; eauto with nocore
                       | [ |- (?f = true /\ ?x = true) /\ (?f' = true /\ ?x' = true) ]
                         => cut ((f = true /\ f' = true) /\ (x = true /\ x' = true));
                            [ tauto | split ]
                       | [ |- BinPos.Pos.lt _ _ ]
                         => repeat match goal with
                                   | [ H : ?T, H' : ?T |- _ ] => clear H'
                                   | [ H : BinPos.Pos.lt _ _ |- _ ] => revert H
                                   | [ H : _ |- _ ] => clear H
                                   end;
                            lia
                       end
                     | apply conj ].
    Qed.

    Lemma wf_to_flat
          {t}
          (e1 e2 : expr t)
      : expr.wf nil e1 e2 -> Flat.wf (PositiveMap.empty _) (to_flat e1) = true /\ Flat.wf (PositiveMap.empty _) (to_flat e2) = true.
    Proof.
      intro; apply wf_to_flat'_gen with (G:=nil); eauto; intros *; cbn [In];
        rewrite ?PositiveMap.mem_find, ?PositiveMap.gempty; intuition congruence.
    Qed.

    Lemma Wf_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e) : Flat.wf (PositiveMap.empty _) (ToFlat e) = true.
    Proof. eapply wf_to_flat, Hwf. Qed.

    Lemma Wf_FromFlat_to_flat {t} (e : expr t) : expr.wf nil e e -> expr.Wf (FromFlat (to_flat e)).
    Proof. intro Hwf; eapply Wf_FromFlat, wf_to_flat, Hwf. Qed.
    Lemma Wf_FromFlat_ToFlat {t} (e : Expr t) : expr.Wf e -> expr.Wf (FromFlat (ToFlat e)).
    Proof. intro H; apply Wf_FromFlat_to_flat, H. Qed.
    Lemma Wf_GeneralizeVar {t} (e : Expr t) : expr.Wf e -> expr.Wf (GeneralizeVar (e _)).
    Proof. apply Wf_FromFlat_ToFlat. Qed.

    Local Ltac t :=
      repeat first [ reflexivity
                   | progress saturate_pos
                   | progress cbn [from_flat to_flat' projT1 projT2 fst snd eq_rect expr.interp List.In type.eqv] in *
                   | progress fold @type.interp
                   | progress cbv [Option.bind LetIn.Let_In respectful] in *
                   | destructure_step
                   | erewrite type.try_make_transport_cps_correct
                     by first [ exact base.type.internal_type_dec_lb | exact base.try_make_transport_cps_correct ]
                   | erewrite type.try_transport_correct
                     by first [ exact base.type.internal_type_dec_lb | exact base.try_make_transport_cps_correct ]
                   | progress intros
                   | congruence
                   | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                   | progress cbn [type.app_curried type.for_each_lhs_of_arrow] in *
                   | destructure_split_step
                   | match goal with
                     | [ |- ident.interp _ == ident.interp _ ] => apply ident.eqv_Reflexive
                     | [ H : forall x : prod _ _, _ |- _ ] => specialize (fun a b => H (a, b))
                     | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 <-> _ |- _ ] => rewrite H' in H
                     | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 -> _ |- _ ] => apply H' in H
                     | [ H' : forall t v1 v2, In _ ?G2 <-> _ |- context[In _ ?G2] ] => rewrite H'
                     | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ] => assert (a = b) by congruence; clear H'
                     | [ H : BinPos.Pos.lt ?x ?x |- _ ] => exfalso; lia
                     | [ H : BinPos.Pos.lt (BinPos.Pos.succ ?x) ?x |- _ ] => exfalso; lia
                     | [ |- BinPos.Pos.lt _ _ ] => lia
                     | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
                     | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
                     | [ |- _ \/ None = Some _ ] => left
                     | [ |- Some _ = Some _ ] => apply f_equal
                     | [ |- existT _ ?x _ = existT _ ?x _ ] => apply f_equal
                     | [ |- pair _ _ = pair _ _ ] => apply f_equal2
                     | [ H : context[interp _ == interp _] |- interp _ == interp _ ] => eapply H; clear H; solve [ t ]
                     end ].
    Lemma interp_from_flat_to_flat' {t} (e1 : expr t) (e2 : expr t) G ctx
          (H_ctx_G : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                     -> (exists v2', PositiveMap.find v1 ctx = Some (existT _ t v2') /\ v2' == v2))
          (Hwf : expr.wf G e1 e2)
          cur_idx
          (Hidx : forall p, PositiveMap.mem p ctx = true -> BinPos.Pos.lt p cur_idx)
      : interp (from_flat (to_flat' e1 cur_idx) _ ctx) == interp e2.
    Proof.
      setoid_rewrite PositiveMap.mem_find in Hidx.
      revert dependent cur_idx; revert dependent ctx; induction Hwf; intros;
        t.
    Qed.

    Lemma Interp_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e) : Interp (FromFlat (ToFlat e)) == Interp e.
    Proof.
      cbv [Interp FromFlat ToFlat to_flat].
      apply interp_from_flat_to_flat' with (G:=nil); eauto; intros *; cbn [List.In]; rewrite ?PositiveMap.mem_find, ?PositiveMap.gempty;
        intuition congruence.
    Qed.

    Lemma Interp_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e) : Interp (GeneralizeVar (e _)) == Interp e.
    Proof. apply Interp_FromFlat_ToFlat, Hwf. Qed.
  End GeneralizeVar.

  Ltac prove_Wf _ :=
    lazymatch goal with
    | [ |- expr.Wf ?e ] => apply (@GeneralizeVar.Wf_via_flat _ e); vm_compute; split; reflexivity
    end.
End Compilers.
