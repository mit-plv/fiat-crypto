Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Logic.ProdForall.
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

  Create HintDb wf discriminated.
  Create HintDb interp discriminated.

  Module type.
    Section eqv.
      Context {base_type} {interp_base_type : base_type -> Type}.
      Local Notation eqv := (@type.related base_type interp_base_type (fun _ => eq)).

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

    Section app_curried_instances.
      Context {base_type} {base_interp : base_type -> Type}.
      (* Might want to add the following to make [app_curried_Proper] usable by [setoid_rewrite]? *)
      (* See https://github.com/coq/coq/issues/8179
<<
Lemma PER_valid_l {A} {R : relation A} {HS : Symmetric R} {HT : Transitive R} x y (H : R x y) : Proper R x.
Proof. hnf; etransitivity; eassumption || symmetry; eassumption. Qed.
Lemma PER_valid_r {A} {R : relation A} {HS : Symmetric R} {HT : Transitive R} x y (H : R x y) : Proper R y.
Proof. hnf; etransitivity; eassumption || symmetry; eassumption. Qed.
Hint Extern 10 (Proper ?R ?x) => simple eapply (@PER_valid_l _ R); [ | | solve [ eauto with nocore ] ] : typeclass_instances.
Hint Extern 10 (Proper ?R ?x) => simple eapply (@PER_valid_r _ R); [ | | solve [ eauto with nocore ] ] : typeclass_instances.
>>
*)
      Global Instance app_curried_Proper_gen {base_type base_interp R t}
        : Proper (@type.related base_type base_interp R t ==> type.and_for_each_lhs_of_arrow (@type.related base_type base_interp R)  ==> R (type.final_codomain t))
                 (@type.app_curried base_type base_interp t) | 1.
      Proof.
        cbv [Proper respectful]; induction t; cbn [type.related type.app_curried]; cbv [Proper respectful]; [ intros; assumption | ].
        intros f g Hfg x y [Hxy ?]; eauto.
      Qed.
      Lemma app_curried_Proper {t}
        : Proper (@type.related base_type base_interp (fun _ => eq) t ==> type.and_for_each_lhs_of_arrow (@type.eqv) ==> eq)
                 (@type.app_curried base_type base_interp t).
      Proof. exact _. Qed.
      Global Instance and_for_each_lhs_of_arrow_Reflexive {f} {R} {_ : forall t, Reflexive (R t)} {t}
        : Reflexive (@type.and_for_each_lhs_of_arrow base_type f f R t) | 1.
      Proof. cbv [Reflexive] in *; induction t; cbn; repeat split; eauto. Qed.
      Global Instance and_for_each_lhs_of_arrow_Symmetric {f} {R} {_ : forall t, Symmetric (R t)} {t}
        : Symmetric (@type.and_for_each_lhs_of_arrow base_type f f R t) | 1.
      Proof. cbv [Symmetric] in *; induction t; cbn; repeat split; intuition eauto. Qed.
      Global Instance and_for_each_lhs_of_arrow_Transitive {f} {R} {_ : forall t, Transitive (R t)} {t}
        : Transitive (@type.and_for_each_lhs_of_arrow base_type f f R t) | 1.
      Proof. cbv [Transitive] in *; induction t; cbn; repeat split; intuition eauto. Qed.
    End app_curried_instances.

    Lemma related_iff_app_curried {base_type base_interp R} t F G
      : (@type.related base_type base_interp R t F G)
        <-> (forall x y, type.and_for_each_lhs_of_arrow (@type.related base_type base_interp R) x y -> R (type.final_codomain t) (type.app_curried F x) (type.app_curried G y)).
    Proof using Type.
      induction t as [t|s IHs d IHd]; cbn; [ tauto | ].
      cbv [respectful].
      rewrite pull_prod_forall.
      lazymatch goal with
      | [ |- (forall x y, @?P x y) <-> (forall z w, @?Q z w) ]
        => cut (forall x y, (P x y <-> Q x y)); [ intro H'; setoid_rewrite H'; reflexivity | intros ??; cbn [fst snd] ]
      end.
      lazymatch goal with
      | [ |- (?P -> ?Q) <-> (forall z w, ?P' /\ @?R z w -> @?S z w) ]
        => unify P P'; cut (P' -> (Q <-> (forall z w, R z w -> S z w))); [ change P with P'; solve [ intuition ] | intro; cbn [fst snd] ]
      end.
      eauto.
    Qed.

    Lemma andb_bool_impl_and_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
          (R : forall t, f t -> g t -> bool)
          (R' : forall t, f t -> g t -> Prop)
          (HR : forall t x y, R t x y = true -> R' t x y)
          {t} x y
      : @type.andb_bool_for_each_lhs_of_arrow base_type f g R t x y = true
        -> @type.and_for_each_lhs_of_arrow base_type f g R' t x y.
    Proof.
      induction t; cbn in *; rewrite ?Bool.andb_true_iff; destruct_head'_prod; cbn [fst snd]; intuition.
    Qed.

    Lemma and_impl_andb_bool_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
          (R : forall t, f t -> g t -> bool)
          (R' : forall t, f t -> g t -> Prop)
          (HR : forall t x y, R' t x y -> R t x y = true)
          {t} x y
      : @type.and_for_each_lhs_of_arrow base_type f g R' t x y
        -> @type.andb_bool_for_each_lhs_of_arrow base_type f g R t x y = true.
    Proof.
      induction t; cbn in *; rewrite ?Bool.andb_true_iff; destruct_head'_prod; cbn [fst snd]; intuition.
    Qed.

    Lemma andb_bool_iff_and_for_each_lhs_of_arrow {base_type} {f g : type base_type -> Type}
          (R : forall t, f t -> g t -> bool)
          (R' : forall t, f t -> g t -> Prop)
          (HR : forall t x y, R t x y = true <-> R' t x y)
          {t} x y
      : @type.andb_bool_for_each_lhs_of_arrow base_type f g R t x y = true
        <-> @type.and_for_each_lhs_of_arrow base_type f g R' t x y.
    Proof.
      induction t; cbn in *; rewrite ?Bool.andb_true_iff; destruct_head'_prod; cbn [fst snd]; split_iff; intuition.
    Qed.
  End type.

  Module ident.
    Local Open Scope etype_scope.
    Global Instance gen_eqv_Reflexive_Proper cast_outside_of_range {t} (idc : ident t) : Proper type.eqv (ident.gen_interp cast_outside_of_range idc) | 1.
    Proof.
      destruct idc; cbn [type.eqv ident.gen_interp type.interp base.interp base.base_interp];
        try solve [ typeclasses eauto
                  | cbv [respectful]; repeat intro; subst; destruct_head_hnf bool; destruct_head_hnf prod; eauto
                  | cbv [respectful]; repeat intro; (apply nat_rect_Proper_nondep || apply list_rect_Proper || apply list_case_Proper); repeat intro; eauto ].
    Qed.

    Global Instance eqv_Reflexive_Proper {t} (idc : ident t) : Proper type.eqv (ident.interp idc) | 1.
    Proof. exact _. Qed.

    Global Instance gen_interp_Proper {cast_outside_of_range} {t} : Proper (@eq (ident t) ==> type.eqv) (ident.gen_interp cast_outside_of_range) | 1.
    Proof. intros idc idc' ?; subst idc'; apply gen_eqv_Reflexive_Proper. Qed.

    Global Instance interp_Proper {t} : Proper (@eq (ident t) ==> type.eqv) ident.interp | 1.
    Proof. exact _. Qed.

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

      Section with_var3.
        Context {var1 var2 var3 : type.type base_type -> Type}.
        Local Notation wfvP := (fun t => (var1 t * var2 t * var3 t)%type).
        Local Notation wfvT := (list (sigT wfvP)).
        Local Notation expr := (@expr.expr base_type ident). (* But can't use this to define other notations, see COQBUG(https://github.com/coq/coq/issues/8126) *)
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation expr3 := (@expr.expr base_type ident var3).
        Inductive wf3 : wfvT -> forall {t}, expr1 t -> expr2 t -> expr3 t -> Prop :=
        | Wf3Ident
          : forall G {t} (idc : ident t), wf3 G (expr.Ident idc) (expr.Ident idc) (expr.Ident idc)
        | Wf3Var
          : forall G {t} (v1 : var1 t) (v2 : var2 t) (v3 : var3 t), List.In (existT _ t (v1, v2, v3)) G -> wf3 G (expr.Var v1) (expr.Var v2) (expr.Var v3)
        | Wf3Abs
          : forall G {s d} (f1 : var1 s -> expr1 d) (f2 : var2 s -> expr2 d) (f3 : var3 s -> expr3 d),
            (forall (v1 : var1 s) (v2 : var2 s) (v3 : var3 s), wf3 (existT _ s (v1, v2, v3) :: G) (f1 v1) (f2 v2) (f3 v3))
            -> wf3 G (expr.Abs f1) (expr.Abs f2) (expr.Abs f3)
        | Wf3App
          : forall G {s d}
                   (f1 : expr1 (s -> d)) (f2 : expr2 (s -> d)) (f3 : expr3 (s -> d)) (wf_f : wf3 G f1 f2 f3)
                   (x1 : expr1 s) (x2 : expr2 s) (x3 : expr3 s) (wf_x : wf3 G x1 x2 x3),
            wf3 G (expr.App f1 x1) (expr.App f2 x2) (expr.App f3 x3)
        | Wf3LetIn
          : forall G {A B}
                   (x1 : expr1 A) (x2 : expr2 A) (x3 : expr3 A) (wf_x : wf3 G x1 x2 x3)
                   (f1 : var1 A -> expr1 B) (f2 : var2 A -> expr2 B) (f3 : var3 A -> expr3 B),
            (forall (v1 : var1 A) (v2 : var2 A) (v3 : var3 A), wf3 (existT _ A (v1, v2, v3) :: G) (f1 v1) (f2 v2) (f3 v3))
            -> wf3 G (expr.LetIn x1 f1) (expr.LetIn x2 f2) (expr.LetIn x3 f3).
      End with_var3.

      Definition Wf {t} (e : @expr.Expr base_type ident t) : Prop
        := forall var1 var2, @wf var1 var2 nil t (e var1) (e var2).

      Definition Wf3 {t} (e : @expr.Expr base_type ident t) : Prop
        := forall var1 var2 var3, @wf3 var1 var2 var3 nil t (e var1) (e var2) (e var3).
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

      Lemma wf3_of_wf {var1 var2 var3} G1 G2 G {t}
            (HG1 : G1 = List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v2)) G)
            (HG2 : G2 = List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v2, v3)) G)
            e1 e2 e3
            (Hwf12 : @wf var1 var2 G1 t e1 e2)
            (Hwf23 : @wf var2 var3 G2 t e2 e3)
        : @wf3 base_type ident var1 var2 var3 G t e1 e2 e3.
      Proof.
        revert dependent G; revert dependent G2; revert dependent e3; induction Hwf12; intros.
        all: try solve [ repeat first [ progress subst
                          | progress destruct_head' False
                          | progress destruct_head'_sig
                          | progress destruct_head'_and
                          | progress intros
                          | progress expr.invert_subst
                          | progress inversion_wf_one_constr
                          | progress cbn [projT1 projT2 fst snd eq_rect] in *
                          | solve [ eauto ]
                          | break_innermost_match_hyps_step
                          | match goal with
                            | [ |- wf3 _ _ _ _ ] => constructor
                            | [ H : _ |- wf3 _ _ _ _ ] => eapply H
                            end ] ].
        repeat first [ progress subst
                          | progress inversion_sigma
                          | progress inversion_prod
                          | progress destruct_head' False
                          | progress destruct_head'_sig
                          | progress destruct_head'_and
                          | progress destruct_head'_ex
                          | progress intros
                          | progress expr.invert_subst
                          | progress inversion_wf_one_constr
                          | progress cbn [projT1 projT2 fst snd eq_rect] in *
                          | solve [ eauto ]
                          | break_innermost_match_hyps_step
                          | match goal with
                            | [ |- wf3 _ _ _ _ ] => constructor
                            | [ H : _ |- wf3 _ _ _ _ ] => eapply H
                            end
                          | rewrite in_map_iff in * ].
        (* seems false? *)
      Abort.
    End wf_properties.

    Section interp_gen.
      Context {base_type}
              {ident : type base_type -> Type}
              {base_interp : base_type -> Type}
              {R : forall t, relation (base_interp t)}.
      Section with_2.
        Context {ident_interp1 ident_interp2 : forall t, ident t -> type.interp base_interp t}
                {ident_interp_Proper : forall t, (eq ==> type.related R)%signature (ident_interp1 t) (ident_interp2 t)}.

        Lemma wf_interp_Proper_gen2
              G {t} e1 e2
              (Hwf : @wf _ _ _ _ G t e1 e2)
              (HG : forall t v1 v2, In (existT _ t (v1, v2)) G -> type.related R v1 v2)
          : type.related R (expr.interp ident_interp1 e1) (expr.interp ident_interp2 e2).
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
                           | [ |- type.related R (ident_interp1 _ ?x) (ident_interp2 _ ?y) ] => apply ident_interp_Proper
                           | [ |- Proper type.eqv (ident.interp _) ] => apply ident.eqv_Reflexive_Proper
                           | [ H : context[?R (expr.interp _ _) (expr.interp _ _)] |- ?R (expr.interp _ _) (expr.interp _ _) ] => eapply H; eauto with nocore
                           end ].
        Qed.
      End with_2.

      Section with_1.
        Context {ident_interp : forall t, ident t -> type.interp base_interp t}
                {ident_interp_Proper : forall t, Proper (eq ==> type.related R) (ident_interp t)}.

        Lemma wf_interp_Proper_gen1 G {t}
              (HG : forall t v1 v2, In (existT _ t (v1, v2)) G -> type.related R v1 v2)
          : Proper (@wf _ _ _ _ G t ==> type.related R) (expr.interp ident_interp).
        Proof. intros ? ? Hwf; eapply @wf_interp_Proper_gen2; eassumption. Qed.

        Lemma wf_interp_Proper_gen {t}
          : Proper (@wf _ _ _ _ nil t ==> type.related R) (expr.interp ident_interp).
        Proof. apply wf_interp_Proper_gen1; cbn [In]; tauto. Qed.

        Lemma Wf_Interp_Proper_gen {t} (e : expr.Expr t) : Wf e -> Proper (type.related R) (expr.Interp ident_interp e).
        Proof. intro Hwf; apply wf_interp_Proper_gen, Hwf. Qed.
      End with_1.
    End interp_gen.

    Section for_interp.
      Local Open Scope etype_scope.
      Import defaults.
      Lemma wf_interp_Proper G {t} e1 e2
            (Hwf : @wf _ _ _ _ G t e1 e2)
            (HG : forall t v1 v2, In (existT _ t (v1, v2)) G -> v1 == v2)
        : interp e1 == interp e2.
      Proof. apply @wf_interp_Proper_gen1 with (G:=G); eauto using ident.interp_Proper. Qed.

      Lemma Wf_Interp_Proper {t} (e : Expr t) : Wf e -> Proper type.eqv (Interp e).
      Proof. repeat intro; apply wf_interp_Proper with (G:=nil); cbn [List.In]; intuition eauto. Qed.
    End for_interp.

    Section invert.
      Section with_var2.
        Context {var1 var2 : type.type base.type -> Type}.
        Local Notation expr1 := (@expr.expr base.type ident.ident var1).
        Local Notation expr2 := (@expr.expr base.type ident.ident var2).

        Lemma wf_reify_list G {t} e1 e2
          : @wf _ _ var1 var2 G _ (reify_list (t:=t) e1) (reify_list (t:=t) e2)
            <-> (List.length e1 = List.length e2
               /\ forall e1' e2', List.In (e1', e2') (List.combine e1 e2) -> wf G e1' e2').
        Proof.
          revert e2; induction e1 as [|e1 e1s IHe1s], e2 as [|e2 e2s];
            rewrite ?expr.reify_list_cons, ?expr.reify_list_nil; cbn [length combine];
              repeat first [ progress apply conj
                           | progress intros
                           | progress destruct_head'_and
                           | progress destruct_head'_sig
                           | progress type.inversion_type
                           | progress base.type.inversion_type
                           | congruence
                           | tauto
                           | progress cbn [In] in *
                           | match goal with |- wf _ _ _ => constructor end
                           | progress inversion_wf_constr
                           | rewrite IHe1s in *
                           | progress destruct_head'_or
                           | solve [ eauto ] ].
        Qed.

        Lemma wf_reflect_list G {t} e1 e2
           : @wf _ _ var1 var2 G (type.base (base.type.list t)) e1 e2
            -> (invert_expr.reflect_list e1 = None <-> invert_expr.reflect_list e2 = None).
        Proof.
          destruct (invert_expr.reflect_list e1) eqn:H1, (invert_expr.reflect_list e2) eqn:H2;
            try (split; congruence); expr.invert_subst;
              try revert dependent e2; try revert dependent e1;
                match goal with
                | [ |- context[Some ?l = None] ]
                  => induction l as [|x xs IHxs]
                end;
                rewrite ?expr.reify_list_cons, ?expr.reify_list_nil;
                intro; rewrite expr.reflect_list_step; cbv [option_map];
                  break_innermost_match; try congruence; intros;
                    lazymatch goal with
                    | [ |- Some (?x :: ?xs) = None <-> ?P ]
                      => cut (Some xs = None <-> P); [ intuition congruence | ]
                    | [ |- ?P <-> Some (?x :: ?xs) = None ]
                      => cut (P <-> Some xs = None); [ intuition congruence | ]
                    | _ => idtac
                    end.
          all: repeat first [ congruence
                            | progress inversion_wf_constr
                            | progress subst
                            | progress cbv [option_map] in *
                            | progress destruct_head' False
                            | progress destruct_head'_sig
                            | progress destruct_head'_and
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress inversion_prod
                            | progress type.inversion_type
                            | progress base.type.inversion_type
                            | progress break_match_hyps
                            | progress cbn [fst snd invert_expr.invert_Ident invert_expr.invert_nil invert_expr.invert_cons invert_expr.invert_AppIdent2 invert_expr.invert_Ident invert_expr.invert_App2 invert_expr.invert_App Option.bind fst snd projT1 projT2 eq_rect] in *
                            | progress expr.invert_subst
                            | solve [ eauto ]
                            | progress inversion_wf_one_constr
                            | progress expr.invert_match ].
        Qed.

        Lemma wf_reify {t} v G : expr.wf G (@GallinaReify.base.reify var1 t v) (@GallinaReify.base.reify var2 t v).
        Proof.
          induction t; cbn; break_innermost_match; repeat constructor; auto; [].
          rewrite wf_reify_list, !map_length, combine_map_map, combine_same, map_map; split; auto; intros *; [].
          cbn [fst snd]; rewrite in_map_iff; intros.
          repeat first [ progress destruct_head'_and
                       | progress destruct_head'_ex
                       | progress inversion_prod
                       | progress subst
                       | solve [ eauto ] ].
        Qed.
      End with_var2.

      Lemma Wf_Reify_as {t} v : expr.Wf (@GallinaReify.base.Reify_as t v).
      Proof. repeat intro; apply wf_reify. Qed.

      Section interp.
        Import defaults.
        Lemma interp_reify_list {t} ls : interp (reify_list (t:=t) ls) = List.map interp ls.
        Proof.
          cbv [reify_list]; induction ls as [|l ls IHls]; [ reflexivity | ];
            cbn [list_rect map expr.interp ident.interp ident.gen_interp]; rewrite <- IHls;
              reflexivity.
        Qed.

        Lemma interp_reify {t} v : interp (GallinaReify.base.reify (t:=t) v) = v.
        Proof.
          induction t; cbn [GallinaReify.base.reify]; break_innermost_match; cbn; f_equal;
            rewrite ?interp_reify_list, ?map_map; auto.
          { etransitivity; [ | apply map_id ]; apply map_ext; auto. }
        Qed.

        Lemma Interp_Reify_as {t} v : Interp (GallinaReify.base.Reify_as t v) = v.
        Proof. apply interp_reify. Qed.
      End interp.
    End invert.

    (** [Reify] is a notation for [Reify_as] + better type inference, so we make [Wf_Reify] available for ease of memory / lookup *)
    Notation Wf_Reify := Wf_Reify_as.
    Notation Interp_Reify := Interp_Reify_as.
  End expr.

  Hint Resolve expr.Wf_Reify : wf.
  Hint Rewrite @expr.Interp_Reify @expr.interp_reify @expr.interp_reify_list : interp.

  Notation Wf := expr.Wf.

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
          | progress destruct_head' False
          | progress cbn [List.In eq_rect] in *
          | match goal with
            | [ |- expr.wf _ _ _ ] => constructor
            end
          | solve [ eauto using conj, eq_refl, or_introl, or_intror with nocore ]
          | progress destruct_head'_or
          | match goal with
            | [ |- context[List.In _ (_ ++ _)%list] ] => rewrite in_app_iff
            | [ H : context[List.In _ (_ ++ _)%list] |- _ ] => rewrite in_app_iff in H
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
  Module DefaultValue.
    Import Language.Compilers.DefaultValue.
    Module expr.
      Module base.
        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Lemma wf_default G {t : base.type} : expr.wf G (@expr.base.default var1 t) (@expr.base.default var2 t).
          Proof.
            induction t; destruct_head' base.type.base; wf_t.
          Qed.
        End with_var2.

        Lemma Wf_Default {t : base.type} : Wf (@expr.base.Default t).
        Proof. repeat intro; apply @wf_default. Qed.
      End base.

      Section with_var2.
        Context {var1 var2 : type -> Type}.

        Lemma wf_default G {t : type} : expr.wf G (@expr.default var1 t) (@expr.default var2 t).
        Proof. revert G; induction t; intros; wf_t; apply base.wf_default. Qed.
      End with_var2.

      Lemma Wf_Default {t : type} : Wf (@expr.Default t).
      Proof. repeat intro; apply @wf_default. Qed.
    End expr.
  End DefaultValue.

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

    Section with_var3.
      Context {var1 var2 var3 : type -> Type}.

      Lemma wf3_from_flat_gen
            {t}
            (e : Flat.expr t)
        : forall (G1 : PositiveMap.t type) (G2 : list { t : _ & var1 t * var2 t * var3 t }%type)
                 (ctx1 : PositiveMap.t { t : type & var1 t })
                 (ctx2 : PositiveMap.t { t : type & var2 t })
                 (ctx3 : PositiveMap.t { t : type & var3 t })
                 (H_G1_ctx1 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx1))
                 (H_G1_ctx2 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx2))
                 (H_G1_ctx3 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx3))
                 (H_ctx_G2 : forall t v1 v2 v3, List.In (existT _ t (v1, v2, v3)) G2
                                             <-> (exists p, PositiveMap.find p ctx1 = Some (existT _ t v1) /\ PositiveMap.find p ctx2 = Some (existT _ t v2) /\ PositiveMap.find p ctx3 = Some (existT _ t v3))),
          Flat.wf G1 e = true -> expr.wf3 G2 (from_flat e var1 ctx1) (from_flat e var2 ctx2) (from_flat e var3 ctx3).
      Proof.
        induction e;
          repeat first [ progress cbn [Flat.wf from_flat option_map projT1 projT2 List.In fst snd] in *
                       | progress intros
                       | destructure_step
                       | progress cbv [Option.bind type.try_transport type.try_transport_cps cpsreturn cpsbind cpscall cps_option_bind eq_rect id] in *
                       | match goal with |- expr.wf3 _ _ _ _ => constructor end
                       | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                       | congruence
                       | destructure_split_step
                       | erewrite type.try_make_transport_cps_correct
                         by first [ exact base.type.internal_type_dec_lb | exact base.try_make_transport_cps_correct ]
                       | match goal with
                         | [ H : context[expr.wf3 _ _ _ _] |- expr.wf3 _ _ _ _ ] => eapply H; clear H; eauto with nocore
                         | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
                         | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
                         | [ H : forall t v1 v2 v3, In _ ?G2 <-> _ |- context[In _ ?G2] ] => rewrite H
                         | [ H : In _ ?G2, H' : forall t v1 v2 v3, In _ ?G2 <-> _ |- _ ] => rewrite H' in H
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

      Lemma wf3_from_flat
            {t}
            (e : Flat.expr t)
        : Flat.wf (PositiveMap.empty _) e = true -> expr.wf3 nil (from_flat e var1 (PositiveMap.empty _)) (from_flat e var2 (PositiveMap.empty _)) (from_flat e var3 (PositiveMap.empty _)).
      Proof.
        apply wf3_from_flat_gen; intros *;
          repeat setoid_rewrite PositiveMap.gempty;
          cbn [In option_map];
          intuition (destruct_head'_ex; intuition (congruence || auto)).
      Qed.
    End with_var3.

    Lemma Wf_FromFlat {t} (e : Flat.expr t) : Flat.wf (PositiveMap.empty _) e = true -> expr.Wf (FromFlat e).
    Proof. intros H ??; apply wf_from_flat, H. Qed.

    Lemma Wf3_FromFlat {t} (e : Flat.expr t) : Flat.wf (PositiveMap.empty _) e = true -> expr.Wf3 (FromFlat e).
    Proof. intros H ???; apply wf3_from_flat, H. Qed.

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

    Lemma Wf3_FromFlat_to_flat {t} (e : expr t) : expr.wf nil e e -> expr.Wf3 (FromFlat (to_flat e)).
    Proof. intro Hwf; eapply Wf3_FromFlat, wf_to_flat, Hwf. Qed.
    Lemma Wf3_FromFlat_ToFlat {t} (e : Expr t) : expr.Wf e -> expr.Wf3 (FromFlat (ToFlat e)).
    Proof. intro H; apply Wf3_FromFlat_to_flat, H. Qed.
    Lemma Wf3_GeneralizeVar {t} (e : Expr t) : expr.Wf e -> expr.Wf3 (GeneralizeVar (e _)).
    Proof. apply Wf3_FromFlat_ToFlat. Qed.

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
                     | [ H : context[type.related _ (expr.interp _ _) (expr.interp _ _)] |- type.related _ (expr.interp _ _) (expr.interp _ _) ] => eapply H; clear H; solve [ t ]
                     end ].
    Section gen2.
      Context {base_interp : base.type -> Type}
              {ident_interp1 ident_interp2 : forall t, ident t -> type.interp base_interp t}
              {R : forall t, relation (base_interp t)}
              {ident_interp_Proper : forall t, (eq ==> type.related R)%signature (ident_interp1 t) (ident_interp2 t)}.

      Lemma interp_gen2_from_flat_to_flat'
            {t} (e1 : expr t) (e2 : expr t) G ctx
            (H_ctx_G : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                       -> (exists v2', PositiveMap.find v1 ctx = Some (existT _ t v2') /\ type.related R v2' v2))
            (Hwf : expr.wf G e1 e2)
            cur_idx
            (Hidx : forall p, PositiveMap.mem p ctx = true -> BinPos.Pos.lt p cur_idx)
        : type.related R (expr.interp ident_interp1 (from_flat (to_flat' e1 cur_idx) _ ctx)) (expr.interp ident_interp2 e2).
      Proof.
        setoid_rewrite PositiveMap.mem_find in Hidx.
        revert dependent cur_idx; revert dependent ctx; induction Hwf; intros;
          t.
      Qed.

      Lemma Interp_gen2_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e)
        : type.related R (expr.Interp ident_interp1 (FromFlat (ToFlat e))) (expr.Interp ident_interp2 e).
      Proof.
        cbv [Interp FromFlat ToFlat to_flat].
        apply interp_gen2_from_flat_to_flat' with (G:=nil); eauto; intros *; cbn [List.In]; rewrite ?PositiveMap.mem_find, ?PositiveMap.gempty;
          intuition congruence.
      Qed.

      Lemma Interp_gen2_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e)
        : type.related R (expr.Interp ident_interp1 (GeneralizeVar (e _))) (expr.Interp ident_interp2 e).
      Proof. apply Interp_gen2_FromFlat_ToFlat, Hwf. Qed.
    End gen2.
    Section gen1.
      Context {base_interp : base.type -> Type}
              {ident_interp : forall t, ident t -> type.interp base_interp t}
              {R : forall t, relation (base_interp t)}
              {ident_interp_Proper : forall t, Proper (eq ==> type.related R) (ident_interp t)}.

      Lemma interp_gen1_from_flat_to_flat'
            {t} (e1 : expr t) (e2 : expr t) G ctx
            (H_ctx_G : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                       -> (exists v2', PositiveMap.find v1 ctx = Some (existT _ t v2') /\ type.related R v2' v2))
            (Hwf : expr.wf G e1 e2)
            cur_idx
            (Hidx : forall p, PositiveMap.mem p ctx = true -> BinPos.Pos.lt p cur_idx)
        : type.related R (expr.interp ident_interp (from_flat (to_flat' e1 cur_idx) _ ctx)) (expr.interp ident_interp e2).
      Proof. apply @interp_gen2_from_flat_to_flat' with (G:=G); eassumption. Qed.

      Lemma Interp_gen1_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e)
        : type.related R (expr.Interp ident_interp (FromFlat (ToFlat e))) (expr.Interp ident_interp e).
      Proof. apply @Interp_gen2_FromFlat_ToFlat; eassumption. Qed.

      Lemma Interp_gen1_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e)
        : type.related R (expr.Interp ident_interp (GeneralizeVar (e _))) (expr.Interp ident_interp e).
      Proof. apply @Interp_gen2_GeneralizeVar; eassumption. Qed.
    End gen1.

    Lemma interp_from_flat_to_flat'
          {t} (e1 : expr t) (e2 : expr t) G ctx
          (H_ctx_G : forall t v1 v2, List.In (existT _ t (v1, v2)) G
                                     -> (exists v2', PositiveMap.find v1 ctx = Some (existT _ t v2') /\ v2' == v2))
          (Hwf : expr.wf G e1 e2)
          cur_idx
          (Hidx : forall p, PositiveMap.mem p ctx = true -> BinPos.Pos.lt p cur_idx)
      : interp (from_flat (to_flat' e1 cur_idx) _ ctx) == interp e2.
    Proof. apply @interp_gen1_from_flat_to_flat' with (G:=G); eauto using ident.interp_Proper. Qed.

    Lemma Interp_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e) : Interp (FromFlat (ToFlat e)) == Interp e.
    Proof. apply @Interp_gen1_FromFlat_ToFlat; eauto using ident.interp_Proper. Qed.

    Lemma Interp_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e) : Interp (GeneralizeVar (e _)) == Interp e.
    Proof. apply Interp_FromFlat_ToFlat, Hwf. Qed.
  End GeneralizeVar.

  Ltac prove_Wf _ :=
    lazymatch goal with
    | [ |- expr.Wf ?e ] => apply (@GeneralizeVar.Wf_via_flat _ e); vm_cast_no_check (conj (eq_refl e) (eq_refl true))
    end.

  Global Hint Extern 0 (?x == ?x) => apply expr.Wf_Interp_Proper : wf interp.
  Hint Resolve GeneralizeVar.Wf_FromFlat_ToFlat GeneralizeVar.Wf_GeneralizeVar : wf.
  Hint Resolve GeneralizeVar.Wf3_FromFlat_ToFlat GeneralizeVar.Wf3_GeneralizeVar : wf.
  Hint Rewrite @GeneralizeVar.Interp_GeneralizeVar @GeneralizeVar.Interp_FromFlat_ToFlat : interp.
End Compilers.
