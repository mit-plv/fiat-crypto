Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Logic.ProdForall.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import expr.Notations.

  Create HintDb wf discriminated.
  Create HintDb interp discriminated.

  Hint Extern 2 => typeclasses eauto : wf.

  Module type.
    Section eqv.
      Context {base_type} {interp_base_type : base_type -> Type}.
      Local Notation eqv := (@type.related base_type interp_base_type (fun _ => eq)).

      Lemma eqv_iff_eq_of_funext
            (funext : forall A B (f g : type.interp interp_base_type A -> type.interp interp_base_type B),
                (forall x, f x = g x)
                -> f = g)
            {t f g}
        : @eqv t f g <-> f = g.
      Proof using Type.
        induction t as [|s IHs d IHd]; cbn [type.related]; cbv [respectful]; [ reflexivity | ].
        split; intro H.
        { apply funext; intro; apply IHd, H, IHs; reflexivity. }
        { intros; apply IHd; subst; f_equal; apply IHs; assumption. }
      Qed.

      Local Instance related_Symmetric {t} {R : forall t, relation (interp_base_type t)}
             {R_sym : forall t, Symmetric (R t)}
        : Symmetric (@type.related base_type interp_base_type R t) | 100.
      Proof.
        cbv [Symmetric] in *;
          induction t; cbn [type.related type.interp] in *; repeat intro; eauto.
      Qed.

      Local Instance related_Transitive {t} {R : forall t, relation (interp_base_type t)}
             {R_sym : forall t, Symmetric (R t)}
             {R_trans : forall t, Transitive (R t)}
        : Transitive (@type.related base_type interp_base_type R t) | 100.
      Proof.
        induction t; cbn [type.related]; [ exact _ | ].
        cbv [respectful]; cbn [type.interp].
        intros f g h Hfg Hgh x y Hxy.
        etransitivity; [ eapply Hfg; eassumption | eapply Hgh ].
        etransitivity; first [ eassumption | symmetry; eassumption ].
      Qed.

      Global Instance eqv_Transitive {t} : Transitive (@eqv t) | 10 := _.
      Global Instance eqv_Symmetric {t} : Symmetric (@eqv t) | 10 := _.
    End eqv.
    Hint Extern 100 (Symmetric (@type.related ?base_type ?interp_base_type ?R ?t))
    => (tryif has_evar R then fail else simple apply (@related_Symmetric base_type interp_base_type t R)) : typeclass_instances.
    Hint Extern 100 (Transitive (@type.related ?base_type ?interp_base_type ?R ?t))
    => (tryif has_evar R then fail else simple apply (@related_Transitive base_type interp_base_type t R)) : typeclass_instances.

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
      Global Instance app_curried_Proper_gen {R t}
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

    Lemma and_eqv_for_each_lhs_of_arrow_not_higher_order {base_type base_interp t}
           (Ht : type.is_not_higher_order t = true)
           (v : @type.for_each_lhs_of_arrow base_type (type.interp base_interp) t)
      : Proper (type.and_for_each_lhs_of_arrow (@type.eqv) (t:=t)) v.
    Proof using Type.
      cbv [Proper]; induction t as [t|s IHs d IHd]; cbn in *; [ tauto | ].
      rewrite Bool.andb_true_iff in Ht; destruct Ht.
      destruct s; cbn in *; try discriminate.
      eauto.
    Qed.

    Global Hint Immediate and_eqv_for_each_lhs_of_arrow_not_higher_order : typeclass_instances.

    Lemma related_hetero_iff_app_curried {base_type base_interp1 base_interp2 R} t F G
      : (@type.related_hetero base_type base_interp1 base_interp2 R t F G)
        <-> (forall x y, type.and_for_each_lhs_of_arrow (@type.related_hetero base_type base_interp1 base_interp2 R) x y -> R (type.final_codomain t) (type.app_curried F x) (type.app_curried G y)).
    Proof using Type.
      induction t as [t|s IHs d IHd]; cbn; [ tauto | ].
      cbv [respectful_hetero].
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

    Lemma related_hetero_iff_related {base_type base_interp R} t F G
      : (@type.related_hetero base_type base_interp base_interp R t F G)
        <-> (@type.related base_type base_interp R t F G).
    Proof.
      induction t as [t|s IHs d IHd]; cbn; [ tauto | ].
      cbv [respectful respectful_hetero]; split_iff; intuition eauto.
    Qed.

    Global Instance and_for_each_lhs_of_arrow_Proper_iff {base_type f g}
      : Proper (forall_relation (fun t => pointwise_relation _ (pointwise_relation _ iff)) ==> forall_relation (fun t => eq ==> eq ==> iff))
               (@type.and_for_each_lhs_of_arrow base_type f g) | 10.
    Proof.
      cbv [forall_relation pointwise_relation respectful]; intros ? ? H t ? ? ? ? ? ?; subst.
      induction t; cbn [type.and_for_each_lhs_of_arrow]; split_iff; intuition eauto.
    Qed.

    Lemma related_iff_app_curried {base_type base_interp R} t F G
      : (@type.related base_type base_interp R t F G)
        <-> (forall x y, type.and_for_each_lhs_of_arrow (@type.related base_type base_interp R) x y -> R (type.final_codomain t) (type.app_curried F x) (type.app_curried G y)).
    Proof using Type.
      rewrite <- related_hetero_iff_related.
      change (@type.related base_type base_interp R) with (fun t x y => @type.related base_type base_interp R t x y).
      setoid_rewrite <- related_hetero_iff_related.
      apply related_hetero_iff_app_curried.
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

      Section with_interp.
        Context {interp_base_type : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp interp_base_type t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

        Lemma eqv_of_interp_related {t e v}
          : expr.interp_related interp_ident e v
            -> @type.eqv t (expr.interp interp_ident e) v.
        Proof using Type.
          cbv [expr.interp_related]; induction e; cbn [expr.interp_related_gen expr.interp type.related]; cbv [respectful LetIn.Let_In].
          all: repeat first [ progress intros
                            | assumption
                            | solve [ eauto ]
                            | progress destruct_head'_ex
                            | progress destruct_head'_and
                            | progress subst
                            | match goal with H : _ |- _ => apply H; clear H end ].
        Qed.

        Lemma interp_related_gen_of_wf {var R G t e1 e2}
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> (R t v1 v2 : Prop))
              (Hwf : wf G e1 e2)
          : @expr.interp_related_gen _ _ _ interp_ident var R t e1 (expr.interp interp_ident e2).
        Proof using interp_ident_Proper.
          induction Hwf.
          all: repeat first [ progress cbn [expr.interp_related_gen expr.interp List.In eq_rect] in *
                            | progress cbv [LetIn.Let_In] in *
                            | reflexivity
                            | solve [ eauto ]
                            | progress intros
                            | progress destruct_head'_or
                            | progress inversion_sigma
                            | progress inversion_prod
                            | progress specialize_by_assumption
                            | progress subst
                            | apply interp_ident_Proper
                            | match goal with
                              | [ |- exists fv xv, _ /\ _ /\ _ ]
                                => eexists (expr.interp interp_ident (expr.Abs _)), _;
                                   cbn [expr.interp]; repeat apply conj; [ eassumption | | reflexivity ]
                              | [ H : _ |- _ ] => apply H; clear H
                              end ].
        Qed.
      End with_interp.

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

      Local Hint Constructors wf : wf.
      Lemma Wf_APP {s d f x} : @Wf (s -> d) f -> @Wf s x -> @Wf d (expr.APP f x).
      Proof using Type. cbv [Wf expr.APP]; auto with wf. Qed.
    End with_ty.
    Global Hint Constructors wf : wf.
    Global Hint Resolve @Wf_APP : wf.
    Hint Rewrite @expr.Interp_APP : interp.

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

      Lemma wf_of_wf3 {var1 var2} G {t}
            (G1 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v1, v2)) G)
            (G2 := List.map (fun '(existT t (v1, v2, v3)) => existT _ t (v2, v3)) G)
            e1 e2 e3
            (Hwf : @wf3 base_type ident var1 var2 var2 G t e1 e2 e3)
        : @wf _ _ G1 t e1 e2.
      Proof.
        subst G1 G2.
        induction Hwf; cbn [map] in *; constructor; rewrite ?in_map_iff; intros;
          try eexists (existT (fun t => _ * _ * _)%type _ (_, _, _));
          split_and;
          repeat apply conj; try reflexivity; try eassumption;
            eauto.
      Qed.

      Lemma Wf_of_Wf3 {t} (e : expr.Expr t) : @Wf3 base_type ident t e -> @Wf base_type ident t e.
      Proof. intros Hwf var1 var2; eapply wf_of_wf3 with (G:=nil), Hwf. Qed.
    End wf_properties.
    Global Hint Resolve Wf_of_Wf3 : wf.

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

    Section invert.
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
              {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}
              {buildInvertIdentCorrect : BuildInvertIdentCorrectT}.
      Section with_var2.
        Context {var1 var2 : type -> Type}.
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).

        Lemma wf_reify_list G {t} e1 e2
          : @wf _ _ var1 var2 G _ (reify_list (t:=t) e1) (reify_list (t:=t) e2)
            <-> List.Forall2 (wf G) e1 e2.
        Proof using reflect_base_beq.
          revert e2; induction e1 as [|e1 e1s IHe1s], e2 as [|e2 e2s];
            rewrite ?expr.reify_list_cons, ?expr.reify_list_nil;
            repeat first [ progress apply conj
                         | progress intros
                         | progress destruct_head'_and
                         | progress destruct_head'_sig
                         | progress inversion_type
                         | congruence
                         | tauto
                         | progress cbn [In] in *
                         | match goal with |- wf _ _ _ => constructor end
                         | progress inversion_wf_constr
                         | rewrite IHe1s in *
                         | progress destruct_head'_or
                         | match goal with
                           | [ H : Forall2 _ ?xs ?ys |- _ ]
                             => match xs with nil => idtac | _::_ => idtac end;
                                match ys with nil => idtac | _::_ => idtac end;
                                inversion H; clear H
                           end
                         | solve [ eauto ] ].
        Qed.

        Lemma wf_reflect_list G {t} e1 e2
           : @wf _ _ var1 var2 G (type.base (base.type.list t)) e1 e2
            -> (invert_expr.reflect_list e1 = None <-> invert_expr.reflect_list e2 = None).
        Proof using buildInvertIdentCorrect try_make_transport_base_cps_correct.
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
          all: repeat first [ progress cbn [fst snd projT1 projT2 eq_rect] in *
                            | progress destruct_head'_False
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress inversion_prod
                            | discriminate
                            | progress destruct_head'_sig
                            | progress destruct_head'_and
                            | progress expr.invert_subst
                            | progress inversion_wf_constr
                            | solve [ eauto ]
                            | progress inversion_type
                            | break_innermost_match_hyps_step
                            | progress expr.invert_match
                            | progress expr.inversion_expr
                            | progress inversion_wf_one_constr ].
        Qed.

        Lemma wf_reify_option G {t} e1 e2
          : @wf _ _ var1 var2 G _ (reify_option (t:=t) e1) (reify_option (t:=t) e2)
            <-> option_eq (wf G) e1 e2.
        Proof using reflect_base_beq.
          destruct_head' option; cbn in *; split; intros.
          all: repeat first [ assumption
                            | progress inversion_option
                            | exfalso; assumption
                            | progress inversion_wf_constr
                            | progress destruct_head'_sig
                            | progress destruct_head'_and
                            | progress inversion_type
                            | constructor ].
        Qed.

        Lemma wf_reflect_option G {t} e1 e2
           : @wf _ _ var1 var2 G (type.base (base.type.option t)) e1 e2
            -> (invert_expr.reflect_option e1 = None <-> invert_expr.reflect_option e2 = None).
        Proof using buildInvertIdentCorrect try_make_transport_base_cps_correct.
          destruct (invert_expr.reflect_option e1) eqn:H1, (invert_expr.reflect_option e2) eqn:H2;
            try (split; congruence); expr.invert_subst;
              try (revert dependent e2; intro); try (revert dependent e1; intro);
                match goal with
                | [ |- context[Some ?l = None] ]
                  => destruct l
                end;
                rewrite ?expr.reify_option_Some, ?expr.reify_option_None;
                cbv [invert_expr.reflect_option];
                break_innermost_match; try congruence; intros.
          all: repeat first [ congruence
                            | progress inversion_wf_constr
                            | progress subst
                            | progress cbv [option_map] in *
                            | progress cbn [fst snd projT1 projT2 eq_rect] in *
                            | progress destruct_head' False
                            | progress destruct_head'_sig
                            | progress destruct_head'_and
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress inversion_prod
                            | progress inversion_type
                            | progress break_match_hyps
                            | progress expr.invert_subst
                            | solve [ eauto ]
                            | progress inversion_wf_one_constr
                            | progress expr.invert_match
                            | progress expr.inversion_expr ].
        Qed.

        Lemma wf_smart_Literal {t v G}
          : expr.wf G (ident.smart_Literal (var:=var1) (t:=t) v) (ident.smart_Literal (var:=var2) (t:=t) v).
        Proof using reflect_base_beq.
          induction t; cbn; cbv [option_map]; break_innermost_match; repeat constructor; auto; [].
          rewrite wf_reify_list, Forall2_map_map_iff, Forall2_Forall, Forall_forall; cbv [Proper]; auto.
        Qed.

        Lemma wf_reify {t} v G : expr.wf G (GallinaReify.base.reify (var:=var1) (t:=t) v) (GallinaReify.base.reify (var:=var2) (t:=t) v).
        Proof using reflect_base_beq. exact wf_smart_Literal. Qed.

        Lemma wf_smart_Literal_eq {t v1 v2 G}
          : v1 = v2 -> expr.wf G (ident.smart_Literal (var:=var1) (t:=t) v1) (ident.smart_Literal (var:=var2) (t:=t) v2).
        Proof using reflect_base_beq. intro; subst; apply wf_smart_Literal. Qed.
      End with_var2.

      Lemma Wf_Reify_as {t} v : expr.Wf (GallinaReify.base.Reify_as t v).
      Proof. repeat intro; apply wf_reify. Qed.

      Lemma Wf_reify {t} v : expr.Wf (fun var => GallinaReify.base.reify (t:=t) v).
      Proof. repeat intro; apply wf_reify. Qed.

      Section interp.
        Context {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}.
        Context {buildInterpIdentCorrect : ident.BuildInterpIdentCorrectT ident_interp}.

        Local Notation interp := (expr.interp ident_interp).
        Local Notation expr_interp_related := (@expr.interp_related _ _ _ (@ident_interp)).

        Lemma interp_reify_list {t} ls : interp (reify_list (t:=t) ls) = List.map interp ls.
        Proof using buildInterpIdentCorrect.
          cbv [reify_list]; induction ls as [|l ls IHls];
            cbn [list_rect map expr.interp];
            [ now rewrite ident.interp_ident_nil
            | now rewrite ident.interp_ident_cons, IHls ].
        Qed.

        Lemma interp_reify_option {t} v : interp (reify_option (t:=t) v) = Option.map interp v.
        Proof using buildInterpIdentCorrect.
          destruct v;
            rewrite ?expr.reify_option_None, ?expr.reify_option_Some; cbn [expr.interp];
              now (rewrite ident.interp_ident_None + rewrite ident.interp_ident_Some).
        Qed.

        Lemma smart_Literal_interp_related {t} v
          : expr.interp_related (@ident_interp) (ident.smart_Literal (t:=t) v) v.
        Proof using buildInterpIdentCorrect.
          induction t;
            repeat first [ progress cbn [ident.smart_Literal expr.interp_related_gen type.related base.interp] in *
                         | progress cbv [reify_option option_map option_rect expr.interp_related] in *
                         | rewrite ident.interp_ident_Literal
                         | rewrite ident.interp_ident_pair
                         | rewrite ident.interp_ident_Some
                         | rewrite ident.interp_ident_None
                         | break_innermost_match_step
                         | reflexivity
                         | do 2 eexists; repeat apply conj; [ | | reflexivity ]
                         | solve [ eauto ]
                         | apply (proj2 expr.reify_list_interp_related_iff)
                         | rewrite Forall2_map_l_iff, Forall2_Forall, Forall_forall; cbv [Proper]; intros
                         | match goal with
                           | [ |- ?x = ?y :> unit ] => now destruct x, y
                           end ].
        Qed.

        Lemma interp_smart_Literal {t} v : interp (ident.smart_Literal (t:=t) v) = v.
        Proof using buildInterpIdentCorrect.
          pose proof (@smart_Literal_interp_related t v) as H.
          eapply eqv_of_interp_related in H; assumption.
        Qed.

        Lemma reify_interp_related {t} v
          : expr_interp_related (GallinaReify.base.reify (t:=t) v) v.
        Proof. apply smart_Literal_interp_related. Qed.

        Lemma interp_reify {t} v : interp (GallinaReify.base.reify (t:=t) v) = v.
        Proof.
          pose proof (@reify_interp_related t v) as H.
          eapply eqv_of_interp_related in H; assumption.
        Qed.

        Lemma interp_reify_as_interp {t} v1 v2
          : v1 == v2 -> interp (GallinaReify.reify_as_interp (t:=t) v1) == v2.
        Proof using buildInterpIdentCorrect.
          induction t as [|s IHs d IHd]; cbn [GallinaReify.reify_as_interp type.related interp]; cbv [respectful]; eauto.
          intro; subst; apply interp_reify.
        Qed.

        Lemma Reify_as_interp_related {t} v
          : expr_interp_related (GallinaReify.base.Reify_as t v _) v.
        Proof. apply reify_interp_related. Qed.

        Lemma Interp_Reify_as {t} v : expr.Interp ident_interp (GallinaReify.base.Reify_as t v) = v.
        Proof. apply interp_reify. Qed.

        Lemma Interp_reify {t} v : expr.Interp ident_interp (fun var => GallinaReify.base.reify (t:=t) v) = v.
        Proof. apply interp_reify. Qed.
      End interp.
    End invert.

    (** [Reify] is a notation for [Reify_as] + better type inference, so we make [Wf_Reify] available for ease of memory / lookup *)
    Notation Wf_Reify := Wf_Reify_as.
    Notation Interp_Reify := Interp_Reify_as.
  End expr.

  Hint Constructors expr.wf : wf.
  Hint Resolve @expr.Wf_APP expr.Wf_Reify expr.Wf_reify : wf.
  Hint Rewrite @expr.Interp_Reify @expr.interp_reify @expr.interp_reify_list @expr.interp_reify_option @expr.Interp_reify @expr.Interp_APP : interp.

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
            | [ H : ?x = Some _, H' : ?x = Some _ |- _ ]
              => lazymatch x with
                 | Some _ => fail
                 | _ => rewrite H in H'
                 end
            end ].

  Local Ltac destructure_destruct_step :=
    first [ progress destruct_head'_or
          | break_innermost_match_hyps_step
          | break_innermost_match_step
          | match goal with
            | [ H : None = option_map _ _ |- _ ] => cbv [option_map] in H
            | [ H : Some _ = option_map _ _ |- _ ] => cbv [option_map] in H
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
            end
          | match goal with
            | [ |- _ \/ _ ] => constructor; solve [ repeat wf_safe_t_step ]
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
          | progress cbn [List.In eq_rect expr.interp (*ident.interp*) type.interp base.interp (*base.base_interp*) type.eqv] in *
          | progress cbv [respectful LetIn.Let_In] in *
          | solve [ eauto using conj, eq_refl, or_introl, or_intror with nocore ]
          | progress destruct_head'_or
          | match goal with
            (*| [ |- ident.interp ?x == ident.interp ?x ] => apply ident.eqv_Reflexive*)
            (*| [ |- Proper (fun x y => ident.interp x == ident.interp y) _ ] => apply ident.eqv_Reflexive_Proper*)
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


  Module DefaultValue.
    Import Language.Compilers.DefaultValue.
    Module expr.
      Class ExprDefault_wfT {base_type ident} {d : forall var, @type.base.DefaultT _ (@expr base_type ident var)}
        := ExprDefault_wf : forall var1 var2 G t, expr.wf G (d var1 t) (d var2 t).
      Class ExprDefault_WfT {base_type ident} {d : @type.base.DefaultT _ (@Expr base_type ident)}
        := ExprDefault_Wf : forall t, expr.Wf (d t).
      Global Arguments ExprDefault_wfT {_ _} _.
      Global Arguments ExprDefault_WfT {_ _} _.
      Module base.
        Section with_base.
          Context {base : Type}
                  {base_interp : base -> Type}.
          Local Notation base_type := (@base.type base).
          Local Notation type := (@type.type base_type).
          Local Notation base_type_interp := (@base.interp base base_interp).
          Context {ident : type -> Type}.
          Context {baseDefault : @type.base.DefaultT base base_interp}
                  {buildIdent : @ident.BuildIdentT base base_interp ident}.

          Section with_var2.
            Context {var1 var2 : type -> Type}.

            Lemma wf_default G {t : base_type} : expr.wf (var1:=var1) (var2:=var2) (t:=type.base t) G expr.base.default expr.base.default.
            Proof.
              induction t; wf_t.
            Qed.
          End with_var2.

          Lemma Wf_Default {t : base_type} : Wf (t:=type.base t) expr.base.Default.
          Proof. repeat intro; apply @wf_default. Qed.
        End with_base.
      End base.

      Section with_base.
        Context {base : Type}
                {base_interp : base -> Type}.
        Local Notation base_type := (@base.type base).
        Local Notation type := (@type.type base_type).
        Local Notation base_type_interp := (@base.interp base base_interp).
        Context {ident : type -> Type}.
        Context {baseDefault : @type.base.DefaultT base base_interp}
                {buildIdent : @ident.BuildIdentT base base_interp ident}.

        Global Instance wf_default : @ExprDefault_wfT base_type ident _.
        Proof. intros var1 var2 G t; revert G; induction t; intros; wf_t; apply base.wf_default. Qed.
        Global Instance Wf_Default : @ExprDefault_WfT base_type ident _.
        Proof. repeat intro; apply @wf_default. Qed.
      End with_base.
    End expr.
  End DefaultValue.

  Module GeneralizeVar.
    Import Language.Compilers.GeneralizeVar.
    Local Open Scope etype_scope.
    Module Flat.
      Section with_base_type.
        Context {base_type : Type}
                {ident : type base_type -> Type}
                {base_type_beq : base_type -> base_type -> bool}.
        Local Notation type := (@type.type base_type).

        Fixpoint wf (G : PositiveMap.t type) {t} (e : @Flat.expr base_type ident t) : bool
          := match e with
             | Flat.Ident t idc => true
             | Flat.Var t n
               => match PositiveMap.find n G with
                  | Some t' => type.type_beq _ base_type_beq t t'
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
      End with_base_type.
    End Flat.

    Section with_base_type.
      Context {base_type : Type}
              {ident : type base_type -> Type}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
              {base_type_beq : base_type -> base_type -> bool}
              {reflect_base_type_beq : reflect_rel (@eq base_type) base_type_beq}
              {try_make_transport_base_type_cps_correct : @type.try_make_transport_cps_correctT base_type base_type_beq _ _}.
      Local Notation type := (@type.type base_type).
      Local Notation Flat_expr := (@Flat.expr base_type ident).
      Context {exprDefault : forall var, @DefaultValue.type.base.DefaultT type (@expr base_type ident var)}
              {wf_exprDefault : DefaultValue.expr.ExprDefault_wfT exprDefault}.

      Section with_var.
        Import BinPos.
        Context {var1 var2 : type -> Type}.

        Lemma wf_from_flat_gen
              {t}
              (e : Flat_expr t)
          : forall (G1 : PositiveMap.t type) (G2 : list { t : _ & var1 t * var2 t }%type)
                   (ctx1 : PositiveMap.t { t : type & var1 t })
                   (ctx2 : PositiveMap.t { t : type & var2 t })
                   (H_G1_ctx1 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx1))
                   (H_G1_ctx2 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx2))
                   (H_ctx_G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G2
                                               <-> (exists p, PositiveMap.find p ctx1 = Some (existT _ t v1) /\ PositiveMap.find p ctx2 = Some (existT _ t v2))),
            Flat.wf (base_type_beq:=base_type_beq) G1 e = true -> expr.wf G2 (from_flat e var1 ctx1) (from_flat e var2 ctx2).
        Proof using try_make_transport_base_type_cps_correct.
          induction e;
            repeat first [ progress cbn [Flat.wf from_flat option_map projT1 projT2 List.In fst snd] in *
                         | progress intros
                         | destructure_step
                         | progress cbv [Option.bind cpsreturn cpsbind cpscall cps_option_bind eq_rect id] in *
                         | match goal with |- expr.wf _ _ _ => constructor end
                         | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                         | congruence
                         | destructure_split_step
                         | progress rewrite_type_transport_correct
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
              (e : Flat_expr t)
          : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) e = true -> expr.wf nil (from_flat e var1 (PositiveMap.empty _)) (from_flat e var2 (PositiveMap.empty _)).
        Proof using try_make_transport_base_type_cps_correct.
          apply wf_from_flat_gen; intros *;
            repeat setoid_rewrite PositiveMap.gempty;
            cbn [In option_map];
            intuition (destruct_head'_ex; intuition (congruence || auto)).
        Qed.

        Lemma wf_from_flat_to_flat_gen
              offset G1 G2 ctx
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf G1 e1 e2)
              (HG1G2 : forall t v1 v2,
                  List.In (existT _ t (v1, v2)) G1
                  -> exists v1', PositiveMap.find v1 ctx = Some (existT _ t v1')
                                 /\ List.In (existT _ t (v1', v2)) G2)
              (Hoffset : forall p, PositiveMap.find p ctx <> None -> (p < offset)%positive)
          : expr.wf G2 (var2:=var2) (from_flat (to_flat' (t:=t) e1 offset) var1 ctx) e2.
        Proof.
          revert dependent offset; revert dependent G2; revert dependent ctx; induction Hwf; intros.
          all: repeat first [ progress cbn [from_flat to_flat' List.In projT1 projT2 fst snd] in *
                            | progress intros
                            | destructure_step
                            | progress cbv [Option.bind cpsreturn cpsbind cpscall cps_option_bind eq_rect id] in *
                            | match goal with |- expr.wf _ _ _ => constructor end
                            | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                            | congruence
                            | destructure_split_step
                            | progress rewrite_type_transport_correct
                            | match goal with
                              | [ H : List.In (existT _ ?t (?v1, ?v2)) ?G, H' : forall t' v1' v2', List.In _ ?G -> _ |- _ ]
                                => specialize (H' _ _ _ H)
                              | [ H : _ |- expr.wf _ _ _ ] => apply H; clear H
                              | [ v' : var1 ?t |- exists v : var1 ?t, _ ] => exists v'
                              | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ] => rewrite PositiveMapAdditionalFacts.gsspec
                              | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _ ] => rewrite PositiveMapAdditionalFacts.gsspec in H
                              | [ H : forall p, _ <> None -> (_ < _)%positive, H' : _ <> None |- _ ]
                                => unique pose proof (H _ H')
                              | [ H : forall p, PositiveMap.find p ?ctx <> None -> (p < ?offset)%positive,
                                    H' : PositiveMap.find ?p' ?ctx = Some _ |- _]
                                => unique assert ((p' < offset)%positive) by (apply H; rewrite H'; congruence)
                              | [ H : (?x < ?x)%positive |- _ ] => exfalso; clear -H; lia
                              | [ |- (_ < _)%positive ] => lia
                              end ].
        Qed.

        Lemma wf_from_flat_to_flat
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
          : expr.wf nil (var2:=var2) (from_flat (to_flat (t:=t) e1) var1 (PositiveMap.empty _)) e2.
        Proof using try_make_transport_base_type_cps_correct.
          eapply wf_from_flat_to_flat_gen; eauto; cbn [List.In]; try tauto; intros *;
            rewrite PositiveMap.gempty; congruence.
        Qed.
      End with_var.

      Section with_var3.
        Context {var1 var2 var3 : type -> Type}.

        Lemma wf3_from_flat_gen
              {t}
              (e : Flat_expr t)
          : forall (G1 : PositiveMap.t type) (G2 : list { t : _ & var1 t * var2 t * var3 t }%type)
                   (ctx1 : PositiveMap.t { t : type & var1 t })
                   (ctx2 : PositiveMap.t { t : type & var2 t })
                   (ctx3 : PositiveMap.t { t : type & var3 t })
                   (H_G1_ctx1 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx1))
                   (H_G1_ctx2 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx2))
                   (H_G1_ctx3 : forall p, PositiveMap.find p G1 = option_map (@projT1 _ _) (PositiveMap.find p ctx3))
                   (H_ctx_G2 : forall t v1 v2 v3, List.In (existT _ t (v1, v2, v3)) G2
                                                  <-> (exists p, PositiveMap.find p ctx1 = Some (existT _ t v1) /\ PositiveMap.find p ctx2 = Some (existT _ t v2) /\ PositiveMap.find p ctx3 = Some (existT _ t v3))),
            Flat.wf (base_type_beq:=base_type_beq) G1 e = true -> expr.wf3 G2 (from_flat e var1 ctx1) (from_flat e var2 ctx2) (from_flat e var3 ctx3).
        Proof using try_make_transport_base_type_cps_correct.
          induction e.
          all: repeat first [ progress cbn [Flat.wf from_flat option_map projT1 projT2 List.In fst snd] in *
                            | progress intros
                            | discriminate
                            | match goal with
                              | [ |- expr.wf3 _ _ _ _ ] => constructor
                              | [ H : match ?x with Some _ => false | _ => _ end = true |- _ ]
                                => destruct x eqn:?
                              | [ H : match ?x with None => false | _ => _ end = true |- _ ]
                                => destruct x eqn:?
                              | [ H : andb _ _ = true |- _ ] => rewrite Bool.andb_true_iff in H; destruct H
                              end
                            | progress specialize_by_assumption
                            | assumption
                            | progress inversion_option
                            | match goal with
                              | [ H : ?x = ?y |- _ ]
                                => is_var y;
                                   match goal with
                                   | [ H' : context[rew H in _] |- _ ] => idtac
                                   | [ H' : context[rew <- H in _] |- _ ] => idtac
                                   | [ |- context[rew H in _] ] => idtac
                                   | [ |- context[rew <- H in _] ] => idtac
                                   end;
                                   destruct H
                              end
                            | progress subst
                            | reflexivity
                            | progress cbn [Option.bind projT1 projT2 eq_rect] in *
                            | match goal with
                              | [ IH : forall G : PositiveMap.t type, _ |- _ ]
                                => match goal with
                                   | [ H' : Flat.wf ?G ?e = true |- _ ]
                                     => lazymatch type of IH with
                                        | context[e] => specialize (IH G)
                                        end
                                   end
                              | [ IH : forall G : list ?T, _ |- _ ]
                                => lazymatch goal with
                                   | [ |- context[@cons T ?x ?xs] ] => specialize (IH (x :: xs))
                                   | [ ls : list T |- _ ] => specialize (IH ls)
                                   end
                              | [ IH : forall G : PositiveMap.t ?T, _ |- _ ]
                                => lazymatch goal with
                                   | [ |- context[@PositiveMap.add T ?n ?t ?Gv] ]
                                     => specialize (IH (PositiveMap.add n t Gv))
                                   | [ G : PositiveMap.t T |- _ ]
                                     => specialize (IH G)
                                   end
                              | [ IH : (forall p, PositiveMap.find p (PositiveMap.add _ _ _) = option_map _ (PositiveMap.find p (PositiveMap.add _ _ ?ctx))) -> _,
                                       H : forall p', PositiveMap.find p' _ = option_map _ (PositiveMap.find p' ?ctx) |- _ ]
                                => let T := match type of IH with (?A -> _)%type => A end in
                                   let H' := fresh in
                                   cut T; [ intro H'; specialize (IH H'); clear H'
                                          | clear -H reflect_base_type_beq; do 1 (let x := fresh "x" in intro x; specialize (H x)) ]
                              | [ IH : (forall p, PositiveMap.find p _ = option_map _ (PositiveMap.find p ?ctx)) -> _,
                                       H : forall p', PositiveMap.find p' _ = option_map _ (PositiveMap.find p' ?ctx) |- _ ]
                                => let T := match type of IH with (?A -> _)%type => A end in
                                   let H' := fresh in
                                   cut T; [ intro H'; specialize (IH H'); clear H'
                                          | clear -H reflect_base_type_beq; do 1 (let x := fresh "x" in intro x; specialize (H x)) ]
                              | [ IH : (forall t v1 v2 v3, _ <-> _) -> _, H : forall t' v1' v2' v3', _ <-> _ |- _ ]
                                => let T := match type of IH with (?A -> _)%type => A end in
                                   let H' := fresh in
                                   cut T; [ intro H'; specialize (IH H'); clear H'
                                          | (*clear -H reflect_base_type_beq;*) do 4 (let x := fresh "x" in intro x; specialize (H x)) ]
                              end
                            | progress cbn [List.In] in *
                            | match goal with
                              | [ H : ?A <-> _ |- (_ \/ ?A) <-> _ ] => rewrite H; clear H
                              | [ |- context[PositiveMap.find _ (PositiveMap.add _ _ _)] ]
                                => rewrite !PositiveMapAdditionalFacts.gsspec || setoid_rewrite PositiveMapAdditionalFacts.gsspec
                              | [ H : _ |- _ ] => eapply H; eassumption
                              end
                            | progress destruct_head'_and
                            | progress destruct_head'_sigT
                            | match goal with
                              | [ H : forall p, PositiveMap.find p ?G = _, H' : PositiveMap.find ?pv ?G = _ |- _ ]
                                => specialize (H pv); rewrite H' in H
                              | [ H : Some _ = option_map _ ?x |- _ ] => destruct x eqn:?; cbn [option_map] in H
                              end
                            | progress rewrite_type_transport_correct
                            | progress break_match_when_head (@sumbool)
                            | progress type_beq_to_eq
                            | match goal with
                              | [ H : forall t v1 v2 v3, In _ ?G <-> ex _ |- In _ ?G ]
                                => rewrite H; clear H; try solve [ repeat esplit; eassumption ]
                              end
                            | repeat apply conj; (reflexivity || assumption)
                            | match goal with
                              | [ |- (_ = _ \/ ex _) <-> (exists p, (if ?dec p ?n then _ else _) = _ /\ _ /\ _) ]
                                => let H := fresh in
                                   let p := fresh "p" in
                                   split; intro H;
                                   [ destruct H as [ | [p H] ];
                                     [ exists n; destruct (dec n n) | exists p; destruct (dec p n) ];
                                     repeat first [ congruence
                                                  | progress subst
                                                  | progress inversion_sigma
                                                  | progress inversion_prod
                                                  | progress cbn [eq_rect fst snd] in * ]
                                   | destruct H as [p H];
                                     destruct (dec p n); [ left | right; exists p ];
                                     repeat first [ progress inversion_option
                                                  | progress inversion_sigma
                                                  | progress subst
                                                  | progress eliminate_hprop_eq
                                                  | reflexivity
                                                  | assumption
                                                  | progress destruct_head'_and ] ]
                              | [ H : None = option_map _ ?x |- _ ] => destruct x eqn:?; cbn [option_map] in H
                              end ].
        Qed.

        Lemma wf3_from_flat
              {t}
              (e : Flat_expr t)
          : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) e = true -> expr.wf3 nil (from_flat e var1 (PositiveMap.empty _)) (from_flat e var2 (PositiveMap.empty _)) (from_flat e var3 (PositiveMap.empty _)).
        Proof using try_make_transport_base_type_cps_correct.
          apply wf3_from_flat_gen; intros *;
            repeat setoid_rewrite PositiveMap.gempty;
            cbn [In option_map];
            intuition (destruct_head'_ex; intuition (congruence || auto)).
        Qed.
      End with_var3.

      Lemma Wf_FromFlat {t} (e : Flat_expr t) : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) e = true -> expr.Wf (FromFlat e).
      Proof. intros H ??; apply wf_from_flat, H. Qed.

      Lemma Wf3_FromFlat {t} (e : Flat_expr t) : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) e = true -> expr.Wf3 (FromFlat e).
      Proof. intros H ???; apply wf3_from_flat, H. Qed.

      Lemma Wf_via_flat {t} (e : Expr t)
        : (e = GeneralizeVar (e _) /\ Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (to_flat (e _)) = true)
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
          Flat.wf (ident:=ident) (base_type_beq:=base_type_beq) ctx1 (to_flat' e1 cur_idx1) = true
          /\ Flat.wf (base_type_beq:=base_type_beq) ctx2 (to_flat' e2 cur_idx2) = true.
      Proof using try_make_transport_base_type_cps_correct.
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
                         | [ H : BinPos.Pos.lt ?x ?y |- BinPos.Pos.lt ?x (Pos.succ ?y) ] => clear -H; lia
                         | [ |- BinPos.Pos.lt _ _ ] => progress saturate_pos
                         end
                       | match goal with
                         | [ H : ?x = Some _ |- context[?x] ] => rewrite H
                         | [ H : ?x = None |- context[?x] ] => rewrite H
                         | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : In _ ?G2, H' : forall t v1 v2, In _ ?G2 -> _ |- _ ] => apply H' in H
                         | [ H : match ?x with Some _ => true | None => false end = true |- _ ]
                           => destruct x eqn:?; try discriminate
                         | [ H : match ?x with Some _ => false | None => true end = true |- _ ]
                           => destruct x eqn:?; try discriminate
                         | [ H : context[PositiveMap.E.eq_dec ?x ?y] |- (?x < Pos.succ ?y)%positive ]
                           => destruct (PositiveMap.E.eq_dec x y); [ subst; clear; lia | ]
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
        : expr.wf (ident:=ident) nil e1 e2 -> Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (to_flat e1) = true /\ Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (to_flat e2) = true.
      Proof using try_make_transport_base_type_cps_correct.
        intro; apply wf_to_flat'_gen with (G:=nil); eauto; intros *; cbn [In];
          rewrite ?PositiveMap.mem_find, ?PositiveMap.gempty; intuition congruence.
      Qed.

      Lemma Wf_ToFlat {t} (e : Expr (ident:=ident) t) (Hwf : expr.Wf e) : Flat.wf (base_type_beq:=base_type_beq) (PositiveMap.empty _) (ToFlat e) = true.
      Proof. eapply wf_to_flat, Hwf. Qed.

      Lemma Wf_FromFlat_to_flat {t} (e : expr t) : expr.wf (ident:=ident) nil e e -> expr.Wf (FromFlat (to_flat e)).
      Proof. intro Hwf; eapply Wf_FromFlat, wf_to_flat, Hwf. Qed.
      Lemma Wf_FromFlat_ToFlat {t} (e : Expr t) : expr.Wf (ident:=ident) e -> expr.Wf (FromFlat (ToFlat e)).
      Proof. intro H; apply Wf_FromFlat_to_flat, H. Qed.
      Lemma Wf_GeneralizeVar {t} (e : Expr t) : expr.Wf (ident:=ident) e -> expr.Wf (GeneralizeVar (e _)).
      Proof. apply Wf_FromFlat_ToFlat. Qed.

      Lemma Wf3_FromFlat_to_flat {t} (e : expr t) : expr.wf (ident:=ident) nil e e -> expr.Wf3 (FromFlat (to_flat e)).
      Proof. intro Hwf; eapply Wf3_FromFlat, wf_to_flat, Hwf. Qed.
      Lemma Wf3_FromFlat_ToFlat {t} (e : Expr t) : expr.Wf (ident:=ident) e -> expr.Wf3 (FromFlat (ToFlat e)).
      Proof. intro H; apply Wf3_FromFlat_to_flat, H. Qed.
      Lemma Wf3_GeneralizeVar {t} (e : Expr t) : expr.Wf (ident:=ident) e -> expr.Wf3 (GeneralizeVar (e _)).
      Proof. apply Wf3_FromFlat_ToFlat. Qed.

      Local Ltac t :=
        repeat first [ reflexivity
                     | progress saturate_pos
                     | progress cbn [from_flat to_flat' projT1 projT2 fst snd eq_rect expr.interp List.In type.eqv] in *
                     | progress fold @type.interp
                     | progress cbv [Option.bind LetIn.Let_In respectful] in *
                     | destructure_step
                     | progress rewrite_type_transport_correct
                     | progress intros
                     | congruence
                     | solve [ eauto using conj, ex_intro, eq_refl, or_introl, or_intror with nocore ]
                     | progress cbn [type.app_curried type.for_each_lhs_of_arrow] in *
                     | destructure_split_step
                     | match goal with
                       (*| [ |- ident.interp _ == ident.interp _ ] => apply ident.eqv_Reflexive*)
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
        Context {base_interp : base_type -> Type}
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
        Proof using try_make_transport_base_type_cps_correct ident_interp_Proper.
          setoid_rewrite PositiveMap.mem_find in Hidx.
          revert dependent cur_idx; revert dependent ctx; induction Hwf; intros;
            t.
        Qed.

        Lemma Interp_gen2_FromFlat_ToFlat {t} (e : Expr t) (Hwf : expr.Wf e)
          : type.related R (expr.Interp ident_interp1 (FromFlat (ToFlat e))) (expr.Interp ident_interp2 e).
        Proof using try_make_transport_base_type_cps_correct ident_interp_Proper.
          cbv [expr.Interp FromFlat ToFlat to_flat].
          apply interp_gen2_from_flat_to_flat' with (G:=nil); eauto; intros *; cbn [List.In]; rewrite ?PositiveMap.mem_find, ?PositiveMap.gempty;
            intuition congruence.
        Qed.

        Lemma Interp_gen2_GeneralizeVar {t} (e : Expr t) (Hwf : expr.Wf e)
          : type.related R (expr.Interp ident_interp1 (GeneralizeVar (e _))) (expr.Interp ident_interp2 e).
        Proof. apply Interp_gen2_FromFlat_ToFlat, Hwf. Qed.
      End gen2.
      Section gen1.
        Context {base_interp : base_type -> Type}
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
    End with_base_type.
  End GeneralizeVar.

  Ltac prove_Wf_with extra_tac :=
    lazymatch goal with
    | [ |- @expr.Wf ?base_type ?ident ?t ?e ]
      => refine (@GeneralizeVar.Wf_via_flat base_type ident _ _ _ _ _ t e _);
         [ solve [ assumption | auto with nocore | typeclasses eauto | extra_tac ()
                   | let G := match goal with |- ?G => G end in
                     fail 1 "Could not automatically solve" G ]..
         | vm_cast_no_check (conj (eq_refl e) (eq_refl true)) ]
    end.

  Ltac prove_Wf _ := prove_Wf_with ltac:(fun _ => idtac).

  Global Hint Extern 0 (?x == ?x) => apply expr.Wf_Interp_Proper_gen : wf interp.
  Hint Resolve GeneralizeVar.Wf_FromFlat_ToFlat GeneralizeVar.Wf_GeneralizeVar : wf.
  Hint Resolve GeneralizeVar.Wf3_FromFlat_ToFlat GeneralizeVar.Wf3_GeneralizeVar : wf.
  Hint Rewrite @GeneralizeVar.Interp_gen1_GeneralizeVar @GeneralizeVar.Interp_gen1_FromFlat_ToFlat : interp.
End Compilers.
