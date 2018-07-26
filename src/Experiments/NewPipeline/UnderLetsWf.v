Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLets.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Import ListNotations. Local Open Scope list_scope.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLets.Compilers.
  Import expr.Notations.
  Import invert_expr.

  Module SubstVarLike.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Section with_var.
        Context {var1 var2 : type -> Type}.
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Section with_var_like.
          Context (is_var_like1 : forall t, @expr var1 t -> bool)
                  (is_var_like2 : forall t, @expr var2 t -> bool).
          Local Notation subst_var_like1 := (@SubstVarLike.subst_var_like base_type ident var1 is_var_like1).
          Local Notation subst_var_like2 := (@SubstVarLike.subst_var_like base_type ident var2 is_var_like2).
          Definition is_var_like_wfT := forall G t e1 e2, expr.wf G (t:=t) e1 e2 -> is_var_like1 t e1 = is_var_like2 t e2.
          Context (is_var_like_good : is_var_like_wfT).

          Lemma wf_subst_var_like G1 G2 t e1 e2
                (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> expr.wf G2 v1 v2)
            : expr.wf G1 (t:=t) e1 e2 -> expr.wf G2 (subst_var_like1 e1) (subst_var_like2 e2).
          Proof.
            cbv [is_var_like_wfT] in *.
            intro Hwf; revert dependent G2; induction Hwf;
              cbn [SubstVarLike.subst_var_like];
              repeat first [ match goal with
                             | [ H : is_var_like1 _ ?x = _, H' : is_var_like2 _ ?y = _ |- _ ]
                               => assert (is_var_like1 _ x = is_var_like2 _ y) by eauto; congruence
                             end
                           | progress wf_safe_t
                           | progress break_innermost_match
                           | solve [ wf_t ] ].
          Qed.
        End with_var_like.

        Section with_ident_like.
          Context (ident_is_good : forall t, ident t -> bool).

          Lemma wfT_is_recursively_var_or_ident
            : is_var_like_wfT (fun t => SubstVarLike.is_recursively_var_or_ident ident_is_good)
                              (fun t => SubstVarLike.is_recursively_var_or_ident ident_is_good).
          Proof.
            intros G t e1 e2 Hwf; induction Hwf; cbn [SubstVarLike.is_recursively_var_or_ident];
              congruence.
          Qed.
        End with_ident_like.

        Lemma wfT_is_var
          : is_var_like_wfT (fun _ e => match invert_Var e with Some _ => true | None => false end)
                            (fun _ e => match invert_Var e with Some _ => true | None => false end).
        Proof. intros G t e1 e2 Hwf; destruct Hwf; cbn [invert_Var]; reflexivity. Qed.
      End with_var.

      Local Notation SubstVarLike := (@SubstVarLike.SubstVarLike base_type ident).
      Local Notation SubstVar := (@SubstVarLike.SubstVar base_type ident).
      Local Notation SubstVarOrIdent := (@SubstVarLike.SubstVarOrIdent base_type ident).

      Lemma Wf_SubstVarLike (is_var_like : forall var t, @expr var t -> bool)
            (is_var_like_good : forall var1 var2, is_var_like_wfT (is_var_like var1) (is_var_like var2))
            {t} (e : expr.Expr t)
        : expr.Wf e -> expr.Wf (SubstVarLike is_var_like e).
      Proof.
        intros Hwf var1 var2; eapply wf_subst_var_like; eauto with nocore; cbn [In]; tauto.
      Qed.

      Lemma Wf_SubstVar {t} (e : expr.Expr t)
        : expr.Wf e -> expr.Wf (SubstVar e).
      Proof.
        intros Hwf var1 var2; eapply wf_subst_var_like; eauto using wfT_is_var with nocore; cbn [In]; tauto.
      Qed.

      Lemma Wf_SubstVarOrIdent (should_subst_ident : forall t, ident t -> bool)
            {t} (e : expr.Expr t)
        : expr.Wf e -> expr.Wf (SubstVarOrIdent should_subst_ident e).
      Proof.
        intros Hwf var1 var2; eapply wf_subst_var_like; eauto using wfT_is_recursively_var_or_ident with nocore; cbn [In]; tauto.
      Qed.

      Section interp.
        Context {base_interp : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp base_interp t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.
        Section with_is_var_like.
          Context (is_var_like : forall t, @expr (type.interp base_interp) t -> bool).

          Lemma interp_subst_var_like_gen G t (e1 e2 : expr t)
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> expr.interp interp_ident v1 == v2)
                (Hwf : expr.wf G e1 e2)
            : expr.interp interp_ident (SubstVarLike.subst_var_like is_var_like e1) == expr.interp interp_ident e2.
          Proof.
            induction Hwf; cbn [SubstVarLike.subst_var_like]; cbv [Proper respectful] in *;
              interp_safe_t; break_innermost_match; interp_safe_t.
          Qed.

          Lemma interp_subst_var_like_gen_nil t (e1 e2 : expr t)
                (Hwf : expr.wf nil e1 e2)
            : expr.interp interp_ident (SubstVarLike.subst_var_like is_var_like e1) == expr.interp interp_ident e2.
          Proof. apply interp_subst_var_like_gen with (G:=nil); cbn [In]; eauto with nocore; tauto. Qed.
        End with_is_var_like.

        Lemma Interp_SubstVarLike (is_var_like : forall var t, @expr var t -> bool)
              {t} (e : expr.Expr t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (SubstVarLike is_var_like e) == expr.Interp interp_ident e.
        Proof. apply interp_subst_var_like_gen_nil, Hwf. Qed.

        Lemma Interp_SubstVar {t} (e : expr.Expr t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (SubstVar e) == expr.Interp interp_ident e.
        Proof. apply interp_subst_var_like_gen_nil, Hwf. Qed.

        Lemma Interp_SubstVarOrIdent (should_subst_ident : forall t, ident t -> bool)
              {t} (e : expr.Expr t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (SubstVarOrIdent should_subst_ident e) == expr.Interp interp_ident e.
        Proof. apply interp_subst_var_like_gen_nil, Hwf. Qed.
      End interp.
    End with_ident.

    Lemma Wf_SubstVarFstSndPairOpp {t} (e : expr.Expr t)
      : expr.Wf e -> expr.Wf (SubstVarLike.SubstVarFstSndPairOpp e).
    Proof. apply Wf_SubstVarOrIdent. Qed.

    Lemma Interp_SubstVarFstSndPairOpp {t} (e : expr.Expr t) (Hwf : expr.Wf e)
      : defaults.Interp (SubstVarLike.SubstVarFstSndPairOpp e) == defaults.Interp e.
    Proof. apply Interp_SubstVarOrIdent, Hwf. Qed.
  End SubstVarLike.

  (*
  Module UnderLets.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {var : type -> Type}.
      Local Notation expr := (@expr base_type ident var).

      Inductive UnderLets {T : Type} :=
      | Base (v : T)
      | UnderLet {A} (x : expr A) (f : var A -> UnderLets).

      Fixpoint splice {A B} (x : @UnderLets A) (e : A -> @UnderLets B) : @UnderLets B
        := match x with
           | Base v => e v
           | UnderLet A x f => UnderLet x (fun v => @splice _ _ (f v) e)
           end.

      Fixpoint splice_list {A B} (ls : list (@UnderLets A)) (e : list A -> @UnderLets B) : @UnderLets B
        := match ls with
           | nil => e nil
           | cons x xs
             => splice x (fun x => @splice_list A B xs (fun xs => e (cons x xs)))
           end.

      Fixpoint to_expr {t} (x : @UnderLets (expr t)) : expr t
        := match x with
           | Base v => v
           | UnderLet A x f
             => expr.LetIn x (fun v => @to_expr _ (f v))
           end.
      Fixpoint of_expr {t} (x : expr t) : @UnderLets (expr t)
        := match x in expr.expr t return @UnderLets (expr t) with
           | expr.LetIn A B x f
             => UnderLet x (fun v => @of_expr B (f v))
           | e => Base e
           end.
    End with_var.
    Module Export Notations.
      Global Arguments UnderLets : clear implicits.
      Delimit Scope under_lets_scope with under_lets.
      Bind Scope under_lets_scope with UnderLets.UnderLets.
      Notation "x <-- y ; f" := (UnderLets.splice y (fun x => f%under_lets)) : under_lets_scope.
      Notation "x <---- y ; f" := (UnderLets.splice_list y (fun x => f%under_lets)) : under_lets_scope.
    End Notations.

    Section reify.
      Context {var : type.type base.type -> Type}.
      Local Notation type := (type.type base.type).
      Local Notation expr := (@expr.expr base.type ident var).
      Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
      Let type_base (t : base.type) : type := type.base t.
      Coercion type_base : base.type >-> type.

      Let default_reify_and_let_binds_base_cps {t : base.type} : expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T
        := fun e T k
           => match invert_expr.invert_Var e with
              | Some v => k ($v)%expr
              | None => if SubstVarLike.is_var_fst_snd_pair_opp e
                        then k e
                        else UnderLets.UnderLet e (fun v => k ($v)%expr)
              end.

      Fixpoint reify_and_let_binds_base_cps {t : base.type} : expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T
        := match t return expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T with
           | base.type.type_base t
             => fun e T k
                => match invert_Literal e with
                   | Some v => k (expr.Ident (ident.Literal v))
                   | None => @default_reify_and_let_binds_base_cps _ e T k
                   end
           | base.type.prod A B
             => fun e T k
                => match invert_pair e with
                   | Some (a, b)
                     => @reify_and_let_binds_base_cps
                          A a _
                          (fun ae
                           => @reify_and_let_binds_base_cps
                                B b _
                                (fun be
                                 => k (ae, be)%expr))
                   | None => @default_reify_and_let_binds_base_cps _ e T k
                   end
           | base.type.list A
             => fun e T k
                => match reflect_list e with
                   | Some ls
                     => list_rect
                          _
                          (fun k => k []%expr)
                          (fun x _ rec k
                           => @reify_and_let_binds_base_cps
                                A x _
                                (fun xe
                                 => rec (fun xse => k (xe :: xse)%expr)))
                          ls
                          k
                   | None => @default_reify_and_let_binds_base_cps _ e T k
                   end
           end%under_lets.

      Fixpoint let_bind_return {t} : expr t -> expr t
        := match t return expr t -> expr t with
           | type.base t
             => fun e => to_expr (v <-- of_expr e; reify_and_let_binds_base_cps v _ Base)
           | type.arrow s d
             => fun e
                => expr.Abs (fun v => @let_bind_return
                                        d
                                        match invert_Abs e with
                                        | Some f => f v
                                        | None => e @ $v
                                        end%expr)
           end.
    End reify.
    Definition LetBindReturn {t} (e : expr.Expr t) : expr.Expr t
      := fun var => let_bind_return (e _).
  End UnderLets.
  Export UnderLets.Notations.
   *)
End Compilers.
