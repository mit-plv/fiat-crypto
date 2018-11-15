Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.MiscCompilerPasses.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope list_scope.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import MiscCompilerPasses.Compilers.
  Import expr.Notations.
  Import invert_expr.
  Import defaults.

  Module Subst01.
    Import MiscCompilerPasses.Compilers.Subst01.

    Local Ltac simplifier_t_step :=
      first [ progress cbn [fst snd] in *
            | progress eta_expand ].

    Section with_counter.
      Context {T : Type}
              (one : T)
              (incr : T -> T).

      Section with_ident.
        Context {base_type : Type}.
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}.
        Local Notation expr := (@expr.expr base_type ident).

        Section with_var.
          Context {doing_subst : forall T1 T2, T1 -> T2 -> T1}
                  {should_subst : T -> bool}
                  (Hdoing_subst : forall T1 T2 x y, doing_subst T1 T2 x y = x)
                  {var1 var2 : type -> Type}
                  (live : PositiveMap.t T).
          Local Notation expr1 := (@expr.expr base_type ident var1).
          Local Notation expr2 := (@expr.expr base_type ident var2).
          Local Notation subst0n'1 := (@subst0n' T base_type ident doing_subst var1 should_subst live).
          Local Notation subst0n'2 := (@subst0n' T base_type ident doing_subst var2 should_subst live).
          Local Notation subst0n1 := (@subst0n T base_type ident doing_subst var1 should_subst live).
          Local Notation subst0n2 := (@subst0n T base_type ident doing_subst var2 should_subst live).

          Lemma wf_subst0n' G1 G2 t e1 e2 p
                (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> expr.wf G2 v1 v2)
            : expr.wf G1 (t:=t) e1 e2 -> expr.wf G2 (snd (subst0n'1 e1 p)) (snd (subst0n'2 e2 p))
                                         /\ fst (subst0n'1 e1 p) = fst (subst0n'2 e2 p).
          Proof using Hdoing_subst.
            intro Hwf; revert dependent G2; revert p; induction Hwf;
              cbn [subst0n'];
              repeat first [ progress wf_safe_t
                           | simplifier_t_step
                           | progress split_and
                           | rewrite Hdoing_subst
                           | apply conj
                           | match goal with
                             | [ H : context[fst _ = fst _] |- _ ] => progress erewrite H by eauto
                             end
                           | break_innermost_match_step
                           | solve [ wf_t ] ].
          Qed.

          Lemma wf_subst0n t e1 e2
            : expr.wf nil (t:=t) e1 e2 -> expr.wf nil (subst0n1 e1) (subst0n2 e2).
          Proof using Hdoing_subst. clear -Hdoing_subst; intro Hwf; apply wf_subst0n' with (G1:=nil); cbn [In]; eauto with nocore; tauto. Qed.
        End with_var.

        Lemma Wf_Subst0n
              {doing_subst : forall T1 T2, T1 -> T2 -> T1}
              {should_subst : T -> bool}
              (Hdoing_subst : forall T1 T2 x y, doing_subst T1 T2 x y = x)
              {t} (e : @expr.Expr base_type ident t)
          : expr.Wf e -> expr.Wf (Subst0n one incr doing_subst should_subst e).
        Proof using Type. intros Hwf var1 var2; eapply wf_subst0n, Hwf; assumption. Qed.

        Section interp.
          Context {base_interp : base_type -> Type}
                  {interp_ident : forall t, ident t -> type.interp base_interp t}
                  {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

          Section with_doing_subst.
            Context {doing_subst : forall T1 T2, T1 -> T2 -> T1}
                    {should_subst : T -> bool}
                    (Hdoing_subst : forall T1 T2 x y, doing_subst T1 T2 x y = x).

            Lemma interp_subst0n'_gen (live : PositiveMap.t T) G t (e1 e2 : expr t)
                  (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> expr.interp interp_ident v1 == v2)
                  (Hwf : expr.wf G e1 e2)
                  p
              : expr.interp interp_ident (snd (subst0n' doing_subst should_subst live e1 p)) == expr.interp interp_ident e2.
            Proof using Hdoing_subst interp_ident_Proper.
              revert p; induction Hwf; cbn [subst0n']; cbv [Proper respectful] in *;
                repeat first [ progress interp_safe_t
                             | simplifier_t_step
                             | rewrite Hdoing_subst
                             | break_innermost_match_step
                             | interp_unsafe_t_step ].
            Qed.

            Lemma interp_subst0n live t (e1 e2 : expr t)
                  (Hwf : expr.wf nil e1 e2)
              : expr.interp interp_ident (subst0n doing_subst should_subst live e1) == expr.interp interp_ident e2.
            Proof using Hdoing_subst interp_ident_Proper. clear -Hwf Hdoing_subst interp_ident_Proper. apply interp_subst0n'_gen with (G:=nil); cbn [In]; eauto with nocore; tauto. Qed.

            Lemma Interp_Subst0n {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
              : expr.Interp interp_ident (Subst0n one incr doing_subst should_subst e) == expr.Interp interp_ident e.
            Proof using Hdoing_subst interp_ident_Proper. apply interp_subst0n, Hwf. Qed.
          End with_doing_subst.
        End interp.
      End with_ident.
    End with_counter.

    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Lemma Wf_Subst01 {t} (e : @expr.Expr base_type ident t)
        : expr.Wf e -> expr.Wf (Subst01 e).
      Proof using Type. eapply Wf_Subst0n; reflexivity. Qed.

      Section interp.
        Context {base_interp : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp base_interp t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.
        Lemma Interp_Subst01 {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (Subst01 e) == expr.Interp interp_ident e.
        Proof using interp_ident_Proper. apply Interp_Subst0n, Hwf; auto. Qed.
      End interp.
    End with_ident.
  End Subst01.

  Hint Resolve Subst01.Wf_Subst01 : wf.
  Hint Rewrite @Subst01.Interp_Subst01 : interp.

  Module DeadCodeElimination.
    Import MiscCompilerPasses.Compilers.DeadCodeElimination.

    (** Rather than proving correctness of the computation of live
            variables and requiring something about [live], we instead
            rely on the fact that DCE in fact just inlines code it
            believes to be dead. *)
    Local Transparent OUGHT_TO_BE_UNUSED.
    Lemma OUGHT_TO_BE_UNUSED_id {T1 T2} (v : T1) (v' : T2) : OUGHT_TO_BE_UNUSED v v' = v.
    Proof. exact eq_refl. Qed.
    Local Opaque OUGHT_TO_BE_UNUSED.

    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Lemma Wf_EliminateDead {t} (e : @expr.Expr base_type ident t)
        : expr.Wf e -> expr.Wf (EliminateDead e).
      Proof using Type. apply Subst01.Wf_Subst0n, @OUGHT_TO_BE_UNUSED_id. Qed.

      Section interp.
        Context {base_interp : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp base_interp t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

        Lemma Interp_EliminateDead {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (EliminateDead e) == expr.Interp interp_ident e.
        Proof using interp_ident_Proper. apply Subst01.Interp_Subst0n, Hwf; auto using @OUGHT_TO_BE_UNUSED_id. Qed.
      End interp.
    End with_ident.
  End DeadCodeElimination.

  Hint Resolve DeadCodeElimination.Wf_EliminateDead : wf.
  Hint Rewrite @DeadCodeElimination.Interp_EliminateDead : interp.
End Compilers.
