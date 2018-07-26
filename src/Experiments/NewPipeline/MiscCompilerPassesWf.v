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

(*


Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.
*)
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import MiscCompilerPasses.Compilers.
  Import expr.Notations.
  Import invert_expr.
  Import defaults.

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

    Local Ltac simplifier_t_step :=
      first [ progress cbn [fst snd] in *
            | progress eta_expand
            | rewrite OUGHT_TO_BE_UNUSED_id ].

    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Section with_var.
        Context {var1 var2 : type -> Type}
                (live : PositiveSet.t).
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation eliminate_dead'1 := (@eliminate_dead' base_type ident var1 live).
        Local Notation eliminate_dead'2 := (@eliminate_dead' base_type ident var2 live).
        Local Notation eliminate_dead1 := (@eliminate_dead base_type ident var1 live).
        Local Notation eliminate_dead2 := (@eliminate_dead base_type ident var2 live).

        Lemma wf_eliminate_dead' G1 G2 t e1 e2 p
              (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> expr.wf G2 v1 v2)
          : expr.wf G1 (t:=t) e1 e2 -> expr.wf G2 (snd (eliminate_dead'1 e1 p)) (snd (eliminate_dead'2 e2 p))
                                      /\ fst (eliminate_dead'1 e1 p) = fst (eliminate_dead'2 e2 p).
        Proof.
          intro Hwf; revert dependent G2; revert p; induction Hwf;
            cbn [eliminate_dead'];
            repeat first [ progress wf_safe_t
                         | simplifier_t_step
                         | progress split_and
                         | apply conj
                         | match goal with
                           | [ H : context[fst _ = fst _] |- _ ] => progress erewrite H by eauto
                           end
                         | break_innermost_match_step
                         | solve [ wf_t ] ].
        Qed.

        Lemma wf_eliminate_dead t e1 e2
          : expr.wf nil (t:=t) e1 e2 -> expr.wf nil (eliminate_dead1 e1) (eliminate_dead2 e2).
        Proof. intro Hwf; apply wf_eliminate_dead' with (G1:=nil); cbn [In]; eauto with nocore; tauto. Qed.
      End with_var.

      Lemma Wf_EliminateDead {t} (e : @expr.Expr base_type ident t)
        : expr.Wf e -> expr.Wf (EliminateDead e).
      Proof. intros Hwf var1 var2; eapply wf_eliminate_dead, Hwf. Qed.

      Section interp.
        Context {base_interp : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp base_interp t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

        Lemma interp_eliminate_dead'_gen (live : PositiveSet.t) G t (e1 e2 : expr t)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> expr.interp interp_ident v1 == v2)
              (Hwf : expr.wf G e1 e2)
              p
          : expr.interp interp_ident (snd (eliminate_dead' live e1 p)) == expr.interp interp_ident e2.
        Proof.
          revert p; induction Hwf; cbn [eliminate_dead']; cbv [Proper respectful] in *;
            repeat first [ progress interp_safe_t
                         | simplifier_t_step
                         | break_innermost_match_step
                         | interp_unsafe_t_step ].
        Qed.

        Lemma interp_eliminate_dead live t (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
          : expr.interp interp_ident (eliminate_dead live e1) == expr.interp interp_ident e2.
        Proof. apply interp_eliminate_dead'_gen with (G:=nil); cbn [In]; eauto with nocore; tauto. Qed.

        Lemma Interp_EliminateDead {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (EliminateDead e) == expr.Interp interp_ident e.
        Proof. apply interp_eliminate_dead, Hwf. Qed.
      End interp.
    End with_ident.
  End DeadCodeElimination.

  Module Subst01.
    Import MiscCompilerPasses.Compilers.Subst01.

    Local Ltac simplifier_t_step :=
      first [ progress cbn [fst snd] in *
            | progress eta_expand ].

    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Section with_var.
        Context {var1 var2 : type -> Type}
                (live : PositiveMap.t nat).
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation subst01'1 := (@subst01' base_type ident var1 live).
        Local Notation subst01'2 := (@subst01' base_type ident var2 live).
        Local Notation subst011 := (@subst01 base_type ident var1 live).
        Local Notation subst012 := (@subst01 base_type ident var2 live).

        Lemma wf_subst01' G1 G2 t e1 e2 p
              (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> expr.wf G2 v1 v2)
          : expr.wf G1 (t:=t) e1 e2 -> expr.wf G2 (snd (subst01'1 e1 p)) (snd (subst01'2 e2 p))
                                      /\ fst (subst01'1 e1 p) = fst (subst01'2 e2 p).
        Proof.
          intro Hwf; revert dependent G2; revert p; induction Hwf;
            cbn [subst01'];
            repeat first [ progress wf_safe_t
                         | simplifier_t_step
                         | progress split_and
                         | apply conj
                         | match goal with
                           | [ H : context[fst _ = fst _] |- _ ] => progress erewrite H by eauto
                           end
                         | break_innermost_match_step
                         | solve [ wf_t ] ].
        Qed.

        Lemma wf_subst01 t e1 e2
          : expr.wf nil (t:=t) e1 e2 -> expr.wf nil (subst011 e1) (subst012 e2).
        Proof. intro Hwf; apply wf_subst01' with (G1:=nil); cbn [In]; eauto with nocore; tauto. Qed.
      End with_var.

      Lemma Wf_Subst01 {t} (e : @expr.Expr base_type ident t)
        : expr.Wf e -> expr.Wf (Subst01 e).
      Proof. intros Hwf var1 var2; eapply wf_subst01, Hwf. Qed.

      Section interp.
        Context {base_interp : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp base_interp t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

        Lemma interp_subst01'_gen (live : PositiveMap.t nat) G t (e1 e2 : expr t)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> expr.interp interp_ident v1 == v2)
              (Hwf : expr.wf G e1 e2)
              p
          : expr.interp interp_ident (snd (subst01' live e1 p)) == expr.interp interp_ident e2.
        Proof.
          revert p; induction Hwf; cbn [subst01']; cbv [Proper respectful] in *;
            repeat first [ progress interp_safe_t
                         | simplifier_t_step
                         | break_innermost_match_step
                         | interp_unsafe_t_step ].
        Qed.

        Lemma interp_subst01 live t (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
          : expr.interp interp_ident (subst01 live e1) == expr.interp interp_ident e2.
        Proof. apply interp_subst01'_gen with (G:=nil); cbn [In]; eauto with nocore; tauto. Qed.

        Lemma Interp_Subst01 {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (Subst01 e) == expr.Interp interp_ident e.
        Proof. apply interp_subst01, Hwf. Qed.
      End interp.
    End with_ident.
  End Subst01.
End Compilers.
