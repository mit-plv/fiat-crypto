Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Inversion.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.TreeCaching.
Require Import Crypto.MiscCompilerPasses.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope list_scope.

Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import MiscCompilerPasses.Compilers.
  Import expr.Notations.
  Import invert_expr.

  Module Subst01.
    Import MiscCompilerPasses.Compilers.Subst01.

    Local Ltac simplifier_t_step :=
      first [ progress cbn [fst snd] in *
            | progress eta_expand ].

    Section with_counter.
      Context {T : Type}
              (one : T)
              (incr : T -> T)
              (incr_always_live : option T -> T).

      Section with_ident.
        Context {base_type : Type}.
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}.
        Local Notation expr := (@expr.expr base_type ident).
        Context {base_type_beq : base_type -> base_type -> bool}
          {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
          {reflect_base_type_beq : reflect_rel (@eq base_type) base_type_beq}
          {exprDefault : forall var, @DefaultValue.type.base.DefaultT type (@expr var)}
          {try_make_transport_base_type_cps_correct : type.try_make_transport_cps_correctT base_type}.
        Context (is_ident_always_live : forall t, ident t -> bool).

        Section with_var.
          Context {doing_subst_debug : forall T1 T2, T1 -> (unit -> T2) -> T1}
                  {should_subst : T -> bool}
                  (Hdoing_subst_debug : forall T1 T2 x y, doing_subst_debug T1 T2 x y = x)
                  {var1 var2 : type -> Type}.
          Local Notation tree := (@tree_nd.tree (option T * (unit -> positive * list (positive * T)))).
          Local Notation expr1 := (@expr.expr base_type ident var1).
          Local Notation expr2 := (@expr.expr base_type ident var2).
          Local Notation subst0n1 := (@subst0n T base_type ident doing_subst_debug var1 should_subst).
          Local Notation subst0n2 := (@subst0n T base_type ident doing_subst_debug var2 should_subst).

          Lemma wf_subst0n_gen live G1 G2 t e1 e2
                (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> expr.wf G2 v1 v2)
            : expr.wf G1 (t:=t) e1 e2 -> expr.wf G2 (subst0n1 live e1) (subst0n2 live e2).
          Proof using Hdoing_subst_debug.
            intro Hwf; revert dependent G2; revert live; induction Hwf;
              cbn [subst0n];
              repeat first [ progress wf_safe_t
                           | simplifier_t_step
                           | rewrite Hdoing_subst_debug
                           | break_innermost_match_step
                           | solve [ wf_t ] ].
          Qed.

          Lemma wf_subst0n live t e1 e2
            : expr.wf nil (t:=t) e1 e2 -> expr.wf nil (subst0n1 live e1) (subst0n2 live e2).
          Proof using Hdoing_subst_debug. intro Hwf; eapply wf_subst0n_gen, Hwf; wf_safe_t. Qed.
        End with_var.

        Lemma Wf_Subst0n
              {doing_subst_debug : forall T1 T2, T1 -> (unit -> T2) -> T1}
              {should_subst : T -> bool}
              (Hdoing_subst_debug : forall T1 T2 x y, doing_subst_debug T1 T2 x y = x)
              {t} (e : @expr.Expr base_type ident t)
          : expr.Wf e -> expr.Wf (Subst0n one incr incr_always_live is_ident_always_live doing_subst_debug should_subst e).
        Proof using try_make_transport_base_type_cps_correct.
          intros Hwf var1 var2; cbv [Subst0n Let_In].
          apply wf_subst0n, GeneralizeVar.Wf_FromFlat_ToFlat, Hwf; assumption.
        Qed.

        Section interp.
          Context {base_interp : base_type -> Type}
                  {interp_ident : forall t, ident t -> type.interp base_interp t}
                  {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

          Section with_doing_subst_debug.
            Context {doing_subst_debug : forall T1 T2, T1 -> (unit -> T2) -> T1}
                    {should_subst : T -> bool}
                    (Hdoing_subst_debug : forall T1 T2 x y, doing_subst_debug T1 T2 x y = x).

            Lemma interp_subst0n_gen live G t (e1 e2 : expr t)
                  (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> expr.interp interp_ident v1 == v2)
                  (Hwf : expr.wf G e1 e2)
              : expr.interp interp_ident (subst0n doing_subst_debug should_subst live e1) == expr.interp interp_ident e2.
            Proof using Hdoing_subst_debug interp_ident_Proper.
              revert live; induction Hwf; cbn [subst0n]; cbv [Proper respectful] in *;
                repeat first [ progress interp_safe_t
                             | simplifier_t_step
                             | rewrite Hdoing_subst_debug
                             | break_innermost_match_step
                             | interp_unsafe_t_step ].
            Qed.

            Lemma interp_subst0n live t (e1 e2 : expr t)
                  (Hwf : expr.wf nil e1 e2)
              : expr.interp interp_ident (subst0n doing_subst_debug should_subst live e1) == expr.interp interp_ident e2.
            Proof using Hdoing_subst_debug interp_ident_Proper. clear -Hwf Hdoing_subst_debug interp_ident_Proper. apply interp_subst0n_gen with (G:=nil); cbn [In]; eauto with nocore; tauto. Qed.

            Lemma Interp_Subst0n {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
              : expr.Interp interp_ident (Subst0n one incr incr_always_live is_ident_always_live doing_subst_debug should_subst e) == expr.Interp interp_ident e.
            Proof using Hdoing_subst_debug interp_ident_Proper try_make_transport_base_type_cps_correct.
              cbv [Subst0n Let_In expr.Interp].
              etransitivity; [ apply interp_subst0n, GeneralizeVar.Wf_FromFlat_ToFlat, Hwf | ].
              apply GeneralizeVar.Interp_gen1_FromFlat_ToFlat; assumption.
            Qed.
          End with_doing_subst_debug.
        End interp.
      End with_ident.
    End with_counter.

    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Context {base_type_beq : base_type -> base_type -> bool}
        {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
        {reflect_base_type_beq : reflect_rel (@eq base_type) base_type_beq}
        {exprDefault : forall var, @DefaultValue.type.base.DefaultT type (@expr var)}
        {try_make_transport_base_type_cps_correct : type.try_make_transport_cps_correctT base_type}.
      Context (is_ident_always_live : forall t, ident t -> bool).

      Lemma Wf_Subst01 {t} (e : @expr.Expr base_type ident t)
        : expr.Wf e -> expr.Wf (Subst01 is_ident_always_live e).
      Proof using try_make_transport_base_type_cps_correct. eapply Wf_Subst0n; try assumption; reflexivity. Qed.

      Section interp.
        Context {base_interp : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp base_interp t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.
        Lemma Interp_Subst01 {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (Subst01 is_ident_always_live e) == expr.Interp interp_ident e.
        Proof using interp_ident_Proper try_make_transport_base_type_cps_correct. eapply Interp_Subst0n, Hwf; auto. Qed.
      End interp.
    End with_ident.

    Ltac autorewrite_interp_side_condition_solver := assumption.
  End Subst01.

#[global]
  Hint Resolve Subst01.Wf_Subst01 : wf.
#[global]
  Hint Opaque Subst01.Subst01 : wf interp rewrite.
#[global]
  Hint Rewrite @Subst01.Interp_Subst01 using Subst01.autorewrite_interp_side_condition_solver : interp.

  Module DeadCodeElimination.
    Import MiscCompilerPasses.Compilers.DeadCodeElimination.

    (** Rather than proving correctness of the computation of live
            variables and requiring something about [live], we instead
            rely on the fact that DCE in fact just inlines code it
            believes to be dead. *)
    Local Transparent OUGHT_TO_BE_UNUSED.
    Lemma OUGHT_TO_BE_UNUSED_id {T1 T2} v v' : @OUGHT_TO_BE_UNUSED T1 T2 v v' = v.
    Proof. exact eq_refl. Qed.
    Local Opaque OUGHT_TO_BE_UNUSED.

    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Context {base_type_beq : base_type -> base_type -> bool}
        {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base_type}
        {reflect_base_type_beq : reflect_rel (@eq base_type) base_type_beq}
        {exprDefault : forall var, @DefaultValue.type.base.DefaultT type (@expr var)}
        {try_make_transport_base_type_cps_correct : type.try_make_transport_cps_correctT base_type}.
      Context (is_ident_always_live : forall t, ident t -> bool).

      Lemma Wf_EliminateDead {t} (e : @expr.Expr base_type ident t)
        : expr.Wf e -> expr.Wf (EliminateDead is_ident_always_live e).
      Proof using try_make_transport_base_type_cps_correct. eapply Subst01.Wf_Subst0n; auto using @OUGHT_TO_BE_UNUSED_id. Qed.

      Section interp.
        Context {base_interp : base_type -> Type}
                {interp_ident : forall t, ident t -> type.interp base_interp t}
                {interp_ident_Proper : forall t, Proper (eq ==> type.eqv) (interp_ident t)}.

        Lemma Interp_EliminateDead {t} (e : @expr.Expr base_type ident t) (Hwf : expr.Wf e)
          : expr.Interp interp_ident (EliminateDead is_ident_always_live e) == expr.Interp interp_ident e.
        Proof using interp_ident_Proper try_make_transport_base_type_cps_correct. eapply Subst01.Interp_Subst0n, Hwf; auto using @OUGHT_TO_BE_UNUSED_id. Qed.
      End interp.
    End with_ident.
    Ltac autorewrite_interp_side_condition_solver := Subst01.autorewrite_interp_side_condition_solver.
  End DeadCodeElimination.

#[global]
  Hint Resolve DeadCodeElimination.Wf_EliminateDead : wf.
#[global]
  Hint Opaque DeadCodeElimination.EliminateDead : wf interp rewrite.
#[global]
  Hint Rewrite @DeadCodeElimination.Interp_EliminateDead using DeadCodeElimination.autorewrite_interp_side_condition_solver : interp.
End Compilers.
