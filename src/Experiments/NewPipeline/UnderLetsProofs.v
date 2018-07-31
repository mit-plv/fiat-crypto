Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.SetoidList.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLets.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Import ListNotations. Local Open Scope list_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLets.Compilers.
  Import ident.Notations.
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

  Hint Resolve SubstVarLike.Wf_SubstVar SubstVarLike.Wf_SubstVarFstSndPairOpp SubstVarLike.Wf_SubstVarLike SubstVarLike.Wf_SubstVarOrIdent : wf.
  Hint Rewrite @SubstVarLike.Interp_SubstVar @SubstVarLike.Interp_SubstVarFstSndPairOpp @SubstVarLike.Interp_SubstVarLike @SubstVarLike.Interp_SubstVarOrIdent : interp.

  Module UnderLets.
    Import UnderLets.Compilers.UnderLets.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident).

      Section with_var.
        Context {var1 var2 : type -> Type}.

        Inductive wf {T1 T2} {P : list { t : type & var1 t * var2 t }%type -> T1 -> T2 -> Prop}
          : list { t : type & var1 t * var2 t }%type -> @UnderLets var1 T1 -> @UnderLets var2 T2 -> Prop :=
        | Wf_Base G e1 e2 : P G e1 e2 -> wf G (Base e1) (Base e2)
        | Wf_UnderLet G A x1 x2 f1 f2
          : expr.wf G x1 x2
            -> (forall v1 v2, wf (existT _ A (v1, v2) :: G) (f1 v1) (f2 v2))
            -> wf G (UnderLet x1 f1) (UnderLet x2 f2).
        Global Arguments wf {T1 T2} P _ _ _.

        Lemma wf_Proper_list_impl {T1 T2}
              (P1 P2 : list { t : type & var1 t * var2 t }%type -> T1 -> T2 -> Prop)
              G1 G2
              (HP : forall seg v1 v2, P1 (seg ++ G1) v1 v2 -> P2 (seg ++ G2) v1 v2)
              (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
              e1 e2
              (Hwf : @wf T1 T2 P1 G1 e1 e2)
          : @wf T1 T2 P2 G2 e1 e2.
        Proof.
          revert dependent G2; induction Hwf; constructor;
            repeat first [ progress cbn in *
                         | progress intros
                         | solve [ eauto ]
                         | progress subst
                         | progress destruct_head'_or
                         | progress inversion_sigma
                         | progress inversion_prod
                         | match goal with H : _ |- _ => apply H; clear H end
                         | wf_unsafe_t_step
                         | eapply (HP nil)
                         | rewrite ListUtil.app_cons_app_app in * ].
        Qed.

        Lemma wf_Proper_list {T1 T2}
              {P : list { t : type & var1 t * var2 t }%type -> T1 -> T2 -> Prop}
              (HP : forall G1 G2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                  -> forall v1 v2, P G1 v1 v2 -> P G2 v1 v2)
              G1 G2
              (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
              e1 e2
              (Hwf : @wf T1 T2 P G1 e1 e2)
          : @wf T1 T2 P G2 e1 e2.
        Proof.
          eapply wf_Proper_list_impl; [ intros | | eassumption ]; eauto.
          eapply HP; [ | eassumption ]; intros *.
          rewrite !in_app_iff; intuition eauto.
        Qed.

        Lemma wf_to_expr {t} (x : @UnderLets var1 (@expr var1 t)) (y : @UnderLets var2 (@expr var2 t))
              G
          : wf (fun G => expr.wf G) G x y -> expr.wf G (to_expr x) (to_expr y).
        Proof.
          intro Hwf; induction Hwf; cbn [to_expr]; [ assumption | constructor; auto ].
        Qed.

        Lemma wf_splice {A1 B1 A2 B2}
              {P : list { t : type & var1 t * var2 t }%type -> A1 -> A2 -> Prop}
              {Q : list { t : type & var1 t * var2 t }%type -> B1 -> B2 -> Prop}
              G
              (x1 : @UnderLets var1 A1) (x2 : @UnderLets var2 A2) (Hx : @wf _ _ P G x1 x2)
              (e1 : A1 -> @UnderLets var1 B1) (e2 : A2 -> @UnderLets var2 B2)
              (He : forall G' a1 a2, (exists seg, G' = seg ++ G) -> P G' a1 a2 -> @wf _ _ Q G' (e1 a1) (e2 a2))
          : @wf _ _ Q G (splice x1 e1) (splice x2 e2).
        Proof.
          induction Hx; cbn [splice]; [ | constructor ];
            eauto using (ex_intro _ nil); intros.
          match goal with H : _ |- _ => eapply H end;
            intros; destruct_head'_ex; subst.
          rewrite ListUtil.app_cons_app_app in *.
          eauto using (ex_intro _ nil).
        Qed.

        (*
        Lemma wf_splice_list {A1 B1 A2 B2}
              {P : list { t : type & var1 t * var2 t }%type -> A1 -> A2 -> Prop}
              {Q : list { t : type & var1 t * var2 t }%type -> B1 -> B2 -> Prop}
              G
              (x1 : list (@UnderLets var1 A1)) (x2 : list (@UnderLets var2 A2))
              (Hx_len : length x1 = length x2)
              (Hx : forall v1 v2, List.In (v1, v2) (List.combine x1 x2) -> @wf _ _ P G v1 v2)
              (e1 : list A1 -> @UnderLets var1 B1) (e2 : list A2 -> @UnderLets var2 B2)
              (He : forall G' a1 a2, (exists seg, G' = seg ++ G) -> P G' a1 a2 -> @wf _ _ Q G' (e1 a1) (e2 a2))
          : @wf _ _ Q G (splice_list x1 e1) (splice_list x2 e2).
        Proof.
          induction Hx; cbn [splice]; [ | constructor ];
            eauto using (ex_intro _ nil); intros.
          match goal with H : _ |- _ => eapply H end;
            intros; destruct_head'_ex; subst.
          rewrite ListUtil.app_cons_app_app in *.
          eauto using (ex_intro _ nil).
        Qed.
         *)
      End with_var.
    End with_ident.

    Section reify.
      Local Notation type := (type.type base.type).
      Local Notation expr := (@expr.expr base.type ident).
      Local Notation UnderLets := (@UnderLets.UnderLets base.type ident).

      Section with_var.
        Context {var1 var2 : type -> Type}.
        Local Notation expr1 := (@expr.expr base.type ident var1).
        Local Notation expr2 := (@expr.expr base.type ident var2).
        Local Notation UnderLets1 := (@UnderLets.UnderLets base.type ident var1).
        Local Notation UnderLets2 := (@UnderLets.UnderLets base.type ident var2).

        Local Ltac wf_reify_and_let_binds_base_cps_t Hk :=
          repeat first [ lazymatch goal with
                         | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e1 = Some _, H'' : reflect_list ?e2 = None |- _ ]
                           => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                         | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e2 = Some _, H'' : reflect_list ?e1 = None |- _ ]
                           => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                         | [ H : expr.wf _ (reify_list _) (reify_list _) |- _ ] => apply expr.wf_reify_list in H
                         end
                       | progress subst
                       | progress destruct_head' False
                       | progress expr.inversion_wf_constr
                       | progress expr.inversion_expr
                       | progress expr.invert_subst
                       | progress destruct_head'_sig
                       | progress destruct_head'_ex
                       | progress destruct_head'_and
                       | progress type.inversion_type
                       | progress base.type.inversion_type
                       | progress cbn [invert_Var invert_Literal ident.invert_Literal eq_rect f_equal f_equal2 type.decode fst snd projT1 projT2 invert_pair Option.bind combine list_rect length] in *
                       | progress cbv [type.try_transport type.try_transport_cps CPSNotations.cps_option_bind CPSNotations.cpsreturn CPSNotations.cpsbind CPSNotations.cpscall type.try_make_transport_cps id] in *
                       | rewrite base.try_make_transport_cps_correct in *
                       | progress type_beq_to_eq
                       | discriminate
                       | congruence
                       | apply Hk
                       | exists nil; reflexivity
                       | eexists (cons _ nil); reflexivity
                       | rewrite app_assoc; eexists; reflexivity
                       | progress wf_safe_t
                       | match goal with
                         | [ H : _ = _ :> ident _ |- _ ] => inversion H; clear H
                         end
                       | progress inversion_option
                       | progress break_innermost_match_hyps
                       | progress expr.inversion_wf_one_constr
                       | progress expr.invert_match_step
                       | match goal with |- wf _ _ _ _ => constructor end
                       | match goal with
                         | [ H : context[wf _ _ _ _] |- wf _ _ _ _ ] => apply H; eauto with nocore
                         end
                       | progress wf_unsafe_t_step
                       | match goal with
                         | [ H : context[match Compilers.reify_list ?ls with _ => _ end] |- _ ]
                           => is_var ls; destruct ls; rewrite ?expr.reify_list_cons, ?expr.reify_list_nil in H
                         | [ H : SubstVarLike.is_recursively_var_or_ident _ _ = _ |- _ ] => clear H
                         | [ H : forall x y, @?A x y \/ @?B x y -> @?C x y |- _ ]
                           => pose proof (fun x y pf => H x y (or_introl pf));
                              pose proof (fun x y pf => H x y (or_intror pf));
                              clear H
                         end ].

        Lemma wf_reify_and_let_binds_base_cps {t : base.type} {T1 T2} (e1 : expr1 (type.base t)) (e2 : expr2 (type.base t))
              (k1 : expr1 (type.base t) -> UnderLets1 T1) (k2 : expr2 (type.base t) -> UnderLets2 T2)
              (P : _ -> _ -> _ -> Prop) G
              (Hwf : expr.wf G e1 e2)
              (Hk : forall G' e1 e2, (exists seg, G' = seg ++ G) -> expr.wf G' e1 e2 -> wf P G' (k1 e1) (k2 e2))
          : wf P G (reify_and_let_binds_base_cps e1 T1 k1) (reify_and_let_binds_base_cps e2 T2 k2).
        Proof.
          revert dependent G; induction t; cbn [reify_and_let_binds_base_cps]; intros;
            try (cbv [SubstVarLike.is_var_fst_snd_pair_opp] in *; erewrite !SubstVarLike.wfT_is_recursively_var_or_ident by eassumption);
            break_innermost_match; wf_reify_and_let_binds_base_cps_t Hk.
          all: repeat match goal with H : list (sigT _) |- _ => revert dependent H end.
          all: revert dependent k1; revert dependent k2.
          all: lazymatch goal with
               | [ H : length ?l1 = length ?l2 |- _ ]
                 => is_var l1; is_var l2; revert dependent l2; induction l1; intro l2; destruct l2; intros
               end;
            wf_reify_and_let_binds_base_cps_t Hk.
        Qed.

        Lemma wf_let_bind_return {t} (e1 : expr1 t) (e2 : expr2 t)
              G
              (Hwf : expr.wf G e1 e2)
          : expr.wf G (let_bind_return e1) (let_bind_return e2).
        Proof.
          revert dependent G; induction t; intros; cbn [let_bind_return]; cbv [invert_Abs];
            wf_safe_t;
            expr.invert_match; expr.inversion_wf; try solve [ wf_t ].
          { apply wf_to_expr.
            pose (P := fun t => { e1e2 : expr1 t * expr2 t | expr.wf G (fst e1e2) (snd e1e2) }).
            pose ((exist _ (e1, e2) Hwf) : P _) as pkg.
            change e1 with (fst (proj1_sig pkg)).
            change e2 with (snd (proj1_sig pkg)).
            clearbody pkg; clear Hwf e1 e2.
            type.generalize_one_eq_var pkg; subst P; destruct pkg as [ [e1 e2] Hwf ].
            cbn [fst snd proj1_sig proj2_sig] in *.
            repeat match goal with
                   | [ |- context[proj1_sig (rew [fun t => @sig (@?A t) (@?P t)] ?pf in exist ?P0 ?x ?p)] ]
                     => progress replace (proj1_sig (rew pf in exist P0 x p)) with (rew [A] pf in x) by (case pf; reflexivity)
                   | [ |- context[fst (rew [fun t => @prod (@?A t) (@?B t)] ?pf in pair ?x ?y)] ]
                     => progress replace (fst (rew pf in pair x y)) with (rew [A] pf in x) by (case pf; reflexivity)
                   | [ |- context[snd (rew [fun t => @prod (@?A t) (@?B t)] ?pf in pair ?x ?y)] ]
                     => progress replace (fst (rew pf in pair x y)) with (rew [B] pf in y) by (case pf; reflexivity)
                   end.
            assert (H' : t = match t' with type.base t' => t' | _ => t end) by (subst; reflexivity).
            revert pf.
            rewrite H'; clear H'.
            induction Hwf; break_innermost_match; break_innermost_match_hyps;
              repeat first [ progress intros
                           | progress type.inversion_type
                           | progress base.type.inversion_type
                           | progress wf_safe_t
                           | progress cbn [of_expr fst snd splice eq_rect type.decode f_equal] in *
                           | match goal with
                             | [ H : forall pf : ?x = ?x, _ |- _ ] => specialize (H eq_refl)
                             | [ H : forall x y (pf : ?a = ?a), _ |- _ ] => specialize (fun x y => H x y eq_refl)
                             | [ |- wf _ _ _ _ ] => constructor
                             end
                           | solve [ eauto ]
                           | apply wf_reify_and_let_binds_base_cps ]. }
        Qed.
      End with_var.

      Lemma Wf_LetBindReturn {t} (e : expr.Expr t) (Hwf : expr.Wf e) : expr.Wf (LetBindReturn e).
      Proof. intros ??; apply wf_let_bind_return, Hwf. Qed.

      Local Ltac interp_to_expr_reify_and_let_binds_base_cps_t Hk :=
        repeat first [ progress subst
                     | progress destruct_head' False
                     | progress destruct_head'_and
                     | progress destruct_head' iff
                     | progress specialize_by_assumption
                     | progress expr.inversion_wf_constr
                     | progress expr.inversion_expr
                     | progress expr.invert_subst
                     | progress destruct_head'_sig
                     | progress destruct_head'_ex
                     | progress destruct_head'_and
                     | progress type.inversion_type
                     | progress base.type.inversion_type
                     | progress cbn [invert_Var invert_Literal ident.invert_Literal eq_rect f_equal f_equal2 type.decode fst snd projT1 projT2 invert_pair Option.bind to_expr expr.interp ident.interp ident.gen_interp type.eqv length list_rect combine In] in *
                     | progress cbv [type.try_transport type.try_transport_cps CPSNotations.cps_option_bind CPSNotations.cpsreturn CPSNotations.cpsbind CPSNotations.cpscall type.try_make_transport_cps id] in *
                     | rewrite base.try_make_transport_cps_correct in *
                     | progress type_beq_to_eq
                     | discriminate
                     | congruence
                     | apply Hk
                     | exists nil; reflexivity
                     | eexists (cons _ nil); reflexivity
                     | rewrite app_assoc; eexists; reflexivity
                     | rewrite expr.reify_list_cons
                     | rewrite expr.reify_list_nil
                     | progress interp_safe_t
                     | match goal with
                       | [ H : _ = _ :> ident _ |- _ ] => inversion H; clear H
                       | [ H : forall t v1 v2, In _ _ -> _ == _, H' : In _ _ |- _ ] => apply H in H'
                       end
                     | progress inversion_option
                     | progress break_innermost_match_hyps
                     | progress expr.inversion_wf_one_constr
                     | progress expr.invert_match_step
                     | match goal with
                       | [ |- ?R (expr.interp _ ?e1) (expr.interp _ ?e2) ]
                         => solve [ eapply (@expr.wf_interp_Proper _ _ e1 e2); eauto ]
                       | [ H : context[reflect_list (reify_list _)] |- _ ] => rewrite expr.reflect_reify_list in H
                       | [ H : forall x y, @?A x y \/ @?B x y -> @?C x y |- _ ]
                         => pose proof (fun x y pf => H x y (or_introl pf));
                            pose proof (fun x y pf => H x y (or_intror pf));
                            clear H
                       end
                     | progress interp_unsafe_t_step
                     | match goal with
                       | [ H : expr.wf _ (reify_list _) ?e |- _ ]
                         => is_var e; destruct (reflect_list e) eqn:?; expr.invert_subst;
                            [ rewrite expr.wf_reify_list in H | apply expr.wf_reflect_list in H ]
                       | [ H : SubstVarLike.is_recursively_var_or_ident _ _ = _ |- _ ] => clear H
                       | [ H : context[expr.interp _ _ = _] |- expr.interp _ (to_expr _) = ?k2 _ ]
                         => erewrite H; clear H;
                            [ match goal with
                              | [ |- ?k (expr.interp ?ii ?e) = ?k' ?v ]
                                => has_evar e;
                                   let p := fresh in
                                   set (p := expr.interp ii e);
                                   match v with
                                   | context G[expr.interp ii ?e']
                                     => unify e e'; let v' := context G[p] in change (k p = k' v')
                                   end;
                                   clearbody p; reflexivity
                              end
                            | .. ]
                       end ].

      Lemma interp_to_expr_reify_and_let_binds_base_cps {t : base.type} {t' : base.type} (e1 : expr (type.base t)) (e2 : expr (type.base t))
            G
            (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
            (Hwf : expr.wf G e1 e2)
            (k1 : expr (type.base t) -> UnderLets _ (expr (type.base t')))
            (k2 : base.interp t -> base.interp t')
            (Hk : forall e1 v, defaults.interp e1 == v -> defaults.interp (to_expr (k1 e1)) == k2 v)
        : defaults.interp (to_expr (reify_and_let_binds_base_cps e1 _ k1)) == k2 (defaults.interp e2).
      Proof.
        revert dependent G; revert dependent t'; induction t; cbn [reify_and_let_binds_base_cps]; intros;
            try (cbv [SubstVarLike.is_var_fst_snd_pair_opp] in *; erewrite !SubstVarLike.wfT_is_recursively_var_or_ident by eassumption);
            break_innermost_match; interp_to_expr_reify_and_let_binds_base_cps_t Hk.
        all: repeat match goal with H : list (sigT _) |- _ => revert dependent H end.
        all: revert dependent k1; revert dependent k2.
        all: lazymatch goal with
             | [ H : length ?l1 = length ?l2 |- _ ]
               => is_var l1; is_var l2; revert dependent l2; induction l1; intro l2; destruct l2; intros
             end;
          interp_to_expr_reify_and_let_binds_base_cps_t Hk.
      Qed.

      Lemma interp_let_bind_return {t} (e1 e2 : expr t)
            G
            (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
            (Hwf : expr.wf G e1 e2)
        : defaults.interp (let_bind_return e1) == defaults.interp e2.
      Proof.
        revert dependent G; induction t; intros; cbn [let_bind_return type.eqv expr.interp] in *; cbv [invert_Abs respectful] in *;
          repeat first [ progress wf_safe_t
                       | progress expr.invert_subst
                       | progress expr.invert_match
                       | progress expr.inversion_wf
                       | progress break_innermost_match_hyps
                       | progress destruct_head' False
                       | solve [ wf_t ]
                       | match goal with
                         | [ H : _ |- expr.interp _ (let_bind_return ?e0) == expr.interp _ ?e ?v ]
                           => eapply (H e0 (e @ $v)%expr (cons _ _)); [ .. | solve [ wf_t ] ]; solve [ wf_t ]
                         | [ H : _ |- expr.interp _ (let_bind_return ?e0) == expr.interp _ ?e ?v ]
                           => cbn [expr.interp]; eapply H; [ | solve [ wf_t ] ]; solve [ wf_t ]
                         end ];
          [].
        { pose (P := fun t => { e1e2 : expr t * expr t | expr.wf G (fst e1e2) (snd e1e2) }).
          pose ((exist _ (e1, e2) Hwf) : P _) as pkg.
          change e1 with (fst (proj1_sig pkg)).
          change e2 with (snd (proj1_sig pkg)).
          clearbody pkg; clear Hwf e1 e2.
          type.generalize_one_eq_var pkg; subst P; destruct pkg as [ [e1 e2] Hwf ].
          cbn [fst snd proj1_sig proj2_sig] in *.
          repeat match goal with
                 | [ |- context[proj1_sig (rew [fun t => @sig (@?A t) (@?P t)] ?pf in exist ?P0 ?x ?p)] ]
                   => progress replace (proj1_sig (rew pf in exist P0 x p)) with (rew [A] pf in x) by (case pf; reflexivity)
                 | [ |- context[fst (rew [fun t => @prod (@?A t) (@?B t)] ?pf in pair ?x ?y)] ]
                   => progress replace (fst (rew pf in pair x y)) with (rew [A] pf in x) by (case pf; reflexivity)
                 | [ |- context[snd (rew [fun t => @prod (@?A t) (@?B t)] ?pf in pair ?x ?y)] ]
                   => progress replace (fst (rew pf in pair x y)) with (rew [B] pf in y) by (case pf; reflexivity)
                 end.
          assert (H' : t = match t' with type.base t' => t' | _ => t end) by (subst; reflexivity).
          revert pf.
          rewrite H'; clear H'.
          induction Hwf; break_innermost_match; break_innermost_match_hyps;
            repeat first [ progress intros
                         | progress type.inversion_type
                         | progress base.type.inversion_type
                         | progress wf_safe_t
                         | progress cbn [of_expr fst snd splice eq_rect type.decode f_equal to_expr] in *
                         | match goal with
                           | [ H : forall pf : ?x = ?x, _ |- _ ] => specialize (H eq_refl)
                           | [ H : forall x (pf : ?a = ?a), _ |- _ ] => specialize (fun x => H x eq_refl)
                           | [ H : forall x y (pf : ?a = ?a), _ |- _ ] => specialize (fun x y => H x y eq_refl)
                           | [ H : forall x y z (pf : ?a = ?a), _ |- _ ] => specialize (fun x y z => H x y z eq_refl)
                           | [ |- context[(expr_let x := _ in _)%expr] ] => progress cbn [expr.interp]; cbv [LetIn.Let_In]
                           | [ H : context[expr.interp _ _ = expr.interp _ _] |- expr.interp _ _ = expr.interp _ _ ]
                             => eapply H; eauto with nocore
                           end
                         | solve [ eauto ]
                         | solve [ eapply expr.wf_interp_Proper; eauto ] ].
          all: eapply interp_to_expr_reify_and_let_binds_base_cps with (k1:=Base) (k2:=(fun x => x)); eauto; wf_safe_t. }
      Qed.

      Lemma Interp_LetBindReturn {t} (e : expr.Expr t) (Hwf : expr.Wf e) : defaults.Interp (LetBindReturn e) == defaults.Interp e.
      Proof.
        apply interp_let_bind_return with (G:=nil); cbn [List.In]; eauto; tauto.
      Qed.
    End reify.
  End UnderLets.

  Hint Resolve UnderLets.Wf_LetBindReturn : wf.
  Hint Rewrite @UnderLets.Interp_LetBindReturn : interp.
End Compilers.
