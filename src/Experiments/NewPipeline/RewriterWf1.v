Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Import ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import GENERATEDIdentifiersWithoutTypesProofs.Compilers.
  Import Rewriter.Compilers.
  Import expr.Notations.
  Import defaults.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    Module Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.

      Section with_type0.
        Context {base_type} {ident : type.type base_type -> Type}.
        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident).
        Let type_base (t : base_type) : type := type.base t.
        Coercion type_base : base_type >-> type.

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Local Notation value'1 := (@value' base_type ident var1).
          Local Notation value'2 := (@value' base_type ident var2).
          Local Notation value1 := (@value base_type ident var1).
          Local Notation value2 := (@value base_type ident var2).
          Local Notation value_with_lets1 := (@value_with_lets base_type ident var1).
          Local Notation value_with_lets2 := (@value_with_lets base_type ident var2).
          Local Notation Base_value := (@Base_value base_type ident).
          Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base_type ident).
          Local Notation splice_value_with_lets := (@splice_value_with_lets base_type ident).

          Fixpoint wf_value' {with_lets : bool} G {t : type} : value'1 with_lets t -> value'2 with_lets t -> Prop
            := match t, with_lets with
               | type.base t, true => UnderLets.wf (fun G' => expr.wf G') G
               | type.base t, false => expr.wf G
               | type.arrow s d, _
                 => fun f1 f2
                    => (forall seg G' v1 v2,
                           G' = (seg ++ G)%list
                           -> @wf_value' false seg s v1 v2
                           -> @wf_value' true G' d (f1 v1) (f2 v2))
               end.

          Definition wf_value G {t} : value1 t -> value2 t -> Prop := @wf_value' false G t.
          Definition wf_value_with_lets G {t} : value_with_lets1 t -> value_with_lets2 t -> Prop := @wf_value' true G t.

          Lemma wf_value'_Proper_list {with_lets} G1 G2
                (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                t e1 e2
                (Hwf : @wf_value' with_lets G1 t e1 e2)
            : @wf_value' with_lets G2 t e1 e2.
          Proof.
            revert Hwf; revert dependent with_lets; revert dependent G2; revert dependent G1; induction t;
              repeat first [ progress cbn in *
                           | progress intros
                           | solve [ eauto ]
                           | progress subst
                           | progress destruct_head'_or
                           | progress inversion_sigma
                           | progress inversion_prod
                           | progress break_innermost_match_hyps
                           | eapply UnderLets.wf_Proper_list; [ .. | solve [ eauto ] ]
                           | wf_unsafe_t_step
                           | match goal with H : _ |- _ => solve [ eapply H; [ .. | solve [ eauto ] ]; wf_t ] end ].
          Qed.

          Lemma wf_Base_value G {t} v1 v2 (Hwf : @wf_value G t v1 v2)
            : @wf_value_with_lets G t (Base_value v1) (Base_value v2).
          Proof.
            destruct t; cbn; intros; subst; hnf; try constructor; try assumption.
            eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; trivial.
          Qed.

          Lemma wf_splice_under_lets_with_value {T1 T2 t}
                G
                (x1 : @UnderLets var1 T1) (x2 : @UnderLets var2 T2)
                (e1 : T1 -> value_with_lets1 t) (e2 : T2 -> value_with_lets2 t)
                (Hx : UnderLets.wf (fun G' a1 a2 => wf_value_with_lets G' (e1 a1) (e2 a2)) G x1 x2)
            : wf_value_with_lets G (splice_under_lets_with_value x1 e1) (splice_under_lets_with_value x2 e2).
          Proof.
            cbv [wf_value_with_lets] in *.
            revert dependent G; induction t as [t|s IHs d IHd]; cbn [splice_under_lets_with_value wf_value']; intros.
            { eapply UnderLets.wf_splice; eauto. }
            { intros; subst; apply IHd.
              eapply UnderLets.wf_Proper_list_impl; [ | | solve [ eauto ] ]; wf_t.
              eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; wf_t. }
          Qed.

          Lemma wf_splice_value_with_lets {t t'}
                G
                (x1 : value_with_lets1 t) (x2 : value_with_lets2 t)
                (e1 : value1 t -> value_with_lets1 t') (e2 : value2 t -> value_with_lets2 t')
                (Hx : wf_value_with_lets G x1 x2)
                (He : forall seg G' v1 v2, (G' = (seg ++ G)%list) -> wf_value G' v1 v2 -> wf_value_with_lets G' (e1 v1) (e2 v2))
            : wf_value_with_lets G (splice_value_with_lets x1 e1) (splice_value_with_lets x2 e2).
          Proof.
            destruct t; cbn [splice_value_with_lets].
            { eapply wf_splice_under_lets_with_value.
              eapply UnderLets.wf_Proper_list_impl; [ | | eassumption ]; trivial; wf_t. }
            { eapply wf_value'_Proper_list; [ | eapply He with (seg:=nil); hnf in Hx |- * ].
              { eauto; subst G'; wf_t. }
              { reflexivity. }
              { intros; subst; eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; wf_t. } }
          Qed.

          Section wf.
            Context (G : list { t : _ & var1 t * var2 t }%type).
            Inductive wf_anyexpr : forall t, @AnyExpr.anyexpr base_type ident var1 -> @AnyExpr.anyexpr base_type ident var2 -> Prop :=
            | Wf_wrap {t : base_type} {e1 e2} : expr.wf (t:=t) G e1 e2 -> @wf_anyexpr (type.base t) (AnyExpr.wrap e1) (AnyExpr.wrap e2).
          End wf.
        End with_var2.
      End with_type0.
      Import AnyExpr.
      Section with_type.
        Context {ident : type.type base.type -> Type}
                {pident : Type}
                (full_types : pident -> Type)
                (invert_bind_args : forall t (idc : ident t) (pidc : pident), option (full_types pidc))
                (type_of_pident : forall (pidc : pident), full_types pidc -> type.type base.type)
                (pident_to_typed : forall (pidc : pident) (args : full_types pidc), ident (type_of_pident pidc args))
                (eta_ident_cps : forall {T : type.type base.type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                (eta_ident_cps_correct : forall T t idc f, @eta_ident_cps T t idc f = f _ idc)
                (of_typed_ident : forall {t}, ident t -> pident)
                (arg_types : pident -> option Type)
                (bind_args : forall {t} (idc : ident t), match arg_types (of_typed_ident idc) return Type with Some t => t | None => unit end)
                (pident_beq : pident -> pident -> bool)
                (try_make_transport_ident_cps : forall (P : pident -> Type) (idc1 idc2 : pident), ~> option (P idc1 -> P idc2))
                (pident_to_typed_invert_bind_args_type
                 : forall t idc p f, invert_bind_args t idc p = Some f -> t = type_of_pident p f)
                (pident_to_typed_invert_bind_args
                 : forall t idc p f (pf : invert_bind_args t idc p = Some f),
                    pident_to_typed p f = rew [ident] pident_to_typed_invert_bind_args_type t idc p f pf in idc)
                (pident_bl : forall p q, pident_beq p q = true -> p = q)
                (pident_lb : forall p q, p = q -> pident_beq p q = true)
                (try_make_transport_ident_cps_correct
                 : forall P idc1 idc2 T k,
                    try_make_transport_ident_cps P idc1 idc2 T k
                    = k (match Sumbool.sumbool_of_bool (pident_beq idc1 idc2) with
                         | left pf => Some (fun v => rew [P] pident_bl _ _ pf in v)
                         | right _ => None
                         end)).
        Local Notation type := (type.type base.type).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation expr := (@expr.expr base.type ident).
        Local Notation anyexpr := (@anyexpr base.type ident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value' := (@value' base.type ident).
        Local Notation value := (@value base.type ident).
        Local Notation value_with_lets := (@value_with_lets base.type ident).
        Local Notation Base_value := (@Base_value base.type ident).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base.type ident).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base.type ident).
        Local Notation reify := (@reify ident).
        Local Notation reflect := (@reflect ident).
        Local Notation rawexpr := (@rawexpr ident).
        Local Notation eval_decision_tree var := (@eval_decision_tree ident var pident full_types invert_bind_args type_of_pident pident_to_typed).
        Local Notation reveal_rawexpr e := (@reveal_rawexpr_cps ident _ e _ id).
        Local Notation bind_data_cps var := (@bind_data_cps ident var pident of_typed_ident arg_types bind_args try_make_transport_ident_cps).
        Local Notation bind_data e p := (@bind_data_cps _ e p _ id).
        Local Notation ptype_interp := (@ptype_interp ident).
        Local Notation binding_dataT var := (@binding_dataT ident var pident arg_types).

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Context (reify_and_let_binds_base_cps1 : forall (t : base.type), @expr var1 t -> forall T, (@expr var1 t -> @UnderLets var1 T) -> @UnderLets var1 T)
                  (reify_and_let_binds_base_cps2 : forall (t : base.type), @expr var2 t -> forall T, (@expr var2 t -> @UnderLets var2 T) -> @UnderLets var2 T)
                  (wf_reify_and_let_binds_base_cps
                   : forall G (t : base.type) x1 x2 T1 T2 P
                            (Hx : expr.wf G x1 x2)
                            (e1 : expr t -> @UnderLets var1 T1) (e2 : expr t -> @UnderLets var2 T2)
                            (He : forall x1 x2 G' seg, (G' = (seg ++ G)%list) -> expr.wf G' x1 x2 -> UnderLets.wf P G' (e1 x1) (e2 x2)),
                      UnderLets.wf P G (reify_and_let_binds_base_cps1 t x1 T1 e1) (reify_and_let_binds_base_cps2 t x2 T2 e2)).

          Local Notation wf_value' := (@wf_value' base.type ident var1 var2).
          Local Notation wf_value := (@wf_value base.type ident var1 var2).
          Local Notation wf_value_with_lets := (@wf_value_with_lets base.type ident var1 var2).
          Local Notation reify_and_let_binds_cps1 := (@reify_and_let_binds_cps ident var1 reify_and_let_binds_base_cps1).
          Local Notation reify_and_let_binds_cps2 := (@reify_and_let_binds_cps ident var2 reify_and_let_binds_base_cps2).
          Local Notation rewrite_rulesT1 := (@rewrite_rulesT ident var1 pident arg_types).
          Local Notation rewrite_rulesT2 := (@rewrite_rulesT ident var2 pident arg_types).
          Local Notation eval_rewrite_rules1 := (@eval_rewrite_rules ident var1 pident full_types invert_bind_args type_of_pident pident_to_typed of_typed_ident arg_types bind_args try_make_transport_ident_cps).
          Local Notation eval_rewrite_rules2 := (@eval_rewrite_rules ident var2 pident full_types invert_bind_args type_of_pident pident_to_typed of_typed_ident arg_types bind_args try_make_transport_ident_cps).

          Fixpoint wf_reify {with_lets} G {t}
            : forall e1 e2, @wf_value' with_lets G t e1 e2 -> expr.wf G (@reify _ with_lets t e1) (@reify _ with_lets t e2)
          with wf_reflect {with_lets} G {t}
               : forall e1 e2, expr.wf G e1 e2 -> @wf_value' with_lets G t (@reflect _ with_lets t e1) (@reflect _ with_lets t e2).
          Proof using Type.
            { destruct t as [t|s d];
                [ clear wf_reflect wf_reify
                | specialize (fun with_lets G => @wf_reify with_lets G d); specialize (fun with_lets G => wf_reflect with_lets G s) ].
              { destruct with_lets; cbn; intros; auto using UnderLets.wf_to_expr. }
              { intros e1 e2 Hwf.
                change (reify e1) with (λ x, @reify _ _ d (e1 (@reflect _ _ s ($x))))%expr.
                change (reify e2) with (λ x, @reify _ _ d (e2 (@reflect _ _ s ($x))))%expr.
                constructor; intros; eapply wf_reify, Hwf with (seg:=cons _ nil); [ | eapply wf_reflect; constructor ]; wf_t. } }
            { destruct t as [t|s d];
                [ clear wf_reflect wf_reify
                | specialize (fun with_lets G => @wf_reify with_lets G s); specialize (fun with_lets G => wf_reflect with_lets G d) ].
              { destruct with_lets; repeat constructor; auto. }
              { intros e1 e2 Hwf.
                change (reflect e1) with (fun x => @reflect _ true d (e1 @ (@reify _ false s x)))%expr.
                change (reflect e2) with (fun x => @reflect _ true d (e2 @ (@reify _ false s x)))%expr.
                hnf; intros; subst.
                eapply wf_reflect; constructor; [ wf_t | ].
                eapply wf_reify, wf_value'_Proper_list; [ | eassumption ]; wf_t. } }
          Qed.

          Lemma wf_reify_and_let_binds_cps {with_lets} G {t} x1 x2
                (Hx : @wf_value' with_lets G t x1 x2)
                T1 T2 P
                (e1 : expr t -> @UnderLets var1 T1) (e2 : expr t -> @UnderLets var2 T2)
                (He : forall x1 x2 G' seg, (G' = (seg ++ G)%list) -> expr.wf G' x1 x2 -> UnderLets.wf P G' (e1 x1) (e2 x2))
            : UnderLets.wf P G (@reify_and_let_binds_cps1 with_lets t x1 T1 e1) (@reify_and_let_binds_cps2 with_lets t x2 T2 e2).
          Proof.
            destruct t; [ destruct with_lets | ]; cbn [reify_and_let_binds_cps]; auto.
            { eapply UnderLets.wf_splice; [ eapply Hx | ]; wf_t; destruct_head'_ex; wf_t.
              eapply wf_reify_and_let_binds_base_cps; wf_t.
              eapply He; rewrite app_assoc; wf_t. }
            { eapply He with (seg:=nil); [ reflexivity | ].
              eapply wf_reify; auto. }
          Qed.

          Inductive wf_rawexpr : list { t : type & var1 t * var2 t }%type -> forall {t}, @rawexpr var1 -> @expr var1 t -> @rawexpr var2 -> @expr var2 t -> Prop :=
          | Wf_rIdent {t} G (idc : ident t) : wf_rawexpr G (rIdent idc (expr.Ident idc)) (expr.Ident idc) (rIdent idc (expr.Ident idc)) (expr.Ident idc)
          | Wf_rApp {s d} G
                    f1 (f1e : @expr var1 (s -> d)) x1 (x1e : @expr var1 s)
                    f2 (f2e : @expr var2 (s -> d)) x2 (x2e : @expr var2 s)
            : wf_rawexpr G f1 f1e f2 f2e
              -> wf_rawexpr G x1 x1e x2 x2e
              -> wf_rawexpr G
                            (rApp f1 x1 (expr.App f1e x1e)) (expr.App f1e x1e)
                            (rApp f2 x2 (expr.App f2e x2e)) (expr.App f2e x2e)
          | Wf_rExpr {t} G (e1 e2 : expr t)
            : expr.wf G e1 e2 -> wf_rawexpr G (rExpr e1) e1 (rExpr e2) e2
          | Wf_rValue {t} G (v1 v2 : value t)
            : wf_value G v1 v2
              -> wf_rawexpr G (rValue v1) (reify v1) (rValue v2) (reify v2).

          Lemma wf_rawexpr_Proper_list G1 G2
                (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                t re1 e1 re2 e2
                (Hwf : @wf_rawexpr G1 t re1 e1 re2 e2)
            : @wf_rawexpr G2 t re1 e1 re2 e2.
          Proof.
            revert dependent G2; induction Hwf; intros; constructor; eauto.
            { eapply expr.wf_Proper_list; eauto. }
            { eapply wf_value'_Proper_list; eauto. }
          Qed.

          (* Because [proj1] and [proj2] in the stdlib are opaque *)
          Local Notation proj1 x := (let (a, b) := x in a).
          Local Notation proj2 x := (let (a, b) := x in b).

          Definition eq_type_of_rawexpr_of_wf {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : type_of_rawexpr re1 = t /\ type_of_rawexpr re2 = t.
          Proof. split; destruct Hwf; reflexivity. Defined.

          Definition eq_expr_of_rawexpr_of_wf {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : (rew [expr] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re1) = e1
              /\ (rew [expr] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re2) = e2.
          Proof. split; destruct Hwf; reflexivity. Defined.

          Definition eq_expr_of_rawexpr_of_wf' {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr_of_rawexpr re1 = (rew [expr] (eq_sym (proj1 (eq_type_of_rawexpr_of_wf Hwf))) in e1)
              /\ expr_of_rawexpr re2 = (rew [expr] (eq_sym (proj2 (eq_type_of_rawexpr_of_wf Hwf))) in e2).
          Proof. split; destruct Hwf; reflexivity. Defined.

          Lemma wf_expr_of_wf_rawexpr {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr.wf G e1 e2.
          Proof. induction Hwf; repeat (assumption || constructor || apply wf_reify). Qed.

          Lemma wf_expr_of_wf_rawexpr' {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr.wf G
                      (rew [expr] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re1)
                      (rew [expr] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re2).
          Proof.
            pose proof Hwf as Hwf'.
            rewrite <- (proj1 (eq_expr_of_rawexpr_of_wf Hwf)) in Hwf'.
            rewrite <- (proj2 (eq_expr_of_rawexpr_of_wf Hwf)) in Hwf'.
            eapply wf_expr_of_wf_rawexpr; eassumption.
          Qed.

          Lemma wf_value_of_wf_rawexpr {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : wf_value G
                       (rew [value] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in value_of_rawexpr re1)
                       (rew [value] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in value_of_rawexpr re2).
          Proof.
            pose proof (wf_expr_of_wf_rawexpr Hwf).
            destruct Hwf; cbn; try eapply wf_reflect; try assumption.
          Qed.

          Lemma reveal_rawexpr_cps_id {var} e T k
            : @reveal_rawexpr_cps ident var e T k = k (reveal_rawexpr e).
          Proof.
            cbv [reveal_rawexpr_cps]; break_innermost_match; try reflexivity.
            cbv [value value'] in *; expr.invert_match; try reflexivity.
          Qed.

          Lemma wf_reveal_rawexpr t G re1 e1 re2 e2 (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : @wf_rawexpr G t (reveal_rawexpr re1) e1 (reveal_rawexpr re2) e2.
          Proof.
            pose proof (wf_expr_of_wf_rawexpr Hwf).
            destruct Hwf; cbv [reveal_rawexpr_cps id];
              repeat first [ assumption
                           | constructor
                           | progress subst
                           | progress cbn [reify eq_rect value value'] in *
                           | progress destruct_head'_sig
                           | progress destruct_head'_and
                           | break_innermost_match_step
                           | progress expr.invert_match
                           | progress expr.inversion_wf_constr ].

          Qed.

          Fixpoint wf_pbase_type_interp_cps (quant : quant_type) (t1 t2 : pattern.base.type) (K1 K2 : base.type -> Type)
                   (P : forall t, K1 t -> K2 t -> Prop) {struct t1}
            : pbase_type_interp_cps quant t1 K1 -> pbase_type_interp_cps quant t2 K2 -> Prop
            := match t1, t2, quant with
               | pattern.base.type.any, pattern.base.type.any, qforall
                 => fun v1 v2
                    => forall t : base.type, P _ (v1 t) (v2 t)
               | pattern.base.type.any, pattern.base.type.any, qexists
                 => fun v1 v2
                    => { pf : projT1 v1 = projT1 v2 | P _ (rew pf in projT2 v1) (projT2 v2) }
               | pattern.base.type.type_base t1, pattern.base.type.type_base t2, _
                 => fun v1 v2
                    => { pf : t1 = t2 | P _ (rew [fun t : base.type.base => K1 t] pf in v1) v2 }
               | pattern.base.type.prod A1 B1, pattern.base.type.prod A2 B2, _
                 => @wf_pbase_type_interp_cps
                      quant A1 A2 _ _
                      (fun A' => @wf_pbase_type_interp_cps
                                   quant B1 B2 _ _
                                   (fun B' => P (A' * B')%etype))
               | pattern.base.type.list A1, pattern.base.type.list A2, _
                 => @wf_pbase_type_interp_cps
                      quant A1 A2 _ _
                      (fun A' => P (base.type.list A'))
               | pattern.base.type.any, _, _
               | pattern.base.type.type_base _, _, _
               | pattern.base.type.prod _ _, _, _
               | pattern.base.type.list _, _, _
                 => fun _ _ => False
               end.

          Fixpoint wf_ptype_interp_cps (quant : quant_type) (t1 t2 : pattern.type) (K1 K2 : type -> Type)
                   (P : forall t, K1 t -> K2 t -> Prop) {struct t1}
            : ptype_interp_cps quant t1 K1 -> ptype_interp_cps quant t2 K2 -> Prop
            := match t1, t2 with
               | type.base t1, type.base t2 => wf_pbase_type_interp_cps quant t1 t2 _ _ (fun t => P (type.base t))
               | type.arrow s1 d1, type.arrow s2 d2
                 => wf_ptype_interp_cps
                      quant s1 s2 _ _
                      (fun s => wf_ptype_interp_cps
                                  quant d1 d2 _ _
                                  (fun d => P (type.arrow s d)))
               | type.base _, _
               | type.arrow _ _, _
                 => fun _ _ => False
               end.

          Definition wf_ptype_interp_id G {quant t1 t2} : @ptype_interp var1 quant t1 id -> @ptype_interp var2 quant t2 id -> Prop
            := @wf_ptype_interp_cps quant t1 t2 _ _ (@wf_value G).

          Fixpoint wf_binding_dataT G (p1 p2 : pattern) : @binding_dataT var1 p1 -> @binding_dataT var2 p2 -> Prop
            := match p1, p2 with
               | pattern.Wildcard t1, pattern.Wildcard t2
                 => wf_ptype_interp_id G
               | pattern.Ident idc1, pattern.Ident idc2
                 => fun v1 v2
                    => { pf : idc1 = idc2 | (rew [fun idc => @binding_dataT _ (pattern.Ident idc)] pf in v1) = v2 }
               | pattern.App f1 x1, pattern.App f2 x2
                 => fun v1 v2
                    => @wf_binding_dataT G _ _ (fst v1) (fst v2) /\ @wf_binding_dataT G _ _ (snd v1) (snd v2)
               | pattern.Wildcard _, _
               | pattern.Ident _, _
               | pattern.App _ _, _
                 => fun _ _ => False
               end.

          Lemma bind_base_cps_id t1 t2 K v T k
            : @bind_base_cps t1 t2 K v T k = k (@bind_base_cps t1 t2 K v _ id).
          Proof using Type.
            revert t2 K v T k; induction t1, t2; intros; cbn [bind_base_cps]; try reflexivity;
              rewrite_type_transport_correct; break_innermost_match; try reflexivity;
                repeat first [ progress subst
                             | progress inversion_option
                             | reflexivity
                             | match goal with
                               | [ H : _ |- _ ] => rewrite H; (reflexivity || break_innermost_match_step)
                               end ].
          Qed.

          Lemma wf_bind_base t1 t1' t2 t2' K1 K2 v1 v2 (Ht1 : t1 = t2) (Ht2 : t1' = t2') (P : forall t, K1 t -> K2 t -> Prop)
                (Pv : P _ (rew Ht2 in v1) v2)
            : option_eq (@wf_pbase_type_interp_cps _ _ _ _ _ P) (@bind_base_cps t1 t1' K1 v1 _ id) (@bind_base_cps t2 t2' K2 v2 _ id).
          Proof.
            subst t2' t2; revert t1' K1 v1 K2 v2 P Pv.
            induction t1, t1'; cbn [wf_pbase_type_interp_cps bind_base_cps]; intros; cbv [cpsreturn id cpsbind cpscall cps_option_bind];
              cbn [option_eq projT1 projT2];
              repeat first [ (exists eq_refl)
                           | reflexivity
                           | progress subst
                           | progress base.type.inversion_type
                           | progress destruct_head' False
                           | congruence
                           | progress cbn [eq_rect option_eq] in *
                           | progress cbv [id] in *
                           | solve [ eauto ]
                           | progress rewrite_type_transport_correct
                           | progress type_beq_to_eq
                           | progress break_match_step ltac:(fun v => let h := head v in constr_eq h (@Sumbool.sumbool_of_bool))
                           | rewrite bind_base_cps_id; set (@bind_base_cps _ _ _ _ _ id) at 1
                           | match goal with
                             | [ H : forall P : (forall x, _ -> _ -> Prop), P _ _ _ -> False |- _ ]
                               => specialize (H (fun _ _ _ => True) I)
                             | [ H : forall P : (forall x, _ -> _ -> Prop), P _ _ _ -> Some _ = None |- _ ]
                               => specialize (H (fun _ _ _ => True) I)
                             | [ X := Some _ |- _ ] => subst X
                             | [ X := None |- _ ] => subst X
                             | [ HP : context[?P _ ?v1 ?v2], H' : _, X := @bind_base_cps ?t1 ?t2 ?K1 ?v1 _ (fun x => x), Y := @bind_base_cps ?t1' ?t2 ?K2 ?v2 _ (fun y => y) |- _ ]
                               => specialize (H' t2 K1 v1 K2 v2);
                                  destruct (@bind_base_cps t1 t2 K1 v1 _ (fun x => x)) eqn:?,
                                           (@bind_base_cps t1' t2 K2 v2 _ (fun x => x)) eqn:?
                             end ].
          Qed.

          Lemma bind_value_cps_id t1 t2 K v T k
            : @bind_value_cps t1 t2 K v T k = k (@bind_value_cps t1 t2 K v _ id).
          Proof using Type.
            revert t2 K v T k; induction t1, t2; intros; cbn [bind_value_cps]; try reflexivity; [ apply bind_base_cps_id | ].
            cbv [cps_option_bind cpscall cpsreturn cpsbind].
            repeat first [ progress subst
                         | progress inversion_option
                         | reflexivity
                         | match goal with
                           | [ H : _ |- _ ] => rewrite H; (reflexivity || break_innermost_match_step)
                           end ].
          Qed.

          Lemma wf_bind_value t1 t1' t2 t2' K1 K2 v1 v2 (Ht1 : t1 = t2) (Ht2 : t1' = t2') (P : forall t, K1 t -> K2 t -> Prop)
                (Hv : P _ (rew Ht2 in v1) v2)
            : option_eq (@wf_ptype_interp_cps _ _ _ _ _ P) (@bind_value_cps t1 t1' K1 v1 _ id) (@bind_value_cps t2 t2' K2 v2 _ id).
          Proof.
            subst t2' t2; revert t1' K1 v1 K2 v2 P Hv.
            induction t1, t1'; cbn [wf_ptype_interp_cps bind_value_cps]; cbv [id cpsbind cpscall cpsreturn cps_option_bind];
              cbn [option_eq]; intros; try reflexivity.
            { unshelve eapply wf_bind_base; eauto. }
            { repeat first [ progress destruct_head' False
                           | congruence
                           | progress cbn [eq_rect option_eq] in *
                           | progress cbv [id] in *
                           | solve [ eauto ]
                           | rewrite bind_value_cps_id; set (@bind_value_cps _ _ _ _ _ id) at 1
                           | match goal with
                             | [ H : forall P : (forall x, _ -> _ -> Prop), P _ _ _ -> False |- _ ]
                               => specialize (H (fun _ _ _ => True) I)
                             | [ H : forall P : (forall x, _ -> _ -> Prop), P _ _ _ -> Some _ = None |- _ ]
                               => specialize (H (fun _ _ _ => True) I)
                             | [ X := Some _ |- _ ] => subst X
                             | [ X := None |- _ ] => subst X
                             | [ HP : context[?P _ ?v1 ?v2], H' : _, X := @bind_value_cps ?t1 ?t2 ?K1 ?v1 _ (fun x => x), Y := @bind_value_cps ?t1' ?t2 ?K2 ?v2 _ (fun y => y) |- _ ]
                               => specialize (H' t2 K1 v1 K2 v2);
                                  destruct (@bind_value_cps t1 t2 K1 v1 _ (fun x => x)) eqn:?,
                                           (@bind_value_cps t1' t2 K2 v2 _ (fun x => x)) eqn:?
                             end ]. }
          Qed.

          Lemma bind_data_cps_id {var} e p T k
            : @bind_data_cps var e p T k = k (bind_data e p).
          Proof using try_make_transport_ident_cps_correct.
            revert p T k; induction e, p; intros; cbn [bind_data_cps]; try (reflexivity || apply bind_value_cps_id);
              cbv [cps_option_bind cpscall cpsreturn cpsbind];
              repeat first [ progress subst
                           | progress inversion_option
                           | reflexivity
                           | rewrite try_make_transport_ident_cps_correct
                           | match goal with
                             | [ H : _ |- _ ] => rewrite H; (reflexivity || break_innermost_match_step)
                             end
                           | break_innermost_match_step ].
          Qed.

          Lemma wf_bind_data t G re1 e1 re2 e2 p1 p2 (Hwf : @wf_rawexpr G t re1 e1 re2 e2) (Hp : p1 = p2)
            : option_eq (@wf_binding_dataT G p1 p2) (bind_data re1 p1) (bind_data re2 p2).
          Proof.
            subst p2; revert p1; induction Hwf, p1; cbn [bind_data_cps value_of_rawexpr];
              rewrite_type_transport_correct;
              rewrite ?try_make_transport_ident_cps_correct.
            all: repeat first [ (exists eq_refl)
                              | exact I
                              | reflexivity
                              | unshelve eapply wf_bind_value
                              | progress break_match_step ltac:(fun v => let h := head v in constr_eq h (@Sumbool.sumbool_of_bool))
                              | progress cbn [eq_rect wf_binding_dataT fst snd option_eq] in *
                              | progress cbv [id] in *
                              | progress subst
                              | progress inversion_option
                              | apply wf_reflect
                              | match goal with
                                | [ |- context[pident_bl ?a ?b ?pf] ] => generalize (pident_bl a b pf); intros
                                | [ X := Some _ |- _ ] => subst X
                                | [ X := None |- _ ] => subst X
                                | [ X := @bind_data_cps _ ?e ?p _ (fun y => y), H : context[@bind_data_cps _ ?e _ _ (fun x => x)] |- _ ]
                                  => pose proof (H p); destruct (@bind_data_cps _ e p _ (fun y => y)) eqn:?
                                end
                              | rewrite bind_data_cps_id; set (@bind_data _ _) at 1
                              | solve [ auto ]
                              | eapply wf_expr_of_wf_rawexpr; eassumption
                              | wf_safe_t_step ].
          Qed.

          (*
        Local Notation opt_anyexprP ivar
          := (fun should_do_again : bool => UnderLets (@AnyExpr.anyexpr base.type ident (if should_do_again then ivar else var)))
               (only parsing).
        Local Notation opt_anyexpr ivar
          := (option (sigT (opt_anyexprP ivar))) (only parsing).

        Definition rewrite_ruleTP
          := (fun p : pattern => binding_dataT p -> forall T, (opt_anyexpr value -> T) -> T).
        Definition rewrite_ruleT := sigT rewrite_ruleTP.
        Definition rewrite_rulesT
          := (list rewrite_ruleT).

        Definition ERROR_BAD_REWRITE_RULE {t} (pat : pattern) (value : expr t) : expr t. exact value. Qed.
           *)

          (*
          Fixpoint natural_type_of_pattern_binding_data {var} (p : pattern) : @binding_dataT var p -> option { t : type & @expr var t }.
          Proof.
            refine match p with
                   | pattern.Wildcard t => _
                   | pattern.Ident idc => _
                   | pattern.App f x => _
                   end.
            all: cbn.
            Focus 2.
            Fixpoint natural_of_ptype_interp {var} (t : ptype) k (K : forall t, k t -> option { t : type & @expr var t }) {struct t}
              : @ptype_interp var qexists t k -> option { t : type & @expr var t }.
              refine match t with
                     | type.base t => _
                     | type.arrow s d => _
                     end.
              all: cbn.
              Focus 2.
              Fixpoint natural_of_pbase_type_interp {var} (t : ptype) k (K : forall t, k t -> option { t : type & @expr var t }) {struct t}
              : @ptype_interp var qexists t k -> option { t : type & @expr var t }.
              refine match t with
                     | type.base t => _
                     | type.arrow s d => _
                     end.
              all: cbn.
              refine
          Proof.
            refine match p with
                   | pattern.Wildcard t => _
                   | pattern.Ident idc => _
                   | pattern.App f x => _
                   end.
            cbn.

           *)

          Definition rewrite_rules_goodT
                     (rew1 : rewrite_rulesT1) (rew2 : rewrite_rulesT2)
            : Prop
            := length rew1 = length rew2
               /\ (forall p r, List.In (existT _ p r) rew1 -> forall v T k, r v T k = k (r v _ id))
               /\ (forall p r, List.In (existT _ p r) rew2 -> forall v T k, r v T k = k (r v _ id))
               /\ (forall p1 r1 p2 r2,
                      List.In (existT _ p1 r1, existT _ p2 r2) (combine rew1 rew2)
                      -> p1 = p2
                         /\ (forall G v1 v2,
                                wf_binding_dataT G p1 p2 v1 v2
                                -> option_eq
                                     (fun rv1 rv2
                                      => exists t : base.type, (* TODO: FIXME: This should be the natural type of the rewrite rule, probably *)
                                          match projT1 rv1 as sda1, projT1 rv2 as sda2
                                                return UnderLets _ (@AnyExpr.anyexpr base.type ident (if sda1 then _ else _))
                                                       -> UnderLets _ (@AnyExpr.anyexpr base.type ident (if sda2 then _ else _))
                                                       -> Prop
                                          with
                                          | true, true
                                            => UnderLets.wf
                                                 (fun G' v1 v2
                                                  => exists (pf1 : anyexpr_ty v1 = t) (pf2 : anyexpr_ty v2 = t),
                                                      forall G'',
                                                        (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> wf_value G v1' v2')
                                                        -> expr.wf G''
                                                                   (rew [fun t : base.type => expr t] pf1 in unwrap v1)
                                                                   (rew [fun t : base.type => expr t] pf2 in unwrap v2))
                                                 G
                                          | false, false
                                            => UnderLets.wf (fun G' => wf_anyexpr G' t) G
                                          | true, false | false, true => fun _ _ => False
                                          end (projT2 rv1) (projT2 rv2))
                                     (r1 v1 _ id)
                                     (r2 v2 _ id))).

          (*
        Fixpoint with_bindingsT (p : pattern) (T : Type)
          := match p return Type with
             | pattern.Wildcard t => ptype_interp qforall t (fun eT => eT -> T)
             | pattern.Ident idc
               => match arg_types idc with
                 | Some t => t -> T
                 | None => T
                 end
             | pattern.App f x => with_bindingsT f (with_bindingsT x T)
             end.

        Fixpoint lift_pbase_type_interp_cps {K1 K2} {quant} (F : forall t : base.type, K1 t -> K2 t) {t}
          : pbase_type_interp_cps quant t K1
            -> pbase_type_interp_cps quant t K2
          := match t, quant return pbase_type_interp_cps quant t K1
                                   -> pbase_type_interp_cps quant t K2 with
             | pattern.base.type.any, qforall
               => fun f t => F t (f t)
             | pattern.base.type.any, qexists
               => fun tf => existT _ _ (F _ (projT2 tf))
             | pattern.base.type.type_base t, _
               => F _
             | pattern.base.type.prod A B, _
               => @lift_pbase_type_interp_cps
                   _ _ quant
                   (fun A'
                    => @lift_pbase_type_interp_cps
                        _ _ quant (fun _ => F _) B)
                   A
             | pattern.base.type.list A, _
               => @lift_pbase_type_interp_cps
                   _ _ quant (fun _ => F _) A
             end.

        Fixpoint lift_ptype_interp_cps {K1 K2} {quant} (F : forall t : type.type base.type, K1 t -> K2 t) {t}
          : ptype_interp_cps quant t K1
            -> ptype_interp_cps quant t K2
          := match t return ptype_interp_cps quant t K1
                                   -> ptype_interp_cps quant t K2 with
             | type.base t
               => lift_pbase_type_interp_cps F
             | type.arrow A B
               => @lift_ptype_interp_cps
                   _ _ quant
                   (fun A'
                    => @lift_ptype_interp_cps
                        _ _ quant (fun _ => F _) B)
                   A
             end.

        Fixpoint lift_with_bindings {p} {A B : Type} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
          := match p return with_bindingsT p A -> with_bindingsT p B with
             | pattern.Wildcard t
               => lift_ptype_interp_cps
                   (K1:=fun t => value t -> A)
                   (K2:=fun t => value t -> B)
                   (fun _ f v => F (f v))
             | pattern.Ident idc
               => match arg_types idc as ty
                       return match ty with
                              | Some t => t -> A
                              | None => A
                              end -> match ty with
                                    | Some t => t -> B
                                    | None => B
                                    end
                 with
                 | Some _ => fun f v => F (f v)
                 | None => F
                 end
             | pattern.App f x
               => @lift_with_bindings
                   f _ _
                   (@lift_with_bindings x _ _ F)
             end.

        Fixpoint app_pbase_type_interp_cps {T : Type} {K1 K2 : base.type -> Type}
                 (F : forall t, K1 t -> K2 t -> T)
                 {t}
          : pbase_type_interp_cps qforall t K1
            -> pbase_type_interp_cps qexists t K2 -> T
          := match t return pbase_type_interp_cps qforall t K1
                            -> pbase_type_interp_cps qexists t K2 -> T with
             | pattern.base.type.any
               => fun f tv => F _ (f _) (projT2 tv)
             | pattern.base.type.type_base t
               => fun f v => F _ f v
             | pattern.base.type.prod A B
               => @app_pbase_type_interp_cps
                   _
                   (fun A' => pbase_type_interp_cps qforall B (fun B' => K1 (A' * B')%etype))
                   (fun A' => pbase_type_interp_cps qexists B (fun B' => K2 (A' * B')%etype))
                   (fun A'
                    => @app_pbase_type_interp_cps
                        _
                        (fun B' => K1 (A' * B')%etype)
                        (fun B' => K2 (A' * B')%etype)
                        (fun _ => F _)
                        B)
                   A
             | pattern.base.type.list A
               => @app_pbase_type_interp_cps T (fun A' => K1 (base.type.list A')) (fun A' => K2 (base.type.list A')) (fun _ => F _) A
             end.

        Fixpoint app_ptype_interp_cps {T : Type} {K1 K2 : type -> Type}
                 (F : forall t, K1 t -> K2 t -> T)
                 {t}
          : ptype_interp_cps qforall t K1
            -> ptype_interp_cps qexists t K2 -> T
          := match t return ptype_interp_cps qforall t K1
                            -> ptype_interp_cps qexists t K2 -> T with
             | type.base t => app_pbase_type_interp_cps F
             | type.arrow A B
               => @app_ptype_interp_cps
                   _
                   (fun A' => ptype_interp_cps qforall B (fun B' => K1 (A' -> B')%etype))
                   (fun A' => ptype_interp_cps qexists B (fun B' => K2 (A' -> B')%etype))
                   (fun A'
                    => @app_ptype_interp_cps
                        _
                        (fun B' => K1 (A' -> B')%etype)
                        (fun B' => K2 (A' -> B')%etype)
                        (fun _ => F _)
                        B)
                   A
             end.

        Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
          := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
             | pattern.Wildcard t
               => app_ptype_interp_cps
                   (K1:=fun t => value t -> T)
                   (K2:=fun t => value t)
                   (fun _ f v => f v)
             | pattern.Ident idc
               => match arg_types idc as ty
                       return match ty with
                              | Some t => t -> T
                              | None => T
                              end -> match ty return Type with
                                    | Some t => t
                                    | None => unit
                                    end -> T
                 with
                 | Some t => fun f x => f x
                 | None => fun v 'tt => v
                 end
             | pattern.App f x
               => fun F '(vf, vx)
                 => @app_binding_data _ x (@app_binding_data _ f F vf) vx
             end.

        (** XXX MOVEME? *)
        Definition mkcast {P : type -> Type} {t1 t2 : type} : ~> (option (P t1 -> P t2))
          := fun T k => type.try_make_transport_cps base.try_make_transport_cps P t1 t2 _ k.
        Definition cast {P : type -> Type} {t1 t2 : type} (v : P t1) : ~> (option (P t2))
          := fun T k => type.try_transport_cps base.try_make_transport_cps P t1 t2 v _ k.
        Definition castb {P : base.type -> Type} {t1 t2 : base.type} (v : P t1) : ~> (option (P t2))
          := fun T k => base.try_transport_cps P t1 t2 v _ k.
        Definition castbe {t1 t2 : base.type} (v : expr t1) : ~> (option (expr t2))
          := @castb expr t1 t2 v.
        Definition castv {t1 t2} (v : value t1) : ~> (option (value t2))
          := fun T k => type.try_transport_cps base.try_make_transport_cps value t1 t2 v _ k.
           *)
        End with_var2.
      End with_type.
    End Compile.
  End RewriteRules.
End Compilers.
