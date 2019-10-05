Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.SetoidList.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.UnderLets.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
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
  End SubstVarLike.

  Hint Resolve SubstVarLike.Wf_SubstVar SubstVarLike.Wf_SubstVarLike SubstVarLike.Wf_SubstVarOrIdent : wf.
  Hint Rewrite @SubstVarLike.Interp_SubstVar @SubstVarLike.Interp_SubstVarLike @SubstVarLike.Interp_SubstVarOrIdent : interp.

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

        Lemma wf_of_expr {t} (x : @expr var1 t) (y : @expr var2 t)
              G
          : expr.wf G x y -> wf (fun G => expr.wf G) G (of_expr x) (of_expr y).
        Proof.
          intro Hwf; induction Hwf; cbn [of_expr]; repeat constructor; auto.
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

        Lemma wf_splice_list {A1 B1 A2 B2}
              {P_parts : nat -> list { t : type & var1 t * var2 t }%type -> A1 -> A2 -> Prop}
              {P : list { t : type & var1 t * var2 t }%type -> list A1 -> list A2 -> Prop}
              {Q : list { t : type & var1 t * var2 t }%type -> B1 -> B2 -> Prop}
              G
              (x1 : list (@UnderLets var1 A1)) (x2 : list (@UnderLets var2 A2))
              (P_parts_Proper_list : forall n G1 G2 a1 a2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                  -> P_parts n G1 a1 a2 -> P_parts n G2 a1 a2)
              (HP : forall G' l1 l2,
                  (exists seg, G' = seg ++ G) -> length l1 = length x1 -> length l2 = length x2
                  -> (forall n v1 v2, nth_error l1 n = Some v1 -> nth_error l2 n = Some v2 -> P_parts n G' v1 v2)
                  -> P G' l1 l2)
              (Hx_len : length x1 = length x2)
              (Hx : forall n v1 v2, nth_error x1 n = Some v1 -> nth_error x2 n = Some v2 ->@wf _ _ (P_parts n) G v1 v2)
              (e1 : list A1 -> @UnderLets var1 B1) (e2 : list A2 -> @UnderLets var2 B2)
              (He : forall G' a1 a2, (exists seg, G' = seg ++ G) -> P G' a1 a2 -> @wf _ _ Q G' (e1 a1) (e2 a2))
          : @wf _ _ Q G (splice_list x1 e1) (splice_list x2 e2).
        Proof.
          revert dependent P; revert dependent P_parts; revert dependent G; revert dependent e1; revert dependent e2; revert dependent x2;
            induction x1 as [|x1 xs1 IHx1], x2 as [|x2 xs2];
            cbn [splice_list length nth_error]; intros; try congruence.
          { eapply He; [ exists nil; reflexivity | eapply HP; eauto using (ex_intro _ nil) ].
            intros []; cbn [nth_error]; intros; congruence. }
          { inversion Hx_len; clear Hx_len.
            pose proof (fun n => Hx (S n)) as Hxs.
            specialize (Hx O).
            cbn [nth_error] in *.
            eapply wf_splice; [ eapply Hx; reflexivity | wf_safe_t ].
            destruct_head'_ex; subst.
            lazymatch goal with
            | [ |- wf _ _ (splice_list _ (fun _ => ?e1 (?a1 :: _))) (splice_list _ (fun _ => ?e2 (?a2 :: _))) ]
              => eapply IHx1 with (P_parts:=fun n => P_parts (S n)) (P:=fun G' l1 l2 => P G' (a1::l1) (a2::l2))
            end; wf_safe_t; destruct_head'_ex; wf_safe_t.
            { eapply wf_Proper_list; [ | | eapply Hxs ]; wf_t. }
            { eapply HP; cbn [length]; rewrite ?app_assoc; eauto; [].
              intros []; cbn [nth_error]; wf_safe_t; inversion_option; wf_safe_t.
              { eapply P_parts_Proper_list; [ | eauto ]; wf_t. }
              { eapply P_parts_Proper_list; [ | eauto ]; wf_t. } }
            { eapply He; eauto; rewrite ?app_assoc; eauto. } }
        Qed.

        Lemma wf_splice_list_no_order_nth_error {A1 B1 A2 B2}
              {P : list { t : type & var1 t * var2 t }%type -> A1 -> A2 -> Prop}
              {Q : list { t : type & var1 t * var2 t }%type -> B1 -> B2 -> Prop}
              G
              (x1 : list (@UnderLets var1 A1)) (x2 : list (@UnderLets var2 A2))
              (P_Proper_list : forall G1 G2 a1 a2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                  -> P G1 a1 a2 -> P G2 a1 a2)
              (Hx_len : length x1 = length x2)
              (Hx : forall n v1 v2, nth_error x1 n = Some v1 -> nth_error x2 n = Some v2 ->@wf _ _ P G v1 v2)
              (e1 : list A1 -> @UnderLets var1 B1) (e2 : list A2 -> @UnderLets var2 B2)
              (He : forall G' a1 a2, (exists seg, G' = seg ++ G)
                                     -> length a1 = length x1
                                     -> length a2 = length x2
                                     -> (forall v1 v2, List.In (v1, v2) (combine a1 a2) -> P G' v1 v2)
                                     -> @wf _ _ Q G' (e1 a1) (e2 a2))
          : @wf _ _ Q G (splice_list x1 e1) (splice_list x2 e2).
        Proof.
          apply @wf_splice_list
            with (P_parts := fun _ => P)
                 (P:=fun G' l1 l2 => length l1 = length x1 /\ length l2 = length x2
                                     /\ forall v1 v2, List.In (v1, v2) (combine l1 l2) -> P G' v1 v2);
            repeat first [ progress wf_safe_t
                         | apply conj
                         | progress inversion_option
                         | progress destruct_head'_ex
                         | progress break_innermost_match_hyps
                         | match goal with
                           | [ H : In _ (combine _ _) |- _ ] => apply ListUtil.In_nth_error_value in H
                           | [ H : context[nth_error (combine _ _) _] |- _ ]
                             => rewrite ListUtil.nth_error_combine in H
                           end ].
        Qed.

        Lemma wf_splice_list_no_order {A1 B1 A2 B2}
              {P : list { t : type & var1 t * var2 t }%type -> A1 -> A2 -> Prop}
              {Q : list { t : type & var1 t * var2 t }%type -> B1 -> B2 -> Prop}
              G
              (x1 : list (@UnderLets var1 A1)) (x2 : list (@UnderLets var2 A2))
              (P_Proper_list : forall G1 G2 a1 a2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                  -> P G1 a1 a2 -> P G2 a1 a2)
              (Hx : List.Forall2 (wf P G) x1 x2)
              (e1 : list A1 -> @UnderLets var1 B1) (e2 : list A2 -> @UnderLets var2 B2)
              (He : forall G' a1 a2, (exists seg, G' = seg ++ G)
                                     -> length a1 = length x1
                                     -> length a2 = length x2
                                     -> List.Forall2 (P G') a1 a2
                                     -> @wf _ _ Q G' (e1 a1) (e2 a2))
          : @wf _ _ Q G (splice_list x1 e1) (splice_list x2 e2).
        Proof.
          setoid_rewrite Forall2_forall_In_combine_iff in He.
          apply @wf_splice_list_no_order_nth_error with (P:=P); try assumption;
            eauto using eq_length_Forall2.
          { intro n; rewrite Forall2_forall_iff_nth_error in Hx; specialize (Hx n).
            intros; cbv [option_eq] in *; break_innermost_match_hyps; inversion_option; subst; assumption. }
          { rewrite Forall2_forall_In_combine_iff in Hx; destruct Hx.
            intros; eapply He; try apply conj; eauto; congruence. }
        Qed.

        Lemma wf_list_rect {A B Pnil Pcons ls A' B' Pnil' Pcons' ls'} {RA : A -> A' -> Prop} {RB G}
              (Hnil : wf RB G Pnil Pnil')
              (Hcons : forall x x',
                  RA x x'
                  -> forall l l',
                    List.Forall2 RA l l'
                    -> forall rec rec',
                      wf RB G rec rec'
                      -> wf RB G (Pcons x l rec) (Pcons' x' l' rec'))
              (Hls : List.Forall2 RA ls ls')
          : wf RB G
               (list_rect
                  (fun _ : list _ => @UnderLets var1 B)
                  Pnil
                  Pcons
                  ls)
               (list_rect
                  (fun _ : list _ => @UnderLets var2 B')
                  Pnil'
                  Pcons'
                  ls').
        Proof using Type. induction Hls; cbn [list_rect] in *; auto. Qed.

        Lemma wf_list_rect_arrow {T A B PN PC l v T' A' B' PN' PC' l' v' R}
              {RT : T -> T' -> Prop}
              {R' : _ -> A -> A' -> Prop} {G seg G'}
              (Hnil : forall seg G' x x',
                  G' = seg ++ G
                  -> R' seg x x'
                  -> wf R G' (PN x) (PN' x'))
              (Hcons : forall seg G' x x' xs xs' rec rec',
                  G' = seg ++ G
                  -> RT x x'
                  -> List.Forall2 RT xs xs'
                  -> (forall seg' G'' v v',
                         G'' = seg' ++ G'
                         -> R' seg' v v'
                         -> wf R G'' (rec v) (rec' v'))
                  -> forall v v',
                      R' seg v v'
                      -> wf R G' (PC x xs rec v) (PC' x' xs' rec' v'))
              (HR : forall G1 G2,
                  (forall t v1 v2, In (existT _ t (v1, v2)) G1 -> In (existT _ t (v1, v2)) G2)
                  -> forall v1 v2, R G1 v1 v2 -> R G2 v1 v2)
              (Hl : List.Forall2 RT l l')
              (HG : G' = seg ++ G)
              (Hx : R' seg v v')
          : wf
              R G'
              (list_rect (fun _ : list T => A -> @UnderLets var1 B) PN PC l v)
              (list_rect (fun _ : list T' => A' -> @UnderLets var2 B') PN' PC' l' v').
        Proof using Type.
          revert seg G' HG v v' Hx.
          induction Hl as [|x x' xs xs' Hx Hxs IHxs]; cbn [list_rect] in *; eauto.
          intros; subst; eapply Hcons; try eassumption; eauto.
          intros; subst; eapply wf_Proper_list; revgoals; try assumption.
          { eapply IHxs; try eassumption; reflexivity. }
          { wf_t. }
        Qed.

        Lemma wf_nat_rect {A PO PS n A' PO' PS' n' R G}
              (Hnil : wf R G PO PO')
              (Hcons : forall n rec rec',
                  wf R G rec rec'
                  -> wf R G (PS n rec) (PS' n rec'))
              (Hn : n = n')
          : wf R G
               (nat_rect (fun _ => @UnderLets var1 A) PO PS n)
               (nat_rect (fun _ => @UnderLets var2 A') PO' PS' n').
        Proof using Type. subst n'; induction n; cbn [nat_rect] in *; auto. Qed.

        Lemma wf_nat_rect_arrow {A B PO PS n x A' B' PO' PS' n' x' R}
              {R' : _ -> A -> A' -> Prop} {G seg G'}
              (Hnil : forall seg G' x x',
                  G' = seg ++ G
                  -> R' seg x x'
                  -> wf R G' (PO x) (PO' x'))
              (Hcons : forall seg G' n rec rec',
                  G' = seg ++ G
                  -> (forall seg' G'' x x',
                         G'' = seg' ++ G'
                         -> R' seg' x x'
                         -> wf R G'' (rec x) (rec' x'))
                  -> forall x x',
                      R' seg x x'
                      -> wf R G' (PS n rec x) (PS' n rec' x'))
              (HR : forall G1 G2,
                  (forall t v1 v2, In (existT _ t (v1, v2)) G1 -> In (existT _ t (v1, v2)) G2)
                  -> forall v1 v2, R G1 v1 v2 -> R G2 v1 v2)
              (Hn : n = n')
              (HG : G' = seg ++ G)
              (Hx : R' seg x x')
          : wf R G'
               (nat_rect (fun _ => A -> @UnderLets var1 B) PO PS n x)
               (nat_rect (fun _ => A' -> @UnderLets var2 B') PO' PS' n' x').
        Proof using Type.
          subst n'; revert seg G' HG x x' Hx.
          induction n as [|n IHn]; cbn [nat_rect] in *; eauto.
          intros; subst; eapply Hcons; try eassumption; eauto.
          intros; subst; eapply wf_Proper_list; revgoals; try assumption.
          { eapply IHn; try eassumption; reflexivity. }
          { wf_t. }
        Qed.
      End with_var.

      Section with_var2.
        Context {var1 var2 var1' var2' : type -> Type}.

        Lemma wf_flat_map {T1 T2 e1 e2 f1 f2 f'1 f'2 G G'}
              (R : forall t, list _ -> var1' t -> var2' t -> Prop)
              (P : list _ -> T1 -> T2 -> Prop)
              (HR : forall G1 G2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                  -> forall t e1 e2, R t G1 e1 e2 -> R t G2 e1 e2)
              (Hwf : wf P G' e1 e2)
              (Hf : forall G G',
                  (forall t v1 v2,
                      In (existT _ t (v1, v2)) G' -> R t G v1 v2)
                  -> forall t e1 e2,
                    expr.wf G' e1 e2
                    -> wf (fun G' => expr.wf G') G (f1 t e1) (f2 t e2))
              (Hf' : forall t' G' (v1 : var1 t') (v2 : var2 t'),
                  R t' (existT _ t' (v1, v2) :: G') (f'1 t' v1) (f'2 t' v2))
              (HG : forall t' v1' v2',
                  In (existT _ t' (v1', v2')) G'
                  -> R t' G v1' v2')
          : wf
              (fun G e1 e2
               => exists G',
                   (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> R t G v1 v2)
                   /\ P G' e1 e2)
              G
              (@UnderLets.flat_map _ ident var1' ident var1 f1 f'1 T1 e1)
              (@UnderLets.flat_map _ ident var2' ident var2 f2 f'2 T2 e2).
        Proof using Type.
          revert dependent G; induction Hwf; cbn [UnderLets.flat_map]; intros.
          { constructor; hnf; eauto. }
          { eapply @wf_splice; [ eapply Hf; eassumption | ].
            intros; constructor; auto; intros.
            match goal with H : _ |- _ => eapply H end.
            cbn [List.In]; intros; destruct_head'_or; inversion_sigma; inversion_prod; subst; cbn [eq_rect fst snd] in *.
            { apply Hf'. }
            { destruct_head'_ex; subst.
              eapply HR; revgoals; [ eapply HG | ]; wf_t. } }
        Qed.
      End with_var2.

      Section for_interp2.
        Context {base_interp : base_type -> Type}
                (ident_interp : forall t, ident t -> type.interp base_interp t)
                {var : type -> Type}.

        Fixpoint interp_related_gen {T1 T2} (R' : forall t, var t -> type.interp base_interp t -> Prop) (R : T1 -> T2 -> Prop) (e : @UnderLets var T1) (v2 : T2) : Prop
          := match e with
             | Base v1 => R v1 v2
             | UnderLet t e f (* combine the App rule with the Abs rule *)
               => exists fv ev,
                  expr.interp_related_gen ident_interp R' e ev
                  /\ (forall x1 x2,
                         R' _ x1 x2
                         -> @interp_related_gen T1 T2 R' R (f x1) (fv x2))
                  /\ fv ev = v2
             end.

        Lemma to_expr_interp_related_gen_iff (R : forall t, var t -> type.interp base_interp t -> Prop) {t e v}
          : interp_related_gen R (expr.interp_related_gen ident_interp R (t:=t)) e v
            <-> expr.interp_related_gen ident_interp R (UnderLets.to_expr e) v.
        Proof using Type.
          revert v; induction e; cbn [UnderLets.to_expr interp_related_gen expr.interp_related_gen]; try reflexivity.
          setoid_rewrite H.
          reflexivity.
        Qed.

        Lemma of_expr_interp_related_gen_iff (R : forall t, var t -> type.interp base_interp t -> Prop) {t e v}
          : interp_related_gen R (expr.interp_related_gen ident_interp R (t:=t)) (UnderLets.of_expr e) v
            <-> expr.interp_related_gen ident_interp R e v.
        Proof using Type.
          revert v; induction e; cbn [UnderLets.of_expr interp_related_gen expr.interp_related_gen]; try reflexivity.
          setoid_rewrite H.
          reflexivity.
        Qed.

        Global Instance interp_related_gen_Proper_impl {T1 T2 R}
          : Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> eq ==> eq ==> Basics.impl) (@interp_related_gen T1 T2 R) | 10.
        Proof using Type.
          cbv [pointwise_relation respectful Proper].
          intros R1 R2 HR x y ? x' y' H'; subst y y'.
          revert x'; induction x; [ apply HR | ]; cbn [interp_related_gen].
          setoid_rewrite H; reflexivity.
        Qed.

        Global Instance interp_related_gen_Proper_iff {T1 T2 R}
          : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff) (@interp_related_gen T1 T2 R) | 10.
        Proof using Type.
          cbv [pointwise_relation respectful Proper].
          intros R1 R2 HR x y ? x' y' H'; subst y y'.
          revert x'; induction x; [ apply HR | ]; cbn [interp_related_gen].
          setoid_rewrite H; reflexivity.
        Qed.

        Lemma splice_interp_related_gen_iff {A B T R' R x e} {v : T}
          : interp_related_gen R' R (@UnderLets.splice _ ident _ A B x e) v
            <-> interp_related_gen
                  R'
                  (fun xv => interp_related_gen R' R (e xv))
                  x v.
        Proof using Type.
          revert v; induction x; cbn [UnderLets.splice interp_related_gen]; [ reflexivity | ].
          match goal with H : _ |- _ => setoid_rewrite H end.
          reflexivity.
        Qed.

        Lemma splice_list_interp_related_gen_iff_gen {A B T R' R x e1 e2 base} {v : T}
              (He1e2 : forall ls', e1 ls' = e2 (base ++ ls'))
          : interp_related_gen R' R (@UnderLets.splice_list _ ident _ A B x e1) v
            <-> list_rect
                  (fun _ => list _ -> _ -> Prop)
                  (fun ls v => interp_related_gen R' R (e2 ls) v)
                  (fun x xs recP ls v
                   => interp_related_gen
                        R'
                        (fun x' v => recP (ls ++ [x']) v)
                        x
                        v)
                  x
                  base
                  v.
        Proof using Type.
          revert base v e1 e2 He1e2; induction x as [|? ? IHx]; cbn [UnderLets.splice_list interp_related_gen list_rect]; intros.
          { intros; rewrite He1e2, ?app_nil_r; reflexivity. }
          { setoid_rewrite splice_interp_related_gen_iff.
            apply interp_related_gen_Proper_iff; [ | reflexivity.. ]; cbv [pointwise_relation]; intros.
            specialize (fun v => IHx (base ++ [v])).
            setoid_rewrite IHx; [ reflexivity | ].
            intros; rewrite He1e2, <- ?app_assoc; reflexivity. }
        Qed.

        Lemma splice_list_interp_related_gen_iff {A B T R' R x e} {v : T}
          : interp_related_gen R' R (@UnderLets.splice_list _ ident _ A B x e) v
            <-> list_rect
                  (fun _ => list _ -> _ -> Prop)
                  (fun ls v => interp_related_gen R' R (e ls) v)
                  (fun x xs recP ls v
                   => interp_related_gen
                        R'
                        (fun x' v => recP (ls ++ [x']) v)
                        x
                        v)
                  x
                  nil
                  v.
        Proof using Type.
          apply splice_list_interp_related_gen_iff_gen; reflexivity.
        Qed.

        Lemma splice_interp_related_gen_of_ex {A B T T' R' RA RB x e} {v : T}
          : (exists ev (xv : T'),
                interp_related_gen R' RA x xv
                /\ (forall x1 x2,
                       RA x1 x2
                       -> interp_related_gen R' RB (e x1) (ev x2))
                /\ ev xv = v)
            -> interp_related_gen R' RB (@UnderLets.splice _ ident _ A B x e) v.
        Proof using Type.
          revert e v; induction x; cbn [interp_related_gen UnderLets.splice]; intros.
          all: repeat first [ progress destruct_head'_ex
                            | progress destruct_head'_and
                            | progress subst
                            | reflexivity
                            | match goal with
                              | [ H : _ |- _ ] => apply H; clear H
                              end ].
          do 2 eexists; repeat apply conj; [ eassumption | | ]; intros.
          { match goal with H : _ |- _ => apply H; clear H end.
            do 2 eexists; repeat apply conj; try now eauto. }
          { reflexivity. }
        Qed.

        Lemma splice_list_interp_related_gen_of_ex {A B T T' R' RA RB x e} {v : T}
          : (exists ev (xv : list T'),
                    List.Forall2 (interp_related_gen R' RA) x xv
                    /\ (forall x1 x2,
                           List.length x2 = List.length xv
                           -> List.Forall2 RA x1 x2
                           -> interp_related_gen R' RB (e x1) (ev x2))
                    /\ ev xv = v)
            -> interp_related_gen R' RB (@UnderLets.splice_list _ ident _ A B x e) v.
        Proof using Type.
          revert e v; induction x as [|x xs IHxs]; cbn [interp_related_gen UnderLets.splice_list]; intros.
          all: repeat first [ progress destruct_head'_ex
                            | progress destruct_head'_and
                            | progress cbn [List.length] in *
                            | progress subst
                            | reflexivity
                            | match goal with
                              | [ H : List.Forall2 _ nil ?x |- _ ] => is_var x; inversion H; clear H
                              | [ H : List.Forall2 _ (cons _ _) ?x |- _ ] => is_var x; inversion H; clear H
                              | [ |- List.Forall2 _ _ _ ] => constructor
                              | [ H : _ |- _ ] => apply H; clear H
                              end ].
          lazymatch goal with
          | [ H : forall l1 l2, length l2 = S (length _) -> Forall2 _ l1 l2 -> _ |- _ ]
            => specialize (fun l ls l' ls' (pf0 : length _ = _) pf1 pf2 => H (cons l ls) (cons l' ls') (f_equal S pf0) (Forall2_cons _ _ pf1 pf2))
          end.
          eapply splice_interp_related_gen_of_ex; do 2 eexists; repeat apply conj;
            intros; [ eassumption | | ].
          { eapply IHxs.
            do 2 eexists; repeat apply conj; intros;
              [ eassumption | | ].
            { match goal with H : _ |- _ => eapply H; clear H end; eassumption. }
            { reflexivity. } }
          { reflexivity. }
        Qed.

        Lemma list_rect_interp_related_gen {A B Pnil Pcons ls B' Pnil' Pcons' ls' R' R}
              (Hnil : interp_related_gen R' R Pnil Pnil')
              (Hcons : forall x x',
                  expr.interp_related_gen ident_interp R' x x'
                  -> forall l l',
                    List.Forall2 (expr.interp_related_gen ident_interp R') l l'
                    -> forall rec rec',
                      interp_related_gen R' R rec rec'
                      -> interp_related_gen R' R (Pcons x l rec) (Pcons' x' l' rec'))
              (Hls : List.Forall2 (expr.interp_related_gen ident_interp R' (t:=A)) ls ls')
          : interp_related_gen
              R' R
              (list_rect
                 (fun _ : list _ => UnderLets _ B)
                 Pnil
                 Pcons
                 ls)
              (list_rect
                 (fun _ : list _ => B')
                 Pnil'
                 Pcons'
                 ls').
        Proof using Type. induction Hls; cbn [list_rect] in *; auto. Qed.

        Lemma list_rect_arrow_interp_related_gen {A B C Pnil Pcons ls x B' C' Pnil' Pcons' ls' x' R'' R}
              {R' : B -> B' -> Prop}
              (Hnil : forall x x', R' x x' -> interp_related_gen R'' R (Pnil x) (Pnil' x'))
              (Hcons : forall x x',
                  expr.interp_related_gen ident_interp R'' x x'
                  -> forall l l',
                    List.Forall2 (expr.interp_related_gen ident_interp R'') l l'
                    -> forall rec rec',
                      (forall v v', R' v v' -> interp_related_gen R'' R (rec v) (rec' v'))
                      -> forall v v',
                        R' v v'
                        -> interp_related_gen R'' R (Pcons x l rec v) (Pcons' x' l' rec' v'))
              (Hls : List.Forall2 (expr.interp_related_gen ident_interp R'' (t:=A)) ls ls')
              (Hx : R' x x')
          : interp_related_gen
              R'' R
              (list_rect
                 (fun _ : list _ => B -> UnderLets _ C)
                 Pnil
                 Pcons
                 ls
                 x)
              (list_rect
                 (fun _ : list _ => B' -> C')
                 Pnil'
                 Pcons'
                 ls'
                 x').
        Proof using Type. revert x x' Hx; induction Hls; cbn [list_rect] in *; auto. Qed.

        Lemma nat_rect_interp_related_gen {A PO PS n A' PO' PS' n' R' R}
              (Hnil : interp_related_gen R' R PO PO')
              (Hcons : forall n rec rec',
                  interp_related_gen R' R rec rec'
                  -> interp_related_gen R' R (PS n rec) (PS' n rec'))
              (Hn : n = n')
          : interp_related_gen
              R' R
              (nat_rect (fun _ => UnderLets _ A) PO PS n)
              (nat_rect (fun _ => A') PO' PS' n').
        Proof using Type. subst n'; induction n; cbn [nat_rect] in *; auto. Qed.

        Lemma nat_rect_arrow_interp_related_gen {A B PO PS n x A' B' PO' PS' n' x' R'' R}
              {R' : A -> A' -> Prop}
              (Hnil : forall x x', R' x x' -> interp_related_gen R'' R (PO x) (PO' x'))
              (Hcons : forall n rec rec',
                  (forall x x', R' x x' -> interp_related_gen R'' R (rec x) (rec' x'))
                  -> forall x x',
                    R' x x'
                    -> interp_related_gen R'' R (PS n rec x) (PS' n rec' x'))
              (Hn : n = n')
              (Hx : R' x x')
          : interp_related_gen
              R'' R
              (nat_rect (fun _ => A -> UnderLets _ B) PO PS n x)
              (nat_rect (fun _ => A' -> B') PO' PS' n' x').
        Proof using Type. subst n'; revert x x' Hx; induction n; cbn [nat_rect] in *; auto. Qed.

        Lemma interp_related_gen_Proper_impl_same_UnderLets {A B B' R' R1 R2 e v f}
              (HR : forall e v, (R1 e v : Prop) -> (R2 e (f v) : Prop))
          : @interp_related_gen A B R' R1 e v
            -> @interp_related_gen A B' R' R2 e (f v).
        Proof using Type.
          revert f v HR; induction e; cbn [interp_related_gen]; [ now eauto | ]; intros F v HR H'.
          destruct H' as [fv H']; exists (fun ev => F (fv ev)).
          repeat first [ let x := fresh "x" in destruct H' as [x H']; exists x
                       | let x := fresh "x" in intro x; specialize (H' x)
                       | let H := fresh "H" in destruct H' as [H H']; split; [ exact H || now subst | ]
                       | let H := fresh "H" in destruct H' as [H' H]; split; [ | exact H || now subst ] ].
          auto.
        Qed.
      End for_interp2.

      Section for_interp.
        Context {base_interp : base_type -> Type}
                (ident_interp : forall t, ident t -> type.interp base_interp t).

        Local Notation UnderLets := (@UnderLets (type.interp base_interp)).

        Fixpoint interp {T} (v : UnderLets T) : T
          := match v with
             | Base v => v
             | UnderLet A x f => let xv := expr.interp ident_interp x in
                                 @interp _ (f xv)
             end.

        Definition interp_related {T1 T2} (R : T1 -> T2 -> Prop) (e : UnderLets T1) (v2 : T2) : Prop
          := @interp_related_gen base_interp ident_interp _ T1 T2 (fun t => type.eqv) R e v2.

        Lemma interp_splice {A B} (x : UnderLets A) (e : A -> UnderLets B)
          : interp (splice x e) = interp (e (interp x)).
        Proof. induction x; cbn [splice interp]; eauto. Qed.

        Lemma interp_splice_list {A B} (x : list (UnderLets A)) (e : list A -> UnderLets B)
          : interp (splice_list x e)
            = interp (e (List.map interp x)).
        Proof.
          revert e; induction x as [|x xs IHx]; intros; cbn [splice_list interp List.map]; [ reflexivity | ].
          rewrite interp_splice, IHx; reflexivity.
        Qed.

        Lemma interp_to_expr {t} (x : UnderLets (expr t))
          : expr.interp ident_interp (to_expr x) = expr.interp ident_interp (interp x).
        Proof. induction x; cbn [expr.interp interp to_expr]; cbv [LetIn.Let_In]; eauto. Qed.

        Lemma interp_of_expr {t} (x : expr t)
          : expr.interp ident_interp (interp (of_expr x)) = expr.interp ident_interp x.
        Proof. induction x; cbn [expr.interp interp of_expr]; cbv [LetIn.Let_In]; eauto. Qed.

        Lemma to_expr_interp_related_iff {t e v}
          : interp_related (expr.interp_related ident_interp (t:=t)) e v
            <-> expr.interp_related ident_interp (UnderLets.to_expr e) v.
        Proof using Type. apply to_expr_interp_related_gen_iff. Qed.

        Lemma of_expr_interp_related_iff {t e v}
          : interp_related (expr.interp_related ident_interp (t:=t)) (UnderLets.of_expr e) v
            <-> expr.interp_related ident_interp e v.
        Proof using Type. apply of_expr_interp_related_gen_iff. Qed.

        Global Instance interp_related_Proper_impl {T1 T2}
          : Proper (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> eq ==> eq ==> Basics.impl) (@interp_related T1 T2) | 10.
        Proof using Type. apply interp_related_gen_Proper_impl. Qed.

        Global Instance interp_related_Proper_iff {T1 T2}
          : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff) (@interp_related T1 T2) | 10.
        Proof using Type. apply interp_related_gen_Proper_iff. Qed.

        Lemma splice_interp_related_iff {A B T R x e} {v : T}
          : interp_related R (@UnderLets.splice _ ident _ A B x e) v
            <-> interp_related
                  (fun xv => interp_related R (e xv))
                  x v.
        Proof using Type. apply splice_interp_related_gen_iff. Qed.

        Lemma splice_list_interp_related_iff_gen {A B T R x e1 e2 base} {v : T}
              (He1e2 : forall ls', e1 ls' = e2 (base ++ ls'))
          : interp_related R (@UnderLets.splice_list _ ident _ A B x e1) v
            <-> list_rect
                  (fun _ => list _ -> _ -> Prop)
                  (fun ls v => interp_related R (e2 ls) v)
                  (fun x xs recP ls v
                   => interp_related
                        (fun x' v => recP (ls ++ [x']) v)
                        x
                        v)
                  x
                  base
                  v.
        Proof using Type. now apply splice_list_interp_related_gen_iff_gen. Qed.

        Lemma splice_list_interp_related_iff {A B T R x e} {v : T}
          : interp_related R (@UnderLets.splice_list _ ident _ A B x e) v
            <-> list_rect
                  (fun _ => list _ -> _ -> Prop)
                  (fun ls v => interp_related R (e ls) v)
                  (fun x xs recP ls v
                   => interp_related
                        (fun x' v => recP (ls ++ [x']) v)
                        x
                        v)
                  x
                  nil
                  v.
        Proof using Type. apply splice_list_interp_related_gen_iff. Qed.

        Lemma splice_interp_related_of_ex {A B T T' RA RB x e} {v : T}
          : (exists ev (xv : T'),
                interp_related RA x xv
                /\ (forall x1 x2,
                       RA x1 x2
                       -> interp_related RB (e x1) (ev x2))
                /\ ev xv = v)
            -> interp_related RB (@UnderLets.splice _ ident _ A B x e) v.
        Proof using Type. apply splice_interp_related_gen_of_ex. Qed.

        Lemma splice_list_interp_related_of_ex {A B T T' RA RB x e} {v : T}
          : (exists ev (xv : list T'),
                    List.Forall2 (interp_related RA) x xv
                    /\ (forall x1 x2,
                           List.length x2 = List.length xv
                           -> List.Forall2 RA x1 x2
                           -> interp_related RB (e x1) (ev x2))
                    /\ ev xv = v)
            -> interp_related RB (@UnderLets.splice_list _ ident _ A B x e) v.
        Proof using Type. apply splice_list_interp_related_gen_of_ex. Qed.

        Lemma list_rect_interp_related {A B Pnil Pcons ls B' Pnil' Pcons' ls' R}
              (Hnil : interp_related R Pnil Pnil')
              (Hcons : forall x x',
                  expr.interp_related ident_interp x x'
                  -> forall l l',
                    List.Forall2 (expr.interp_related ident_interp) l l'
                    -> forall rec rec',
                      interp_related R rec rec'
                      -> interp_related R (Pcons x l rec) (Pcons' x' l' rec'))
              (Hls : List.Forall2 (expr.interp_related ident_interp (t:=A)) ls ls')
          : interp_related
              R
              (list_rect
                 (fun _ : list _ => UnderLets B)
                 Pnil
                 Pcons
                 ls)
              (list_rect
                 (fun _ : list _ => B')
                 Pnil'
                 Pcons'
                 ls').
        Proof using Type. now apply list_rect_interp_related_gen. Qed.

        Lemma list_rect_arrow_interp_related {A B C Pnil Pcons ls x B' C' Pnil' Pcons' ls' x' R}
              {R' : B -> B' -> Prop}
              (Hnil : forall x x', R' x x' -> interp_related R (Pnil x) (Pnil' x'))
              (Hcons : forall x x',
                  expr.interp_related ident_interp x x'
                  -> forall l l',
                    List.Forall2 (expr.interp_related ident_interp) l l'
                    -> forall rec rec',
                      (forall v v', R' v v' -> interp_related R (rec v) (rec' v'))
                      -> forall v v',
                        R' v v'
                        -> interp_related R (Pcons x l rec v) (Pcons' x' l' rec' v'))
              (Hls : List.Forall2 (expr.interp_related ident_interp (t:=A)) ls ls')
              (Hx : R' x x')
          : interp_related
              R
              (list_rect
                 (fun _ : list _ => B -> UnderLets C)
                 Pnil
                 Pcons
                 ls
                 x)
              (list_rect
                 (fun _ : list _ => B' -> C')
                 Pnil'
                 Pcons'
                 ls'
                 x').
        Proof using Type. eapply list_rect_arrow_interp_related_gen; now eauto. Qed.

        Lemma nat_rect_interp_related {A PO PS n A' PO' PS' n' R}
              (Hnil : interp_related R PO PO')
              (Hcons : forall n rec rec',
                  interp_related R rec rec'
                  -> interp_related R (PS n rec) (PS' n rec'))
              (Hn : n = n')
          : interp_related
              R
              (nat_rect (fun _ => UnderLets A) PO PS n)
              (nat_rect (fun _ => A') PO' PS' n').
        Proof using Type. now apply nat_rect_interp_related_gen. Qed.

        Lemma nat_rect_arrow_interp_related {A B PO PS n x A' B' PO' PS' n' x' R}
              {R' : A -> A' -> Prop}
              (Hnil : forall x x', R' x x' -> interp_related R (PO x) (PO' x'))
              (Hcons : forall n rec rec',
                  (forall x x', R' x x' -> interp_related R (rec x) (rec' x'))
                  -> forall x x',
                    R' x x'
                    -> interp_related R (PS n rec x) (PS' n rec' x'))
              (Hn : n = n')
              (Hx : R' x x')
          : interp_related
              R
              (nat_rect (fun _ => A -> UnderLets B) PO PS n x)
              (nat_rect (fun _ => A' -> B') PO' PS' n' x').
        Proof using Type. eapply nat_rect_arrow_interp_related_gen; now eauto. Qed.

        Lemma interp_related_Proper_impl_same_UnderLets {A B B' R1 R2 e v f}
              (HR : forall e v, (R1 e v : Prop) -> (R2 e (f v) : Prop))
          : @interp_related A B R1 e v
            -> @interp_related A B' R2 e (f v).
        Proof using Type. now apply interp_related_gen_Proper_impl_same_UnderLets. Qed.

        Lemma eqv_of_interp_related {t e v}
          : interp_related (expr.interp_related (@ident_interp)) e v
            -> @type.eqv t (expr.interp ident_interp (interp e)) v.
        Proof using Type.
          induction e; cbn [interp_related interp_related_gen interp type.related]; intros; destruct_head'_ex; destruct_head'_and; subst.
          { now apply expr.eqv_of_interp_related. }
          { repeat match goal with H : _ |- _ => apply H end.
            now apply expr.eqv_of_interp_related. }
        Qed.
      End for_interp.

      Section for_interp2'.
        Context {base_interp1 base_interp2 : base_type -> Type}
                {ident_interp1 : forall t, ident t -> type.interp base_interp1 t}
                {ident_interp2 : forall t, ident t -> type.interp base_interp2 t}.

        Lemma wf_interp_Proper {T1 T2}
              {P : list { t : type & type.interp base_interp1 t * type.interp base_interp2 t }%type -> T1 -> T2 -> Prop}
              {G v1 v2}
              (Hwf : @wf _ _ T1 T2 P G v1 v2)
          : exists seg, P (seg ++ G) (interp ident_interp1 v1) (interp ident_interp2 v2).
        Proof using Type.
          induction Hwf; [ exists nil; cbn [List.app]; assumption | ].
          let H := match goal with H : forall v1 v2, ex _ |- _ => H end in
          edestruct H as [seg ?]; eexists (seg ++ [_]).
          rewrite <- List.app_assoc; cbn [List.app].
          eassumption.
        Qed.
      End for_interp2'.

      Section with_var2_for_interp.
        Context {base_interp : base_type -> Type}
                {ident_interp : forall t, ident t -> type.interp base_interp t}
                {var1 var2 : type -> Type}.

        Lemma flat_map_interp_related_iff
              {T1 T2} f f' R'' R' R e v
              (Hf : forall t e v, expr.interp_related_gen ident_interp R'' e v -> interp_related_gen ident_interp R' (expr.interp_related_gen ident_interp R') (f t e) v)
              (Hf' : forall t e v, R' t e v -> R'' t (f' t e) v)
              (He : @interp_related_gen _ ident_interp _ _ _ R'' R e v)
          : @interp_related_gen
              _ ident_interp _ _ T2 R' R
              (@flat_map _ ident var1 ident var2 f f' T1 e)
              v.
        Proof using Type.
          revert dependent v; induction e as [|? ? ? IHe]; cbn [flat_map interp_related_gen] in *; intros; [ assumption | ].
          repeat first [ progress destruct_head'_ex
                       | progress destruct_head'_and
                       | progress subst
                       | eapply splice_interp_related_gen_of_ex; do 2 eexists; repeat apply conj;
                         [ eapply Hf | | reflexivity ]
                       | solve [ auto ]
                       | progress intros
                       | match goal with
                         | [ |- interp_related_gen _ _ _ (UnderLet _ _) _ ]
                           => cbn [interp_related_gen]; do 2 eexists; repeat apply conj;
                              [ | | reflexivity ]
                         end ].
        Qed.
      End with_var2_for_interp.
    End with_ident.

    Section reify.
      Context {base : Type}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Context {ident : type -> Type}
              {base_interp : base -> Type}
              {base_beq : base -> base -> bool}
              {reflect_base_beq : Reflect.reflect_rel (@eq base) base_beq}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base}
              {invertIdent : @InvertIdentT base base_interp ident}
              {buildIdent : @ident.BuildIdentT base base_interp ident}
              {buildInvertIdentCorrect : BuildInvertIdentCorrectT}
              {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}.
      Local Notation UnderLets := (@UnderLets base_type ident).
      Context (ident_is_var_like : forall t, ident t -> bool).
      Let type_base (x : base) : @base.type base := base.type.type_base x.
      Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base' : base.type >-> type.type.
      Local Coercion type_base : base >-> base.type.

      Section with_var.
        Context {var1 var2 : type -> Type}.
        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Local Notation UnderLets1 := (@UnderLets.UnderLets base_type ident var1).
        Local Notation UnderLets2 := (@UnderLets.UnderLets base_type ident var2).

        Local Ltac wf_reify_and_let_binds_base_cps_t_step Hk :=
          first [ lazymatch goal with
                  | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e1 = Some _, H'' : reflect_list ?e2 = None |- _ ]
                    => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                  | [ H : expr.wf _ ?e1 ?e2, H' : reflect_list ?e2 = Some _, H'' : reflect_list ?e1 = None |- _ ]
                    => apply expr.wf_reflect_list in H; rewrite H', H'' in H; exfalso; clear -H; intuition congruence
                  | [ H : expr.wf _ (reify_list _) (reify_list _) |- _ ] => apply expr.wf_reify_list in H
                  | [ H : List.Forall2 _ ?xs ?ys |- _ ]
                    => match xs with nil => idtac | _::_ => idtac end;
                       match ys with nil => idtac | _::_ => idtac end;
                       inversion H; clear H
                  end
                | progress subst
                | progress destruct_head' False
                | progress expr.inversion_wf_constr
                | progress expr.inversion_expr
                | progress expr.invert_subst
                | progress destruct_head'_sig
                | progress destruct_head'_ex
                | progress destruct_head'_and
                | progress inversion_type
                | progress cbn [eq_rect f_equal f_equal2 type.decode fst snd projT1 projT2 Option.bind combine list_rect length] in *
                | progress cbv [CPSNotations.cps_option_bind CPSNotations.cpsreturn CPSNotations.cpsbind CPSNotations.cpscall id] in *
                | progress rewrite_type_transport_correct
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
                  | [ H : Forall2 (expr.wf _) ?xs ?ys |- Forall2 (expr.wf _) ?xs ?ys ]
                    => eapply Forall2_Proper_impl; [ .. | exact H ]; repeat intro; try reflexivity
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
        Local Ltac wf_reify_and_let_binds_base_cps_t Hk := repeat wf_reify_and_let_binds_base_cps_t_step Hk.

        Lemma wf_reify_and_let_binds_base_cps {t : base_type} {T1 T2} (e1 : expr1 (type.base t)) (e2 : expr2 (type.base t))
              (k1 : expr1 (type.base t) -> UnderLets1 T1) (k2 : expr2 (type.base t) -> UnderLets2 T2)
              (P : _ -> _ -> _ -> Prop) G
              (Hwf : expr.wf G e1 e2)
              (Hk : forall G' e1 e2, (exists seg, G' = seg ++ G) -> expr.wf G' e1 e2 -> wf P G' (k1 e1) (k2 e2))
          : wf P G (reify_and_let_binds_base_cps ident_is_var_like e1 T1 k1) (reify_and_let_binds_base_cps ident_is_var_like e2 T2 k2).
        Proof.
          revert dependent G; induction t; cbn [reify_and_let_binds_base_cps]; intros;
            cbv [option_rect];
            try erewrite !SubstVarLike.wfT_is_recursively_var_or_ident by eassumption;
            break_innermost_match; wf_reify_and_let_binds_base_cps_t Hk; eauto.
          all: repeat match goal with H : list (sigT _) |- _ => revert dependent H end.
          all: revert dependent k1; revert dependent k2.
          all: lazymatch goal with
               | [ |- context[List.Forall2 _ ?l1 ?l2] ]
                 => is_var l1; is_var l2; revert dependent l2; induction l1; intro l2; destruct l2; intros
               end;
            wf_reify_and_let_binds_base_cps_t Hk.
        Qed.

        Lemma wf_let_bind_return {t} (e1 : expr1 t) (e2 : expr2 t)
              G
              (Hwf : expr.wf G e1 e2)
          : expr.wf G (let_bind_return ident_is_var_like e1) (let_bind_return ident_is_var_like e2).
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

      Section with_interp.
        Context {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}
                {ident_interp_Proper : forall t : type, Proper (eq ==> type.eqv) (ident_interp t)}.
        Context {buildInterpIdentCorrect : ident.BuildInterpIdentCorrectT ident_interp}.
        Local Notation interp := (expr.interp (@ident_interp)).
        (*Local Notation Interp := (@expr.Interp _ _ _ (@ident_interp)).*)

        Lemma interp_reify_and_let_binds_base_cps
              {t e T k}
              (P : T -> Prop)
              (Hk : forall e', interp e' = interp e -> P (UnderLets.interp (@ident_interp) (k e')))
          : P (UnderLets.interp (@ident_interp) (reify_and_let_binds_base_cps ident_is_var_like (t:=t) e T k)).
        Proof using buildInvertIdentCorrect try_make_transport_base_cps_correct.
          clear buildInterpIdentCorrect.
          revert T k P Hk; induction t; cbn [reify_and_let_binds_base_cps]; intros;
            cbv [option_rect]; break_innermost_match;
            expr.invert_subst; cbn [type.related UnderLets.interp fst snd expr.interp] in *; subst; eauto;
              repeat first [ progress intros
                           | reflexivity
                           | progress cbn [expr.interp List.map]
                           | apply (f_equal2 (@pair _ _))
                           | apply (f_equal2 (@cons _))
                           | apply (f_equal (@Some _))
                           | match goal with
                             | [ H : _ |- _ ] => apply H; clear H
                             | [ H : context[interp (reify_list _)] |- _ ]
                               => rewrite expr.interp_reify_list in H
                             | [ H : SubstVarLike.is_recursively_var_or_ident _ _ = _ |- _ ] => clear H
                             | [ |- ?Q (UnderLets.interp _ (list_rect ?P ?X ?Y ?ls ?k)) ]
                               => is_var ls; is_var k;
                                  revert dependent k; induction ls; cbn [list_rect];
                                  [ | generalize dependent (list_rect P X Y) ]; intros
                             | [ |- ?x = ?y :> unit ] => destruct x, y; reflexivity
                             | [ |- context[reify_list (_ :: _)] ] => rewrite expr.reify_list_cons
                             end
                           | progress cbn [type.interp base.interp] in *
                           | congruence ].
        Qed.

        Lemma interp_reify_and_let_binds_base
              {t e}
          : interp (UnderLets.interp (@ident_interp) (reify_and_let_binds_base_cps ident_is_var_like (t:=t) e _ UnderLets.Base))
            = interp e.
        Proof using buildInvertIdentCorrect try_make_transport_base_cps_correct.
          eapply interp_reify_and_let_binds_base_cps; cbn [UnderLets.interp].
          trivial.
        Qed.

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
                       | progress inversion_type
                       | progress cbn [eq_rect f_equal f_equal2 type.decode fst snd projT1 projT2 invert_pair Option.bind to_expr expr.interp type.eqv length list_rect combine In] in *
                       | progress cbv [CPSNotations.cps_option_bind CPSNotations.cpsreturn CPSNotations.cpsbind CPSNotations.cpscall id] in *
                       | progress rewrite_type_transport_correct
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
                         | [ |- ?R' (expr.interp _ ?e1) (expr.interp _ ?e2) ]
                           => solve [ unshelve eapply (expr.wf_interp_Proper_gen1 (R:=fun _ => eq) _ _ e1 e2); shelve_unifiable; eauto ]
                         | [ H : context[reflect_list (reify_list _)] |- _ ] => rewrite expr.reflect_reify_list in H
                         | [ H : forall x y, @?A x y \/ @?B x y -> @?C x y |- _ ]
                           => pose proof (fun x y pf => H x y (or_introl pf));
                              pose proof (fun x y pf => H x y (or_intror pf));
                              clear H
                         | [ H : List.Forall2 _ ?xs ?ys |- _ ]
                           => match xs with nil => idtac | _::_ => idtac end;
                              match ys with nil => idtac | _::_ => idtac end;
                              inversion H; clear H
                         | [ |- @eq unit ?x ?y ] => case x; case y; reflexivity
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

        Lemma interp_to_expr_reify_and_let_binds_base_cps {t : base_type} {t' : base_type} (e1 : expr (type.base t)) (e2 : expr (type.base t))
              G
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
              (Hwf : expr.wf G e1 e2)
              (k1 : expr (type.base t) -> UnderLets _ (expr (type.base t')))
              (k2 : base.interp base_interp t -> base.interp base_interp t')
              (Hk : forall e1 v, interp e1 == v -> interp (to_expr (k1 e1)) == k2 v)
          : interp (to_expr (reify_and_let_binds_base_cps ident_is_var_like e1 _ k1)) == k2 (interp e2).
        Proof using buildInvertIdentCorrect ident_interp_Proper try_make_transport_base_cps_correct.
          revert dependent G; revert dependent t'; induction t; cbn [reify_and_let_binds_base_cps]; intros;
            cbv [option_rect];
            try erewrite !SubstVarLike.wfT_is_recursively_var_or_ident by eassumption;
            break_innermost_match; interp_to_expr_reify_and_let_binds_base_cps_t Hk.
          all: repeat match goal with H : list (sigT _) |- _ => revert dependent H end.
          all: revert dependent k1; revert dependent k2.
          all: lazymatch goal with
               | [ |- context[List.Forall2 _ ?l1 ?l2 ] ]
                 => is_var l1; is_var l2; revert dependent l2; induction l1; intro l2; destruct l2; intros
               end;
            interp_to_expr_reify_and_let_binds_base_cps_t Hk.
        Qed.

        Lemma interp_let_bind_return {t} (e1 e2 : expr t)
              G
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
              (Hwf : expr.wf G e1 e2)
          : interp (let_bind_return ident_is_var_like e1) == interp e2.
        Proof using buildInvertIdentCorrect ident_interp_Proper try_make_transport_base_cps_correct.
          revert dependent G; induction t; intros; cbn [let_bind_return type.eqv expr.interp] in *; cbv [invert_Abs respectful] in *;
            repeat first [ progress wf_safe_t
                         | progress expr.invert_subst
                         | progress expr.invert_match
                         | progress expr.inversion_wf
                         | progress break_innermost_match_hyps
                         | progress destruct_head'_False
                         | solve [ wf_t ]
                         | match goal with
                           | [ H : _ |- expr.interp _ (let_bind_return _ ?e0) == expr.interp _ ?e ?v ]
                             => eapply (H e0 (e @ $v)%expr (cons _ _)); [ .. | solve [ wf_t ] ]; solve [ wf_t ]
                           | [ H : _ |- expr.interp _ (let_bind_return _ ?e0) == expr.interp _ ?e ?v ]
                             => cbn [expr.interp]; eapply H; [ | solve [ wf_t ] ]; solve [ wf_t ]
                           end ];
            [].
          { epose (P := fun t => { e1e2 : expr t * expr t | expr.wf G (fst e1e2) (snd e1e2) }).
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
                           | solve [ eapply expr.wf_interp_Proper_gen1; eauto ] ].
            all: eapply interp_to_expr_reify_and_let_binds_base_cps with (k1:=Base) (k2:=(fun x => x)); eauto; wf_safe_t. }
        Qed.

        Ltac recurse_interp_related_step :=
          let do_replace v :=
              ((tryif is_evar v then fail else idtac);
               let v' := open_constr:(_) in
               let v'' := fresh in
               cut (v = v'); [ generalize v; intros v'' ?; subst v'' | symmetry ]) in
          match goal with
          | _ => progress cbv [expr.interp_related] in *
          | _ => progress cbn [type.interp]
          | [ |- context[(fst ?x, snd ?x)] ] => progress eta_expand
          | [ |- context[match ?x with pair a b => _ end] ] => progress eta_expand
          | [ |- expr.interp_related_gen ?ident_interp ?R ?f ?v ]
            => do_replace v
          | [ |- exists (fv : ?T1 -> ?T2) (ev : ?T1),
                _ /\ _ /\ fv ev = ?x ]
            => first [ do_replace x
                     | is_evar x; do 2 eexists; repeat apply conj; [ | | reflexivity ] ]
          | _ => progress intros
          | [ |- expr.interp_related_gen _ _ _ ?ev ] => is_evar ev; eassumption
          | [ |- expr.interp_related_gen _ _ (?f @ ?x) ?ev ]
            => is_evar ev;
               let fh := fresh in
               let xh := fresh in
               set (fh := f); set (xh := x); cbn [expr.interp_related_gen]; subst fh xh;
               do 2 eexists; repeat apply conj; [ | | reflexivity ]
          | [ |- expr.interp_related_gen _ _ (expr.Abs ?f) _ ]
            => let fh := fresh in set (fh := f); cbn [expr.interp_related_gen]; subst fh
          | [ |- expr.interp_related_gen _ _ (expr.Ident ?idc) ?ev ]
            => is_evar ev;
               cbn [expr.interp_related_gen]; apply ident_interp_Proper; reflexivity
          | [ H : ?x == _ |- ?x == _ ] => exact H
          | [ |- ?x = ?y ] => tryif first [ has_evar x | has_evar y ] then fail else (progress subst)
          | [ |- ?x = ?x ] => tryif has_evar x then fail else reflexivity
          | [ |- ?ev = _ ] => is_evar ev; reflexivity
          | [ |- _ = ?ev ] => is_evar ev; reflexivity
          | [ |- ?x = ?y :> unit ] => case x; case y; reflexivity
          | [ |- ?G ] => tryif has_evar G then fail else rewrite ident.interp_ident_cons
          end.

        Local Ltac do_interp_related :=
          repeat first [ progress cbv beta
                       | progress recurse_interp_related_step
                       | match goal with
                         | [ x : type.interp (base.interp base_interp) (type.base ()) |- _ ] => destruct x
                         end
                       | eassumption
                       | do 2 eexists; repeat apply conj; intros
                       | match goal with
                         | [ H : _ |- _ ] => apply H; clear H; solve [ do_interp_related ]
                         end ].

        Lemma reify_and_let_binds_base_interp_related_of_ex {t e T k T' R} {v : T'}
          : (exists kv xv,
                expr.interp_related (@ident_interp) e xv
                /\ (forall x1 x2,
                       expr.interp_related (@ident_interp) x1 x2
                       -> interp_related (@ident_interp) R (k x1) (kv x2))
                /\ kv xv = v)
            -> interp_related (@ident_interp) R (reify_and_let_binds_base_cps ident_is_var_like (t:=t) e T k) v.
        Proof using buildInterpIdentCorrect buildInvertIdentCorrect ident_interp_Proper try_make_transport_base_cps_correct.
          cbv [expr.interp_related]; revert T T' k R v; induction t.
          all: repeat first [ progress cbn [expr.interp_related_gen interp_related reify_and_let_binds_base_cps fst snd] in *
                            | progress cbv [expr.interp_related option_rect] in *
                            | progress intros
                            | assumption
                            | progress destruct_head'_ex
                            | progress destruct_head'_and
                            | break_innermost_match_step
                            | progress expr.invert_subst
                            | solve [ eauto ]
                            | solve [ do_interp_related ]
                            | match goal with
                              | [ H : expr.interp_related_gen ?ii _ (reify_list ?ls1) ?ls2 |- _ ] => change (expr.interp_related ii (reify_list ls1) ls2) in H; rewrite expr.reify_list_interp_related_iff in H
                              end ].
          all: match goal with
               | [ H : SubstVarLike.is_recursively_var_or_ident _ _ = _ |- _ ] => clear H
               end.
          all: lazymatch goal with
               | [ H : List.Forall2 _ ?ls1 ?ls2
                   |- interp_related _ _
                                     (list_rect ?Pv ?Nv ?Cv ?ls1 ?k)
                                     (?f ?ls2) ]
                 => let P := fresh "P" in
                    let N := fresh "N" in
                    let C := fresh "C" in
                    is_var k; is_var f; is_var ls1; is_var ls2;
                      set (P:=Pv); set (N:=Nv); set (C:=Cv);
                        revert dependent f; intro f; revert dependent k; intro k; revert f k;
                          induction H; cbn [list_rect]; intros
               end.
          all: repeat match goal with
                      | [ F := ?f |- _ ]
                        => match goal with
                           | [ |- context G[F ?x] ]
                             => let G' := context G[f x] in
                                change G'; cbv beta
                           end
                      | [ H : forall x1 x2, ?R x1 x2 -> ?R' (?f1 x1) (?f2 x2) |- ?R' (?f1 _) (?f2 _) ]
                        => apply H; clear H
                      | [ |- expr.interp_related_gen _ _ _ nil ] => reflexivity
                      | [ H : _ |- interp_related _ _ (reify_and_let_binds_base_cps _ _ _ _) _ ] => apply H
                      | [ |- exists kv xv, _ /\ _ /\ kv xv = ?f (?x :: ?xs) ]
                        => exists (fun x' => f (x' :: xs)), x; repeat apply conj; [ | | reflexivity ]
                      | _ => assumption
                      | _ => progress intros
                      | [ IH : (forall k k', _ -> ?R (list_rect ?P ?N ?C ?ls1 k') (k ?ls2))
                          |- ?R (list_rect ?P ?N ?C ?ls1 ?k'v) ?RHS ]
                        => let kv := match (eval pattern ls2 in RHS) with ?kv _ => kv end in
                           apply (IH kv k'v); clear IH
                      | _ => solve [ do_interp_related ]
                      end.
        Qed.

        Lemma reify_and_let_binds_base_interp_related {t e v}
          : expr.interp_related (@ident_interp) e v
            -> interp_related (@ident_interp) (expr.interp_related (@ident_interp)) (reify_and_let_binds_base_cps ident_is_var_like (t:=t) e _ Base) v.
        Proof using buildInterpIdentCorrect buildInvertIdentCorrect ident_interp_Proper try_make_transport_base_cps_correct.
          intro; eapply reify_and_let_binds_base_interp_related_of_ex.
          eexists id, _; eauto.
        Qed.

        Lemma Interp_LetBindReturn {t} (e : expr.Expr t) (Hwf : expr.Wf e) : expr.Interp ident_interp (LetBindReturn ident_is_var_like e) == expr.Interp ident_interp e.
        Proof using buildInvertIdentCorrect ident_interp_Proper try_make_transport_base_cps_correct.
          apply interp_let_bind_return with (G:=nil); cbn [List.In]; eauto; tauto.
        Qed.
      End with_interp.

      Lemma Wf_LetBindReturn {t} (e : expr.Expr t) (Hwf : expr.Wf e) : expr.Wf (LetBindReturn ident_is_var_like e).
      Proof. intros ??; apply wf_let_bind_return, Hwf. Qed.
    End reify.
  End UnderLets.

  Hint Resolve UnderLets.Wf_LetBindReturn : wf.
  Hint Rewrite @UnderLets.Interp_LetBindReturn : interp.
End Compilers.
