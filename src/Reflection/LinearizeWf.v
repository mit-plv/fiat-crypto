(** * Linearize: Place all and only operations in let binders *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation Tbase := (@Tbase base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation wff := (@wff base_type_code op).
  Local Notation wf := (@wf base_type_code op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Local Ltac t_fin_step tac :=
      match goal with
      | _ => assumption
      | _ => progress simpl in *
      | _ => progress subst
      | _ => progress inversion_sigma
      | _ => setoid_rewrite List.in_app_iff
      | [ H : context[List.In _ (_ ++ _)] |- _ ] => setoid_rewrite List.in_app_iff in H
      | _ => progress intros
      | _ => solve [ eauto ]
      | _ => solve [ intuition (subst; eauto) ]
      | [ H : forall (x : prod _ _) (y : prod _ _), _ |- _ ] => specialize (fun x x' y y' => H (x, x') (y, y'))
      | _ => rewrite !List.app_assoc
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : _ |- _ ] => apply H
      | _ => eapply wff_in_impl_Proper; [ solve [ eauto ] | ]
      | _ => progress tac
      | [ |- wff _ _ _ ] => constructor
      | [ |- wf _ _ _ ] => constructor
      end.
    Local Ltac t_fin tac := repeat t_fin_step tac.

    Local Hint Constructors Wf.wff.
    Local Hint Resolve List.in_app_or List.in_or_app.

    Local Ltac small_inversion_helper wf G0 e2 :=
      let t0 := match type of wf with wff (t:=?t0) _ _ _ => t0 end in
      let e1 := match goal with
                | |- context[wff G0 (under_letsf ?e1 _) (under_letsf e2 _)] => e1
                end in
      pattern G0, t0, e1, e2;
      lazymatch goal with
      | [ |- ?retP _ _ _ _ ]
        => first [ refine (match wf in @Wf.wff _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | TT => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfTT _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Wf.wff _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Var _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfVar _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Wf.wff _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Op _ _ _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfOp _ _ _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Wf.wff _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | LetIn _ _ _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfLetIn _ _ _ _ _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end)
                | refine (match wf in @Wf.wff _ _ _ _ G t v1 v2
                                return match v1 return Prop with
                                       | Pair _ _ _ _ => retP G t v1 v2
                                       | _ => forall P : Prop, P -> P
                                       end with
                          | WfPair _ _ _ _ _ _ _ _ _ => _
                          | _ => fun _ p => p
                          end) ]
      end.
    Fixpoint wff_under_letsf G {t} e1 e2 {tC} eC1 eC2
             (wf : @wff var1 var2 G t e1 e2)
             (H : forall (x1 : interp_flat_type var1 t) (x2 : interp_flat_type var2 t),
                 wff (flatten_binding_list x1 x2 ++ G) (eC1 x1) (eC2 x2))
             {struct e1}
      : @wff var1 var2 G tC (under_letsf e1 eC1) (under_letsf e2 eC2).
    Proof.
      revert H.
      set (e1v := e1) in *.
      destruct e1 as [ | | ? ? ? args | tx ex tC0 eC0 | ? ex ? ey ];
        [ clear wff_under_letsf
        | clear wff_under_letsf
        | clear wff_under_letsf
        | generalize (fun G => match e1v return match e1v with LetIn _ _ _ _ => _ | _ => _ end with
                            | LetIn _ ex _ eC => wff_under_letsf G _ ex
                            | _ => I
                            end);
          generalize (fun G => match e1v return match e1v with
                                                | LetIn tx0 _ tC1 e0 => (* 8.4's type inferencer is broken, so we copy/paste the term from 8.5.  This entire clause could just be [_], if Coq 8.4 worked *)
                                                  forall (x : @interp_flat_type base_type_code var1 tx0) (e3 : exprf tC1)
                                                         (tC2 : flat_type) (eC3 : @interp_flat_type base_type_code var1 tC1 -> exprf tC2)
                                                         (eC4 : @interp_flat_type base_type_code var2 tC1 -> exprf tC2),
                                                    wff G (e0 x) e3 ->
                                                    (forall (x1 : @interp_flat_type base_type_code var1 tC1)
                                                            (x2 : @interp_flat_type base_type_code var2 tC1),
                                                        wff (@flatten_binding_list base_type_code var1 var2 tC1 x1 x2 ++ G) (eC3 x1) (eC4 x2)) ->
                                                    wff G (@under_letsf base_type_code op var1 tC1 (e0 x) tC2 eC3)
                                                        (@under_letsf base_type_code op var2 tC1 e3 tC2 eC4)
                                                | _ => _ end with
                               | LetIn _ ex tC' eC => fun x => wff_under_letsf G tC' (eC x)
                               | _ => I
                               end);
          clear wff_under_letsf
        | generalize (fun G => match e1v return match e1v with Pair _ _ _ _ => _ | _ => _ end with
                            | Pair _ ex _ ey => wff_under_letsf G _ ex
                            | _ => I
                            end);
          generalize (fun G => match e1v return match e1v with Pair _ _ _ _ => _ | _ => _ end with
                            | Pair _ ex _ ey => wff_under_letsf G _ ey
                            | _ => I
                            end);
          clear wff_under_letsf ];
        revert eC1 eC2;
        (* alas, Coq's refiner isn't smart enough to figure out these small inversions for us *)
        small_inversion_helper wf G e2;
        t_fin idtac.
    Qed.

    Local Hint Resolve wff_under_letsf.
    Local Hint Constructors or.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.
    Local Hint Resolve wff_SmartVarf.

    Lemma wff_linearizef G {t} e1 e2
      : @wff var1 var2 G t e1 e2
        -> @wff var1 var2 G t (linearizef e1) (linearizef e2).
    Proof.
      induction 1; t_fin ltac:(apply wff_under_letsf).
    Qed.

    Local Hint Resolve wff_linearizef.

    Lemma wf_linearize {t} e1 e2
      : @wf var1 var2 t e1 e2
        -> @wf var1 var2 t (linearize e1) (linearize e2).
    Proof.
      destruct 1; constructor; auto.
    Qed.
  End with_var.

  Lemma Wf_Linearize {t} (e : Expr t) : Wf e -> Wf (Linearize e).
  Proof.
    intros wf var1 var2; apply wf_linearize, wf.
  Qed.
End language.

Hint Resolve Wf_Linearize : wf.
