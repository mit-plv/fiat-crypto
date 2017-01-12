Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation wff := (@wff base_type_code op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.
    Local Hint Constructors Wf.wff.

    Lemma wff_app' {g G0 G1 t e1 e2}
          (wf : @wff var1 var2 (G0 ++ G1) t e1 e2)
      : wff (G0 ++ g ++ G1) e1 e2.
    Proof.
      rewrite !List.app_assoc.
      revert wf; remember (G0 ++ G1)%list as G eqn:?; intro wf.
      revert dependent G0. revert dependent G1.
      induction wf; simpl in *; constructor; simpl; eauto.
      { subst; rewrite !List.in_app_iff in *; intuition. }
      { intros; subst.
        rewrite !List.app_assoc; eauto using List.app_assoc. }
    Qed.

    Lemma wff_app_pre {g G t e1 e2}
          (wf : @wff var1 var2 G t e1 e2)
      : wff (g ++ G) e1 e2.
    Proof.
      apply (@wff_app' _ nil); assumption.
    Qed.

    Lemma wff_app_post {g G t e1 e2}
          (wf : @wff var1 var2 G t e1 e2)
      : wff (G ++ g) e1 e2.
    Proof.
      pose proof (@wff_app' g G nil t e1 e2) as H.
      rewrite !List.app_nil_r in *; auto.
    Qed.

    Lemma wff_in_impl_Proper G0 G1 {t} e1 e2
      : @wff var1 var2 G0 t e1 e2
        -> (forall x, List.In x G0 -> List.In x G1)
        -> @wff var1 var2 G1 t e1 e2.
    Proof.
      intro wf; revert G1; induction wf;
        repeat match goal with
               | _ => setoid_rewrite List.in_app_iff
               | _ => progress intros
               | _ => progress simpl in *
               | [ |- wff _ _ _ ] => constructor
               | [ H : _ |- _ ] => apply H
               | _ => solve [ intuition eauto ]
               end.
    Qed.

    Local Hint Resolve List.in_app_or List.in_or_app.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.

    Lemma wff_SmartVarf {t} x1 x2
      : @wff var1 var2 (flatten_binding_list x1 x2) t (SmartVarf x1) (SmartVarf x2).
    Proof.
      unfold SmartVarf.
      induction t; simpl; constructor; eauto.
    Qed.

    Local Hint Resolve wff_SmartVarf.

    Lemma wff_SmartVarVarf G {t t'} v1 v2 x1 x2
          (Hin : List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x1, x2))
                          (flatten_binding_list (SmartVarVarf v1) (SmartVarVarf v2)))
      : @wff var1 var2 (flatten_binding_list (t:=t') v1 v2 ++ G) (Tbase t) x1 x2.
    Proof.
      revert dependent G; induction t'; intros; simpl in *; try tauto.
      { intuition (inversion_sigma; inversion_prod; subst; simpl; eauto).
        constructor; eauto. }
      { unfold SmartVarVarf in *; simpl in *.
        apply List.in_app_iff in Hin.
        intuition (inversion_sigma; inversion_prod; subst; eauto).
        { rewrite <- !List.app_assoc; eauto. } }
    Qed.

    Lemma wff_SmartVarVarf_nil {t t'} v1 v2 x1 x2
          (Hin : List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x1, x2))
                          (flatten_binding_list (SmartVarVarf v1) (SmartVarVarf v2)))
      : @wff var1 var2 (flatten_binding_list (t:=t') v1 v2) (Tbase t) x1 x2.
    Proof.
      apply wff_SmartVarVarf with (G:=nil) in Hin.
      rewrite List.app_nil_r in Hin; assumption.
    Qed.

    Lemma In_G_wff_SmartVarf G t v1 v2 e
          (Hwf : @wff var1 var2 G t (SmartVarf v1) (SmartVarf v2))
          (Hin : List.In e (flatten_binding_list v1 v2))
      : List.In e G.
    Proof.
      induction t;
        repeat match goal with
               | _ => assumption
               | [ H : False |- _ ] => exfalso; assumption
               | _ => progress subst
               | _ => progress destruct_head' and
               | [ H : context[List.In _ (_ ++ _)] |- _ ] => rewrite List.in_app_iff in H
               | [ H : context[SmartVarf _] |- _ ] => rewrite SmartVarf_Pair in H
               | _ => progress simpl in *
               | _ => progress destruct_head' or
               | _ => solve [ eauto with nocore ]
               | _ => progress inversion_wf
               end.
    Qed.
  End with_var.

  Definition duplicate_type {var1 var2}
    : { t : base_type_code & (var1 t * var2 t)%type }
      -> { t1t2 : _ & (var1 (fst t1t2) * var2 (snd t1t2))%type }
    := fun txy => existT _ (projT1 txy, projT1 txy) (projT2 txy).
  Definition duplicate_types {var1 var2}
    := List.map (@duplicate_type var1 var2).

  Lemma flatten_binding_list_flatten_binding_list2
      {var1 var2 t1} x1 x2
  : duplicate_types (@flatten_binding_list base_type_code var1 var2 t1 x1 x2)
    = @flatten_binding_list2 base_type_code var1 var2 t1 t1 x1 x2.
  Proof.
    induction t1; simpl; try reflexivity.
    rewrite_hyp <- !*.
    unfold duplicate_types; rewrite List.map_app; reflexivity.
  Qed.

  Local Ltac flatten_t :=
    repeat first [ reflexivity
                 | intro
                 | progress simpl @flatten_binding_list
                 | progress simpl @flatten_binding_list2
                 | rewrite !List.map_app
                 | progress simpl in *
                 | rewrite_hyp <- !*; reflexivity
                 | rewrite_hyp !*; reflexivity ].

  Lemma flatten_binding_list2_SmartVarfMap
        {var1 var1' var2 var2' t1 t2} f g (x1 : interp_flat_type var1 t1) (x2 : interp_flat_type var2 t2)
    : flatten_binding_list2 (var1:=var1') (var2:=var2') (base_type_code:=base_type_code) (SmartVarfMap f x1) (SmartVarfMap g x2)
      = List.map (fun txy => existT _ (projT1 txy) (f _ (fst (projT2 txy)), g _ (snd (projT2 txy)))%core)
                 (flatten_binding_list2 x1 x2).
  Proof.
    revert dependent t2; induction t1, t2; flatten_t.
  Qed.

  Lemma flatten_binding_list2_SmartVarfMap1
        {var1 var1' var2' t1 t2} f (x1 : interp_flat_type var1 t1) (x2 : interp_flat_type var2' t2)
    : flatten_binding_list2 (var1:=var1') (var2:=var2') (base_type_code:=base_type_code) (SmartVarfMap f x1) x2
      = List.map (fun txy => existT _ (projT1 txy) (f _ (fst (projT2 txy)), snd (projT2 txy))%core)
                 (flatten_binding_list2 x1 x2).
  Proof.
    revert dependent t2; induction t1, t2; flatten_t.
  Qed.

  Lemma flatten_binding_list2_SmartVarfMap2
        {var1' var2 var2' t1 t2} g (x1 : interp_flat_type var1' t1) (x2 : interp_flat_type var2 t2)
    : flatten_binding_list2 (var1:=var1') (var2:=var2') (base_type_code:=base_type_code) x1 (SmartVarfMap g x2)
      = List.map (fun txy => existT _ (projT1 txy) (fst (projT2 txy), g _ (snd (projT2 txy)))%core)
                 (flatten_binding_list2 x1 x2).
  Proof.
    revert dependent t2; induction t1, t2; flatten_t.
  Qed.

  Lemma flatten_binding_list_SmartVarfMap
        {var1 var1' var2 var2' t} f g (x1 : interp_flat_type var1 t) (x2 : interp_flat_type var2 t)
    : flatten_binding_list (var1:=var1') (var2:=var2') (base_type_code:=base_type_code) (SmartVarfMap f x1) (SmartVarfMap g x2)
      = List.map (fun txy => existT _ (projT1 txy) (f _ (fst (projT2 txy)), g _ (snd (projT2 txy)))%core)
                 (flatten_binding_list x1 x2).
  Proof. induction t; flatten_t. Qed.

  Lemma flatten_binding_list2_SmartValf
        {T1 T2} f g t1 t2
    : flatten_binding_list2 (base_type_code:=base_type_code) (SmartValf T1 f t1) (SmartValf T2 g t2)
      = List.map (fun txy => existT _ (projT1 txy) (f _, g _)%core)
                 (flatten_binding_list2 (SmartFlatTypeUnMap t1) (SmartFlatTypeUnMap t2)).
  Proof.
    revert dependent t2; induction t1, t2; flatten_t.
  Qed.

  Lemma flatten_binding_list_SmartValf
        {T1 T2} f g t
    : flatten_binding_list (base_type_code:=base_type_code) (SmartValf T1 f t) (SmartValf T2 g t)
      = List.map (fun txy => existT _ (projT1 txy) (f _, g _)%core)
                 (flatten_binding_list (SmartFlatTypeUnMap t) (SmartFlatTypeUnMap t)).
  Proof. induction t; flatten_t. Qed.
End language.

Hint Resolve wff_SmartVarf wff_SmartVarVarf wff_SmartVarVarf_nil : wf.
