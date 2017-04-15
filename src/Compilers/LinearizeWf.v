(** * Linearize: Place all and only operations in let binders *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.

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
      | _ => progress destruct_head'_sig
      | _ => progress destruct_head'_and
      | _ => setoid_rewrite List.in_app_iff
      | [ H : context[List.In _ (_ ++ _)] |- _ ] => setoid_rewrite List.in_app_iff in H
      | _ => progress intros
      | _ => solve [ eauto ]
      | _ => solve [ intuition (subst; eauto) ]
      | [ H : forall (x : prod _ _) (y : prod _ _), _ |- _ ] => specialize (fun x x' y y' => H (x, x') (y, y'))
      | _ => rewrite !List.app_assoc
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : _ |- _ ] => apply H
      | [ H : forall G : list _, _ |- _ ] => apply (H nil)
      | _ => eapply wff_in_impl_Proper; [ solve [ eauto using wff_SmartVarf ] | solve [ repeat t_fin_step tac ] ]
      | _ => progress tac
      | [ |- wff _ _ _ ] => constructor
      | [ |- wf _ _ _ ] => constructor
      | _ => break_innermost_match_step
      | _ => progress inversion_expr
      | _ => congruence
      | _ => progress destruct_head' sum
      | _ => progress unfold invert_Op in *
      | _ => break_innermost_match_hyps_step
      end.
    Local Ltac t_fin tac := repeat t_fin_step tac.

    Local Hint Constructors Wf.wff.
    Local Hint Resolve List.in_app_or List.in_or_app.

    Section gen1.
      Context (let_bind_op_args : bool).

      Fixpoint wff_under_letsf' G {t} e1 e2 {tC} eC1 eC2
               let_bind_pairs
               (wf : @wff var1 var2 G t e1 e2)
               (H : forall (x1 : interp_flat_type var1 t) (x2 : interp_flat_type var2 t),
                   wff (flatten_binding_list x1 x2 ++ G) (eC1 (inl x1)) (eC2 (inl x2)))
               (H' : forall G' (x y : exprf t),
                   wff (G' ++ G) x y
                   -> wff (G' ++ G) (eC1 (inr x)) (eC2 (inr y)))
               {struct e1}
        : @wff var1 var2 G tC (under_letsf' let_bind_op_args let_bind_pairs e1 eC1) (under_letsf' let_bind_op_args let_bind_pairs e2 eC2).
      Proof using Type.
        revert H.
        set (e1v := e1) in *.
        destruct e1 as [ | | ? ? ? args | tx ex tC0 eC0 | ? ex ? ey ];
          [ clear wff_under_letsf'
          | clear wff_under_letsf'
          | clear wff_under_letsf'
          | generalize (fun G => match e1v return match e1v with LetIn _ _ _ _ => _ | _ => _ end with
                                 | LetIn _ ex _ eC => wff_under_letsf' G _ ex
                                 | _ => I
                                 end);
            generalize (fun G => match e1v return match e1v with LetIn tx0 _ tC1 e0 => _ | _ => _ end with
                                 | LetIn _ ex tC' eC => fun x => wff_under_letsf' G tC' (eC x)
                                 | _ => I
                                 end);
            clear wff_under_letsf'
          | generalize (fun G => match e1v return match e1v with Pair _ _ _ _ => _ | _ => _ end with
                                 | Pair _ ex _ ey => wff_under_letsf' G _ ex
                                 | _ => I
                                 end);
            generalize (fun G => match e1v return match e1v with Pair _ _ _ _ => _ | _ => _ end with
                                 | Pair _ ex _ ey => wff_under_letsf' G _ ey
                                 | _ => I
                                 end);
            clear wff_under_letsf' ];
          subst e1v;
          cbv beta iota;
          (invert_one_expr e2 || destruct e2); intros; try break_innermost_match_step; try exact I; intros;
            inversion_wf;
            t_fin idtac.
      Qed.

      Lemma  wff_under_letsf G {t} e1 e2 {tC} eC1 eC2
             (wf : @wff var1 var2 G t e1 e2)
             (H' : forall G' (x y : exprf t),
                 wff (G' ++ G) x y
                 -> wff (G' ++ G) (eC1 x) (eC2 y))
        : @wff var1 var2 G tC (under_letsf let_bind_op_args e1 eC1) (under_letsf let_bind_op_args e2 eC2).
      Proof using Type.
        apply wff_under_letsf'; t_fin idtac.
      Qed.
    End gen1.

    Local Hint Resolve wff_under_letsf.
    Local Hint Constructors or.
    Local Hint Extern 1 => progress unfold List.In in *.
    Local Hint Resolve wff_in_impl_Proper.
    Local Hint Resolve wff_SmartVarf.

    Section gen2.
      Context (let_bind_op_args : bool).

      Lemma wff_linearizef_gen G {t} e1 e2
        : @wff var1 var2 G t e1 e2
          -> @wff var1 var2 G t (linearizef_gen let_bind_op_args e1) (linearizef_gen let_bind_op_args e2).
      Proof using Type.
        induction 1; t_fin ltac:(apply wff_under_letsf).
      Qed.

      Local Hint Resolve wff_linearizef_gen.

      Lemma wf_linearize_gen {t} e1 e2
        : @wf var1 var2 t e1 e2
          -> @wf var1 var2 t (linearize_gen let_bind_op_args e1) (linearize_gen let_bind_op_args e2).
      Proof using Type.
        destruct 1; constructor; auto.
      Qed.
    End gen2.
  End with_var.

  Section gen.
    Context (let_bind_op_args : bool).

    Lemma Wf_Linearize_gen {t} (e : Expr t) : Wf e -> Wf (Linearize_gen let_bind_op_args e).
    Proof using Type.
      intros wf var1 var2; apply wf_linearize_gen, wf.
    Qed.
  End gen.

  Definition wff_linearizef {var1 var2} G {t} e1 e2
    : @wff var1 var2 G t e1 e2
      -> @wff var1 var2 G t (linearizef e1) (linearizef e2)
    := wff_linearizef_gen _ G e1 e2.
  Definition wff_a_normalf {var1 var2} G {t} e1 e2
    : @wff var1 var2 G t e1 e2
      -> @wff var1 var2 G t (a_normalf e1) (a_normalf e2)
    := wff_linearizef_gen _ G e1 e2.

  Definition wf_linearize {var1 var2 t} e1 e2
    : @wf var1 var2 t e1 e2
      -> @wf var1 var2 t (linearize e1) (linearize e2)
    := wf_linearize_gen _ e1 e2.
  Definition wf_a_normal {var1 var2 t} e1 e2
    : @wf var1 var2 t e1 e2
      -> @wf var1 var2 t (a_normal e1) (a_normal e2)
    := wf_linearize_gen _ e1 e2.

  Definition Wf_Linearize {t} (e : Expr t) : Wf e -> Wf (Linearize e)
    := Wf_Linearize_gen _ e.
  Definition Wf_ANormal {t} (e : Expr t) : Wf e -> Wf (ANormal e)
    := Wf_Linearize_gen _ e.
End language.

Hint Resolve Wf_Linearize_gen Wf_Linearize Wf_ANormal : wf.
