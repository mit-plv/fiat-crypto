(** * Inline: Remove some [Let] expressions, inline constants, interpret constant operations *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.Inline.
Require Import Crypto.Compilers.InlineWf.
Require Import Crypto.Compilers.InlineConstAndOp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma Crypto.Util.Prod.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}.


  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation Tbase := (@Tbase base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation wff := (@wff base_type_code op).
  Local Notation wf := (@wf base_type_code op).

  Local Hint Constructors Wf.wff.

  Local Notation wff_inline_directive G x y :=
    (wff G (exprf_of_inline_directive x) (exprf_of_inline_directive y)
     /\ (fun x' y'
         => match x', y' with
            | default_inline _ _, default_inline _ _
            | no_inline _ _, no_inline _ _
            | inline _ _, inline _ _
            | partial_inline _ _ _ _, partial_inline _ _ _ _
              => True
            | default_inline _ _, _
            | no_inline _ _, _
            | inline _ _, _
            | partial_inline _ _ _ _, _
              => False
            end) x y).


  Section with_var.
    Context {interp_op1 : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
            {interp_op2 : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
            {var1 var2 : base_type_code -> Type}
            {invert_Const1 : forall s d, op s d -> @exprf var1 s -> option (interp_flat_type interp_base_type d)}
            {invert_Const2 : forall s d, op s d -> @exprf var2 s -> option (interp_flat_type interp_base_type d)}
            {Const1 : forall t, interp_base_type t -> @exprf var1 (Tbase t)}
            {Const2 : forall t, interp_base_type t -> @exprf var2 (Tbase t)}
            (Hinterp_op : forall s d opv args, interp_op1 s d opv args = interp_op2 s d opv args)
            (Hinvert_Const : forall s d opv G e1 e2, wff G e1 e2 -> invert_Const1 s d opv e1 = invert_Const2 s d opv e2)
            (HConst : forall t v G, wff G (Const1 t v) (Const2 t v)).

    Local Ltac t_fin :=
      repeat first [ intro
                   | progress inversion_sigma
                   | progress inversion_prod
                   | exfalso; assumption
                   | exact I
                   | progress destruct_head'_prod
                   | progress destruct_head'_and
                   | progress destruct_head'_sig
                   | progress subst
                   | rewrite Hinterp_op
                   | rewrite SmartPairfSmartVarVarf_SmartVarf
                   | rewrite SmartPairf_Pair
                   | tauto
                   | solve [ auto with nocore
                           | eapply (@wff_SmartVarVarf _ _ _ _ _ _ (_ * _)); auto
                           | eapply wff_SmartVarVarf; eauto with nocore
                           | eapply wff_SmartPairf; eauto with nocore
                           | eapply wff_app_post, wff_SmartVarf
                           | apply wff_SmartPairf_SmartVarfMap_same; auto ]
                   | progress simpl in *
                   | constructor
                   | solve [ eauto
                           | eauto using wff_app_pre, wff_app_post
                           | eapply wff_in_impl_Proper;
                             [ solve [ eauto using wff_SmartVarf ]
                             | intros *;
                               repeat setoid_rewrite List.in_app_iff;
                               tauto ] ]
                   | progress inversion_wf_constr
                   | match goal with
                     | [ H : invert_PairsConst _ _ = ?x, H' : invert_PairsConst _ _ = ?y |- _ ]
                       => assert (x = y)
                         by (rewrite <- H, <- H'; eapply wff_invert_PairsConst; [ eauto | eassumption ]);
                          inversion_option;
                          progress (subst || congruence)
                     end
                   | break_innermost_match_hyps_step
                   | break_innermost_match_step ].

    Lemma wff_postprocess_for_const_and_op
          G t e1 e2
          (Hwf : wff (t:=t) G e1 e2)
      : wff_inline_directive
          G
          (postprocess_for_const_and_op interp_op1 invert_Const1 Const1 e1)
          (postprocess_for_const_and_op interp_op2 invert_Const2 Const2 e2).
    Proof using Hinvert_Const Hinterp_op HConst.
      induction Hwf; split; cbv beta;
        repeat match goal with
               | [ H : wff _ _ _ /\ _ |- match _ with _ => _ end _ ] => destruct H as [_ ?]
               end.
      { t_fin. }
      { t_fin. }
      { t_fin. }
      { t_fin. }
      { destruct IHHwf as [? _]. (* for speed *)
        t_fin. }
      { t_fin. }
      { t_fin. }
      { t_fin. }
      { t_fin. }
      { t_fin. }
    Qed.

    Lemma wff_inline_const_and_op_genf {t} e1 e2 G G'
          (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x, x')) G'
                              -> wff G x x')
          (wf : wff G' e1 e2)
      : @wff var1 var2 G t (inline_const_and_op_genf interp_op1 invert_Const1 Const1 e1) (inline_const_and_op_genf interp_op2 invert_Const2 Const2 e2).
    Proof using HConst Hinvert_Const Hinterp_op.
      unfold inline_const_and_op_genf;
        eauto using wff_inline_const_genf, wff_postprocess_for_const_and_op.
    Qed.

    Lemma wff_inline_const_and_op_gen {t} e1 e2
          (Hwf : wf e1 e2)
      : @wf var1 var2 t (inline_const_and_op_gen interp_op1 invert_Const1 Const1 e1) (inline_const_and_op_gen interp_op2 invert_Const2 Const2 e2).
    Proof using HConst Hinvert_Const Hinterp_op.
      unfold inline_const_and_op_gen;
        eauto using wf_inline_const_gen, wff_postprocess_for_const_and_op.
    Qed.
  End with_var.

  Section const_unit.
    Context {interp_op1 : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
            {interp_op2 : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d}
            {var1 var2 : base_type_code -> Type}
            (OpConst1 OpConst2 : forall t, interp_base_type t -> op Unit (Tbase t))
            (HOpConst : forall t v, OpConst1 t v = OpConst2 t v)
            (Hinterp_op : forall s d opv args, interp_op1 s d opv args = interp_op2 s d opv args).

    Lemma wff_invert_ConstUnit
          s d opv e1 e2
      : @invert_ConstUnit _ _ _ interp_op1 var1 s d opv e1
        = @invert_ConstUnit _ _ _ interp_op2 var2 s d opv e2.
    Proof using Hinterp_op.
      cbv [invert_ConstUnit invert_ConstUnit']; destruct s; f_equal; auto.
    Qed.

    Lemma wff_Const {t} v G
      : wff G (@Const _ _ _ var1 OpConst1 t v) (@Const _ _ _ var2 OpConst2 t v).
    Proof using HOpConst.
      cbv [Const]; rewrite HOpConst; auto.
    Qed.

    Lemma wff_inline_const_and_opf {t} e1 e2 G G'
          (H : forall t x x', List.In (existT (fun t : base_type_code => (exprf (Tbase t) * exprf (Tbase t))%type) t (x, x')) G'
                              -> wff G x x')
          (wf : wff G' e1 e2)
      : @wff var1 var2 G t (inline_const_and_opf interp_op1 OpConst1 e1) (inline_const_and_opf interp_op2 OpConst2 e2).
    Proof using HOpConst Hinterp_op.
      unfold inline_const_and_opf;
        eauto using wff_inline_const_and_op_genf, wff_invert_ConstUnit, wff_Const.
    Qed.

    Lemma wff_inline_const_and_op {t} e1 e2
          (Hwf : wf e1 e2)
      : @wf var1 var2 t (inline_const_and_op interp_op1 OpConst1 e1) (inline_const_and_op interp_op2 OpConst2 e2).
    Proof using HOpConst Hinterp_op.
      unfold inline_const_and_op;
        eauto using wff_inline_const_and_op_gen, wff_invert_ConstUnit, wff_Const.
    Qed.
  End const_unit.

  Lemma Wf_InlineConstAndOpGen
        {interp_op}
        (invert_Const : forall var s d, op s d -> @exprf var s -> option (interp_flat_type interp_base_type d))
        (Const : forall var t, interp_base_type t -> @exprf var (Tbase t))
        (Hinvert_Const
         : forall var1 var2 s d opv G e1 e2,
            wff G e1 e2
            -> invert_Const var1 s d opv e1 = invert_Const var2 s d opv e2)
        (HConst
         : forall var1 var2 t v G,
            wff G (Const var1 t v) (Const var2 t v))
        {t} (e : Expr t)
        (Hwf : Wf e)
    : Wf (InlineConstAndOpGen interp_op invert_Const Const e).
  Proof using Type.
    unfold InlineConstAndOpGen;
      eauto using Wf_InlineConstGen, wff_postprocess_for_const_and_op.
  Qed.

  Lemma Wf_InlineConstAndOp
        {interp_op}
        (OpConst : forall t, interp_base_type t -> op Unit (Tbase t))
        {t} (e : Expr t)
        (Hwf : Wf e)
    : Wf (InlineConstAndOp interp_op OpConst e).
  Proof using Type.
    unfold InlineConstAndOp;
      eauto using Wf_InlineConstGen, wff_postprocess_for_const_and_op, wff_Const.
  Qed.
End language.

Hint Resolve Wf_InlineConstAndOpGen Wf_InlineConstAndOp : wf.
