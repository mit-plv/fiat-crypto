(** * Inline: Remove some [Let] expressions, inline constants, interpret constant operations *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.InlineConstAndOpWf.
Require Import Crypto.Compilers.InterpProofs.
Require Import Crypto.Compilers.Inline.
Require Import Crypto.Compilers.InlineInterp.
Require Import Crypto.Compilers.InlineConstAndOp.
Require Import Crypto.Util.Sigma Crypto.Util.Prod Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.


Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation wff := (@wff base_type_code op).
  Local Notation wf := (@wf base_type_code op).

  Section with_invert.
    Context (invert_Const : forall s d, op s d -> @exprf interp_base_type s -> option (interp_flat_type d))
            (Const : forall t, interp_base_type t -> @exprf interp_base_type (Tbase t))
            (Hinvert_Const
             : forall s d opc e v, invert_Const s d opc e = Some v
                                   -> interp_op s d opc (interpf interp_op e) = v)
            (interpf_Const : forall t v, interpf interp_op (Const t v) = v).

    Lemma interpf_postprocess_for_const_and_op {t} (e : exprf t)
      : interpf interp_op
                (exprf_of_inline_directive
                   (postprocess_for_const_and_op interp_op invert_Const Const e))
        = interpf interp_op e.
    Proof.
      induction e; try reflexivity; simpl in *.
      all:repeat first [ reflexivity
                       | break_innermost_match_step
                       | progress cbv [SmartVarVarf]
                       | progress cbn [interpf exprf_of_inline_directive interpf_step LetIn.Let_In SmartVarVarf fst snd] in *
                       | solve [ auto ]
                       | rewrite SmartPairf_Pair
                       | apply (f_equal2 (@pair _ _))
                       | rewrite interpf_SmartPairf
                       | rewrite SmartVarfMap_compose
                       | rewrite SmartVarfMap_id
                       | setoid_rewrite interpf_Const
                       | erewrite ExprInversion.interpf_invert_PairsConst by eassumption ].
    Qed.

    Lemma interpf_inline_const_and_op_genf
          G {t} e1 e2
          (wf : @wff _ _ G t e1 e2)
          (H : forall t x x',
              List.In
                (existT (fun t : base_type_code => (exprf (Tbase t) * interp_base_type t)%type) t
                        (x, x')) G
              -> interpf interp_op x = x')
      : interpf interp_op (inline_const_and_op_genf (t:=t) interp_op invert_Const Const e1)
        = interpf interp_op e2.
    Proof.
      unfold inline_const_and_op_genf;
        eapply interpf_inline_const_genf; eauto using interpf_postprocess_for_const_and_op.
    Qed.

    Lemma interpf_inline_const_and_op_gen
          {t} e1 e2
          (Hwf : @wf _ _ t e1 e2)
      : forall x,
        interp interp_op (inline_const_and_op_gen (t:=t) interp_op invert_Const Const e1) x
        = interp interp_op e2 x.
    Proof.
      unfold inline_const_and_op_gen;
        eapply interp_inline_const_gen; eauto using interpf_postprocess_for_const_and_op.
    Qed.
  End with_invert.

  Section const_unit.
    Context (OpConst : forall t, interp_base_type t -> op Unit (Tbase t))
            (interp_op_OpConst : forall t v, interp_op _ _ (OpConst t v) tt = v).

    Lemma interpf_invert_ConstUnit s d opc e v
          (H : invert_ConstUnit interp_op opc e = Some v)
      : interp_op s d opc (interpf interp_op e) = v.
    Proof using Type.
      destruct s; simpl in *; inversion_option; subst.
      edestruct interpf; reflexivity.
    Qed.

    Lemma interpf_Const t v
      : interpf interp_op (Const OpConst (t:=t) v) = v.
    Proof using interp_op_OpConst.
      apply interp_op_OpConst.
    Qed.

    Lemma interpf_inline_const_and_opf
          G {t} e1 e2
          (wf : @wff _ _ G t e1 e2)
          (H : forall t x x',
              List.In
                (existT (fun t : base_type_code => (exprf (Tbase t) * interp_base_type t)%type) t
                        (x, x')) G
              -> interpf interp_op x = x')
      : interpf interp_op (inline_const_and_opf (t:=t) interp_op OpConst e1)
        = interpf interp_op e2.
    Proof.
      unfold inline_const_and_opf;
        eapply interpf_inline_const_genf; eauto using interpf_postprocess_for_const_and_op, interpf_invert_ConstUnit, interpf_Const.
    Qed.

    Lemma interpf_inline_const_and_op
          {t} e1 e2
          (Hwf : @wf _ _ t e1 e2)
      : forall x,
        interp interp_op (inline_const_and_op (t:=t) interp_op OpConst e1) x
        = interp interp_op e2 x.
    Proof.
      unfold inline_const_and_op;
        eapply interp_inline_const_gen; eauto using interpf_postprocess_for_const_and_op, interpf_invert_ConstUnit, interpf_Const.
    Qed.
  End const_unit.

  Lemma InterpInlineConstAndOpGen
        (invert_Const : forall var s d, op s d -> @exprf var s -> option (interp_flat_type d))
        (Const : forall var t, interp_base_type t -> @exprf var (Tbase t))

        {t} (e : Expr t)
        (wf : Wf e)
        (Hinvert_Const
         : forall s d opc e v,
            invert_Const _ s d opc e = Some v
            -> interp_op s d opc (interpf interp_op e) = v)
        (interpf_Const : forall t v, interpf interp_op (Const _ t v) = v)
    : forall x, Interp interp_op (InlineConstAndOpGen interp_op invert_Const Const e) x = Interp interp_op e x.
  Proof using Type.
    eapply InterpInlineConstGen;
      eauto using interpf_postprocess_for_const_and_op, interpf_invert_ConstUnit, interpf_Const.
  Qed.

  Lemma InterpInlineConstAndOp
        (OpConst : forall t, interp_base_type t -> op Unit (Tbase t))
        {t} (e : Expr t)
        (wf : Wf e)
        (interp_op_OpConst : forall t v, interp_op _ _ (OpConst t v) tt = v)
    : forall x, Interp interp_op (InlineConstAndOp interp_op OpConst e) x = Interp interp_op e x.
  Proof using Type.
    eapply InterpInlineConstGen;
      eauto using interpf_postprocess_for_const_and_op, interpf_invert_ConstUnit, interpf_Const.
  Qed.
End language.

(*Hint Rewrite @InterpInlineConst @interp_inline_const @interpf_inline_constf using solve_wf_side_condition : reflective_interp.*)
