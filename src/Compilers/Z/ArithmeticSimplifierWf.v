Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.RewriterWf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.OpInversion.
Require Import Crypto.Compilers.Z.ArithmeticSimplifier.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.HProp.

Local Notation exprf := (@exprf base_type op).
Local Notation expr := (@expr base_type op).
Local Notation Expr := (@Expr base_type op).
Local Notation wff := (@wff base_type op).
Local Notation Wf := (@Wf base_type op).

Local Ltac fin_t :=
  first [ exact I
        | reflexivity
        | congruence
        | assumption
        | exfalso; assumption
        | match goal with
          | [ |- _ /\ False ] => exfalso
          | [ |- False /\ _ ] => exfalso
          | [ |- _ /\ _ /\ False ] => exfalso
          | [ |- _ /\ False /\ _ ] => exfalso
          | [ |- False /\ _ /\ _ ] => exfalso
          end ].
Local Ltac break_t_step :=
  first [ progress subst
        | progress inversion_option
        | progress inversion_sum
        | progress inversion_expr
        | progress inversion_prod
        | progress invert_op
        | progress inversion_flat_type
        | progress destruct_head'_and
        | progress destruct_head' iff
        | progress destruct_head'_prod
        | progress destruct_head'_sig
        | progress specialize_by reflexivity
        | progress eliminate_hprop_eq
        | progress break_innermost_match_hyps_step
        | progress break_innermost_match_step
        | progress break_match_hyps
        | progress inversion_wf_constr ].


Lemma interp_as_expr_or_const_None_iff {var1 var2 t} {G e1 e2}
      (Hwf : @wff var1 var2 G t e1 e2)
  : @interp_as_expr_or_const var1 t e1 = None
    <-> @interp_as_expr_or_const var2 t e2 = None.
Proof.
  induction Hwf;
    repeat first [ fin_t
                 | split; congruence
                 | progress simpl in *
                 | progress intros
                 | break_t_step ].
Qed.

Lemma interp_as_expr_or_const_None_Some {var1 var2 t} {G e1 e2 v}
      (Hwf : @wff var1 var2 G t e1 e2)
  : @interp_as_expr_or_const var1 t e1 = None
    -> @interp_as_expr_or_const var2 t e2 = Some v
    -> False.
Proof.
  erewrite interp_as_expr_or_const_None_iff by eassumption; congruence.
Qed.

Lemma interp_as_expr_or_const_Some_None {var1 var2 t} {G e1 e2 v}
      (Hwf : @wff var1 var2 G t e1 e2)
  : @interp_as_expr_or_const var1 t e1 = Some v
    -> @interp_as_expr_or_const var2 t e2 = None
    -> False.
Proof.
  erewrite <- interp_as_expr_or_const_None_iff by eassumption; congruence.
Qed.

Local Ltac pret_step :=
  first [ fin_t
        | progress subst
        | progress inversion_option
        | progress inversion_prod
        | progress simpl in *
        | progress inversion_wf
        | match goal with
          | [ H : match interp_as_expr_or_const ?e with _ => _ end = Some _ |- _ ]
            => is_var e; destruct (interp_as_expr_or_const e) eqn:?
          end ].

Lemma wff_interp_as_expr_or_const_base {var1 var2 t} {G e1 e2 v1 v2}
      (Hwf : @wff var1 var2 G (Tbase t) e1 e2)
  : @interp_as_expr_or_const var1 (Tbase t) e1 = Some v1
    -> @interp_as_expr_or_const var2 (Tbase t) e2 = Some v2
    -> match v1, v2 with
       | const_of z1, const_of z2 => z1 = z2
       | gen_expr e1, gen_expr e2
       | neg_expr e1, neg_expr e2
         => wff G e1 e2
       | const_of _, _
       | gen_expr _, _
       | neg_expr _, _
         => False
       end.
Proof.
  invert_one_expr e1; intros; break_innermost_match; intros;
    try (let e2 := match goal with Hwf : wff ?G ?e1 ?e2 |- _ => e2 end in
         invert_one_expr e2); intros;
      repeat first [ fin_t
                   | progress simpl in *
                   | progress intros
                   | break_t_step
                   | match goal with
                     | [ H : wff _ _ ?e |- _ ] => is_var e; invert_one_expr e
                     end ].
Qed.

Local Ltac pose_wff_base :=
  match goal with
  | [ H1 : _ = Some _, H2 : _ = Some _, Hwf : wff _ _ _ |- _ ]
    => pose proof (wff_interp_as_expr_or_const_base Hwf H1 H2); clear H1 H2
  end.

Lemma wff_interp_as_expr_or_const_prod_base {var1 var2 A B} {G e1 e2} {v1 v2 : _ * _}
      (Hwf : wff G e1 e2)
  : @interp_as_expr_or_const var1 (Prod (Tbase A) (Tbase B)) e1 = Some v1
    -> @interp_as_expr_or_const var2 (Prod (Tbase A) (Tbase B)) e2 = Some v2
    -> match fst v1, fst v2 with
       | const_of z1, const_of z2 => z1 = z2
       | gen_expr e1, gen_expr e2
       | neg_expr e1, neg_expr e2
         => wff G e1 e2
       | const_of _, _
       | gen_expr _, _
       | neg_expr _, _
         => False
       end
       /\ match snd v1, snd v2 with
          | const_of z1, const_of z2 => z1 = z2
          | gen_expr e1, gen_expr e2
          | neg_expr e1, neg_expr e2
            => wff G e1 e2
          | const_of _, _
          | gen_expr _, _
          | neg_expr _, _
            => False
          end.
Proof.
  invert_one_expr e1; intros; break_innermost_match; intros; try exact I;
    try (let e2 := match goal with Hwf : wff ?G ?e1 ?e2 |- _ => e2 end in
         invert_one_expr e2);
    intros; break_innermost_match; intros; try exact I;
      repeat first [ pret_step
                   | pose_wff_base
                   | break_t_step
                   | apply conj ].
Qed.

Local Ltac pose_wff_prod :=
  match goal with
  | [ H1 : _ = Some _, H2 : _ = Some _, Hwf : wff _ _ _ |- _ ]
    => pose proof (wff_interp_as_expr_or_const_prod_base Hwf H1 H2); clear H1 H2
  end.

Lemma wff_interp_as_expr_or_const_prod3_base {var1 var2 A B C} {G e1 e2} {v1 v2 : _ * _ * _}
      (Hwf : wff G e1 e2)
  : @interp_as_expr_or_const var1 (Prod (Prod (Tbase A) (Tbase B)) (Tbase C)) e1 = Some v1
    -> @interp_as_expr_or_const var2 (Prod (Prod (Tbase A) (Tbase B)) (Tbase C)) e2 = Some v2
    -> match fst (fst v1), fst (fst v2) with
       | const_of z1, const_of z2 => z1 = z2
       | gen_expr e1, gen_expr e2
       | neg_expr e1, neg_expr e2
         => wff G e1 e2
       | const_of _, _
       | gen_expr _, _
       | neg_expr _, _
         => False
       end
       /\ match snd (fst v1), snd (fst v2) with
          | const_of z1, const_of z2 => z1 = z2
          | gen_expr e1, gen_expr e2
          | neg_expr e1, neg_expr e2
            => wff G e1 e2
          | const_of _, _
          | gen_expr _, _
          | neg_expr _, _
            => False
          end
       /\ match snd v1, snd v2 with
          | const_of z1, const_of z2 => z1 = z2
          | gen_expr e1, gen_expr e2
          | neg_expr e1, neg_expr e2
            => wff G e1 e2
          | const_of _, _
          | gen_expr _, _
          | neg_expr _, _
            => False
          end.
Proof.
  invert_one_expr e1; intros; break_innermost_match; intros; try exact I;
    try (let e2 := match goal with Hwf : wff ?G ?e1 ?e2 |- _ => e2 end in
         invert_one_expr e2);
    intros; break_innermost_match; intros; try exact I;
      repeat first [ pret_step
                   | pose_wff_base
                   | pose_wff_prod
                   | break_t_step
                   | apply conj ].
Qed.

Local Ltac pose_wff_prod3 :=
  match goal with
  | [ H1 : _ = Some _, H2 : _ = Some _, Hwf : wff _ _ _ |- _ ]
    => pose proof (wff_interp_as_expr_or_const_prod3_base Hwf H1 H2); clear H1 H2
  end.

Lemma Wf_SimplifyArith {convert_adc_to_sbb} {t} (e : Expr t)
      (Hwf : Wf e)
  : Wf (SimplifyArith convert_adc_to_sbb e).
Proof.
  apply Wf_RewriteOp; [ | assumption ].
  intros ???????? Hwf'; unfold simplify_op_expr;
    repeat match goal with
           | [ H : ?T |- ?T ] => exact H
           | [ H : False |- _ ] => exfalso; assumption
           | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
           | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
           | _ => pose_wff_base
           | _ => pose_wff_prod
           | _ => pose_wff_prod3
           | _ => progress destruct_head'_and
           | _ => progress subst
           | [ H1 : _ = Some _, H2 : _ = None, Hwf : wff _ _ _ |- _ ]
             => pose proof (interp_as_expr_or_const_Some_None Hwf H1 H2); clear H1 H2
           | [ H1 : _ = None, H2 : _ = Some _, Hwf : wff _ _ _ |- _ ]
             => pose proof (interp_as_expr_or_const_None_Some Hwf H1 H2); clear H1 H2
           | [ |- wff _ (Op _ _) (LetIn _ _) ] => exfalso
           | [ |- wff _ (LetIn _ _) (Op _ _) ] => exfalso
           | [ |- wff _ (Pair _ _) (LetIn _ _) ] => exfalso
           | [ |- wff _ (LetIn _ _) (Pair _ _) ] => exfalso
           | [ |- wff _ _ _ ] => constructor; intros
           | [ |- List.In _ _ ] => progress (simpl; auto)
           | _ => break_innermost_match_step; simpl in *
           end.
Qed.

Hint Resolve Wf_SimplifyArith : wf.
