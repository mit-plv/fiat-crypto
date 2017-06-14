Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.RewriterWf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.OpInversion.
Require Import Crypto.Compilers.Z.ArithmeticSimplifier.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Compilers.Z.Syntax.Util.
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

Fixpoint wff_as_expr_or_const {var1 var2} G {t}
  : interp_flat_type (@inverted_expr var1) t
    -> interp_flat_type (@inverted_expr var2) t
    -> Prop
  := match t with
     | Tbase T
       => fun z1 z2 => match z1, z2 return Prop with
                       | const_of z1, const_of z2 => z1 = z2
                       | gen_expr e1, gen_expr e2
                       | neg_expr e1, neg_expr e2
                         => wff G e1 e2
                       | const_of _, _
                       | gen_expr _, _
                       | neg_expr _, _
                         => False
                       end
     | Unit => fun _ _ => True
     | Prod A B => fun a b : interp_flat_type _ A * interp_flat_type _ B
                   => and (@wff_as_expr_or_const var1 var2 G A (fst a) (fst b))
                          (@wff_as_expr_or_const var1 var2 G B (snd a) (snd b))
     end.

Lemma wff_interp_as_expr_or_const {var1 var2 t} {G e1 e2 v1 v2}
      (Hwf : @wff var1 var2 G t e1 e2)
  : @interp_as_expr_or_const var1 t e1 = Some v1
    -> @interp_as_expr_or_const var2 t e2 = Some v2
    -> wff_as_expr_or_const G v1 v2.
Proof.
  induction Hwf;
    repeat first [ progress subst
                 | progress inversion_option
                 | progress simpl in *
                 | progress cbn [wff_as_expr_or_const]
                 | reflexivity
                 | break_innermost_match_hyps_step
                 | intro
                 | match goal with
                   | [ H : forall z, Some _ = Some z -> _ |- _ ] => specialize (H _ eq_refl)
                   | [ |- context[match ?e with _ => _ end] ]
                     => is_var e; invert_one_op e
                   end
                 | break_innermost_match_step
                 | solve [ auto with wf ] ].
Qed.

Local Ltac pose_wff _ :=
  match goal with
  | [ H1 : _ = Some _, H2 : _ = Some _, Hwf : wff _ _ _ |- _ ]
    => pose proof (wff_interp_as_expr_or_const Hwf H1 H2); clear H1 H2
  end.

Lemma Wf_SimplifyArith {convert_adc_to_sbb} {t} (e : Expr t)
      (Hwf : Wf e)
  : Wf (SimplifyArith convert_adc_to_sbb e).
Proof.
  apply Wf_RewriteOp; [ | assumption ].
  intros ???????? Hwf'; unfold simplify_op_expr.
  repeat match goal with
         | [ H : ?T |- ?T ] => exact H
         | [ H : False |- _ ] => exfalso; assumption
         | [ |- True ] => exact I
         | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
         | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
         | [ H : None = Some _ |- _ ] => exfalso; clear -H; discriminate
         | [ H : Some _ = None |- _ ] => exfalso; clear -H; discriminate
         | [ H : TT = Op _ _ |- _ ] => exfalso; clear -H; discriminate
         | [ H : invert_Op ?e = None, H' : wff _ (Op ?opc _) ?e |- _ ]
           => progress (exfalso; clear -H H'; generalize dependent opc; intros; try (is_var e; destruct e))
         | [ H : invert_Op ?e = None, H' : wff _ ?e (Op ?opc _) |- _ ]
           => progress (exfalso; clear -H H'; generalize dependent opc; intros; try (is_var e; destruct e))
         | _ => progress destruct_head'_and
         | _ => progress subst
         | _ => progress destruct_head'_prod
         | _ => progress destruct_head'_sig
         | _ => progress destruct_head'_sigT
         | _ => inversion_base_type_constr_step
         | _ => inversion_wf_step_constr
         | _ => progress invert_expr_subst
         | _ => progress rewrite_eta_match_base_type_impl
         | [ H : ?x = ?x |- _ ] => clear H || (progress eliminate_hprop_eq)
         | [ H : match ?e with @const_of _ _ _ => _ = _ | _ => _ end |- _ ]
           => is_var e; destruct e
         | [ H : match ?e with @const_of _ _ _ => False | _ => _ end |- _ ]
           => is_var e; destruct e
         | [ H1 : _ = Some _, H2 : _ = None, Hwf : wff _ _ _ |- _ ]
           => pose proof (interp_as_expr_or_const_Some_None Hwf H1 H2); clear H1 H2
         | [ H1 : _ = None, H2 : _ = Some _, Hwf : wff _ _ _ |- _ ]
           => pose proof (interp_as_expr_or_const_None_Some Hwf H1 H2); clear H1 H2
         | [ |- wff _ (Op _ _) (LetIn _ _) ] => exfalso
         | [ |- wff _ (LetIn _ _) (Op _ _) ] => exfalso
         | [ |- wff _ (Pair _ _) (LetIn _ _) ] => exfalso
         | [ |- wff _ (LetIn _ _) (Pair _ _) ] => exfalso
         | _ => pose_wff ()
         | _ => progress cbn [fst snd projT1 projT2 interp_flat_type wff_as_expr_or_const eq_rect invert_Op] in *
         | [ |- wff _ _ _ ] => constructor; intros
         | [ H : match ?e with @const_of _ _ _ => _ | _ => _ end |- _ ]
           => is_var e; destruct e
         | [ |- context[match @interp_as_expr_or_const ?var ?t ?e with _ => _ end] ]
           => destruct (@interp_as_expr_or_const var t e) eqn:?
         | [ |- context[match base_type_eq_semidec_transparent ?t1 ?t2 with _ => _ end] ]
           => destruct (base_type_eq_semidec_transparent t1 t2)
         | [ |- context[match @invert_Op ?base_type ?op ?var ?t ?e with _ => _ end] ]
           => destruct (@invert_Op base_type op var t e) eqn:?
         | [ |- context[if BinInt.Z.eqb ?x ?y then _ else _] ]
           => destruct (BinInt.Z.eqb x y) eqn:?
         | [ |- context[if BinInt.Z.ltb ?x ?y then _ else _] ]
           => destruct (BinInt.Z.ltb x y) eqn:?
         | [ |- context[match ?e with @OpConst _ _ => _ | _ => _ end] ]
           => is_var e; destruct e
         | [ |- context[match ?e with @OpConst _ _ => _ | _ => _ end] ]
           => is_var e; invert_one_op e; try exact I; break_innermost_match_step; intros
         | [ |- List.In _ _ ] => progress (simpl; auto)
         | _ => break_innermost_match_step
         end.
Qed.

Hint Resolve Wf_SimplifyArith : wf.
