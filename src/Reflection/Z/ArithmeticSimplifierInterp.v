Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.RewriterInterp.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.OpInversion.
Require Import Crypto.Reflection.Z.ArithmeticSimplifier.
Require Import Crypto.Reflection.Z.Syntax.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.

Local Notation exprf := (@exprf base_type op interp_base_type).
Local Notation expr := (@expr base_type op interp_base_type).
Local Notation Expr := (@Expr base_type op).

Local Ltac fin_t :=
  first [ exact I
        | reflexivity
        | congruence
        | assumption
        | lia
        | exfalso; assumption ].
Local Ltac break_t_step :=
  first [ progress subst
        | progress inversion_option
        | progress inversion_sum
        | progress inversion_expr
        | progress inversion_prod
        | progress inversion_flat_type
        | progress destruct_head'_and
        | progress destruct_head'_prod
        | progress eliminate_hprop_eq
        | progress break_innermost_match_step
        | progress break_match_hyps ].


Lemma interp_as_expr_or_const_correct_base {t} e z
  : @interp_as_expr_or_const interp_base_type (Tbase t) e = Some z
    -> interpf interp_op e = match z with
                             | inl z => cast_const (t1:=TZ) z
                             | inr e => interpf interp_op e
                             end.
Proof.
  destruct z.
  { repeat first [ fin_t
                 | progress simpl in *
                 | progress intros
                 | break_t_step
                 | progress invert_expr
                 | progress invert_op ]. }
  { do 2 (invert_expr; break_innermost_match; intros);
      repeat first [ fin_t
                   | progress simpl in *
                   | progress intros
                   | break_t_step
                   | progress invert_op ]. }
Qed.

Lemma interp_as_expr_or_const_correct_prod_base {A B} e (v : _ * _)
  : @interp_as_expr_or_const interp_base_type (Prod (Tbase A) (Tbase B)) e = Some v
    -> interpf interp_op e = (match fst v with
                              | inl z => cast_const (t1:=TZ) z
                              | inr e => interpf interp_op e
                              end,
                              match snd v with
                              | inl z => cast_const (t1:=TZ) z
                              | inr e => interpf interp_op e
                              end).
Proof.
  invert_expr;
    repeat first [ fin_t
                 | progress simpl in *
                 | progress intros
                 | break_t_step
                 | erewrite !interp_as_expr_or_const_correct_base by eassumption; cbv beta iota ].
Qed.

Local Arguments Z.mul !_ !_.
Local Arguments Z.add !_ !_.
Local Arguments Z.sub !_ !_.

Lemma InterpSimplifyArith {t} (e : Expr t)
  : forall x, Interp interp_op (SimplifyArith e) x = Interp interp_op e x.
Proof.
  apply InterpRewriteOp; intros; unfold simplify_op_expr.
  break_innermost_match;
    repeat first [ fin_t
                 | progress simpl in *
                 | progress unfold interp_op, lift_op
                 | progress subst
                 | erewrite !interp_as_expr_or_const_correct_prod_base by eassumption; cbv beta iota
                 | erewrite !interp_as_expr_or_const_correct_base by eassumption; cbv beta iota
                 | progress Z.ltb_to_lt
                 | progress rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r ].
Qed.

Hint Rewrite @InterpSimplifyArith : reflective_interp.
