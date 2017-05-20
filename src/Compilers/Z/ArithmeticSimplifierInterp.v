Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.RewriterInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.OpInversion.
Require Import Crypto.Compilers.Z.ArithmeticSimplifier.
Require Import Crypto.Compilers.Z.ArithmeticSimplifierUtil.
Require Import Crypto.Compilers.Z.Syntax.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.AddGetCarry.
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
        | progress inversion_inverted_expr
        | progress inversion_flat_type
        | progress subst_prod
        | progress destruct_head'_and
        | progress destruct_head'_prod
        | progress eliminate_hprop_eq
        | progress break_innermost_match_step
        | progress break_match_hyps ].


Lemma interp_as_expr_or_const_correct_base {t} e z
  : @interp_as_expr_or_const interp_base_type (Tbase t) e = Some z
    -> interpf interp_op e = match z with
                             | const_of z => cast_const (t1:=TZ) z
                             | gen_expr e => interpf interp_op e
                             | neg_expr e => interpf interp_op (Op (Opp _ _) e)
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
  { do 2 (invert_expr; break_innermost_match; intros);
      repeat first [ fin_t
                   | progress simpl in *
                   | progress intros
                   | break_t_step
                   | progress invert_op ]. }
Qed.

Local Ltac rewrite_interp_as_expr_or_const_correct_base _ :=
  match goal with
  | [ |- context[interpf _ ?e] ]
    => erewrite !(@interp_as_expr_or_const_correct_base _ e) by eassumption; cbv beta iota
  end.

Lemma interp_as_expr_or_const_correct_prod_base {A B} e (v : _ * _)
  : @interp_as_expr_or_const interp_base_type (Prod (Tbase A) (Tbase B)) e = Some v
    -> interpf interp_op e = (match fst v with
                              | const_of z => cast_const (t1:=TZ) z
                              | gen_expr e => interpf interp_op e
                              | neg_expr e => interpf interp_op (Op (Opp _ _) e)
                              end,
                              match snd v with
                              | const_of z => cast_const (t1:=TZ) z
                              | gen_expr e => interpf interp_op e
                              | neg_expr e => interpf interp_op (Op (Opp _ _) e)
                              end).
Proof.
  invert_expr;
    repeat first [ fin_t
                 | progress simpl in *
                 | progress intros
                 | break_t_step
                 | rewrite_interp_as_expr_or_const_correct_base () ].
Qed.

Local Ltac rewrite_interp_as_expr_or_const_correct_prod_base _ :=
  match goal with
  | [ |- context[interpf _ ?e] ]
    => erewrite !(@interp_as_expr_or_const_correct_prod_base _ _ e) by eassumption; cbv beta iota
  end.

Lemma interp_as_expr_or_const_correct_prod3_base {A B C} e (v : _ * _ * _)
  : @interp_as_expr_or_const interp_base_type (Prod (Prod (Tbase A) (Tbase B)) (Tbase C)) e = Some v
    -> interpf interp_op e = (match fst (fst v) with
                              | const_of z => cast_const (t1:=TZ) z
                              | gen_expr e => interpf interp_op e
                              | neg_expr e => interpf interp_op (Op (Opp _ _) e)
                              end,
                              match snd (fst v) with
                              | const_of z => cast_const (t1:=TZ) z
                              | gen_expr e => interpf interp_op e
                              | neg_expr e => interpf interp_op (Op (Opp _ _) e)
                              end,
                              match snd v with
                              | const_of z => cast_const (t1:=TZ) z
                              | gen_expr e => interpf interp_op e
                              | neg_expr e => interpf interp_op (Op (Opp _ _) e)
                              end).
Proof.
  invert_expr;
    repeat first [ fin_t
                 | progress simpl in *
                 | progress intros
                 | break_t_step
                 | rewrite_interp_as_expr_or_const_correct_base ()
                 | rewrite_interp_as_expr_or_const_correct_prod_base () ].
Qed.

Local Ltac rewrite_interp_as_expr_or_const_correct_prod3_base _ :=
  match goal with
  | [ |- context[interpf _ ?e] ]
    => erewrite !(@interp_as_expr_or_const_correct_prod3_base _ _ _ e) by eassumption; cbv beta iota
  end.

Local Arguments Z.mul !_ !_.
Local Arguments Z.add !_ !_.
Local Arguments Z.sub !_ !_.
Local Arguments Z.opp !_.

Lemma InterpSimplifyArith {t} (e : Expr t)
  : forall x, Interp interp_op (SimplifyArith e) x = Interp interp_op e x.
Proof.
  apply InterpRewriteOp; intros; unfold simplify_op_expr.
  break_innermost_match;
    repeat first [ fin_t
                 | progress cbv [LetIn.Let_In]
                 | progress simpl in *
                 | progress subst
                 | progress subst_prod
                 | rewrite_interp_as_expr_or_const_correct_base ()
                 | rewrite_interp_as_expr_or_const_correct_prod_base ()
                 | rewrite_interp_as_expr_or_const_correct_prod3_base ()
                 | progress unfold interp_op, lift_op
                 | progress Z.ltb_to_lt
                 | progress rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r
                 | rewrite !Z.sub_with_borrow_to_add_get_carry
                 | progress autorewrite with zsimplify_fast ].
Qed.

Hint Rewrite @InterpSimplifyArith : reflective_interp.
