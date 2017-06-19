Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
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
Require Import Crypto.Util.Tactics.UniquePose.

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

Local Ltac solve_word_small _ :=
  lazymatch goal with
  | [ H : (2^Z.of_nat ?b <= ?bw)%Z |- (0 <= FixedWordSizes.wordToZ ?x < 2^?bw)%Z ]
    => cut (0 <= FixedWordSizes.wordToZ x < 2^(Z.of_nat (2^b)%nat))%Z;
       [ rewrite Z.pow_Zpow; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
         assert ((2^2^Z.of_nat b <= 2^bw)%Z) by auto with zarith;
         auto with zarith
       | apply FixedWordSizesEquality.wordToZ_range ]
  end.

Definition interpf_as_expr_or_const {t}
  : interp_flat_type (@inverted_expr interp_base_type) t -> interp_flat_type interp_base_type t
  := SmartVarfMap
       (fun t z => match z with
                   | const_of z => cast_const (t1:=TZ) z
                   | gen_expr e => interpf interp_op e
                   | neg_expr e => interpf interp_op (Op (Opp _ _) e)
                   end).

Lemma interp_as_expr_or_const_correct {t} e z
  : @interp_as_expr_or_const interp_base_type t e = Some z
    -> interpf interp_op e = interpf_as_expr_or_const z.
Proof.
  induction e;
    repeat first [ progress subst
                 | progress inversion_option
                 | progress simpl in *
                 | progress cbn [interpf_as_expr_or_const SmartVarfMap smart_interp_flat_map]
                 | reflexivity
                 | break_innermost_match_hyps_step
                 | intro
                 | match goal with
                   | [ H : forall z, Some _ = Some z -> _ |- _ ] => specialize (H _ eq_refl)
                   | [ H : interpf _ ?e = interpf_as_expr_or_const _ |- _ ]
                     => rewrite H
                   | [ |- context[match ?e with _ => _ end] ]
                     => is_var e; invert_one_op e
                   end
                 | break_innermost_match_step ].
Qed.

Local Ltac rewrite_interp_as_expr_or_const_correct _ :=
  match goal with
  | [ |- context[interpf _ ?e] ]
    => erewrite !(@interp_as_expr_or_const_correct _ e) by eassumption; cbv beta iota;
       cbn [interpf_as_expr_or_const SmartVarfMap smart_interp_flat_map]
  end.

Local Arguments Z.mul !_ !_.
Local Arguments Z.add !_ !_.
Local Arguments Z.sub !_ !_.
Local Arguments Z.opp !_.
Local Arguments interp_op _ _ !_ _ / .
Local Arguments lift_op / .
Local Opaque Z.pow.

Lemma InterpSimplifyArith {convert_adc_to_sbb} {t} (e : Expr t)
  : forall x, Interp interp_op (SimplifyArith convert_adc_to_sbb e) x = Interp interp_op e x.
Proof.
  apply InterpRewriteOp; intros; unfold simplify_op_expr.
  Time break_innermost_match;
    repeat first [ reflexivity
                 | progress subst
                 | progress simpl in *
                 | progress inversion_prod
                 | progress invert_expr_subst
                 | inversion_base_type_constr_step
                 | match goal with
                   | [ |- context[match ?e with _ => _ end] ]
                     => is_var e; invert_one_op e;
                        repeat match goal with
                               | [ |- match ?T with _ => _ end _ ]
                                 => break_innermost_match_step; try exact I
                               end
                   end
                 | break_innermost_match_step
                 | rewrite_interp_as_expr_or_const_correct ()
                 | intro ].
  all:repeat first [ reflexivity
                   | omega
                   | discriminate
                   | progress cbv [LetIn.Let_In Z.zselect IdfunWithAlt.id_with_alt]
                   | progress subst
                   | progress simpl in *
                   | progress Bool.split_andb
                   | progress Z.ltb_to_lt
                   | break_innermost_match_step
                   | apply (f_equal2 pair)
                   | progress cbv [cast_const ZToInterp interpToZ]
                   | match goal with
                     | [ |- interpf ?interp_op ?e = ?x ]
                       => rewrite <- (FixedWordSizesEquality.ZToWord_wordToZ (interpf interp_op e)), <- FixedWordSizesEquality.eq_ZToWord
                     end
                   | rewrite <- FixedWordSizesEquality.eq_ZToWord ].
  all:repeat first [ rewrite FixedWordSizesEquality.ZToWord_wordToZ
                   | rewrite FixedWordSizesEquality.ZToWord_wordToZ_ZToWord by reflexivity
                   | rewrite FixedWordSizesEquality.wordToZ_ZToWord_0
                   | rewrite !FixedWordSizesEquality.wordToZ_ZToWord_mod_full ].
  all:repeat match goal with
             | [ H : _ = Some eq_refl |- _ ] => clear H
             | [ H : interp_as_expr_or_const _ = Some _ |- _ ] => clear H
             | [ H : interpf _ _ = _ |- _ ] => clear H
             | [ H : Syntax.exprf _ _ _ |- _ ] => clear H
             | [ H : Expr _ |- _ ] => clear H
             | [ H : type _ |- _ ] => clear H
             | [ H : bool |- _ ] => clear H
             | [ |- context[FixedWordSizes.wordToZ ?e] ]
               => pose proof (FixedWordSizesEquality.wordToZ_range e);
                    lazymatch e with
                    | interpf interp_op ?e'
                      => generalize dependent (FixedWordSizes.wordToZ e); clear e'; intros
                    | _ => is_var e; generalize dependent (FixedWordSizes.wordToZ e);
                             clear e; intros
                    end
             | [ |- context[interpf interp_op ?e] ]
               => is_var e; generalize dependent (interpf interp_op e); clear e; intros
             | [ |- context[Z.of_nat (2^?e)] ]
               => is_var e; assert ((0 < Z.of_nat (2^e))%Z)
                    by (rewrite Z.pow_Zpow; simpl Z.of_nat; Z.zero_bounds);
                  generalize dependent (Z.of_nat (2^e)); clear e; intros
             end.
  all:try nia.
  Time
    all:repeat first [ reflexivity
                     | omega
                     | progress change (2^0)%Z with 1%Z in *
                     | progress change (2^1)%Z with 2%Z in *
                     | progress rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r, ?Z.opp_involutive, ?Z.shiftr_0_r
                     | progress rewrite ?Z.land_ones by lia
                     | progress autorewrite with Zshift_to_pow in *
                     | rewrite !Z.sub_with_borrow_to_add_get_carry
                     | progress cbv [Z.add_with_carry]
                     | rewrite Z.mod_mod by Z.zero_bounds
                     | match goal with
                       | [ |- context[(?x mod ?y)%Z] ]
                         => lazymatch goal with
                            | [ H : (0 <= x mod y)%Z |- _ ] => fail
                            | [ H : (0 <= x mod y < _)%Z |- _ ] => fail
                            | _ => assert (0 <= x mod y < y)%Z by (apply Z.mod_pos_bound; Z.zero_bounds; lia)
                            end
                       | [ |- context[(?x / ?y)%Z] ]
                         => lazymatch goal with
                            | [ H : (0 <= x / y)%Z |- _ ] => fail
                            | _ => assert (0 <= x / y)%Z by Z.zero_bounds
                            end
                       | [ H : (2^Z.of_nat ?bw <= ?bw')%Z |- context[(2^?bw')%Z] ]
                         => unique assert ((2^Z.of_nat (2^bw) <= 2^bw')%Z)
                           by (rewrite Z.pow_Zpow; simpl @Z.of_nat; auto with zarith)
                       end
                     | progress autorewrite with zsimplify_const in *
                     | match goal with
                       | [ H : (2^?x <= 1)%Z, H' : (0 < ?x)%Z |- _ ]
                         => lazymatch goal with
                            | [ |- False ] => fail
                            | _ => exfalso; clear -H H'; assert (2^1 <= 2^x)%Z by auto with zarith
                            end
                       | [ H : (0 <= ?x < _)%Z |- context[Z.max 0 ?x] ]
                         => rewrite (Z.max_r 0 x) in * by apply H
                       | [ H : (0 <= ?x)%Z |- context[Z.max 0 ?x] ]
                         => rewrite (Z.max_r 0 x) in * by apply H
                       | [ H : (0 <= ?x < _)%Z, H' : (0 <= ?y < _)%Z |- context[Z.max 0 (?x * ?y)] ]
                         => rewrite (Z.max_r 0 (x * y)) in * by (apply Z.mul_nonneg_nonneg; first [ apply H | apply H' ])
                       | [ H : (0 <= ?x < _)%Z, H' : (0 <= ?y < _)%Z |- context[Z.max 0 (?x + ?y)] ]
                         => rewrite (Z.max_r 0 (x + y)) in * by (apply Z.add_nonneg_nonneg; first [ apply H | apply H' ])
                       | [ H : ?x = 0%Z |- context[?x] ] => rewrite H
                       | [ H : ?x = 0%Z, H' : context[?x] |- _ ] => rewrite H in H'
                       | [ H : ?x = Z.pos _ |- context[?x] ] => rewrite H
                       | [ H : ?x = Z.pos _, H' : context[?x] |- _ ] => rewrite H in H'
                       | [ H : context[(_^Z.neg ?p)%Z] |- _ ]
                         => rewrite (Z.pow_neg_r _ (Z.neg p)) in H by lia
                       | [ H : (?x mod ?y = 0)%Z |- context[((?x * _) mod ?y)%Z] ]
                         => rewrite (Z.mul_mod_full x _ y)
                       | [ H : (?x mod ?y = 0)%Z |- context[((_ * ?x) mod ?y)%Z] ]
                         => rewrite (Z.mul_mod_full _ x y)
                       | [ H : ?x = Z.pos _ |- context[?x] ] => rewrite H
                       | [ H : (?x mod ?y = Z.pos _)%Z |- context[((?x * _) mod ?y)%Z] ]
                         => rewrite (Z.mul_mod_full x _ y)
                       | [ H : (?x mod ?y = Z.pos _)%Z |- context[((_ * ?x) mod ?y)%Z] ]
                         => rewrite (Z.mul_mod_full _ x y)
                       | [ |- context[(?x mod ?m)%Z] ]
                         => rewrite (Z.mod_small x m) by Z.rewrite_mod_small_solver
                       | [ |- context[(?x / ?m)%Z] ]
                         => rewrite (Z.div_small x m) by Z.rewrite_mod_small_solver
                       end
                     | progress pull_Zmod ].
Qed.

Hint Rewrite @InterpSimplifyArith : reflective_interp.
