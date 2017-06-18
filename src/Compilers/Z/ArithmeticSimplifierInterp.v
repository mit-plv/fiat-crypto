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
                   | rewrite FixedWordSizesEquality.ZToWord_wordToZ
                   | rewrite FixedWordSizesEquality.ZToWord_wordToZ_ZToWord by reflexivity
                   | rewrite FixedWordSizesEquality.wordToZ_ZToWord_0
                   | progress rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r
                   | rewrite !Z.sub_with_borrow_to_add_get_carry
                   | progress autorewrite with zsimplify_fast
                   | progress cbv [cast_const ZToInterp interpToZ]
                   | progress change (Z.pow_pos 2 1) with 2%Z in *
                   | progress change (Z.pow_pos 2 2) with 4%Z in *
                   | nia
                   | progress cbv [Z.add_with_carry]
                   | match goal with
                     | [ |- context[(?x mod ?m)%Z] ]
                       => rewrite (Z.mod_small x m) by solve_word_small ()
                     | [ |- context[(?x / ?m)%Z] ]
                       => rewrite (Z.div_small x m) by solve_word_small ()
                     | [ H : ?x = 0%Z |- context[?x] ] => rewrite H
                     | [ H : ?x = 1%Z |- context[?x] ] => rewrite H
                     | [ H : (_ =? _)%nat = true |- _ ] => apply beq_nat_true in H
                     | [ H : (_ <? _)%nat = true |- _ ] => apply NPeano.Nat.ltb_lt in H
                     | [ |- context[FixedWordSizes.wordToZ_gen ?x] ]
                       => lazymatch goal with
                          | [ H : (0 <= FixedWordSizes.wordToZ_gen x)%Z |- _ ] => fail
                          | [ H : (0 <= FixedWordSizes.wordToZ_gen x < _)%Z |- _ ] => fail
                          | _ => pose proof (FixedWordSizesEquality.wordToZ_gen_range x)
                          end
                     | [ |- context[Z.max ?x ?y] ]
                       => first [ rewrite (Z.max_r x y) by omega
                                | rewrite (Z.max_l x y) by omega ]
                     | [ H : 0 < ?e |- context[(_ mod (2^Z.of_nat (2^?e)))%Z] ]
                       => lazymatch goal with
                          | [ H : (_ <= 2^Z.of_nat (2^e))%Z |- _ ] => fail
                          | _ => assert (2^Z.of_nat (2^1) <= 2^Z.of_nat (2^e))%Z
                              by (rewrite !Z.pow_Zpow; simpl Z.of_nat; auto with zarith)
                          end
                     | [ H : (1 < ?e)%Z |- context[(_ mod (2^?e))%Z] ]
                       => lazymatch goal with
                          | [ H : (_ <= 2^e)%Z |- _ ] => fail
                          | _ => assert (2^2 <= 2^e)%Z
                              by auto with zarith
                          end
                     | [ |- context[Z.max 0 (?x mod ?y)] ]
                       => rewrite (Z.max_r 0 (x mod y))
                         by Z.zero_bounds
                     | [ |- context[Z.max 0 ((?x mod ?y) * (?z mod ?w))] ]
                       => rewrite (Z.max_r 0 ((x mod y) * (z mod w)))
                         by Z.zero_bounds
                     end
                   | rewrite !FixedWordSizesEquality.wordToZ_ZToWord_mod_full
                   | progress Z.rewrite_mod_small
                   | rewrite Z.div_small by omega
                   | rewrite <- FixedWordSizesEquality.eq_ZToWord ].
  all:repeat first [ reflexivity
                   | omega
                   | discriminate
                   | progress cbv [LetIn.Let_In Z.zselect IdfunWithAlt.id_with_alt]
                   | progress subst
                   | progress simpl in *
                   | progress Bool.split_andb
                   | progress Z.ltb_to_lt
                   | break_innermost_match_step
                   | rewrite FixedWordSizesEquality.ZToWord_wordToZ
                   | rewrite FixedWordSizesEquality.ZToWord_wordToZ_ZToWord by reflexivity
                   | rewrite FixedWordSizesEquality.wordToZ_ZToWord_0
                   | progress rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r
                   | rewrite !Z.sub_with_borrow_to_add_get_carry
                   | progress autorewrite with zsimplify_fast
                   | progress cbv [cast_const ZToInterp interpToZ]
                   | progress change (Z.pow_pos 2 1) with 2%Z in *
                   | progress change (Z.pow_pos 2 2) with 4%Z in *
                   | nia
                   | progress cbv [Z.add_with_carry]
                   | match goal with
                     | [ |- context[(?x mod ?m)%Z] ]
                       => rewrite (Z.mod_small x m) by solve_word_small ()
                     | [ |- context[(?x / ?m)%Z] ]
                       => rewrite (Z.div_small x m) by solve_word_small ()
                     | [ H : ?x = 0%Z |- context[?x] ] => rewrite H
                     | [ H : ?x = 1%Z |- context[?x] ] => rewrite H
                     | [ H : (_ =? _)%nat = true |- _ ] => apply beq_nat_true in H
                     | [ H : (_ <? _)%nat = true |- _ ] => apply NPeano.Nat.ltb_lt in H
                     | [ |- context[FixedWordSizes.wordToZ_gen ?x] ]
                       => lazymatch goal with
                          | [ H : (0 <= FixedWordSizes.wordToZ_gen x)%Z |- _ ] => fail
                          | [ H : (0 <= FixedWordSizes.wordToZ_gen x < _)%Z |- _ ] => fail
                          | _ => pose proof (FixedWordSizesEquality.wordToZ_gen_range x)
                          end
                     | [ |- context[Z.max ?x ?y] ]
                       => first [ rewrite (Z.max_r x y) by omega
                                | rewrite (Z.max_l x y) by omega ]
                     | [ H : 0 < ?e |- context[(_ mod (2^Z.of_nat (2^?e)))%Z] ]
                       => lazymatch goal with
                          | [ H : (_ <= 2^Z.of_nat (2^e))%Z |- _ ] => fail
                          | _ => assert (2^Z.of_nat (2^1) <= 2^Z.of_nat (2^e))%Z
                              by (rewrite !Z.pow_Zpow; simpl Z.of_nat; auto with zarith)
                          end
                     | [ H : (1 < ?e)%Z |- context[(_ mod (2^?e))%Z] ]
                       => lazymatch goal with
                          | [ H : (_ <= 2^e)%Z |- _ ] => fail
                          | _ => assert (2^2 <= 2^e)%Z
                              by auto with zarith
                          end
                     | [ |- context[Z.max 0 (?x mod ?y)] ]
                       => rewrite (Z.max_r 0 (x mod y))
                         by Z.zero_bounds
                     | [ |- context[Z.max 0 ((?x mod ?y) * (?z mod ?w))] ]
                       => rewrite (Z.max_r 0 ((x mod y) * (z mod w)))
                         by Z.zero_bounds
                     | [ |- context[Z.max 0 ((?x mod ?y) * (FixedWordSizes.wordToZ ?z))] ]
                       => rewrite (Z.max_r 0 ((x mod y) * (FixedWordSizes.wordToZ z)))
                         by (Z.zero_bounds; apply FixedWordSizesEquality.wordToZ_range)
                     | [ |- context[Z.max 0 ((FixedWordSizes.wordToZ ?z) * (?x mod ?y))] ]
                       => rewrite (Z.max_r 0 ((FixedWordSizes.wordToZ z) * (x mod y)))
                         by (Z.zero_bounds; apply FixedWordSizesEquality.wordToZ_range)
                     | [ |- context[((?x * ?y) mod ?z)%Z] ]
                       => lazymatch constr:((x * y)%Z) with
                          | ((_ mod z) * (_ mod z))%Z => fail
                          | _ => rewrite (Z.mul_mod x y z)
                          end
                     | [ |- (_ <> 0)%Z ] => apply Z.pow_nonzero; lia
                     | [ |- interpf ?interp_op ?e = ?x ]
                       => rewrite <- (FixedWordSizesEquality.ZToWord_wordToZ (interpf interp_op e)), <- FixedWordSizesEquality.eq_ZToWord
                     | [ |- context[Z.max 0 (FixedWordSizes.wordToZ ?e)] ]
                       => rewrite (Z.max_r 0 (FixedWordSizes.wordToZ e))
                         by apply FixedWordSizesEquality.wordToZ_range
                     end
                   | rewrite !FixedWordSizesEquality.wordToZ_ZToWord_mod_full
                   | progress Z.rewrite_mod_small
                   | rewrite Z.div_small by omega
                   | rewrite <- FixedWordSizesEquality.eq_ZToWord ].
Qed.

Hint Rewrite @InterpSimplifyArith : reflective_interp.
