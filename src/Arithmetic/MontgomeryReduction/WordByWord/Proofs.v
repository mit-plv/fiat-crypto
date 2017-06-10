(*** Word-By-Word Montgomery Multiplication Proofs *)
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.micromega.Lia.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Local Open Scope Z_scope.

Section WordByWordMontgomery.
  Context
    {T : Type}
    {eval : T -> Z}
    {numlimbs : T -> nat}
    {zero : nat -> T}
    {divmod : T -> T * Z} (* returns lowest limb and all-but-lowest-limb *)
    {r : positive}
    {r_big : r > 1}
    {eval_zero : forall n, eval (zero n) = 0}
    {eval_div : forall v, eval (fst (divmod v)) = eval v / r}
    {eval_mod : forall v, snd (divmod v) = eval v mod r}
    {scmul : Z -> T -> T} (* uses double-output multiply *)
    {eval_scmul: forall a v, eval (scmul a v) = a * eval v}
    {R : positive}
    {R_big : R > 3} (* needed for [(N + B - 1) / R <= 1] *).
  Local Notation bn := (r * R) (only parsing).
  Context
    {add : T -> T -> T} (* joins carry *)
    {eval_add : forall a b, eval (add a b) = eval a + eval b}
    {eval_nonneg : forall v, 0 <= eval v}
    (N : T) (Npos : positive) (Npos_correct: eval N = Z.pos Npos)
    (N_small : eval N < R)
    (B : T)
    (B_small : eval B < R)
    ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N)).
  Context (k : Z) (k_correct : k * eval N mod r = -1).

  Create HintDb push_eval discriminated.
  Hint Rewrite
       eval_zero
       eval_div
       eval_mod
       eval_add
       eval_scmul
    : push_eval.

  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (A S : T)
            (S_small : eval S / R <= 1).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)

    Local Coercion eval : T >-> Z.

    Local Notation a := (@WordByWord.Definition.a T divmod A).
    Local Notation S3 := (@WordByWord.Definition.S3 T divmod r scmul add N B k A S).
    Local Notation S1 := (@WordByWord.Definition.S1 T divmod scmul add B A S).
    Local Notation cS2 := (@WordByWord.Definition.cS2 T divmod r scmul add N B k A S).

    Lemma S3_bound
      : 0 <= eval S < eval N + eval B
        -> 0 <= eval S3 < eval N + eval B.
    Proof.
      assert (Hmod : forall a b, 0 < b -> a mod b <= b - 1)
        by (intros x y; pose proof (Z_mod_lt x y); omega).
      intro HS.
      unfold S3, WordByWord.Definition.cS2, WordByWord.Definition.S1.
      autorewrite with push_eval.
      split;
        [ solve
            [ autounfold with word_by_word_montgomery;
              unfold Let_In; autorewrite with push_eval;
              Z.zero_bounds ]
        | ].
      eapply Z.le_lt_trans.
      { transitivity ((N+B-1 + (r-1)*B + (r-1)*N) / r);
          [ | set_evars; ring_simplify_subterms; subst_evars; reflexivity ].
        Z.peel_le; repeat apply Z.add_le_mono; repeat apply Z.mul_le_mono_nonneg; try lia;
          autounfold with word_by_word_montgomery;
          unfold Let_In; autorewrite with push_eval;
            try Z.zero_bounds;
            auto with lia. }
      rewrite (Z.mul_comm _ r), <- Z.add_sub_assoc, <- Z.add_opp_r, !Z.div_add_l' by lia.
      autorewrite with zsimplify.
      omega.
    Qed.

    Lemma S1_eq : eval S1 = S + a*B.
    Proof.
      cbv [S1 a WordByWord.Definition.A'].
      repeat autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma cS2_mod_N : (eval cS2) mod N = (S + a*B) mod N.
    Proof.
      assert (bn_large : bn >= r) by (unfold bn; nia).
      cbv [cS2 WordByWord.Definition.q WordByWord.Definition.s]; autorewrite with push_eval zsimplify. rewrite S1_eq. reflexivity.
    Qed.

    Lemma cS2_mod_r : cS2 mod r = 0.
      cbv [cS2 WordByWord.Definition.q WordByWord.Definition.s]; autorewrite with push_eval.
      assert (r > 0) by lia.
      assert (Hr : (-(1 mod r)) mod r = r - 1 /\ (-(1)) mod r = r - 1).
      { destruct (Z.eq_dec r 1) as [H'|H'].
        { rewrite H'; split; reflexivity. }
        { rewrite !Z_mod_nz_opp_full; rewrite ?Z.mod_mod; Z.rewrite_mod_small; [ split; reflexivity | omega.. ]. } }
      autorewrite with pull_Zmod.
      replace 0 with (0 mod r) by apply Zmod_0_l.
      eapply F.eq_of_Z_iff.
      repeat rewrite ?F.of_Z_add, ?F.of_Z_mul, <-?F.of_Z_mod.
      rewrite <-Algebra.Hierarchy.associative.
      replace ((F.of_Z r k * F.of_Z r (eval N))%F) with (F.opp (m:=r) F.one).
      { cbv [F.of_Z F.add]; simpl.
        apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ].
        simpl.
        rewrite (proj1 Hr), Z.mul_sub_distr_l.
        push_Zmod; pull_Zmod.
        autorewrite with zsimplify; reflexivity. }
      { rewrite <- F.of_Z_mul.
        rewrite F.of_Z_mod.
        rewrite k_correct.
        cbv [F.of_Z F.add F.opp F.one]; simpl.
        change (-(1)) with (-1) in *.
        apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ]; simpl.
        rewrite (proj1 Hr), (proj2 Hr); reflexivity. }
    Qed.

    Lemma S3_mod_N
      : S3 mod N = (S + a*B)*ri mod N.
    Proof.
      assert (r_div_bn : (r | bn)) by apply Z.divide_factor_l.
      cbv [S3]; autorewrite with push_eval cancel_pair.
      pose proof fun a => Z.div_to_inv_modulo N a r ri eq_refl ri_correct as HH;
                            cbv [Z.equiv_modulo] in HH; rewrite HH; clear HH.
      etransitivity; [rewrite (fun a => Z.mul_mod_l a ri N)|
                      rewrite (fun a => Z.mul_mod_l a ri N); reflexivity].
      rewrite <-cS2_mod_N; repeat (f_equal; []); autorewrite with push_eval.
      autorewrite with push_Zmod;
        replace (bn mod r) with 0
        by (symmetry; apply Z.mod_divide; try assumption; try lia);
        rewrite cS2_mod_r;
        autorewrite with zsimplify.
      reflexivity.
    Qed.

    Lemma small_from_bound
      : forall x, 0 <= x < eval N + eval B -> x / R <= 1.
    Proof.
      clear -R_big N_small B_small.
      intros x Hbound.
      cut ((N + B - 1) / R <= 1);
        [ Z.div_mod_to_quot_rem; subst; nia | ].
      transitivity (((R-1) + (R-1) - 1) / R);
        [ Z.peel_le; omega | ].
      autorewrite with zsimplify.
      reflexivity.
    Qed.
  End Iteration.

  Local Notation redc_body := (@redc_body T divmod r scmul add N B k).
  Local Notation redc_loop := (@redc_loop T divmod r scmul add N B k).
  Local Notation redc A := (@redc T numlimbs zero divmod r scmul add N A B k).

  Fixpoint redc_loop_rev (count : nat) : T * T -> T * T
    := match count with
       | O => fun A_S => A_S
       | S count' => fun A_S => redc_body (redc_loop_rev count' A_S)
       end.

  Lemma redc_loop_comm_body count
    : forall A_S, redc_loop count (redc_body A_S) = redc_body (redc_loop count A_S).
  Proof.
    induction count as [|count IHcount]; try reflexivity.
    simpl; intro; rewrite IHcount; reflexivity.
  Qed.

  Lemma redc_loop__redc_loop_rev count
    : forall A_S, redc_loop count A_S = redc_loop_rev count A_S.
  Proof.
    induction count as [|count IHcount]; try reflexivity.
    simpl; intro; rewrite <- IHcount, redc_loop_comm_body; reflexivity.
  Qed.

  Section body.
    Context (A_S : T * T).
    Let A':=fst A_S.
    Let S:=snd A_S.
    Let A_a:=divmod A'.
    Let a:=snd A_a.
    Context (S_small : eval S / R <= 1).

    Lemma redc_body_mod_N
      : (eval (snd (redc_body A_S))) mod (eval N) = (eval S + a*eval B)*ri mod (eval N).
    Proof.
      destruct A_S; apply S3_mod_N; assumption.
    Qed.

    Lemma fst_redc_body
      : (eval (fst (redc_body A_S))) = eval (fst A_S) / r.
    Proof.
      destruct A_S; simpl; unfold WordByWord.Definition.A', WordByWord.Definition.A_a, Let_In, a, A_a, A'; simpl.
      autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma fst_redc_body_mod_N
      : (eval (fst (redc_body A_S))) mod (eval N) = ((eval (fst A_S) - a)*ri) mod (eval N).
    Proof.
      rewrite fst_redc_body.
      etransitivity; [ eapply Z.div_to_inv_modulo; try eassumption; lia | ].
      unfold a, A_a, A'.
      autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma redc_body_bound
      : 0 <= eval S < eval N + eval B
        -> 0 <= eval (snd (redc_body A_S)) < eval N + eval B.
    Proof.
      destruct A_S; apply S3_bound.
    Qed.
  End body.

  Local Arguments Z.pow !_ !_.
  Local Arguments Z.of_nat !_.
  Lemma redc_loop_bound A_S count
    : 0 <= eval (snd A_S) < eval N + eval B
      -> 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
  Proof.
    rewrite redc_loop__redc_loop_rev.
    induction count as [|count IHcount].
    { simpl; trivial. }
    { simpl; intro;
        repeat first [ apply redc_body_bound
                     | apply IHcount
                     | assumption
                     | apply small_from_bound ]. }
  Qed.

  Lemma fst_redc_loop A_S count
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : eval (fst (redc_loop count A_S)) = eval (fst A_S) / r^(Z.of_nat count).
  Proof.
    rewrite redc_loop__redc_loop_rev.
    induction count as [|count IHcount].
    { simpl; autorewrite with zsimplify; reflexivity. }
    { simpl @redc_loop_rev.
      rewrite fst_redc_body, IHcount
        by (apply small_from_bound; rewrite <-redc_loop__redc_loop_rev; apply redc_loop_bound; auto).
      rewrite Zdiv_Zdiv by Z.zero_bounds.
      rewrite <- (Z.pow_1_r r) at 2.
      rewrite <- Z.pow_add_r by lia.
      replace (Z.of_nat count + 1) with (Z.of_nat (S count)) by (simpl; lia).
      reflexivity. }
  Qed.

  Lemma fst_redc_loop_mod_N A_S count
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : eval (fst (redc_loop count A_S)) mod (eval N) = eval (fst A_S) * ri^(Z.of_nat count) mod (eval N).
  Proof.
    rewrite fst_redc_loop by assumption.
    destruct count.
    { simpl; autorewrite with zsimplify; reflexivity. }
    { etransitivity; [ eapply Z.div_to_inv_modulo; try eassumption | ].
      Focus 2.
      erewrite <- Z.pow_mul_l, <- Z.pow_1_l.
  Admitted.

  Lemma redc_loop_mod_N A_S count
        (S_bound : 0 <= eval (snd A_S) < eval N + eval B)
    : (eval (snd (redc_loop count A_S))) mod (eval N) = ((eval (snd A_S) + (eval (fst A_S) mod ri^(Z.of_nat count))*eval B)*ri^(Z.of_nat count)) mod (eval N).
  Proof.
    rewrite redc_loop__redc_loop_rev.
    induction count as [|count IHcount].
    { simpl; autorewrite with zsimplify; reflexivity. }
    { simpl; rewrite redc_body_mod_N
        by (apply small_from_bound; rewrite <- redc_loop__redc_loop_rev; apply redc_loop_bound; auto).
      push_Zmod; rewrite IHcount; pull_Zmod.
      autorewrite with push_eval.
      rewrite <- redc_loop__redc_loop_rev, fst_redc_loop by omega.
      match goal with
      | [ |- ?x mod ?N = ?y mod ?N ]
        => change (Z.equiv_modulo N x y)
      end.
      destruct A_S as [A S].
      cbn [fst snd].
      change (Z.pos (Pos.of_succ_nat ?n)) with (Z.of_nat (Datatypes.S n)).
      rewrite !Z.mul_add_distr_r.
      rewrite <- !Z.mul_assoc.
      replace (ri^(Z.of_nat count) * ri) with (ri^(Z.of_nat (Datatypes.S count)))
        by (change (Datatypes.S count) with (1 + count)%nat;
            autorewrite with push_Zof_nat; rewrite Z.pow_add_r by lia; simpl Z.succ; rewrite Z.pow_1_r; nia).
      rewrite <- !Z.add_assoc.
      apply Z.add_mod_Proper; [ reflexivity | ].
      Unset Printing Coercions.
      Coercion eval : T >-> Z.
      Coercion Z.of_nat : nat >-> Z.
      Notation "x '.+1'" := (Datatypes.S x) (format "x '.+1'", at level 10).
      Infix "≡" := (Z.equiv_modulo _) (at level 70).
  Admitted.

  Lemma redc_mod_N A
    : (eval (redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat (numlimbs A))) mod (eval N).
  Proof.
    unfold redc.
    rewrite redc_loop_mod_N; cbn [fst snd];
      autorewrite with push_eval zsimplify;
      [ | rewrite Npos_correct; pose proof (eval_nonneg B); lia ].
  Admitted.
End WordByWordMontgomery.
