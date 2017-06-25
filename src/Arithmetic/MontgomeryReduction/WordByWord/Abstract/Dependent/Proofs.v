(*** Word-By-Word Montgomery Multiplication Proofs *)
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.micromega.Lia.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Definition.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Section WordByWordMontgomery.
  Context
    {T : nat -> Type}
    {eval : forall {n}, T n -> Z}
    {zero : forall {n}, T n}
    {divmod : forall {n}, T (S n) -> T n * Z} (* returns lowest limb and all-but-lowest-limb *)
    {r : positive}
    {r_big : r > 1}
    {R : positive}
    {R_numlimbs : nat}
    {R_correct : R = r^Z.of_nat R_numlimbs :> Z}
    {small : forall {n}, T n -> Prop}
    {eval_zero : forall n, eval (@zero n) = 0}
    {small_zero : forall n, small (@zero n)}
    {eval_div : forall n v, small v -> eval (fst (@divmod n v)) = eval v / r}
    {eval_mod : forall n v, small v -> snd (@divmod n v) = eval v mod r}
    {small_div : forall n v, small v -> small (fst (@divmod n v))}
    {scmul : forall {n}, Z -> T n -> T (S n)} (* uses double-output multiply *)
    {eval_scmul: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < R -> eval (@scmul n a v) = a * eval v}
    {small_scmul : forall n a v, small v -> 0 <= a < r -> 0 <= eval v < R -> small (@scmul n a v)}
    {addT : forall {n}, T n -> T n -> T (S n)} (* joins carry *)
    {eval_addT : forall n a b, eval (@addT n a b) = eval a + eval b}
    {small_addT : forall n a b, small a -> small b -> small (@addT n a b)}
    {addT' : forall {n}, T (S n) -> T n -> T (S (S n))} (* joins carry *)
    {eval_addT' : forall n a b, eval (@addT' n a b) = eval a + eval b}
    {small_addT' : forall n a b, small a -> small b -> small (@addT' n a b)}
    {drop_high : T (S (S R_numlimbs)) -> T (S R_numlimbs)} (* drops the highest limb *)
    {eval_drop_high : forall v, small v -> eval (drop_high v) = eval v mod (r * r^Z.of_nat R_numlimbs)}
    {small_drop_high : forall v, small v -> small (drop_high v)}
    (N : T R_numlimbs) (Npos : positive) (Npos_correct: eval N = Z.pos Npos)
    (small_N : small N)
    (N_lt_R : eval N < R)
    {conditional_sub : T (S R_numlimbs) -> T R_numlimbs} (* computes [arg - N] if [N <= arg], and drops high bit *)
    {eval_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> eval (conditional_sub v) = eval v + if eval N <=? eval v then -eval N else 0}
    {small_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> small (conditional_sub v)}
    {sub_then_maybe_add : T R_numlimbs -> T R_numlimbs -> T R_numlimbs} (* computes [a - b + if (a - b) <? 0 then N else 0] *)
    {eval_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> eval (sub_then_maybe_add a b) = eval a - eval b + if eval a - eval b <? 0 then eval N else 0}
    {small_sub_then_maybe_add : forall a b, small (sub_then_maybe_add a b)}
    (B : T R_numlimbs)
    (B_bounds : 0 <= eval B < R)
    (small_B : small B)
    ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
    (k : Z) (k_correct : k * eval N mod r = (-1) mod r).

  Create HintDb push_eval discriminated.
  Local Ltac t_small :=
    repeat first [ assumption
                 | apply small_addT
                 | apply small_addT'
                 | apply small_div
                 | apply small_drop_high
                 | apply small_zero
                 | apply small_scmul
                 | apply small_conditional_sub
                 | apply small_sub_then_maybe_add
                 | apply Z_mod_lt
                 | rewrite Z.mul_split_mod
                 | solve [ auto with zarith ]
                 | lia
                 | progress autorewrite with push_eval
                 | progress autounfold with word_by_word_montgomery
                 | match goal with
                   | [ H : and _ _ |- _ ] => destruct H
                   end ].
  Hint Rewrite
       eval_zero
       eval_div
       eval_mod
       eval_addT
       eval_addT'
       eval_scmul
       eval_drop_high
       eval_conditional_sub
       eval_sub_then_maybe_add
       using (repeat autounfold with word_by_word_montgomery; t_small)
    : push_eval.

  Local Arguments eval {_} _.
  Local Arguments small {_} _.
  Local Arguments divmod {_} _.

  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (pred_A_numlimbs : nat)
            (A : T (S pred_A_numlimbs))
            (S : T (S R_numlimbs))
            (small_A : small A)
            (small_S : small S)
            (S_nonneg : 0 <= eval S).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)

    Local Coercion eval : T >-> Z.

    Local Notation a := (@WordByWord.Abstract.Dependent.Definition.a T (@divmod) pred_A_numlimbs A).
    Local Notation A' := (@WordByWord.Abstract.Dependent.Definition.A' T (@divmod) pred_A_numlimbs A).
    Local Notation S1 := (@WordByWord.Abstract.Dependent.Definition.S1 T (@divmod) R_numlimbs scmul addT pred_A_numlimbs B A S).
    Local Notation s := (@WordByWord.Abstract.Dependent.Definition.s T (@divmod) R_numlimbs scmul addT pred_A_numlimbs B A S).
    Local Notation q := (@WordByWord.Abstract.Dependent.Definition.q T (@divmod) r R_numlimbs scmul addT pred_A_numlimbs B k A S).
    Local Notation S2 := (@WordByWord.Abstract.Dependent.Definition.S2 T (@divmod) r R_numlimbs scmul addT addT' N pred_A_numlimbs B k A S).
    Local Notation S3 := (@WordByWord.Abstract.Dependent.Definition.S3 T (@divmod) r R_numlimbs scmul addT addT' N pred_A_numlimbs B k A S).
    Local Notation S4 := (@WordByWord.Abstract.Dependent.Definition.S4 T (@divmod) r R_numlimbs scmul addT addT' drop_high N pred_A_numlimbs B k A S).

    Lemma S3_bound
      : eval S < eval N + eval B
        -> eval S3 < eval N + eval B.
    Proof.
      assert (Hmod : forall a b, 0 < b -> a mod b <= b - 1)
        by (intros x y; pose proof (Z_mod_lt x y); omega).
      intro HS.
      unfold S3, S2, S1.
      autorewrite with push_eval; [].
      eapply Z.le_lt_trans.
      { transitivity ((N+B-1 + (r-1)*B + (r-1)*N) / r);
          [ | set_evars; ring_simplify_subterms; subst_evars; reflexivity ].
        Z.peel_le; repeat apply Z.add_le_mono; repeat apply Z.mul_le_mono_nonneg; try lia;
          repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
          autorewrite with push_eval;
            try Z.zero_bounds;
            auto with lia. }
      rewrite (Z.mul_comm _ r), <- Z.add_sub_assoc, <- Z.add_opp_r, !Z.div_add_l' by lia.
      autorewrite with zsimplify.
      simpl; omega.
    Qed.

    Lemma small_A'
      : small A'.
    Proof.
      repeat autounfold with word_by_word_montgomery; auto.
    Qed.

    Lemma small_S3
      : small S3.
    Proof. repeat autounfold with word_by_word_montgomery; t_small. Qed.

    Lemma S3_nonneg : 0 <= eval S3.
    Proof.
      repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
        autorewrite with push_eval; [].
      rewrite ?Npos_correct; Z.zero_bounds; lia.
    Qed.

    Lemma S4_nonneg : 0 <= eval S4.
    Proof. unfold S4; rewrite eval_drop_high by apply small_S3; Z.zero_bounds. Qed.

    Lemma S4_bound
      : eval S < eval N + eval B
        -> eval S4 < eval N + eval B.
    Proof.
      intro H; pose proof (S3_bound H); pose proof S3_nonneg.
      unfold S4.
      rewrite eval_drop_high by apply small_S3.
      rewrite Z.mod_small by nia.
      assumption.
    Qed.

    Lemma small_S4
      : small S4.
    Proof. repeat autounfold with word_by_word_montgomery; t_small. Qed.

    Lemma S1_eq : eval S1 = S + a*B.
    Proof.
      cbv [S1 a A'].
      repeat autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma S2_mod_N : (eval S2) mod N = (S + a*B) mod N.
    Proof.
      cbv [S2]; autorewrite with push_eval zsimplify. rewrite S1_eq. reflexivity.
    Qed.

    Lemma S2_mod_r : S2 mod r = 0.
    Proof.
      cbv [S2 q s]; autorewrite with push_eval.
      assert (r > 0) by lia.
      assert (Hr : (-(1 mod r)) mod r = r - 1 /\ (-(1)) mod r = r - 1).
      { destruct (Z.eq_dec r 1) as [H'|H'].
        { rewrite H'; split; reflexivity. }
        { rewrite !Z_mod_nz_opp_full; rewrite ?Z.mod_mod; Z.rewrite_mod_small; [ split; reflexivity | omega.. ]. } }
      autorewrite with pull_Zmod.
      replace 0 with (0 mod r) by apply Zmod_0_l.
      eapply F.eq_of_Z_iff.
      rewrite Z.mul_split_mod.
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
        rewrite (proj1 Hr), (proj2 Hr); Z.rewrite_mod_small; reflexivity. }
    Qed.

    Lemma S3_mod_N
      : S3 mod N = (S + a*B)*ri mod N.
    Proof.
      cbv [S3]; autorewrite with push_eval cancel_pair.
      pose proof fun a => Z.div_to_inv_modulo N a r ri eq_refl ri_correct as HH;
                            cbv [Z.equiv_modulo] in HH; rewrite HH; clear HH.
      etransitivity; [rewrite (fun a => Z.mul_mod_l a ri N)|
                      rewrite (fun a => Z.mul_mod_l a ri N); reflexivity].
      rewrite <-S2_mod_N; repeat (f_equal; []); autorewrite with push_eval.
      autorewrite with push_Zmod;
        rewrite S2_mod_r;
        autorewrite with zsimplify.
      reflexivity.
    Qed.

    Lemma S4_mod_N
          (Hbound : eval S < eval N + eval B)
      : S4 mod N = (S + a*B)*ri mod N.
    Proof.
      pose proof (S3_bound Hbound); pose proof S3_nonneg.
      unfold S4; autorewrite with push_eval.
      rewrite (Z.mod_small _ (r * _)) by nia.
      apply S3_mod_N.
    Qed.
  End Iteration.

  Local Notation redc_body := (@redc_body T (@divmod) r R_numlimbs scmul addT addT' drop_high N B k).
  Local Notation redc_loop := (@redc_loop T (@divmod) r R_numlimbs scmul addT addT' drop_high N B k).
  Local Notation pre_redc A := (@pre_redc T zero (@divmod) r R_numlimbs scmul addT addT' drop_high N _ A B k).
  Local Notation redc A := (@redc T zero (@divmod) r R_numlimbs scmul addT addT' drop_high conditional_sub N _ A B k).

  Section body.
    Context (pred_A_numlimbs : nat)
            (A_S : T (S pred_A_numlimbs) * T (S R_numlimbs)).
    Let A:=fst A_S.
    Let S:=snd A_S.
    Let A_a:=divmod A.
    Let a:=snd A_a.
    Context (small_A : small A)
            (small_S : small S)
            (S_bound : 0 <= eval S < eval N + eval B).

    Lemma small_fst_redc_body : small (fst (redc_body A_S)).
    Proof. destruct A_S; apply small_A'; assumption. Qed.
    Lemma small_snd_redc_body : small (snd (redc_body A_S)).
    Proof. destruct A_S; unfold redc_body; apply small_S4; assumption. Qed.
    Lemma snd_redc_body_nonneg : 0 <= eval (snd (redc_body A_S)).
    Proof. destruct A_S; apply S4_nonneg; assumption. Qed.

    Lemma snd_redc_body_mod_N
      : (eval (snd (redc_body A_S))) mod (eval N) = (eval S + a*eval B)*ri mod (eval N).
    Proof. destruct A_S; apply S4_mod_N; auto; omega. Qed.

    Lemma fst_redc_body
      : (eval (fst (redc_body A_S))) = eval (fst A_S) / r.
    Proof.
      destruct A_S; simpl; repeat autounfold with word_by_word_montgomery; simpl.
      autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma fst_redc_body_mod_N
      : (eval (fst (redc_body A_S))) mod (eval N) = ((eval (fst A_S) - a)*ri) mod (eval N).
    Proof.
      rewrite fst_redc_body.
      etransitivity; [ eapply Z.div_to_inv_modulo; try eassumption; lia | ].
      unfold a, A_a, A.
      autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma redc_body_bound
      : eval S < eval N + eval B
        -> eval (snd (redc_body A_S)) < eval N + eval B.
    Proof.
      destruct A_S; apply S4_bound; unfold S in *; cbn [snd] in *; try assumption; try omega.
    Qed.
  End body.

  Local Arguments Z.pow !_ !_.
  Local Arguments Z.of_nat !_.
  Local Ltac induction_loop count IHcount
    := induction count as [|count IHcount]; intros; cbn [redc_loop] in *; [ | (*rewrite redc_loop_comm_body in * *) ].
  Lemma redc_loop_good count A_S
        (Hsmall : small (fst A_S) /\ small (snd A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : (small (fst (redc_loop count A_S)) /\ small (snd (redc_loop count A_S)))
      /\ 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
  Proof.
    induction_loop count IHcount; auto; [].
    change (id (0 <= eval B < R)) in B_bounds (* don't let [destruct_head'_and] loop *).
    destruct_head'_and.
    repeat first [ apply conj
                 | apply small_fst_redc_body
                 | apply small_snd_redc_body
                 | apply redc_body_bound
                 | apply snd_redc_body_nonneg
                 | apply IHcount
                 | solve [ auto ] ].
  Qed.

  Lemma small_redc_loop count A_S
        (Hsmall : small (fst A_S) /\ small (snd A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : small (fst (redc_loop count A_S)) /\ small (snd (redc_loop count A_S)).
  Proof. apply redc_loop_good; assumption. Qed.

  Lemma redc_loop_bound count A_S
        (Hsmall : small (fst A_S) /\ small (snd A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
  Proof. apply redc_loop_good; assumption. Qed.

  Local Ltac handle_IH_small :=
    repeat first [ apply redc_loop_good
                 | apply small_fst_redc_body
                 | apply small_snd_redc_body
                 | apply redc_body_bound
                 | apply snd_redc_body_nonneg
                 | apply conj
                 | progress cbn [fst snd]
                 | progress destruct_head' and
                 | solve [ auto ] ].

  Lemma fst_redc_loop count A_S
        (Hsmall : small (fst A_S) /\ small (snd A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : eval (fst (redc_loop count A_S)) = eval (fst A_S) / r^(Z.of_nat count).
  Proof.
    induction_loop count IHcount.
    { simpl; autorewrite with zsimplify; reflexivity. }
    { rewrite IHcount, fst_redc_body by handle_IH_small.
      change (1 + R_numlimbs)%nat with (S R_numlimbs) in *.
      rewrite Zdiv_Zdiv by Z.zero_bounds.
      rewrite <- (Z.pow_1_r r) at 1.
      rewrite <- Z.pow_add_r by lia.
      replace (1 + Z.of_nat count) with (Z.of_nat (S count)) by lia.
      reflexivity. }
  Qed.

  Lemma fst_redc_loop_mod_N count A_S
        (Hsmall : small (fst A_S) /\ small (snd A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : eval (fst (redc_loop count A_S)) mod (eval N)
      = (eval (fst A_S) - eval (fst A_S) mod r^Z.of_nat count)
        * ri^(Z.of_nat count) mod (eval N).
  Proof.
    rewrite fst_redc_loop by assumption.
    destruct count.
    { simpl; autorewrite with zsimplify; reflexivity. }
    { etransitivity;
        [ eapply Z.div_to_inv_modulo;
          try solve [ eassumption
                    | apply Z.lt_gt, Z.pow_pos_nonneg; lia ]
        | ].
      { erewrite <- Z.pow_mul_l, <- Z.pow_1_l.
        { apply Z.pow_mod_Proper; [ eassumption | reflexivity ]. }
        { lia. } }
      reflexivity. }
  Qed.

  Local Arguments Z.pow : simpl never.
  Lemma snd_redc_loop_mod_N count A_S
        (Hsmall : small (fst A_S) /\ small (snd A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : (eval (snd (redc_loop count A_S))) mod (eval N)
      = ((eval (snd A_S) + (eval (fst A_S) mod r^(Z.of_nat count))*eval B)*ri^(Z.of_nat count)) mod (eval N).
  Proof.
    induction_loop count IHcount.
    { simpl; autorewrite with zsimplify; reflexivity. }
    { rewrite IHcount by handle_IH_small.
      push_Zmod; rewrite snd_redc_body_mod_N, fst_redc_body by handle_IH_small; pull_Zmod.
      autorewrite with push_eval; [].
      match goal with
      | [ |- ?x mod ?N = ?y mod ?N ]
        => change (Z.equiv_modulo N x y)
      end.
      destruct A_S as [A S].
      cbn [fst snd].
      change (Z.pos (Pos.of_succ_nat ?n)) with (Z.of_nat (Datatypes.S n)).
      rewrite !Z.mul_add_distr_r.
      rewrite <- !Z.mul_assoc.
      replace (ri * ri^(Z.of_nat count)) with (ri^(Z.of_nat (Datatypes.S count)))
        by (change (Datatypes.S count) with (1 + count)%nat;
            autorewrite with push_Zof_nat; rewrite Z.pow_add_r by lia; simpl Z.succ; rewrite Z.pow_1_r; nia).
      rewrite <- !Z.add_assoc.
      apply Z.add_mod_Proper; [ reflexivity | ].
      unfold Z.equiv_modulo; push_Zmod; rewrite (Z.mul_mod_l (_ mod r) _ (eval N)).
      rewrite Z.mod_pull_div by auto with zarith lia.
      push_Zmod.
      erewrite Z.div_to_inv_modulo;
        [
        | apply Z.lt_gt; lia
        | eassumption ].
      pull_Zmod.
      match goal with
      | [ |- ?x mod ?N = ?y mod ?N ]
        => change (Z.equiv_modulo N x y)
      end.
      repeat first [ rewrite <- !Z.pow_succ_r, <- !Nat2Z.inj_succ by lia
                   | rewrite (Z.mul_comm _ ri)
                   | rewrite (Z.mul_assoc _ ri _)
                   | rewrite (Z.mul_comm _ (ri^_))
                   | rewrite (Z.mul_assoc _ (ri^_) _) ].
      repeat first [ rewrite <- Z.mul_assoc
                   | rewrite <- Z.mul_add_distr_l
                   | rewrite (Z.mul_comm _ (eval B))
                   | rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia;
                     rewrite <- Znumtheory.Zmod_div_mod by (apply Z.divide_factor_r || Z.zero_bounds)
                   | rewrite Zplus_minus
                   | rewrite (Z.mul_comm r (r^_))
                   | reflexivity ]. }
  Qed.

  Lemma pre_redc_bound A_numlimbs (A : T A_numlimbs)
        (small_A : small A)
    : 0 <= eval (pre_redc A) < eval N + eval B.
  Proof.
    unfold pre_redc.
    apply redc_loop_good; simpl; autorewrite with push_eval;
      rewrite ?Npos_correct; auto; lia.
  Qed.

  Lemma small_pre_redc A_numlimbs (A : T A_numlimbs)
        (small_A : small A)
    : small (pre_redc A).
  Proof.
    unfold pre_redc.
    apply redc_loop_good; simpl; autorewrite with push_eval;
      rewrite ?Npos_correct; auto; lia.
  Qed.

  Lemma pre_redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
    : (eval (pre_redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
  Proof.
    unfold pre_redc.
    rewrite snd_redc_loop_mod_N; cbn [fst snd];
      autorewrite with push_eval zsimplify;
      [ | rewrite ?Npos_correct; auto; lia.. ].
    Z.rewrite_mod_small.
    reflexivity.
  Qed.

  Lemma redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
    : (eval (redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
  Proof.
    pose proof (@small_pre_redc _ A small_A).
    pose proof (@pre_redc_bound _ A small_A).
    unfold redc.
    autorewrite with push_eval; [].
    break_innermost_match;
      try rewrite Z.add_opp_r, Zminus_mod, Z_mod_same_full;
      autorewrite with zsimplify_fast;
      apply pre_redc_mod_N; auto.
  Qed.

  Lemma redc_bound_tight A_numlimbs (A : T A_numlimbs)
        (small_A : small A)
    : 0 <= eval (redc A) < eval N + eval B + if eval N <=? eval (pre_redc A) then -eval N else 0.
  Proof.
    pose proof (@small_pre_redc _ A small_A).
    pose proof (@pre_redc_bound _ A small_A).
    unfold redc.
    rewrite eval_conditional_sub by t_small.
    break_innermost_match; Z.ltb_to_lt; omega.
  Qed.

  Lemma redc_bound_N A_numlimbs (A : T A_numlimbs)
        (small_A : small A)
    : eval B < eval N -> 0 <= eval (redc A) < eval N.
  Proof.
    pose proof (@small_pre_redc _ A small_A).
    pose proof (@pre_redc_bound _ A small_A).
    unfold redc.
    rewrite eval_conditional_sub by t_small.
    break_innermost_match; Z.ltb_to_lt; omega.
  Qed.

  Lemma redc_bound A_numlimbs (A : T A_numlimbs)
        (small_A : small A)
        (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
    : 0 <= eval (redc A) < R.
  Proof.
    pose proof (@small_pre_redc _ A small_A).
    pose proof (@pre_redc_bound _ A small_A).
    unfold redc.
    rewrite eval_conditional_sub by t_small.
    break_innermost_match; Z.ltb_to_lt; try omega.
  Qed.

  Lemma small_redc A_numlimbs (A : T A_numlimbs)
        (small_A : small A)
        (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
    : small (redc A).
  Proof.
    pose proof (@small_pre_redc _ A small_A).
    pose proof (@pre_redc_bound _ A small_A).
    unfold redc.
    apply small_conditional_sub; [ apply small_pre_redc | .. ]; auto; omega.
  Qed.

  Local Notation add := (@add T R_numlimbs addT conditional_sub).
  Local Notation sub := (@sub T R_numlimbs sub_then_maybe_add).
  Local Notation opp := (@opp T (@zero) R_numlimbs sub_then_maybe_add).

  Section add_sub.
    Context (Av Bv : T R_numlimbs)
            (small_Av : small Av)
            (small_Bv : small Bv)
            (Av_bound : 0 <= eval Av < eval N)
            (Bv_bound : 0 <= eval Bv < eval N).

    Local Ltac do_clear :=
      clear dependent B; clear dependent k; clear dependent ri; clear dependent Npos.

    Lemma small_add : small (add Av Bv).
    Proof. do_clear; unfold add; t_small. Qed.
    Lemma small_sub : small (sub Av Bv).
    Proof. do_clear; unfold sub; t_small. Qed.
    Lemma small_opp : small (opp Av).
    Proof. clear dependent Bv; do_clear; unfold opp, sub; t_small. Qed.

    Lemma eval_add : eval (add Av Bv) = eval Av + eval Bv + if (eval N <=? eval Av + eval Bv) then -eval N else 0.
    Proof. do_clear; unfold add; autorewrite with push_eval; reflexivity. Qed.
    Lemma eval_sub : eval (sub Av Bv) = eval Av - eval Bv + if (eval Av - eval Bv <? 0) then eval N else 0.
    Proof. do_clear; unfold sub; autorewrite with push_eval; reflexivity. Qed.
    Lemma eval_opp : eval (opp Av) = (if (eval Av =? 0) then 0 else eval N) - eval Av.
    Proof.
      clear dependent Bv; do_clear; unfold opp, sub; autorewrite with push_eval.
      break_innermost_match; Z.ltb_to_lt; lia.
    Qed.

    Local Ltac t_mod_N :=
      repeat first [ progress break_innermost_match
                   | reflexivity
                   | let H := fresh in intro H; rewrite H; clear H
                   | progress autorewrite with zsimplify_const
                   | rewrite Z.add_opp_r
                   | progress (push_Zmod; pull_Zmod) ].

    Lemma eval_add_mod_N : eval (add Av Bv) mod eval N = (eval Av + eval Bv) mod eval N.
    Proof. generalize eval_add; clear. t_mod_N. Qed.
    Lemma eval_sub_mod_N : eval (sub Av Bv) mod eval N = (eval Av - eval Bv) mod eval N.
    Proof. generalize eval_sub; clear. t_mod_N. Qed.
    Lemma eval_opp_mod_N : eval (opp Av) mod eval N = (-eval Av) mod eval N.
    Proof. generalize eval_opp; clear; t_mod_N. Qed.

    Lemma add_bound : 0 <= eval (add Av Bv) < eval N.
    Proof. do_clear; generalize eval_add; break_innermost_match; Z.ltb_to_lt; lia. Qed.
    Lemma sub_bound : 0 <= eval (sub Av Bv) < eval N.
    Proof. do_clear; generalize eval_sub; break_innermost_match; Z.ltb_to_lt; lia. Qed.
    Lemma opp_bound : 0 <= eval (opp Av) < eval N.
    Proof. do_clear; generalize eval_opp; break_innermost_match; Z.ltb_to_lt; lia. Qed.
  End add_sub.
End WordByWordMontgomery.
