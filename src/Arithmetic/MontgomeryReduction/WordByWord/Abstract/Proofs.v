(*** Word-By-Word Montgomery Multiplication Proofs *)
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.micromega.Lia.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Definition.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.DestructHead.
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
    {R : positive}
    {R_numlimbs : nat}
    {R_correct : R = r^Z.of_nat R_numlimbs :> Z}
    {small : T -> Prop}
    {eval_zero : forall n, eval (zero n) = 0}
    {numlimbs_zero : forall n, numlimbs (zero n) = n}
    {eval_div : forall v, small v -> eval (fst (divmod v)) = eval v / r}
    {eval_mod : forall v, small v -> snd (divmod v) = eval v mod r}
    {small_div : forall v, small v -> small (fst (divmod v))}
    {numlimbs_div : forall v, numlimbs (fst (divmod v)) = pred (numlimbs v)}
    {scmul : Z -> T -> T} (* uses double-output multiply *)
    {eval_scmul: forall a v, 0 <= a < r -> 0 <= eval v < R -> eval (scmul a v) = a * eval v}
    {numlimbs_scmul : forall a v, 0 <= a < r -> numlimbs (scmul a v) = S (numlimbs v)}
    {add : T -> T -> T} (* joins carry *)
    {eval_add : forall a b, eval (add a b) = eval a + eval b}
    {small_add : forall a b, small (add a b)}
    {numlimbs_add : forall a b, numlimbs (add a b) = Datatypes.S (max (numlimbs a) (numlimbs b))}
    {drop_high : T -> T} (* drops things after [S R_numlimbs] *)
    {eval_drop_high : forall v, small v -> eval (drop_high v) = eval v mod (r * r^Z.of_nat R_numlimbs)}
    {numlimbs_drop_high : forall v, numlimbs (drop_high v) = min (numlimbs v) (S R_numlimbs)}
    (N : T) (Npos : positive) (Npos_correct: eval N = Z.pos Npos)
    (N_lt_R : eval N < R)
    (B : T)
    (B_bounds : 0 <= eval B < R)
    ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N)).
  Context (k : Z) (k_correct : k * eval N mod r = (-1) mod r).

  Create HintDb push_numlimbs discriminated.
  Create HintDb push_eval discriminated.
  Local Ltac t_small :=
    repeat first [ assumption
                 | apply small_add
                 | apply small_div
                 | apply Z_mod_lt
                 | rewrite Z.mul_split_mod
                 | solve [ auto with zarith ]
                 | lia
                 | progress autorewrite with push_eval
                 | progress autorewrite with push_numlimbs ].
  Hint Rewrite
       eval_zero
       eval_div
       eval_mod
       eval_add
       eval_scmul
       eval_drop_high
       using (repeat autounfold with word_by_word_montgomery; t_small)
    : push_eval.
  Hint Rewrite
       numlimbs_zero
       numlimbs_div
       numlimbs_add
       numlimbs_scmul
       numlimbs_drop_high
       using (repeat autounfold with word_by_word_montgomery; t_small)
    : push_numlimbs.
  Hint Rewrite <- Max.succ_max_distr pred_Sn Min.succ_min_distr : push_numlimbs.


  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (A S : T)
            (small_A : small A)
            (S_nonneg : 0 <= eval S).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)

    Local Coercion eval : T >-> Z.

    Local Notation a := (@WordByWord.Abstract.Definition.a T divmod A).
    Local Notation A' := (@WordByWord.Abstract.Definition.A' T divmod A).
    Local Notation S1 := (@WordByWord.Abstract.Definition.S1 T divmod scmul add B A S).
    Local Notation S2 := (@WordByWord.Abstract.Definition.S2 T divmod r scmul add N B k A S).
    Local Notation S3 := (@WordByWord.Abstract.Definition.S3 T divmod r scmul add N B k A S).
    Local Notation S4 := (@WordByWord.Abstract.Definition.S4 T divmod r scmul add drop_high N B k A S).

    Lemma S3_bound
      : eval S < eval N + eval B
        -> eval S3 < eval N + eval B.
    Proof.
      assert (Hmod : forall a b, 0 < b -> a mod b <= b - 1)
        by (intros x y; pose proof (Z_mod_lt x y); omega).
      intro HS.
      unfold S3, WordByWord.Abstract.Definition.S2, WordByWord.Abstract.Definition.S1.
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
      omega.
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
      repeat autounfold with word_by_word_montgomery; rewrite Z.mul_split_mod;
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

    Lemma numlimbs_S4 : numlimbs S4 = min (max (1 + numlimbs S) (1 + max (1 + numlimbs B) (numlimbs N))) (1 + R_numlimbs).
    Proof.
      cbn [plus].
      repeat autounfold with word_by_word_montgomery; rewrite Z.mul_split_mod.
      repeat autorewrite with push_numlimbs.
      change Init.Nat.max with Nat.max.
      rewrite <- ?(Max.max_assoc (numlimbs S)).
      reflexivity.
    Qed.

    Lemma S1_eq : eval S1 = S + a*B.
    Proof.
      cbv [S1 a WordByWord.Abstract.Definition.A'].
      repeat autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma S2_mod_N : (eval S2) mod N = (S + a*B) mod N.
    Proof.
      cbv [S2 WordByWord.Abstract.Definition.q WordByWord.Abstract.Definition.s]; autorewrite with push_eval zsimplify. rewrite S1_eq. reflexivity.
    Qed.

    Lemma S2_mod_r : S2 mod r = 0.
      cbv [S2 WordByWord.Abstract.Definition.q WordByWord.Abstract.Definition.s]; autorewrite with push_eval.
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

  Local Notation redc_body := (@redc_body T divmod r scmul add drop_high N B k).
  Local Notation redc_loop := (@redc_loop T divmod r scmul add drop_high N B k).
  Local Notation redc A := (@redc T numlimbs zero divmod r scmul add drop_high N A B k).

  Lemma redc_loop_comm_body count
    : forall A_S, redc_loop count (redc_body A_S) = redc_body (redc_loop count A_S).
  Proof.
    induction count as [|count IHcount]; try reflexivity.
    simpl; intro; rewrite IHcount; reflexivity.
  Qed.

  Section body.
    Context (A_S : T * T).
    Let A:=fst A_S.
    Let S:=snd A_S.
    Let A_a:=divmod A.
    Let a:=snd A_a.
    Context (small_A : small A)
            (S_bound : 0 <= eval S < eval N + eval B).

    Lemma small_fst_redc_body : small (fst (redc_body A_S)).
    Proof. destruct A_S; apply small_A'; assumption. Qed.
    Lemma snd_redc_body_nonneg : 0 <= eval (snd (redc_body A_S)).
    Proof. destruct A_S; apply S4_nonneg; assumption. Qed.

    Lemma snd_redc_body_mod_N
      : (eval (snd (redc_body A_S))) mod (eval N) = (eval S + a*eval B)*ri mod (eval N).
    Proof. destruct A_S; apply S4_mod_N; auto; omega. Qed.

    Lemma fst_redc_body
      : (eval (fst (redc_body A_S))) = eval (fst A_S) / r.
    Proof.
      destruct A_S; simpl; unfold WordByWord.Abstract.Definition.A', WordByWord.Abstract.Definition.A_a, Let_In, a, A_a, A; simpl.
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

    Lemma numlimbs_redc_body : numlimbs (snd (redc_body A_S))
                               = min (max (1 + numlimbs (snd A_S)) (1 + max (1 + numlimbs B) (numlimbs N))) (1 + R_numlimbs).
    Proof. destruct A_S; apply numlimbs_S4; assumption. Qed.
  End body.

  Local Arguments Z.pow !_ !_.
  Local Arguments Z.of_nat !_.
  Local Ltac induction_loop count IHcount
    := induction count as [|count IHcount]; intros; cbn [redc_loop] in *; [ | rewrite redc_loop_comm_body in * ].
  Lemma redc_loop_good A_S count
        (Hsmall : small (fst A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : small (fst (redc_loop count A_S))
      /\ 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
  Proof.
    induction_loop count IHcount; auto; [].
    change (id (0 <= eval B < R)) in B_bounds (* don't let [destruct_head'_and] loop *).
    destruct_head'_and.
    repeat first [ apply conj
                 | apply small_fst_redc_body
                 | apply redc_body_bound
                 | apply snd_redc_body_nonneg
                 | solve [ auto ] ].
  Qed.

  Lemma redc_loop_bound A_S count
        (Hsmall : small (fst A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
  Proof. apply redc_loop_good; assumption. Qed.

  Local Ltac t_min_max_step _ :=
    match goal with
    | [ |- context[Init.Nat.max ?x ?y] ]
      => first [ rewrite (Max.max_l x y) by omega
               | rewrite (Max.max_r x y) by omega ]
    | [ |- context[Init.Nat.min ?x ?y] ]
      => first [ rewrite (Min.min_l x y) by omega
               | rewrite (Min.min_r x y) by omega ]
    | _ => progress change Init.Nat.max with Nat.max
    | _ => progress change Init.Nat.min with Nat.min
    end.

  Lemma numlimbs_redc_loop A_S count
        (Hsmall : small (fst A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        (Hnumlimbs : (R_numlimbs <= numlimbs (snd A_S))%nat)
    : numlimbs (snd (redc_loop count A_S))
      = match count with
        | O => numlimbs (snd A_S)
        | S _ => 1 + R_numlimbs
        end%nat.
  Proof.
    assert (Hgen
            : numlimbs (snd (redc_loop count A_S))
              = match count with
                | O => numlimbs (snd A_S)
                | S _ => min (max (count + numlimbs (snd A_S)) (1 + max (1 + numlimbs B) (numlimbs N))) (1 + R_numlimbs)
                end).
    { induction_loop count IHcount; [ reflexivity | ].
      rewrite numlimbs_redc_body by (try apply redc_loop_good; auto).
      rewrite IHcount; clear IHcount.
      destruct count; [ reflexivity | ].
      destruct (Compare_dec.le_lt_dec (1 + max (1 + numlimbs B) (numlimbs N)) (S count + numlimbs (snd A_S))),
      (Compare_dec.le_lt_dec (1 + R_numlimbs) (S count + numlimbs (snd A_S))),
      (Compare_dec.le_lt_dec (1 + R_numlimbs) (1 + max (1 + numlimbs B) (numlimbs N)));
        repeat first [ reflexivity
                     | t_min_max_step ()
                     | progress autorewrite with push_numlimbs
                     | rewrite Nat.min_comm, Nat.min_max_distr ]. }
    rewrite Hgen; clear Hgen.
    destruct count; [ reflexivity | ].
    repeat apply Max.max_case_strong; apply Min.min_case_strong; omega.
  Qed.


  Lemma fst_redc_loop A_S count
        (Hsmall : small (fst A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : eval (fst (redc_loop count A_S)) = eval (fst A_S) / r^(Z.of_nat count).
  Proof.
    induction_loop count IHcount.
    { simpl; autorewrite with zsimplify; reflexivity. }
    { rewrite fst_redc_body, IHcount
        by (apply redc_loop_good; auto).
      rewrite Zdiv_Zdiv by Z.zero_bounds.
      rewrite <- (Z.pow_1_r r) at 2.
      rewrite <- Z.pow_add_r by lia.
      replace (Z.of_nat count + 1) with (Z.of_nat (S count)) by (simpl; lia).
      reflexivity. }
  Qed.

  Lemma fst_redc_loop_mod_N A_S count
        (Hsmall : small (fst A_S))
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
  Lemma snd_redc_loop_mod_N A_S count
        (Hsmall : small (fst A_S))
        (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
    : (eval (snd (redc_loop count A_S))) mod (eval N)
      = ((eval (snd A_S) + (eval (fst A_S) mod r^(Z.of_nat count))*eval B)*ri^(Z.of_nat count)) mod (eval N).
  Proof.
    induction_loop count IHcount.
    { simpl; autorewrite with zsimplify; reflexivity. }
    { simpl; rewrite snd_redc_body_mod_N
        by (apply redc_loop_good; auto).
      push_Zmod; rewrite IHcount; pull_Zmod.
      autorewrite with push_eval; [ | apply redc_loop_good; auto.. ]; [].
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
      unfold Z.equiv_modulo; push_Zmod; rewrite (Z.mul_mod_l (_ mod r) _ (eval N)).
      rewrite fst_redc_loop by (try apply redc_loop_good; auto; omega).
      cbn [fst].
      rewrite Z.mod_pull_div by lia.
      erewrite Z.div_to_inv_modulo;
        [
        | solve [ eassumption | apply Z.lt_gt, Z.pow_pos_nonneg; lia ]
        | erewrite <- Z.pow_mul_l, <- Z.pow_1_l;
          [ apply Z.pow_mod_Proper; [ eassumption | reflexivity ]
          | lia ] ].
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
                   | reflexivity ]. }
  Qed.

  Lemma redc_bound A
        (small_A : small A)
    : 0 <= eval (redc A) < eval N + eval B.
  Proof.
    unfold redc.
    apply redc_loop_good; simpl; autorewrite with push_eval;
      rewrite ?Npos_correct; auto; lia.
  Qed.

  Lemma numlimbs_redc_gen A (small_A : small A) (Hnumlimbs : (R_numlimbs <= numlimbs B)%nat)
    : numlimbs (redc A)
      = match numlimbs A with
        | O => S (numlimbs B)
        | _ => S R_numlimbs
        end.
  Proof.
    unfold redc; rewrite numlimbs_redc_loop by (cbn [fst snd]; t_small);
      cbn [snd]; rewrite ?numlimbs_zero.
    reflexivity.
  Qed.
  Lemma numlimbs_redc A (small_A : small A) (Hnumlimbs : R_numlimbs = numlimbs B)
    : numlimbs (redc A) = S (numlimbs B).
  Proof. rewrite numlimbs_redc_gen; subst; auto; destruct (numlimbs A); reflexivity. Qed.

  Lemma redc_mod_N A (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat (numlimbs A))
    : (eval (redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat (numlimbs A))) mod (eval N).
  Proof.
    unfold redc.
    rewrite snd_redc_loop_mod_N; cbn [fst snd];
      autorewrite with push_eval zsimplify;
      [ | rewrite ?Npos_correct; auto; lia.. ].
    Z.rewrite_mod_small.
    reflexivity.
  Qed.
End WordByWordMontgomery.
