Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.micromega.Lia.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Spec.ModularArithmetic.
Require Import Crypto.Util.Sigma.
Local Open Scope Z_scope.

Section WordByWordMontgomery.
  Context
    {T : Type}
    {eval : T -> Z}
    {numlimbs : T -> nat}
    {divmod : T -> T * Z} (* returns lowest limb and all-but-lowest-limb *)
    {r : positive}
    {r_big : r > 1}
    {eval_div : forall v, eval (fst (divmod v)) = eval v / r}
    {eval_mod : forall v, snd (divmod v) = eval v mod r}
    {scmul : Z -> T -> T} (* uses double-output multiply *)
    {eval_scmul: forall a v, eval (scmul a v) = a * eval v}
    {R : positive}.
  Local Notation bn := (r * R) (only parsing).
  Context
    {add : T -> T -> T * Z} (* produces carry *)
    {eval_fst_add : forall a b, eval (fst (add a b)) = (eval a + eval b) mod bn}
    {eval_snd_add : forall a b, snd (add a b) = (eval a + eval b) / bn}
    {join : T * Z -> T} (* adds limb to high end *)
    {eval_join : forall p, eval (join p) = eval (fst p) + (bn / r) * (snd p)}
    {eval_nonneg : forall v, 0 <= eval v}
    (N : T) (Npos : positive) (Npos_correct: eval N = Z.pos Npos)
    (B : T)
    (B_small : eval B < R).

  Create HintDb push_eval discriminated.
  Hint Rewrite
       eval_div
       eval_mod
       eval_fst_add
       eval_snd_add
       eval_scmul
       eval_join
    : push_eval.


  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (A S : T)
            (S_small : eval S / R <= 1).
    Context (k : Z) (k_correct : k * eval N mod r = -1).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
    Let A_a := dlet p := divmod A in p. Let A' := fst A_a. Let a := snd A_a.
    Let S1 := fst (add S (scmul a B)).
    Let s := snd (divmod S1).
    Let q := s * k mod r.
    Let cS2 := add S1 (scmul q N).
    Let c := snd cS2.
    Let S3 := fst (divmod (fst cS2)).

    Local Coercion eval : T >-> Z.

    Lemma S_aB_over_R_bound : (eval S + a * eval B) / R <= 1 + ((r - 1)^2 / r + 1 + 1).
    Proof.
      assert (Hmod0 : forall v r, 0 < r -> v mod r < r) by (intros; apply Z_mod_lt; lia).
      assert (Hmod : forall v r, 0 < r -> v mod r <= r - 1) by (intros v m; specialize (Hmod0 v m); omega).
      rewrite (Z_div_mod_eq (eval S) R), <- Z.add_assoc, Z.div_add_l' by lia.
      apply Z.add_le_mono; auto.
      transitivity ((R-1 + (r-1)*(R-1)) / R).
      { Z.peel_le; apply Z.add_le_mono; auto with lia.
        unfold a, A_a, Let_In.
        autorewrite with push_eval.
        apply Z.mul_le_mono_nonneg; try solve [ auto with lia | lia | apply Z_mod_lt; lia ]. }
      { admit. (*
      Unset Printing Coercions.
      Require Import Algebra.Ring.
      ring_simplify_subterms.

      transitivity (r + (-r) / R).
      admit.
      transitivity (r - 2 + 1/r + 2); [ | admit ].
      transitivity r.
      admit.

      am
      SearchAbout ((?x * _ + _) / ?x).



      SearchAbout ((?x * _ + _) / ?x).
      SearchAbout (?x / ?y) (?x mod ?y).
      SearchAbout ((_ + _) / _). *) }
    Admitted.

    Lemma S_aB_range : 0 <= eval S + a * eval B < bn.
    Proof.
      pose proof S_aB_over_R_bound.
      assert (eval S + a * eval B <= (R - 1) + R + ((Z.pos r - 1) ^ 2 / Z.pos r + 1 + 1) * R) by admit.
      (*Z.div_mod_to_quot_rem.
      nia.
      assert (eval A mod Z.pos r < r) by (apply Z_mod_lt; lia).
      assert (Hmod : eval A mod Z.pos r <= r - 1) by omega.
      repeat match goal with H := _ |- _ => progress unfold H end.
      unfold Let_In.
      rewrite eval_mod.
      split; [ solve [ auto with zarith ] | ].
      eapply (@Z.le_lt_trans _ (2 * R - 1 + (r - 1) * (R - 1))).
      Focus 2.
      rewrite Z.mul_sub_distr_l, !Z.mul_sub_distr_r, !Z.add_sub_assoc.
      Require Import Crypto.Algebra.Ring.
      ring_simplify_subterms.
      Unset Printing Coercions.
      autorewrite with zsimplify.
      change
      repeat (apply Z.add_le_mono || apply Z.mul_le_mono_nonneg); try lia.
      Z.peel_le.
      rewrite S_small.

      Focus 2.
      Unset Printing Coercions.

      rewrite Z.mul_sub_distr_l, !Z.mul_sub_distr_r, !Z.add_sub_assoc.
      autorewrite with zsimplify.
      omega.
      autorewrite with *)
    Admitted.

    Lemma S1_eq : eval S1 = S + a*B.
    Proof.
      cbv [S1 a A'].
      repeat autorewrite with push_eval.
      rewrite (Z.mod_small _ bn) by (apply S_aB_range).
      reflexivity.
    Qed.

    Lemma cS2_mod_N : (eval (fst cS2) + bn * snd cS2) mod N = (S + a*B) mod N.
    Proof.
      assert (bn_large : bn >= r) by (unfold bn; nia).
      cbv [cS2 q s]; autorewrite with push_eval zsimplify. rewrite S1_eq. reflexivity.
    Qed.

    Lemma cS2_mod_r : fst cS2 mod r = 0.
      cbv [cS2 q s]; autorewrite with push_eval.
      assert (r > 0) by lia.
      assert (Hr : (-(1 mod r)) mod r = r - 1 /\ (-(1)) mod r = r - 1).
      { destruct (Z.eq_dec r 1) as [H'|H'].
        { rewrite H'; split; reflexivity. }
        { rewrite !Z_mod_nz_opp_full; rewrite ?Z.mod_mod; Z.rewrite_mod_small; [ split; reflexivity | omega.. ]. } }
      autorewrite with pull_Zmod.
      rewrite (Z.mod_small _ bn) by admit.
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
      Grab Existential Variables.
      { unfold S1.
        autorewrite with push_eval.
        rewrite (Z.mod_small _ bn) by apply S_aB_range.
        admit. }
    Admitted.

    Lemma cS3_mod_N ri (ri_correct : r*ri mod N = 1 mod N)
      : join (S3, c) mod N = (S + a*B)*ri mod N.
    Proof.
      assert (r_div_bn : (r | bn)) by apply Z.divide_factor_l.
      cbv [S3 c]; autorewrite with push_eval cancel_pair.
      replace (eval (fst cS2) / Z.pos r + (bn / r) * snd cS2)
        with ((eval (fst cS2) + bn * snd cS2) / Z.pos r)
        by (rewrite Z.div_add_exact, !(Z.mul_comm bn), Z.divide_div_mul_exact
             by (assumption || apply cS2_mod_r || lia); nia).
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
End Iteration.
