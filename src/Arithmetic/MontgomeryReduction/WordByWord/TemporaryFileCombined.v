Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.micromega.Lia.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Spec.ModularArithmetic.
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
    {add : T -> T -> T} (* joins carry *)
    {eval_add : forall a b, eval (add a b) = eval a + eval b}
    {eval_nonneg : forall v, 0 <= eval v}
    (N : T) (Npos : positive) (Npos_correct: eval N = Z.pos Npos)
    (B : T)
    (B_small : eval B < R).

  Create HintDb push_eval discriminated.
  Hint Rewrite
       eval_div
       eval_mod
       eval_add
       eval_scmul
    : push_eval.


  (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
  Section Iteration.
    Context (A S : T)
            (S_small : eval S / R <= 1).
    Context (k : Z) (k_correct : k * eval N mod r = -1).
    (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
    Let A_a := dlet p := divmod A in p. Let A' := fst A_a. Let a := snd A_a.
    Let S1 := add S (scmul a B).
    Let s := snd (divmod S1).
    Let q := s * k mod r.
    Let cS2 := add S1 (scmul q N).
    Let S3 := fst (divmod cS2).

    Local Coercion eval : T >-> Z.

    Lemma S3_bound
      : 0 <= eval S < eval N + eval B
        -> 0 <= eval S3 < eval N + eval B.
    Proof.
      assert (Hmod : forall a b, 0 < b -> a mod b <= b - 1)
        by (intros x y; pose proof (Z_mod_lt x y); omega).
      intro HS.
      unfold S3, cS2, S1.
      autorewrite with push_eval.
      split;
        [ solve
            [ repeat match goal with H := _ |- _ => progress unfold H end;
              unfold Let_In; autorewrite with push_eval;
              Z.zero_bounds ]
        | ].
      eapply Z.le_lt_trans.
      { transitivity ((N+B-1 + (r-1)*B + (r-1)*N) / r);
          [ | set_evars; ring_simplify_subterms; subst_evars; reflexivity ].
        Z.peel_le; repeat apply Z.add_le_mono; repeat apply Z.mul_le_mono_nonneg; try lia;
          repeat match goal with H := _ |- _ => progress unfold H end;
          unfold Let_In; autorewrite with push_eval;
            try Z.zero_bounds;
            auto with lia. }
      rewrite (Z.mul_comm _ r), <- Z.add_sub_assoc, <- Z.add_opp_r, !Z.div_add_l' by lia.
      autorewrite with zsimplify.
      omega.
    Qed.

    Lemma S1_eq : eval S1 = S + a*B.
    Proof.
      cbv [S1 a A'].
      repeat autorewrite with push_eval.
      reflexivity.
    Qed.

    Lemma cS2_mod_N : (eval cS2) mod N = (S + a*B) mod N.
    Proof.
      assert (bn_large : bn >= r) by (unfold bn; nia).
      cbv [cS2 q s]; autorewrite with push_eval zsimplify. rewrite S1_eq. reflexivity.
    Qed.

    Lemma cS2_mod_r : cS2 mod r = 0.
      cbv [cS2 q s]; autorewrite with push_eval.
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

    Lemma cS3_mod_N ri (ri_correct : r*ri mod N = 1 mod N)
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
  End Iteration.
End WordByWordMontgomery.
