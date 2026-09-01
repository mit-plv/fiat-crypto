From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic NotationsCustomEntry ZnWords.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
From coqutil Require Import Tactics.Tactics WithBaseName.
From coqutil Require Import CountTrailingZeros.
From bedrock2Examples Require Import full_add full_mul.

Require Import br_ctz u320_shr u256_shr u320_muladd.
Local Open Scope string_scope. Local Open Scope Z_scope.

Require Import Lia ZArith Zdiv.

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

(** * Specification *)

Local Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [|x l]; inversion H; clear H end.

#[export] Instance spec_of_beeu_shrtz : spec_of "beeu_shrtz" :=
    fnspec! "beeu_shrtz" (p_a p_y p_m inv_m : word) / (a y MOD : list word) R,
    {
        requires t m :=
            m =* array p_a a ⋆ array p_y y ⋆ array p_m MOD ⋆ R /\
            (eval MOD) mod 2 = 1 /\ inv_m * (eval MOD) mod (2^64) = 2^64 - 1 /\
            length a = 4%nat /\ length y = 5%nat /\ length MOD = 4%nat /\
            eval a > 0;
        ensures T M := T = t /\ exists (a' y' : list word) (s : Z),
            M =* array p_a a' ⋆ array p_y y' ⋆ array p_m MOD ⋆ R /\
            length a' = 4%nat /\ length y' = 5%nat /\
            (eval a' * (2^s) = eval a) /\ (s = Z.min (lctz 64 (eval a)) 63) /\
            (eval y' * (2^s) mod (eval MOD) = eval y mod (eval MOD)) /\
            (eval y' * (2^s) <= (eval y + (2^s - 1) * (eval MOD)))
    }.

(** * Implementation *)
Definition beeu_shrtz := func! (p_a, p_y, p_m, inv_m) {
    unpack! shift = br_ctz(load(p_a) | ($1 << $63));

    if shift {
        u256_shr(p_a, shift);
        mask = ($1 << shift) - $1;
        c_prime = (load(p_y) * inv_m) & mask;
        unpack! carry = u320_muladd(p_y, p_m, c_prime);
        u320_shr(p_y, carry, shift)
    }
}.

Lemma eval_mod (l : list word) (a : word) :
    eval (a :: l) mod 2^64 = a.
Proof.
    (* If I remove the parameters, ZnWords fails for some reason. *)
    erewrite <- (Z.mod_small a (2^64)) by ZnWords.
    cbn [eval]. erewrite <- (Zdiv.Z_mod_plus_full a (eval l)). ZnWords.
Qed.

Lemma lctz_or (a : Z) : 0 <= a < 2^64 -> lctz 64 (Z.lor a (2^63)) = Z.min (lctz 64 a) 63.
    Proof.
      intros H.
      assert (Hpos : Z.lor a (2 ^ 63) > 0).
      {
        assert (0 <= Z.lor a (2 ^ 63)) by (apply Z.lor_nonneg; lia).
        assert (Z.lor a (2 ^ 63) <> 0) by (intro Heq; apply Z.lor_eq_0_iff in Heq; lia).
        lia.
      }
      symmetry.
      apply lctz_testbit_2; [ exact Hpos | | ].
      {
        rewrite Z.lor_spec.
        destruct (Z.lt_ge_cases (lctz 64 a) 63) as [Hlt | Hge].
        {
          rewrite (Z.min_l (lctz 64 a) 63) by lia.
          assert (Ha : a > 0).
          {
            destruct (Z.eq_dec a 0) as [-> | Hne]; [ | lia ].
            change (lctz 64 0) with 64 in Hlt.
            lia.
          }
          rewrite lctz_testbit_eq by exact Ha.
          reflexivity.
        }
        {
          rewrite (Z.min_r (lctz 64 a) 63) by lia.
          rewrite (Z.pow2_bits_true 63) by lia.
          apply Bool.orb_true_r.
        }
      }
      {
        intros i Hi.
        rewrite Z.lor_spec.
        rewrite (Z.pow2_bits_false 63 i) by lia.
        assert (Ha_bit : Z.testbit a i = false).
        {
          destruct (Z.eq_dec a 0) as [-> | Ha_pos].
          { apply Z.testbit_0_l. }
          { apply (lctz_testbit_lt 64); [ lia | lia ]. }
        }
        rewrite Ha_bit.
        reflexivity.
      }
    Qed.

Lemma lctz_min (z : Z) : z > 0 -> Z.min (lctz 64 (z mod 2^64)) 63 = Z.min (lctz 64 z) 63.
Proof.
    intros Hz.
    destruct (Z.eq_dec (z mod 2 ^ 64) 0) as [Hmod | Hmod].
    {
    rewrite Hmod.
    change (lctz 64 0) with 64.
    change (Z.min 64 63) with 63.
    symmetry.
    apply Z.min_r.
    destruct (Z.lt_ge_cases (lctz 64 z) 64) as [Hlt | Hge]; [ | lia ].
    pose proof (Z.mod_pow2_bits_low z 64 (lctz 64 z) Hlt) as Hlow.
    rewrite Hmod, Z.testbit_0_l, (lctz_testbit_eq 64 z Hz) in Hlow.
    discriminate Hlow.
    }
    {
    change (2 ^ 64) with (2 ^ Z.of_nat 64%nat) in *.
    rewrite lctz_eq_mod_pow2 by (exact Hz + exact Hmod).
    reflexivity.
    }
Qed.

Lemma lctz_nonneg (default x : Z) : x > 0 -> 0 <= lctz default x.
Proof.
    intros Hx.
    destruct x as [ | p | p ]; [ lia | | lia ].
    cbv [lctz].
    lia.
Qed.

Lemma mod_pow2_divides (x a b : Z) :
      0 <= b <= a -> x mod 2 ^ a = 0 -> x mod 2 ^ b = 0.
Proof.
    intros Hba Hmod.
    assert (Hdiv : (2 ^ b | 2 ^ a)).
    {
    exists (2 ^ (a - b)).
    rewrite <- (Z.pow_add_r 2 (a - b) b) by lia.
    f_equal.
    lia.
    }
    rewrite <- (Z.mod_mod_divide x (2 ^ a) (2 ^ b) Hdiv).
    rewrite Hmod.
    apply Z.mod_0_l.
    intro Heq.
    assert (0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
    lia.
Qed.

Lemma beeu_shrtz_ok : program_logic_goal_for_function! beeu_shrtz.
Proof.
    repeat straightline. lists_into_elements. cbn [array] in *.
    straightline.
    fold (array p_a [a0; a1; a2; a3]) in *.
    fold (array p_y [y0; y1; y2; y3; y4]) in *.
    fold (array p_m [MOD0; MOD1; MOD2; MOD3]) in *.
    straightline_call; eauto; repeat straightline. eexists; ssplit; repeat straightline.
    {
        straightline_call; intuition try ecancel_assumption; try ZnWords.
        { rewrite Properties.word.unsigned_or_nowrap, word.unsigned_slu, !word.unsigned_of_Z in * by ZnWords; cbv [word.wrap] in *;
            rewrite Z.shiftl_mul_pow2, !Z.mod_small in H10 by (try rewrite !Z.mod_small; ZnWords);
            rewrite <- (eval_mod [a1; a2;a3] a0) in H10;
            rewrite lctz_or in H10 by (eapply Z.mod_pos_bound; ZnWords).
            lia.
        }
        repeat straightline. lists_into_elements. cbn [array] in *.
        straightline.
        fold (array p_a [x00; x01; x02; x03]) in *.
        fold (array p_y [y0; y1; y2; y3; y4]) in *.
        fold (array p_m [MOD0; MOD1; MOD2; MOD3]) in *.
        repeat straightline. straightline_call; intuition try ecancel_assumption.
        repeat straightline. straightline_call; intuition try ecancel_assumption.
        all:rewrite Properties.word.unsigned_or_nowrap, word.unsigned_slu, !word.unsigned_of_Z in * by ZnWords; cbv [word.wrap] in *;
        rewrite Z.shiftl_mul_pow2, !Z.mod_small in H10 by (try rewrite !Z.mod_small; ZnWords);
        rewrite <- (eval_mod [a1; a2;a3] a0) in H10;
        rewrite lctz_or in H10 by (eapply Z.mod_pos_bound; ZnWords);
        try ZnWords.
        repeat straightline. eexists _, _, _; intuition try ecancel_assumption.
        {
            rewrite H13, H10, Z.shiftr_div_pow2, lctz_min by ZnWords.
            rewrite ZLib.Z.div_mul_undo; try ZnWords;
            pose proof (lctz_nonneg 64 (eval [a0;a1;a2;a3]) H9); try lia.
            eapply mod_pow2_divides with (a := (lctz 64 (eval [a0;a1;a2;a3]))); ssplit;
            try lia; try eapply Z.min_l. eapply lctz_mod_pow2; lia.
        }
        {
            assert (word.unsigned mask = 2 ^ (Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63) -1).
            {
                cbv [mask] in *.
                rewrite word.unsigned_sub, word.unsigned_slu, <- !word.unsigned_of_Z,
                Properties.word.unsigned_of_Z_1, Z.shiftl_mul_pow2, Z.mul_1_l by ZnWords.
                rewrite H10, lctz_min by ZnWords.
                assert (Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63 <= 63) by (eapply Z.le_min_r).
                assert (0 <= Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63) by (eapply Z.min_glb; [eapply lctz_nonneg | ]; ZnWords).
                assert (0 < 2) by econstructor.
                pose proof (Z.pow_le_mono_r _ _ _ H21 H7).

                rewrite_strat bottomup Properties.word.unsigned_of_Z_nowrap. all: ssplit; try ZnWords.
            }
            assert (Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63 <= 63) by (eapply Z.le_min_r).
            assert (0 <= Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63) by (eapply Z.min_glb; [eapply lctz_nonneg | ]; ZnWords).
            replace (2^320 * x0 + eval x1) with (eval (x1 ++ [x0])) in H15 by
                (lists_into_elements; cbv [app eval] in *; ZnWords).
            rewrite H20, H15 in *.
            rewrite Z.shiftr_div_pow2, H10, lctz_min by ZnWords.
            rewrite ZLib.Z.div_mul_undo; try ZnWords.
            { rewrite Z_mod_plus_full. reflexivity. }
            remember (Z.min (lctz 64 (eval [a0;a1;a2;a3])) 63) as s.
            remember (eval [MOD0; MOD1; MOD2; MOD3]) as MOD.
            assert (word.unsigned v = ((eval [y0; y1; y2; y3; y4]) * inv_m) mod 2^s).
            {
                cbv [v] in *.
                rewrite Properties.word.unsigned_and_nowrap.
                rewrite word.unsigned_mul.
                rewrite Z.sub_1_r, <- Z.ones_equiv in H7.
                cbv [word.wrap]. rewrite H7.
                rewrite Z.land_ones by ZnWords.
                rewrite <- (eval_mod [y1;y2;y3;y4] y0).
                remember (eval [y0;y1;y2;y3;y4]) as y.
                rewrite Zmult_mod_idemp_l.
                rewrite Z.mod_mod_divide; eauto.
                exists (2^(64-s)). rewrite <- Z.pow_add_r by lia.
                f_equal. lia.
            }
            remember (eval [y0;y1;y2;y3;y4]) as y.
            assert ((inv_m * MOD) mod (2^s) = (2^64 - 1) mod (2^s)).
            {
                rewrite <- Z.mod_mod_divide with (b:= 2^64).
                1: f_equal; eauto.
                exists (2^(64-s)); rewrite <- Z.pow_add_r by lia;f_equal; lia.
            }
            rewrite H22, Zplus_mod, Zmult_mod_idemp_l,<- Z.mul_assoc, Z.mul_mod, H23 by lia.
            rewrite <- Z.mul_mod, <- Zplus_mod by lia.
            eapply Zdivisibility.Z.mod0_divide.
            exists (y * 2^(64-s)). rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
            replace (64 - s + s) with 64 by lia.
            lia.
        }
        {
            assert (word.unsigned mask = 2 ^ (Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63) -1).
            {
                cbv [mask] in *.
                rewrite word.unsigned_sub, word.unsigned_slu, <- !word.unsigned_of_Z,
                Properties.word.unsigned_of_Z_1, Z.shiftl_mul_pow2, Z.mul_1_l by ZnWords.
                rewrite H10, lctz_min by ZnWords.
                assert (Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63 <= 63) by (eapply Z.le_min_r).
                assert (0 <= Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63) by (eapply Z.min_glb; [eapply lctz_nonneg | ]; ZnWords).
                assert (0 < 2) by econstructor.
                pose proof (Z.pow_le_mono_r _ _ _ H21 H7).

                rewrite_strat bottomup Properties.word.unsigned_of_Z_nowrap. all: ssplit; try ZnWords.
            }
            assert (v < (2 ^ (Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63))).
            {
                cbv [v] in *.
                rewrite Properties.word.unsigned_and_nowrap, H7.
                rewrite Z.sub_1_r in *.
                rewrite <- Z.ones_equiv in *.
                assert (0 <= Z.min (lctz 64 (eval [a0; a1; a2; a3])) 63).
                {
                    eapply Z.min_glb; [eapply lctz_nonneg | ]; ZnWords.
                }
                rewrite Z.land_ones in * by ZnWords.
                eapply Z.mod_pos_bound; ZnWords.
            }
            replace (2 ^ 320 * x0 + eval x1) with (eval (x1 ++ [x0])) in H15 by
            ( lists_into_elements; cbv [app eval] in *; ZnWords).
            lists_into_elements. cbv [app eval] in *.
            rewrite Z.shiftr_div_pow2, lctz_min, H10 in * by ZnWords.
            rewrite H20.
            eapply Z.le_trans. 1: eapply ZLib.Z.div_mul_undo_le; ZnWords.
            rewrite H15. eapply Zorder.Zplus_le_compat_l, Z.mul_le_mono_nonneg_r; ZnWords.
        }
    }
    {
        eexists _, _, _; intuition try ecancel_assumption.
        all:
            rewrite Properties.word.unsigned_or_nowrap, word.unsigned_slu, !word.unsigned_of_Z in * by ZnWords; cbv [word.wrap] in *;
            rewrite Z.shiftl_mul_pow2, !Z.mod_small in H10 by (try rewrite !Z.mod_small; ZnWords);
            rewrite <- (eval_mod [a1; a2;a3] a0), H6 in H10;
            rewrite lctz_or in H10 by (eapply Z.mod_pos_bound; ZnWords);
            destruct (Z.min_dec (lctz 64 (eval [a0; a1;a2;a3] mod (2^64))) 63) as [e | e];
            rewrite e in H10; try discriminate; rewrite <- (lctz_eq_mod_pow2 _ _ 64%nat) by
            ( try assumption;
              rewrite eval_mod in *; intros contra; rewrite contra in *; discriminate
            );
            replace (Z.of_nat 64) with 64 by lia;
            rewrite <- H10;
            rewrite Z.min_l by lia;
            try f_equal; lia.
    }
Qed.

(** * Linking Proof *)
Definition beeu_shrtz_funcs := &[, beeu_shrtz; u320_muladd; u320_shr; u256_shr; br_ctz; br_full_add; br_full_mul].

Lemma link_full_beeu_shrtz :
    spec_of_beeu_shrtz (Interface.map.of_list beeu_shrtz_funcs).
Proof.
    apply beeu_shrtz_ok;
    try (apply br_ctz_ok || apply u256_shr_correct ||
        apply u320_muladd_correct || apply u320_shr_correct);
    try (apply full_mul_ok || apply full_add_ok);
    trivial.
Qed.

