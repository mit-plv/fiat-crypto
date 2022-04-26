Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Crypto.PushButtonSynthesis.SaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Crypto.Stringification.C.
Require Crypto.Stringification.Go.
Require Crypto.Stringification.Java.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Coq.ZArith.Znat.

Require Import Crypto.Util.Notations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations. Local Open Scope Z_scope.

Import
  AbstractInterpretation.Compilers
  Language.Compilers
  Language.API.Compilers.

Import Language.API.Compilers.API.

Import Associational Positional.

Local Existing Instance default_low_level_rewriter_method.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := None.
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.

Local Existing Instance default_output_options.

Module solinas_reduction.

  Import Crypto.Arithmetic.Saturated.

  Section __.

    Context weight {wprops : @weight_properties weight}.

    Definition sat_reduce base s c n (p : list (Z * Z)) :=
      let '(s', _) := Saturated.Rows.adjust_s weight (S (S n)) s in
      let lo_hi := Associational.split s' p in
      let coef := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let hi := Saturated.Associational.sat_mul_const base coef (snd lo_hi) in
      let r := (fst lo_hi) ++ hi in
      r.

    Lemma adjust_s_invariant fuel s (s_nz:s<>0) :
      fst (Saturated.Rows.adjust_s weight fuel s) mod s = 0
      /\ fst (Saturated.Rows.adjust_s weight fuel s) <> 0.
    Proof using wprops.
      cbv [Saturated.Rows.adjust_s]; rewrite fold_right_map; generalize (List.rev (seq 0 fuel)); intro ls; induction ls as [|l ls IHls];
        cbn.
      { rewrite Z.mod_same by assumption; auto. }
      { break_match; cbn in *; auto with zarith. }
    Qed.

    Hint Rewrite Saturated.Associational.eval_sat_mul : push_eval.
    Hint Rewrite Saturated.Associational.eval_sat_mul_const using (lia || assumption) : push_eval.
    Hint Rewrite eval_split using solve [auto] : push_eval.

    Lemma eval_sat_reduce base s c n p :
      base <> 0
      -> s - Associational.eval c <> 0
      -> s <> 0
      -> Associational.eval (sat_reduce base s c n p) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
    Proof using wprops.
      intros; cbv [sat_reduce].
      lazymatch goal with
      | |- context[Saturated.Rows.adjust_s ?weight ?fuel ?s] =>
          destruct (adjust_s_invariant fuel s ltac:(assumption)) as [Hmod ?]
      end.
      eta_expand; autorewrite with push_eval zsimplify_const; cbn [fst snd].
      rewrite <- (Z.mul_comm (Associational.eval c)), <- !Z.mul_assoc, <-Associational.reduction_rule by auto.
        autorewrite with zsimplify_const; rewrite !Z.mul_assoc, Z.mul_div_eq_full, Hmod by auto.
        autorewrite with zsimplify_const push_eval; trivial.
    Qed.
    Hint Rewrite eval_sat_reduce using auto : push_eval.

    (* n is input width *)
    Definition reduce1 base s c n (p : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let r_a := sat_reduce base s c n p_a in
      let r_rows := Saturated.Rows.from_associational weight n r_a in
      let r_flat := Saturated.Rows.flatten weight n r_rows in
      fst r_flat.

    Definition reduce base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) p in
      let r2 := reduce1 base s c (2*n) (r1) in
      let r3 := reduce1 base s c (2*n) (r2) in
      r3.

    Definition reduce' base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) p in
      let r2 := reduce1 base s c (2*n) (r1) in
      let r3 := reduce1 base s c (2*n) (r2) in
      r1.

    Definition mul_no_reduce base n (p q : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      fst pq.

    Definition mulmod base s c n (p q : list Z) :=
      let prod := mul_no_reduce base n p q in
      let red := reduce base s c n prod in
      red.

    Definition valid_number n (p : list Z) : Prop :=
      length p = n /\
        p = Partition.partition weight n (Positional.eval weight n p).

    Hint Rewrite Saturated.Rows.eval_from_associational using auto : push_eval.

    Lemma eval_mod_eq base s c n p :
      Rows.eval weight n
           (Rows.from_associational weight n
                                 (sat_reduce base s c n (to_associational weight n p))) < weight n.
    Proof.
      Search Saturated.Rows.eval.
      intros.
      autorewrite with push_eval.
      Search Associational.eval.
    Admitted.

    Hint Resolve length_partition : push_length.
    Hint Resolve Rows.length_from_associational : push_length.

    Lemma reduce_valid_number base s c n : forall (p : list Z),
        valid_number n (reduce1 base s c n p).
    Proof using wprops.
      intros.
      unfold reduce1 in *.
      unfold valid_number.
      rewrite Saturated.Rows.flatten_correct; auto.
      { intuition.
        { cbn [fst].
          auto with push_length. }
        { simpl.
          rewrite Partition.eval_partition; auto.
          f_equal.
          apply Z.mod_small_sym.
          intuition.
          Search Associational.eval 0.
          admit.
          apply eval_mod_eq. }
      }
      { intros.
        eauto with push_length. }
    Admitted.

    Theorem reduce_second base s c n : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        (valid_number weight n p /\ hi <= 39) ->
        forall q_lo q_hi1 q_hi2,
          let q := reduce1 base s c n p in
          q = q_lo ++ [q_hi1] ++ [q_hi2] ->
          (valid_number weight n q /\
             ((q_hi2 = 1 /\ q_hi1 = 0) \/
                (q_hi2 = 0))).
    Proof using wprops.
      intros.
      intuition.
      { unfold valid_number in *.
        Search Partition.partition eval.
    Admitted.

  End __.

End solinas_reduction.
